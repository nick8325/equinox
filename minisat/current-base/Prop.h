/******************************************************************************************[Prop.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Prop_h
#define Prop_h

#include "Map.h"
#include "Solver.h"


//=================================================================================================
// Node structure

enum { node_and = 0, node_equ = 1, node_ite = 2, node_carry = 3, node_sum = 4, node_atom = 5, node_reintroduced = 6 };

class Node {
    unsigned data[3];

public:
    Node (unsigned type = node_atom, Lit x = lit_Undef, Lit y = lit_Undef, Lit z = lit_Undef){
        unsigned t0 = type&1;
        unsigned t1 = (type>>1)&1;
        unsigned t2 = (type>>2)&1;
        data[0] = (toInt(x) << 1) | t0;
        data[1] = (toInt(y) << 1) | t1;
        data[2] = (toInt(z) << 1) | t2;
    }

    unsigned type ()                   const { return (data[0]&1) | ((data[1]&1)<<1) | ((data[2]&1)<<2); }
    Lit      operator[](int i)         const { return toLit(data[i]>>1); }
    bool     operator==(const Node& n) const { return data[0] == n.data[0] && data[1] == n.data[1] && data[2] == n.data[2]; }
    friend inline uint32_t hash(const Node& n);
};

inline uint32_t hash(const Node& n){ return n.data[0] ^ n.data[1] ^ n.data[2]; }

//=================================================================================================
// To enable constant propagation define two constant literals (steals one variable)

const Lit lit_True  (0, false);
const Lit lit_False (0, true); 

//=================================================================================================
// PropSolver -- the solver class extended with support for propositional formulas
        
class PropSolver : public Solver {

    Map<Node, Var> unique;
    vec<Node>      nodes;

    Var  mkNode (const Node& n) {
        Var v = newVar();
        while (nodes.size() <= v) nodes.push();
        nodes [v] = n;
        unique.insert(n,v);
        return v; }

    template <class T> static inline void swap(T& x, T& y) { T tmp = x; x = y; y = tmp; }

 public:

    PropSolver(char* log = NULL) : Solver(log) { 
        // Leave room for lit_True and lit_False
        newVar(); 
        setVarProp(0, p_decisionvar, false); 
        addClause(lit_True); } 
    ~PropSolver(){
        if (logfile != NULL)
            fclose(logfile); }

    bool addClause (vec<Lit>& ps){
        if (logfile != NULL) { 
            if (ps.size() > 0){
                logLit(logfile, ps[0]);
                for (int i = 1; i < ps.size(); i++){
                    fprintf(logfile, " | ");
                    logLit(logfile, ps[i]);
                }
            }else
                fprintf(logfile, "0");

            fprintf(logfile, "\n"); }

        return Solver::addClause(ps);
    }

    bool solve (vec<Lit>& ps, bool do_simplify = true){
        if (logfile) { fprintf(logfile, "solve "); logLits(logfile, ps); fprintf(logfile, "\n"); }

        return Solver::solve(ps, do_simplify);
    }

    bool    simplify     (bool do_elimination = false, bool turn_off_subsumption = false){
#ifndef NDEBUG
        if (logfile != NULL)
            fprintf(logfile, "simplify(%s,%s)\n", showBool(do_elimination), showBool(turn_off_subsumption));
#endif
        return Solver::simplify(do_elimination, turn_off_subsumption);
    }

    void freezeVar (Var v) { 
        Solver::freezeVar(v); }
    void unfreezeVar (Var v) { 
        Solver::unfreezeVar(v); }

    bool solve (Lit l, bool do_simplify = true) { vec<Lit> tmp; tmp.push(l); return solve(tmp, do_simplify); }

    bool addClause (Lit x) { add_tmp.clear(); add_tmp.push(x); return addClause(add_tmp); }
    bool addClause (Lit x, Lit y) { add_tmp.clear(); add_tmp.push(x); add_tmp.push(y); return addClause(add_tmp); }
    bool addClause (Lit x, Lit y, Lit z) { add_tmp.clear(); add_tmp.push(x); add_tmp.push(y); add_tmp.push(z); return addClause(add_tmp); }
    bool addClause (Lit x, Lit y, Lit z, Lit w) { add_tmp.clear(); add_tmp.push(x); add_tmp.push(y); add_tmp.push(z); add_tmp.push(w); return addClause(add_tmp); }

    Lit  mkLit () { return Lit(newVar()); }
    Lit  mkAnd (Lit f, Lit g);
    Lit  mkEqu (Lit f, Lit g);
    Lit  mkOr  (Lit f, Lit g) { return ~mkAnd(~f, ~g); }
    Lit  mkImp (Lit f, Lit g) { return ~mkAnd(f, ~g); }
    Lit  mkXor (Lit f, Lit g) { return ~mkEqu(f,g); }
    Lit  mkIte (Lit c, Lit t, Lit f);
    void mkAdd (Lit a, Lit b, Lit c, Lit& carry, Lit& sum);
};

#endif
