/* ---------------------------------------------------------------
-- Paradox, a Finite Domain Model Finder for First Order Logic  --
-- Copyright (c) 2003 Koen Claessen and Niklas Sörensson        --
-- {koen,nik}@cs.chalmers.se                                    --
--                                                              --
-- This file is part of Paradox.                                --
--                                                              --
-- Paradox is free software; you can redistribute it and/or     --
-- modify it under the terms of the GNU General Public License  --
-- as published by the Free Software Foundation; either version --
-- 2 of the License, or (at your option) any later version.     --
--                                                              --
-- Paradox is distributed in the hope that it will be useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty  --
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See  --
-- the GNU General Public License for more details.             --
--                                                              --
-- You should have received a copy of the GNU General Public    --
-- License along with Paradox; if not, write to the Free        --
-- Software Foundation, Inc., 59 Temple Place, Suite 330,       --
-- Boston, MA 02111-1307 USA.                                   --
--------------------------------------------------------------- */


#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

#include "Prop.h"
#include "MiniSatInstantiateClause.h"

struct solver : public PropSolver { 
    vec<Lit> tmp;
    int*     contr;
    vec<Lit> prefix;
    FOClause clause;
    Loc*     loc;
    uint     sig;
    vec<int> args;
    vec<int> dummy;

    solver(char* log) : PropSolver(log), contr(NULL), loc(NULL) {}
    ~solver() { delete [] contr; delete loc; }
};

static inline Lit fromDimacs (int l) { int neg = l < 0; return Lit( (neg ? -l : l) - 1, neg); }
static inline int toDimacs   (Lit l) { Var v = var(l)+1; return sign(l) ? -v : v; }

extern "C" {

    const int lit_true  =  1;
    const int lit_false = -1;

    const int l_true  = toInt(l_True);
    const int l_false = toInt(l_False);
    const int l_undef = toInt(l_Undef);

    solver* s_new    (char* log) { return new solver(log); }
    void    s_delete (solver* s) { delete s; }

    int     s_newlit (solver* s) { return toDimacs(s->mkLit()); }

    int s_clause (solver* s, int* ls)
    {
        s->tmp.clear();
        for (int i = 0; ls[i] != 0; i++)
            s->tmp.push(fromDimacs(ls[i]));

        return s->addClause(s->tmp);
    }
    
    int s_solve (solver* s, int do_simplify, int* ls)
    {
        s->tmp.clear();
        for (int i = 0; ls[i] != 0; i++)
            s->tmp.push(fromDimacs(ls[i]));

        return s->solve(s->tmp, do_simplify);
    }

    int s_vclause (solver* s, ...)
    {
        va_list argp;
        va_start (argp, s);

        int l;
        s->tmp.clear();
        while ( (l = va_arg(argp, int)) != 0)
            s->tmp.push(fromDimacs(l));
        va_end(argp);        

        return s->addClause(s->tmp);
    }


    int s_vsolve (solver* s, int do_simplify, ...)
    {
        va_list argp;
        va_start (argp, do_simplify);
        
        int l;
        s->tmp.clear();
        while ( (l = va_arg(argp, int)) != 0)
            s->tmp.push(fromDimacs(l));
        va_end(argp);        

        return s->solve(s->tmp, do_simplify);
    }

    int     s_simplify      (solver* s, int elim, int turnoffelim) { return s->simplify(elim, turnoffelim); }
    void    s_freezelit     (solver* s, int l) { return s->freezeVar(var(fromDimacs(l))); }
    void    s_unfreezelit   (solver* s, int l) { return s->unfreezeVar(var(fromDimacs(l))); }
    void    s_setpolarity   (solver* s, int l) { s->setPolarity(var(fromDimacs(l)), sign(fromDimacs(l))); }
    void    s_setdecisionvar(solver* s, int l, int b) { s->setDecisionVar(var(fromDimacs(l)), b); }
    int     s_value         (solver* s, int l) { return toInt(s->value(fromDimacs(l))); }

    int     s_and           (solver* s, int x, int y) { return toDimacs(s->mkAnd(fromDimacs(x), fromDimacs(y))); }
    int     s_or            (solver* s, int x, int y) { return toDimacs(s->mkOr(fromDimacs(x), fromDimacs(y))); }
    int     s_equ           (solver* s, int x, int y) { return toDimacs(s->mkEqu(fromDimacs(x), fromDimacs(y))); }
    int     s_xor           (solver* s, int x, int y) { return toDimacs(s->mkXor(fromDimacs(x), fromDimacs(y))); }
    int     s_ite           (solver* s, int c, int t, int f) { return toDimacs(s->mkIte(fromDimacs(c), fromDimacs(t), fromDimacs(f))); }
    void    s_add           (solver* s, int a, int b, int c, int* carry, int* sum){
        Lit _carry, _sum;
        s->mkAdd(fromDimacs(a), fromDimacs(b), fromDimacs(c),_carry,_sum);
        *carry = toDimacs(_carry);
        *sum   = toDimacs(_sum);
    }

    int     s_okay       (solver* s)        { return s->okay(); }
    int     s_modelvalue (solver* s, int l) { return (bool)((s->model[var(fromDimacs(l))] == l_True) ^ sign(fromDimacs(l))); }


    int*    s_contr (solver* s)
    {
        delete [] s->contr;
        s->contr = new int[s->conflict.size()+1];
        for (int i = 0; i < s->conflict.size(); i++)
            s->contr[i] = toDimacs(s->conflict[i]);
        s->contr[s->conflict.size()] = 0;
        return s->contr;
    }

    void s_verbose       (solver* s, int l) { s->verbosity = l; }

    int s_nvars      (solver* s) { return s->nVars(); }
    int s_nclauses   (solver* s) { return s->nClauses(); }
    int s_nconflicts (solver* s) { return s->nConflicts(); }
    int s_nremembered(solver* s) { return s->nRemembered(); }


    Loc*     loc_new    (int a)  { Loc* l = (Loc*)malloc(sizeof(Loc)); new (l) Loc(a); return l; }
    void     loc_free   (Loc* l) { free(l); }
    int      loc_arity  (Loc* l) { return l->getArity(); }

    // build a clause
    void solver_clause_begin       (solver* w)                 { w->clause.clear();}
    void solver_clause_add_lit     (solver* w, Loc* l, uint s) { w->clause.addLit(l,(bool)s); }
    void solver_clause_add_lit_var (solver* w, int v)          {
        w->clause.lastLit().addArg(varArg(v-1));}
    void solver_clause_add_lit_con (solver* w, int c)          { 
        w->clause.lastLit().addArg(conArg(c-1));}
    void solver_clause_add_size    (solver* w, int s)          { w->clause.addSize(s); }
    uint solver_clause_commit      (solver* w, int fresh)      { 
        return w->clause.instantiate(*w, fresh) ? 1 : 0; }

    // setting a literal to be read or assumed during solving
    void solver_lit_begin   (solver* w, Loc* l, int sign)  { 
        w->args.clear(); w->loc = l; w->sig = sign; }
    void solver_lit_add_con (solver* w, int c)              { w->args.push(conArg(c-1)); }

    // reading the value of a predicate (location)
    int solver_lit_read     (solver* w) { 
        // creates variables if they don't exists!! (fix?)
        return toDimacs(Lit(w->loc->get(*w, w->args, w->dummy), !w->sig)); 
    }
}
