/****************************************************************************************[Solver.h]
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

#ifndef Solver_h
#define Solver_h

//#define COMPETITION

#include <cstdio>
#include <stdint.h>

struct SolverStats {
    uint64_t starts, decisions, rnd_decisions, propagations, conflicts;
    uint64_t clauses_literals, learnts_literals, max_literals, tot_literals;
    uint64_t asymm_lits;
    uint64_t remembered_clauses;
    uint64_t subsumption_checks, subsumption_misses, merges;
    SolverStats() : 
        starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
      , clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0) 
      , asymm_lits (0)
      , remembered_clauses(0)
      , subsumption_checks(0), subsumption_misses(0), merges(0)
    { }
};


struct SearchParams {
    double  var_decay, clause_decay, random_var_freq;
    double  restart_inc, learntsize_inc, learntsize_factor;
    int     restart_first;
    
    SearchParams(double v = 0.95, double c = 0.999, double r = 0.02,
                 double ri = 1.5, double li = 1.1, double lf = (double)1/(double)3,
                 int rf = 100) : 
        var_decay(1 / v), clause_decay(1 / c), random_var_freq(r),
        restart_inc(ri), learntsize_inc(li), learntsize_factor(lf),
        restart_first(rf) { }
};

//#include "AltVec.h"
#include "Vec.h"
//#define Vec_h
//#define vec altvec

#include "Alg.h"

#include "SolverTypes.h"
#include "VarOrder.h"


//=================================================================================================
// Local helpers:

static inline void logLit(FILE* f, Lit l)
{
    fprintf(f, "%sx%d", sign(l) ? "~" : "", var(l)+1);
}

static inline void logLits(FILE* f, const vec<Lit>& ls)
{
    fprintf(f, "[ ");
    if (ls.size() > 0){
        logLit(f, ls[0]);
        for (int i = 1; i < ls.size(); i++){
            fprintf(f, ", ");
            logLit(f, ls[i]);
        }
    }
    fprintf(f, "] ");
}

static inline const char* showBool(bool b) { return b ? "true" : "false"; }


//=================================================================================================
// Solver -- the main class:


class Solver {

    struct ElimData {
        int          order;      // 0 means not eliminated, >0 gives an index in the elimination order
        vec<Clause*> eliminated;
        ElimData() : order(0) {} };

    struct ElimOrderLt {
        const vec<ElimData>& elimtable;
        ElimOrderLt(const vec<ElimData>& et) : elimtable(et) {}
        bool operator()(Var x, Var y) { return elimtable[x].order > elimtable[y].order; } };

    struct ElimLt {
        const vec<int>& n_occ;
        ElimLt(const vec<int>& no) : n_occ(no) {}
        int  cost      (Var x)        const { return n_occ[toInt(Lit(x))] * n_occ[toInt(~Lit(x))]; }
        bool operator()(Var x, Var y) const { return cost(x) < cost(y); } };

protected:
    // Solver state:
    //
    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    vec<Clause*>        clauses;          // List of problem clauses.
    vec<Clause*>        learnts;          // List of learnt clauses.
    double              cla_inc;          // Amount to bump next clause with.

    vec<double>         activity;         // A heuristic measurement of the activity of a variable.
    double              var_inc;          // Amount to bump next variable with.
    VarOrder            order;            // Keeps track of the decision variable order.

    vec<vec<Clause*> >  watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    vec<char>           assigns;          // The current assignments (lbool:s stored as char:s).
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<Clause*>        reason;           // 'reason[var]' is the clause that implied the variables current value, or 'NULL' if none.
    vec<TrailPos>       trailpos;         // 'trailpos[var]' contains the position in the trail at wich the assigment was made.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    int                 elimorder;

    bool                subsumption;      // Simplification related data structures
    vec<ElimData>       elimtable;        
    vec<char>           touched;
    vec<vec<Clause*> >  occurs;
    vec<int>            n_occ;
    Heap<ElimLt>        heap;
    vec<Clause*>        subsumption_queue;

    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.

    FILE*               logfile;

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    vec<char>           seen;
    vec<Lit>            analyze_stack;
    vec<Lit>            analyze_toclear;
    Clause*             propagate_tmpempty;
    Clause*             propagate_tmpbin;
    Clause*             analyze_tmpbin;
    Clause*             bwdsub_tmpunit;
    vec<Lit>            add_tmp;

    // Main internal methods:
    //
    bool        assume           (Lit p);
    void        cancelUntil      (int level);
    void        record           (const vec<Lit>& clause);

    void        analyze          (Clause* confl, vec<Lit>& out_learnt, int& out_btlevel); // (bt = backtrack)
    bool        analyze_removable(Lit p, unsigned int min_level);                         // (helper method for 'analyze()')
    void        analyzeFinal     (Lit p, vec<Lit>& out_conflict);
    bool        enqueue          (Lit fact, Clause* from = NULL);
    Clause*     propagate        ();
    void        reduceDB         ();
    Lit         pickBranchLit    ();
    lbool       search           (int nof_conflicts, int nof_learnts);
    double      progressEstimate ();

    bool        asymm            (Var v, Clause& c);
    bool        asymmVar         (Var v);

    // Variable properties:
    void        setVarProp (Var v, int prop, bool b) { order.setVarProp(v, prop, b); }
    bool        hasVarProp (Var v, int prop) const   { return order.hasVarProp(v, prop); }
    void        updateHeap (Var v) { 
        if (elimtable[v].order == 0)
            heap.update(v); }

    // Simplification methods:
    //

    void cleanOcc (Var v){
        assert(subsumption);
        Clause **begin = (Clause**)occurs[v];
        Clause **end = begin + occurs[v].size();
        Clause **i, **j;
        for (i = begin, j = end; i < j; i++)
            if ((*i)->mark() == 1){
                *i = *(--j);
                i--;
            }
        //occurs[v].shrink_(end - j);  // varför blir detta långsammare?
        occurs[v].shrink(end - j);
    }

    vec<Clause*>& getOccurs                (Var x) { cleanOcc(x); return occurs[x]; }
    void          gather                   (vec<Clause*>& clauses);
    Lit           subsumes                 (const Clause& c, const Clause& d) const;
    bool          merge                    (const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause);
    bool          merge                    (const Clause& _ps, const Clause& _qs, Var v);
    
    bool          backwardSubsumptionCheck (bool verbose = false);
    bool          eliminateVar             (Var v, bool fail = false);
    void          remember                 (Var v);
    bool          eliminate                ();
    void          extendModel              ();
    void          verifyModel              ();

    void          watchRelevant();


    // Activity:
    //
    void     varBumpActivity(Lit p) {
        if ( (activity[var(p)] += var_inc) > 1e100 ) varRescaleActivity();
        order.update(var(p)); }
    void     varDecayActivity  () { var_inc *= params.var_decay; }
    void     varRescaleActivity();
    void     claDecayActivity  () { cla_inc *= params.clause_decay; }
    void     claRescaleActivity();

    // Operations on clauses:
    //
    bool     newClause(const vec<Lit>& ps, bool learnt = false, bool normalized = false);
    void     claBumpActivity (Clause& c) { if ( (c.activity() += cla_inc) > 1e20 ) claRescaleActivity(); }
    //bool     locked          (const Clause& c) const { return reason[var(c[0])] == &c; }
    bool     locked          (const Clause& c) const { return reason[var(c[0])] == &c && value(c[0]) == l_True; }
    bool     satisfied       (const Clause& c) const;
    bool     strengthen      (Clause& c, Lit l);
    void     removeClause    (Clause& c, bool dealloc = true);

    int      decisionLevel() const { return trail_lim.size(); }

public:
    Solver(char* log = NULL) :
               ok               (true)
             , cla_inc          (1)
             , var_inc          (1)
             , order            (stats, assigns, activity)
             , qhead            (0)
             , simpDB_assigns   (-1)
             , simpDB_props     (0)
             , elimorder        (1)
             , subsumption      (true)
             , heap             (n_occ)
             , logfile          (NULL)
             , params           ()
             , grow             (0)
             , expensive_ccmin  (true)
             , rnd_mode         (rnd_anyheap)
             , polarity_mode    (polarity_false)
             , asymm_mode       (false)
             , verbosity        (0)
             , progress_estimate(0)
             {
                vec<Lit> dummy(2,lit_Undef);
                propagate_tmpbin   = Clause_new(dummy);
                analyze_tmpbin     = Clause_new(dummy);
                dummy.pop();
                bwdsub_tmpunit     = Clause_new(dummy);
                dummy.pop();
                propagate_tmpempty = Clause_new(dummy);
                if (log != NULL){
                    logfile = fopen(log, "w");
                    if (logfile == NULL){
                        fprintf(stderr, "failed to open log-file: %s\n", log);
                        fprintf(stderr, "aborting\n");
                        exit(-1); }
                }
             }

   ~Solver() {
       free(propagate_tmpbin);
       free(analyze_tmpbin);
       free(bwdsub_tmpunit);
       free(propagate_tmpempty);
       for (int i = 0; i < learnts.size();    i++) free(learnts[i]);
       for (int i = 0; i < clauses.size();    i++) free(clauses[i]); 

       //for (int i = 0; i < nVars(); i++)
       // NOTE: elimtable.size() might be lower than nVars() at the moment
       for (int i = 0; i < elimtable.size(); i++)
           for (int j = 0; j < elimtable[i].eliminated.size(); j++)
               free(elimtable[i].eliminated[j]);
   }

    // Helpers: (semi-internal)
    //
    lbool   value(Var x) const { return toLbool(assigns[x]); }
    //lbool   value(Lit p) const { return sign(p) ? ~toLbool(assigns[var(p)]) : toLbool(assigns[var(p)]); }
    lbool   value(Lit p) const { return toLbool(assigns[var(p)]) ^ sign(p); }

    int     nAssigns    () { return trail.size(); }
    int     nClauses    () { return clauses.size(); }
    int     nLearnts    () { return learnts.size(); }
    int     nConflicts  () { return (int)stats.conflicts; }
    int     nRemembered () { return (int)stats.remembered_clauses; }
    int     nVars       () { return assigns.size(); }

    // Statistics: (read-only member variable)
    //
    SolverStats     stats;

    // Mode of operation:
    //
    SearchParams    params;             // Restart frequency etc.
    int             grow;               // Allow a simplification step to grow by a number of clauses (default to zero).
    bool            expensive_ccmin;    // Controls conflict clause minimization. TRUE by default.
    int             rnd_mode;
    int             polarity_mode;
    bool            asymm_mode;
    int             verbosity;          // Verbosity level. 0=silent, 1=some progress report, 2=everything

    // Problem specification:
    //
    Var     newVar    (bool polarity = true, bool dvar = true);
    bool    addClause (const vec<Lit>& ps)  { if (ok && (!newClause(ps) || propagate() != NULL )) ok = false; return ok; }
    //bool    addClause (const vec<Lit>& ps)  { if (ok && (!newClause(ps))) ok = false; return ok; }
    bool    addClause (Lit x) { add_tmp.clear(); add_tmp.push(x); return addClause(add_tmp); }
    bool    addClause (Lit x, Lit y) { add_tmp.clear(); add_tmp.push(x); add_tmp.push(y); return addClause(add_tmp); }
    bool    addClause (Lit x, Lit y, Lit z) { add_tmp.clear(); add_tmp.push(x); add_tmp.push(y); add_tmp.push(z); return addClause(add_tmp); }
    bool    addClause (Lit x, Lit y, Lit z, Lit w) { add_tmp.clear(); add_tmp.push(x); add_tmp.push(y); add_tmp.push(z); add_tmp.push(w); return addClause(add_tmp); }

    // Variable mode:
    // 
    void    freezeVar    (Var v) { 
        setVarProp(v, p_frozen, true); }
    void    unfreezeVar  (Var v) { 
        setVarProp(v, p_frozen, false); updateHeap(v); }
    
    bool    varElimed      (Var v) { return elimtable[v].order > 0; }

    void    setPolarity    (Var v, bool b) { setVarProp(v, p_polarity, b); }
    void    setDecisionVar (Var v, bool b) { setVarProp(v, p_decisionvar, b); }
    
    bool    hasSubsumption() { return subsumption; }

    // Solving:
    //
    bool    simplify     (bool do_elimination = true, bool turn_off_subsumption = false);
    bool    okay         () { return ok; }       // FALSE means solver is in a conflicting state
    bool    solve        (const vec<Lit>& assumps, bool simplify = true);
    bool    solve        (bool simplify = true) { vec<Lit> tmp; return solve(tmp, simplify); }
    bool    solve        (Lit l, bool simplify = true) { vec<Lit> tmp; tmp.push(l); return solve(tmp, simplify); }

    double      progress_estimate;  // Set by 'search()'.
    vec<lbool>  model;              // If problem is satisfiable, this vector contains the model (if any).
    vec<Lit>    conflict;           // If problem is unsatisfiable (possibly under assumptions), this vector represent the conflict clause expressed in the assumptions.

    // !!! VERY TEMPORARY !!!
    bool&      ok_ref() { return ok; }
    vec<char>& assigns_ref() { return assigns; }
    vec<Lit>&  trail_ref() { return trail; }

    inline void printLit(Lit l);
    template<class C>
    inline void printClause(const C& c);
};


#ifdef COMPETITION
#define reportf(format, args...) ( fprintf(stdout, "c " format, ## args), fflush(stdout) )
#else
#define reportf(format, args...) ( fflush(stdout), fprintf(stderr, format, ## args), fflush(stderr) )
#endif

//=================================================================================================
// Debug:


// Just like 'assert()' but expression will be evaluated in the release version as well.
static inline void check(bool expr) { assert(expr); }

inline void Solver::printLit(Lit l)
{
    reportf("%s%d:%c", sign(l) ? "-" : "", var(l)+1, value(l) == l_True ? '1' : (value(l) == l_False ? '0' : 'X'));
}

template<class C>
inline void Solver::printClause(const C& c)
{
    for (int i = 0; i < c.size(); i++){
        printLit(c[i]);
        fprintf(stderr, " ");
    }
}


//=================================================================================================
#endif
