/***************************************************************************************[minisat.h]
Copyright (c) 2008-2011, Niklas Sorensson
              2008, Koen Claessen

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

#ifndef Minisat_C_Bindings_h
#define Minisat_C_Bindings_h

// SolverTypes:
//
typedef struct minisat_solver_t minisat_solver;
#ifdef Minisat_Opaque
#define opaque(x) struct { x f; }
#else
#define opaque(x) x
#endif
typedef opaque(int) minisat_Var;
typedef opaque(int) minisat_Lit;
typedef opaque(int) minisat_lbool;
typedef opaque(int) minisat_bool; // Only for clarity in the declarations below (this is just a plain c-bool).
#undef opaque

// Constants: (can these be made inline-able?)
//

extern "C" {

extern const minisat_lbool minisat_l_True;
extern const minisat_lbool minisat_l_False;
extern const minisat_lbool minisat_l_Undef;


minisat_solver* minisat_new             (void);
void            minisat_delete          (minisat_solver* s);
             
minisat_Var     minisat_newVar          (minisat_solver *s);
minisat_Lit     minisat_newLit          (minisat_solver *s);
             
minisat_Lit     minisat_mkLit           (minisat_Var x);
minisat_Lit     minisat_mkLit_args      (minisat_Var x, int sign);
minisat_Lit     minisat_negate          (minisat_Lit p);
                                    
minisat_Var     minisat_var             (minisat_Lit p);
minisat_bool    minisat_sign            (minisat_Lit p);
             
minisat_bool    minisat_addClause       (minisat_solver *s, int len, minisat_Lit *ps);
void            minisat_addClause_begin (minisat_solver *s);
void            minisat_addClause_addLit(minisat_solver *s, minisat_Lit p);
minisat_bool    minisat_addClause_commit(minisat_solver *s);
             
minisat_bool    minisat_simplify        (minisat_solver *s);
             
minisat_bool    minisat_solve           (minisat_solver *s, int len, minisat_Lit *ps);
minisat_lbool   minisat_limited_solve   (minisat_solver *s, int len, minisat_Lit *ps);
void            minisat_solve_begin     (minisat_solver *s);
void            minisat_solve_addLit    (minisat_solver *s, minisat_Lit p);
minisat_bool    minisat_solve_commit    (minisat_solver *s);
minisat_lbool   minisat_limited_solve_commit
                                        (minisat_solver *s);
             
minisat_bool    minisat_okay            (minisat_solver *s);
             
void            minisat_setPolarity     (minisat_solver *s, minisat_Var v, int b);
void            minisat_setDecisionVar  (minisat_solver *s, minisat_Var v, int b);

minisat_lbool   minisat_get_l_True      (void);
minisat_lbool   minisat_get_l_False     (void);
minisat_lbool   minisat_get_l_Undef     (void);

minisat_lbool   minisat_value_Var       (minisat_solver *s, minisat_Var x);
minisat_lbool   minisat_value_Lit       (minisat_solver *s, minisat_Lit p);
minisat_lbool   minisat_modelValue_Var  (minisat_solver *s, minisat_Var x);
minisat_lbool   minisat_modelValue_Lit  (minisat_solver *s, minisat_Lit p);

int             minisat_num_assigns     (minisat_solver *s);
int             minisat_num_clauses     (minisat_solver *s);     
int             minisat_num_learnts     (minisat_solver *s);     
int             minisat_num_vars        (minisat_solver *s);  
int             minisat_num_freeVars    (minisat_solver *s);

int             minisat_conflict_len    (minisat_solver *s);
minisat_Lit     minisat_conflict_nthLit (minisat_solver *s, int i);

void            minisat_set_conf_budget (minisat_solver* s, int x);
void            minisat_set_prop_budget (minisat_solver* s, int x);
void            minisat_no_budget       (minisat_solver* s);

// Resource constraints:
void minisat_interrupt(minisat_solver* s);
void minisat_clearInterrupt(minisat_solver* s);

// SimpSolver methods:
void            minisat_setFrozen       (minisat_solver* s, minisat_Var v, minisat_bool b);
minisat_bool    minisat_isEliminated    (minisat_solver* s, minisat_Var v);
minisat_bool    minisat_eliminate       (minisat_solver* s, minisat_bool turn_off_elim);

// Setters:

void            minisat_set_verbosity   (minisat_solver *s, int v);

// Getters:

int             minisat_num_conflicts   (minisat_solver *s);
int             minisat_num_decisions   (minisat_solver *s);
int             minisat_num_restarts    (minisat_solver *s);
int             minisat_num_propagations(minisat_solver *s);

/* TODO

    // Mode of operation:
    //
    int       verbosity;
    double    var_decay;
    double    clause_decay;
    double    random_var_freq;
    double    random_seed;
    double    restart_luby_start; // The factor with which the values of the luby sequence is multiplied to get the restart    (default 100)
    double    restart_luby_inc;   // The constant that the luby sequence uses powers of                                        (default 2)
    bool      expensive_ccmin;    // FIXME: describe.
    bool      rnd_pol;            // FIXME: describe.

    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

    int       learntsize_adjust_start_confl;
    double    learntsize_adjust_inc;

    // Statistics: (read-only member variable)
    //
    uint64_t starts, decisions, rnd_decisions, propagations, conflicts;
    uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;
*/

}

#endif
