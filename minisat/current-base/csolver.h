/***************************************************************************************[csolver.h]
MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson

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

#ifndef csolver_h
#define csolver_h

/* Arrays of literals are zero terminated */

typedef struct solver_t solver;


extern const int lit_true;
extern const int lit_false;
extern const int l_true;
extern const int l_false;
extern const int l_undef;

/* create / delete a solver object */
solver* s_new           (char* log);
void    s_delete        (solver* s);

/* create problem / solve */
int     s_newlit        (solver* s);
int     s_clause        (solver* s, int* ls);
int     s_solve         (solver* s, int do_simplify, int* ls);
int     s_vclause       (solver* s, ...);
int     s_vsolve        (solver* s, int do_simplify, ...);
int     s_simplify      (solver* s, int elim, int turnoffelim);
void    s_freezelit     (solver* s, int l);
void    s_unfreezelit   (solver* s, int l);
void    s_setpolarity   (solver* s, int l);
void    s_setdecisionvar(solver* s, int l, int b);

/* inspect variable state */
int     s_value         (solver* s, int l);

/* create propositional formulas */
int     s_and           (solver* s, int x, int y);
int     s_or            (solver* s, int x, int y);
int     s_equ           (solver* s, int x, int y);
int     s_xor           (solver* s, int x, int y);
int     s_ite           (solver* s, int c, int t, int f);
void    s_add           (solver* s, int a, int b, int c, int* carry, int* sum);

/* inspect result of solve */
int     s_modelvalue    (solver* s, int l);  // NOTE: does not allow undefined values for now
int*    s_contr         (solver* s);         // Returned array is freed by solver
int     s_okay          (solver* s);

/* solver settings */
void    s_verbose       (solver* s, int l);

/* inspect solver statistics */
int     s_nvars         (solver* s);
int     s_nclauses      (solver* s);
int     s_nconflicts    (solver* s);
int     s_nremembered   (solver* s);

#endif
