#ifndef __WRAPPER__
#define __WRAPPER__

#include "csolver.h"

Loc*    loc_new    (int a);
void    loc_free   (Loc* l);
int     loc_arity  (Loc* l);

void    solver_clause_begin       (solver* w);           
void    solver_clause_add_lit     (solver* w, Loc* l, int s);
void    solver_clause_add_lit_var (solver* w, int v);
void    solver_clause_add_lit_con (solver* w, int c);
void    solver_clause_add_size    (solver* w, int s);
int     solver_clause_commit      (solver* w, int fresh);

void    solver_lit_begin   (solver* w, Loc* l, int sign);
void    solver_lit_add_con (solver* w, int c);
Var     solver_lit_read    (solver* w);


#endif

