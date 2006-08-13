#ifndef __WRAPPER__
#define __WRAPPER__

#include "csolver.h"

typedef void loc;

loc*    loc_new    (int a);
void    loc_free   (loc* l);
int     loc_arity  (loc* l);

void    solver_clause_begin       (solver* w);           
void    solver_clause_add_lit     (solver* w, loc* l, int s);
void    solver_clause_add_lit_var (solver* w, int v);
void    solver_clause_add_lit_con (solver* w, int c);
void    solver_clause_add_size    (solver* w, int s);
int     solver_clause_commit      (solver* w, int fresh);

void    solver_lit_begin   (solver* w, loc* l, int sign);
void    solver_lit_add_con (solver* w, int c);
int     solver_lit_read    (solver* w);


#endif

