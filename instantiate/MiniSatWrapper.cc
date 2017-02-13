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

#include "MiniSatInstantiateClause.h"
#include "minisat.h"

struct solver {
    minisat_solver *minisat;
    FOClause clause;
    Loc*     loc;
    int      sig;
    vector<int> args;
    vector<int> dummy;

    solver(minisat_solver* minisat) : minisat(minisat), loc(NULL) {}
};

static inline minisat_Lit fromDimacs (int l) { int neg = l < 0; return minisat_mkLit_args( (neg ? -l : l) - 1, neg); }
static inline int toDimacs   (minisat_Lit l) { minisat_Var v = minisat_var(l)+1; return minisat_sign(l) ? -v : v; }

extern "C" {

    solver* s_new    (minisat_solver* minisat) { return new solver(minisat); }
    void    s_delete (solver* s) { delete s; }

    Loc*     loc_new    (int a)  { Loc* l = (Loc*)malloc(sizeof(Loc)); new (l) Loc(a); return l; }
    void     loc_free   (Loc* l) { free(l); }
    int      loc_arity  (Loc* l) { return l->getArity(); }

    // build a clause
    void solver_clause_begin       (solver* w)                 { w->clause.clear();}
    void solver_clause_add_lit     (solver* w, Loc* l, int s)  { w->clause.addLit(l,(bool)s); }
    void solver_clause_add_lit_var (solver* w, int v)          {
        w->clause.lastLit().addArg(varArg(v-1));}
    void solver_clause_add_lit_con (solver* w, int c)          { 
        w->clause.lastLit().addArg(conArg(c-1));}
    void solver_clause_add_size    (solver* w, int s)          { w->clause.addSize(s); }
    int  solver_clause_commit      (solver* w, int fresh)      { 
        return w->clause.instantiate(w->minisat, fresh) ? 1 : 0; }

    // setting a literal to be read or assumed during solving
    void solver_lit_begin   (solver* w, Loc* l, int sign)  { 
        w->args.clear(); w->loc = l; w->sig = sign; }
    void solver_lit_add_con (solver* w, int c)              { w->args.push_back(conArg(c-1)); }

    // reading the value of a predicate (location)
    int solver_lit_read     (solver* w) { 
        // creates variables if they don't exists!! (fix?)
        int lit = minisat_mkLit_args(w->loc->get(w->minisat, w->args, w->dummy), !w->sig);
        return lit; 
    }
}
