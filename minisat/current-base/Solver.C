/****************************************************************************************[Solver.C]
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

#include "Solver.h"
#include "Sort.h"
#include <cmath>


//#define CHECK_IMPLIED

//=================================================================================================
// Minor methods:


/*_________________________________________________________________________________________________
|
|  newClause : (ps : const vec<Lit>&) (learnt : bool)  ->  [void]
|  
|  Description:
|    Allocate and add a new clause to the SAT solvers clause database. 
|  
|  Input:
|    ps     - The new clause as a vector of literals.
|    learnt - Is the clause a learnt clause? For learnt clauses, 'ps[0]' is assumed to be the
|             asserting literal. An appropriate 'enqueue()' operation will be performed on this
|             literal. One of the watches will always be on this literal, the other will be set to
|             the literal with the highest decision level.
|  
|  Effect:
|    Activity heuristics are updated.
|________________________________________________________________________________________________@*/
bool Solver::newClause(const vec<Lit>& ps_, bool learnt, bool normalized)
{
    vec<Lit>    qs;

    if (!learnt)
        for (int i = 0; i < ps_.size(); i++)
            remember(var(ps_[i]));

    if (!learnt && !normalized){
        assert(decisionLevel() == 0);
        ps_.copyTo(qs);             // Make a copy of the input vector.

        // Remove duplicates:
        sortUnique(qs);

        // Check if clause is satisfied:
        for (int i = 0; i < qs.size()-1; i++){
            if (qs[i] == ~qs[i+1])
                return true; }
        for (int i = 0; i < qs.size(); i++){
            if (value(qs[i]) == l_True)
                return true; }

        // Remove false literals:
        int     i, j;
        for (i = j = 0; i < qs.size(); i++)
            if (value(qs[i]) != l_False)
                qs[j++] = qs[i];
        qs.shrink(i - j);
    }
    const vec<Lit>& ps = learnt || normalized ? ps_ : qs;     // 'ps' is now the (possibly) reduced vector of literals.

    //fprintf(stderr, "new clause (%d,%d): ", learnt, normalized); printClause(ps); fprintf(stderr, "\n");

    if (ps.size() == 0)
        return false;
    else if (ps.size() == 1){
        assert(decisionLevel() == 0);
        return enqueue(ps[0]);
    }else{
        // Allocate clause:
        Clause* c   = Clause_new(ps, learnt);

        if (learnt){
            // Put the second watch on the first literal with highest decision level:
            // (requires that this method is called at the level where the clause is asserting!)
            int i;
            for (i = 1; i < ps.size() && position(trailpos[var(ps[i])]) < trail_lim.last(); i++)
                ;
            (*c)[1] = ps[i];
            (*c)[i] = ps[1];

            // Bump, enqueue, store clause:
            claBumpActivity(*c);        // (newly learnt clauses should be considered active)
            check(enqueue((*c)[0], c));
            learnts.push(c);
            stats.learnts_literals += c->size();
        }else{
            // Store clause:
            clauses.push(c);
            stats.clauses_literals += c->size();

            if (subsumption){
                c->calcAbstraction();
                for (int i = 0; i < c->size(); i++){
                    assert(!find(occurs[var((*c)[i])], c));
                    occurs[var((*c)[i])].push(c);
                    n_occ[toInt((*c)[i])]++;
                    touched[var((*c)[i])] = 1;
                    if (heap.inHeap(var((*c)[i])))
                        updateHeap(var((*c)[i]));
                }
            }

        }
        // Watch clause:
        watches[toInt(~(*c)[0])].push(c);
        watches[toInt(~(*c)[1])].push(c);
    }

    return true;
}


// Disposes a clauses and removes it from watcher lists. NOTE! Low-level; does NOT change the 'clauses' and 'learnts' vector.
//
void Solver::removeClause(Clause& c, bool dealloc)
{
    assert(c.mark() == 0);

    if (c.size() > 1){
        assert(find(watches[toInt(~c[0])], &c));
        assert(find(watches[toInt(~c[1])], &c));
        remove(watches[toInt(~c[0])], &c);
        remove(watches[toInt(~c[1])], &c); 
    }

    if (c.learnt()) stats.learnts_literals -= c.size();
    else            stats.clauses_literals -= c.size();

    if (subsumption && !c.learnt()){
        for (int i = 0; i < c.size(); i++){
            if (dealloc){
                assert(find(occurs[var(c[i])], &c));
                remove(occurs[var(c[i])], &c); 
            }
            n_occ[toInt(c[i])]--;
            updateHeap(var(c[i]));
        }
    }

    if (dealloc)
        free(&c);
    else
        c.mark(1);
}


bool Solver::satisfied(const Clause& c) const
{
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool polarity, bool dvar) {
    int     index;
    index = nVars();
    watches .push();          // (list for positive literal)
    watches .push();          // (list for negative literal)
    reason  .push(NULL);
    assigns .push(toInt(l_Undef));
    trailpos.push(TrailPos(0,0));
    activity.push(0);
    seen    .push(0);
    touched .push(0);
    order   .newVar(polarity,dvar);
    if (subsumption){
        n_occ    .push(0);
        n_occ    .push(0);
        occurs   .push();
        heap     .update(index);
        elimtable.push();
    }
    return index; }


// Returns FALSE if immediate conflict.
bool Solver::assume(Lit p) {
    trail_lim.push(trail.size());
    return enqueue(p); }


// Revert to the state at given level.
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var     x  = var(trail[c]);
            assigns[x] = toInt(l_Undef);
            order.undo(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|  
|  Effect:
|    Will undo part of the trail, upto but not beyond the assumption of the current decision level.
|________________________________________________________________________________________________@*/
void Solver::analyze(Clause* confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    int            pathC = 0;
    int            btpos = -1;
    Lit            p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index = trail.size()-1;
    do{
        assert(confl != NULL);          // (otherwise should be UIP)
        Clause& c = *confl;

        if (c.learnt())
            claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];
            if (!seen[var(q)] && position(trailpos[var(q)]) >= trail_lim[0]){
                varBumpActivity(q);
                seen[var(q)] = 1;
                if (position(trailpos[var(q)]) >= trail_lim.last())
                    pathC++;
                else{
                    out_learnt.push(q);
                    if (position(trailpos[var(q)]) > btpos)
                        btpos = position(trailpos[var(q)]);
                }
            }
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason[var(p)];
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Find correct backtrack level
    for (out_btlevel = trail_lim.size()-1; out_btlevel > 0 && trail_lim[out_btlevel-1] > btpos; out_btlevel--)
        ;

    int     i, j;
    if (expensive_ccmin){
        // Simplify conflict clause (a lot):
        //
        unsigned int min_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            min_level |= abstractLevel(trailpos[var(out_learnt[i])]);     // (maintain an abstraction of levels involved in conflict)
        
        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason[var(out_learnt[i])] == NULL || !analyze_removable(out_learnt[i], min_level))
                out_learnt[j++] = out_learnt[i];
    }else{
        // Simplify conflict clause (a little):
        //
        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++){
            Clause& c = *reason[var(out_learnt[i])];
            for (int k = 1; k < c.size(); k++)
                if (!seen[var(c[k])] && position(trailpos[var(c[k])]) >= trail_lim[0]){
                    out_learnt[j++] = out_learnt[i];
                    break; }
        }
    }

    stats.max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    stats.tot_literals += out_learnt.size();

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}

extern "C" {
    void apa (vec<int>& v) { v.push(17); }
};


// Check if 'p' can be removed. 'min_level' is used to abort early if visiting literals at a level that cannot be removed.
//
bool Solver::analyze_removable(Lit p, unsigned int min_level)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason[var(analyze_stack.last())] != NULL);
        Clause& c = *reason[var(analyze_stack.last())]; analyze_stack.pop();

        for (int i = 1; i < c.size(); i++){
            Lit      p   = c[i];
            TrailPos tp = trailpos[var(p)];
            if (!seen[var(p)] && position(tp) >= trail_lim[0]){
                if (reason[var(p)] != NULL && (abstractLevel(tp) & min_level) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit) ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    int start = position(trailpos[var(p)]);
    for (int i = start; i >= trail_lim[0]; i--){
        Var     x = var(trail[i]);
        if (seen[x]){
            if (reason[x] == NULL){
                assert(position(trailpos[x]) >= trail_lim[0]);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = *reason[x];
                for (int j = 1; j < c.size(); j++)
                    if (position(trailpos[var(c[j])]) >= trail_lim[0])
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


/*_________________________________________________________________________________________________
|
|  enqueue : (p : Lit) (from : Clause*)  ->  [bool]
|  
|  Description:
|    Puts a new fact on the propagation queue as well as immediately updating the variable's value.
|    Should a conflict arise, FALSE is returned.
|  
|  Input:
|    p    - The fact to enqueue
|    from - [Optional] Fact propagated from this (currently) unit clause. Stored in 'reason[]'.
|           Default value is NULL (no reason).
|  
|  Output:
|    TRUE if fact was enqueued without conflict, FALSE otherwise.
|________________________________________________________________________________________________@*/
bool Solver::enqueue(Lit p, Clause* from)
{
    if (value(p) != l_Undef)
        return value(p) != l_False;
    else{
        assigns [var(p)] = toInt(lbool(!sign(p)));
        trailpos[var(p)] = TrailPos(trail.size(),decisionLevel());
        reason  [var(p)] = decisionLevel() == 0 ? NULL : from;
        trail.push(p);
        return true;
    }
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise NULL.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
Clause* Solver::propagate()
{
    if (decisionLevel() == 0 && subsumption)
        return backwardSubsumptionCheck() ? NULL : propagate_tmpempty;

    Clause* confl = NULL;
    //fprintf(stderr, "propagate, qhead = %d, qtail = %d\n", qhead, qtail);
    while (qhead < trail.size()){
        stats.propagations++;
        simpDB_props--;

        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Clause*>&  ws  = watches[toInt(p)];
        Clause         **i, **j, **end;

        for (i = j = (Clause**)ws, end = i + ws.size();  i != end;){
            Clause& c = **i++;
            
            // Make sure the false literal is data[1]:
            Lit false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;

            assert(c[1] == false_lit);

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
#ifdef CHECK_IMPLIED
            if (value(first) == l_True || c.mark() == 1){
#else
            if (value(first) == l_True){
#endif
                *j++ = &c;
            }else{
                // Look for new watch:
                for (int k = 2; k < c.size(); k++)
                    if (value(c[k]) != l_False){
                        c[1] = c[k]; c[k] = false_lit;
                        watches[toInt(~c[1])].push(&c);
                        goto FoundWatch; }

                // Did not find watch -- clause is unit under assignment:
                *j++ = &c;
                if (!enqueue(first, &c)){
                    confl = &c; 
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                }
            FoundWatch:;
            }
        }
        ws.shrink(i - j);
    }

    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { bool operator () (Clause* x, Clause* y) { return x->size() > 2 && (y->size() == 2 || x->activity() < y->activity()); } };
void Solver::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt());
    for (i = j = 0; i < learnts.size() / 2; i++){
        if (learnts[i]->size() > 2 && !locked(*learnts[i]))
            removeClause(*learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    for (; i < learnts.size(); i++){
        if (learnts[i]->size() > 2 && !locked(*learnts[i]) && learnts[i]->activity() < extra_lim)
            removeClause(*learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify(bool do_elimination, bool turn_off_subsumption)
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != NULL)
        return ok = false;

    if (!subsumption)
        do_elimination = false;
    
    if (!do_elimination && (nAssigns() == simpDB_assigns || (!subsumption && simpDB_props > 0)))
        return true;

    if (subsumption){

        if (do_elimination && !eliminate())
            return ok = false;

        // Move this cleanup code to its own method ?
        int      i , j;
        vec<Var> dirty;
        for (i = 0; i < clauses.size(); i++)
            if (clauses[i]->mark() == 1){
                Clause& c = *clauses[i];
                for (int k = 0; k < c.size(); k++)
                    if (!seen[var(c[k])]){
                        seen[var(c[k])] = 1;
                        dirty.push(var(c[k]));
                    }
            }
        
        for (i = 0; i < dirty.size(); i++){
            cleanOcc(dirty[i]);
            seen[dirty[i]] = 0;
        }

        for (i = j = 0; i < clauses.size(); i++)
            if (clauses[i]->mark() == 1)
                free(clauses[i]);
            else
                clauses[j++] = clauses[i];
        clauses.shrink(i - j);

        if (turn_off_subsumption){
            subsumption = false;
            touched.clear(true);
            occurs.clear(true);
            n_occ.clear(true);
            subsumption_queue.clear(true);
            heap.clear(true);
        }
    }

    // Remove satisfied clauses:
    for (int type = 0; type < (subsumption ? 1 : 2); type++){  // (dont scan original clauses if subsumption is on)
        vec<Clause*>& cs = type ? learnts : clauses;
        int     j  = 0;
        for (int i = 0; i < cs.size(); i++){
            assert(cs[i]->mark() == 0);
            if (satisfied(*cs[i]))
                removeClause(*cs[i]);
            else
                cs[j++] = cs[i];
        }
        cs.shrink(cs.size()-j);
    }
    order.cleanup();

    simpDB_assigns = nAssigns();
    simpDB_props   = stats.clauses_literals + stats.learnts_literals;   // (shouldn't depend on 'stats' really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (nof_learnts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts, keeping the number of learnt clauses
|    below the provided limit. NOTE! Use negative value for 'nof_conflicts' or 'nof_learnts' to
|    indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts, int nof_learnts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;

    stats.starts++;

    bool first = true;

    for (;;){
        Clause* confl = propagate();
        if (confl != NULL){
            // CONFLICT
            stats.conflicts++; conflictC++;
            if (decisionLevel() == 0) return l_False;

            first = false;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);
            newClause(learnt_clause, true);
            varDecayActivity();
            claDecayActivity();

        }else{
            // NO CONFLICT

            if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if (nof_learnts >= 0 && learnts.size()-nAssigns() >= nof_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            Lit next = lit_Undef;

            if (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                next = assumptions[decisionLevel()]; 
                if (value(next) == l_False){
                    analyzeFinal(~next, conflict);
                    return l_False; }
            }else{
                // New variable decision:
                stats.decisions++;
                //next = order.select(rnd_mode, polarity_mode, first ? 1.0 : params.random_var_freq); }
                //next = order.select(rnd_mode, polarity_mode, 0); }
                next = order.select(rnd_mode, polarity_mode, params.random_var_freq); }

            if (next == lit_Undef)
                // Model found:
                return l_True;

            check(assume(next));
        }
    }
}


// Return search-space coverage. Not extremely reliable.
//
double Solver::progressEstimate()
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}


// Divide all variable activities by 1e100.
//
void Solver::varRescaleActivity()
{
    for (int i = 0; i < nVars(); i++)
        activity[i] *= 1e-100;
    var_inc *= 1e-100;
}


// Divide all constraint activities by 1e100.
//
void Solver::claRescaleActivity()
{
    for (int i = 0; i < learnts.size(); i++)
        learnts[i]->activity() *= 1e-20;
    cla_inc *= 1e-20;
}



/*_________________________________________________________________________________________________
|
|  solve : (assumps : const vec<Lit>&)  ->  [bool]
|  
|  Description:
|    Top-level solve.
|________________________________________________________________________________________________@*/
bool Solver::solve(const vec<Lit>& assumps, bool do_simplify)
{
    model.clear();
    conflict.clear();

    if (!ok) return false;

    // reintroduce variables that were elimination but used in an assumption
    for (int i = 0; i < assumps.size(); i++)
        remember(var(assumps[i]));

    if (do_simplify && subsumption){
        // mark assumptions as non-eliminateable
        for (int i = 0; i < assumps.size(); i++)
            freezeVar(var(assumps[i]));
        
        // do variable elimination
        if (!simplify(true)) return false;
    }else
        if (!simplify(false)) return false;
    assumps.copyTo(assumptions);

    double  nof_conflicts = params.restart_first;
    double  nof_learnts   = nClauses() * params.learntsize_factor;
    lbool   status        = l_Undef;

    //double limit = params.restart_first;

    if (verbosity >= 1){
        reportf("============================[ Search Statistics ]==============================\n");
        reportf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        reportf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        reportf("===============================================================================\n");
    }

    // Search:
    while (status == l_Undef){
        if (verbosity >= 1)
            reportf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", (int)stats.conflicts, order.size(), nClauses(), (int)stats.clauses_literals, (int)nof_learnts, nLearnts(), (double)stats.learnts_literals/nLearnts(), progress_estimate*100), fflush(stdout);
        status = search((int)nof_conflicts, (int)nof_learnts);
        nof_conflicts *= params.restart_inc;
        nof_learnts  *= params.learntsize_inc;

        //if (nof_conflicts > limit){
        //    limit         = nof_conflicts;
        //    nof_conflicts = params.restart_first;
        //    nof_learnts  *= params.learntsize_inc;
        //}
    }

    if (verbosity >= 1)
        reportf("==============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        extendModel();
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
#ifndef NDEBUG
        verifyModel();
#endif
    }else{
        assert(status == l_False);
        if (conflict.size() == 0)
            ok = false;
    }

    if (subsumption && do_simplify)
        // NOTE: forgets the old frozen value and sets if to false !!
        for (int i = 0; i < assumps.size(); i++)
            unfreezeVar(var(assumps[i]));

    cancelUntil(0);
    return status == l_True;
}

//=================================================================================================
// Methods related to variable elimination simplification:

//#define WEAKEN
//#define MATING
//#define ASYMM

bool Solver::strengthen(Clause& c, Lit l)
{
    assert(decisionLevel() == 0);
    assert(c.mark() == 0);
    assert(find(watches[toInt(~c[0])], &c));
    assert(find(watches[toInt(~c[1])], &c));

    if (c.learnt()) stats.learnts_literals -= 1;
    else            stats.clauses_literals -= 1;

    // If l is watched, delete it from watcher list and watch a new literal
    if (c[0] == l || c[1] == l){
        Lit other = c[0] == l ? c[1] : c[0];
        remove(c,l);
        remove(watches[toInt(~l)], &c);
        if (c.size() > 1)
            // Add a watch for the correct literal
            watches[toInt(~(c[1] == other ? c[0] : c[1]))].push(&c); 

            // !! this version assumes that remove does not change the order !!
            //watches[toInt(~c[1])].push(&c); 
        else {
            // Delete both literals and the clause itself if it became unit
            remove(watches[toInt(~c[0])], &c);
            removeClause(c, false);
        }
    }
    else
        remove(c,l);
        
    // if subsumption-indexing is active perform the necessary updates
    if (subsumption){
        remove(occurs[var(l)], &c);
        c.calcAbstraction();
        n_occ[toInt(l)]--;
        updateHeap(var(l));
    }

    return c.size() == 1 ? enqueue(c[0]) : true;
}



// Returns FALSE if clause is always satisfied ('out_clause' should not be used). 
bool Solver::merge(const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause)
{  
    stats.merges++;

    bool  ps_smallest = _ps.size() < _qs.size();
    const Clause& ps =  ps_smallest ? _qs : _ps;
    const Clause& qs =  ps_smallest ? _ps : _qs;

    for (int i = 0; i < qs.size(); i++){
        if (var(qs[i]) != v){
            for (int j = 0; j < ps.size(); j++)
                if (var(ps[j]) == var(qs[i]))
                    if (ps[j] == ~qs[i])
                        return false;
                    else
                        goto next;
            out_clause.push(qs[i]);
        }
        next:;
    }

    for (int i = 0; i < ps.size(); i++)
        if (var(ps[i]) != v)
            out_clause.push(ps[i]);

    return true;
}

// Returns FALSE if clause is always satisfied ('out_clause' should not be used). 
bool Solver::merge(const Clause& _ps, const Clause& _qs, Var v)
{  
    stats.merges++;

    bool  ps_smallest = _ps.size() < _qs.size();
    const Clause& ps =  ps_smallest ? _qs : _ps;
    const Clause& qs =  ps_smallest ? _ps : _qs;
    const Lit* __ps = (const Lit*)ps;
    const Lit* __qs = (const Lit*)qs;

    for (int i = 0; i < qs.size(); i++){
        if (var(__qs[i]) != v){
            for (int j = 0; j < ps.size(); j++)
                if (var(__ps[j]) == var(__qs[i]))
                    if (__ps[j] == ~__qs[i])
                        return false;
                    else
                        goto next;
        }
        next:;
    }

    return true;
}


void Solver::gather(vec<Clause*>& clauses)
{
    //fprintf(stderr, "Gathering clauses for backwards subsumption\n");
    int ntouched = 0;
    assert(touched.size() == occurs.size());
    clauses.clear();
    for (int i = 0; i < touched.size(); i++)
        if (touched[i]){
            const vec<Clause*>& cs = getOccurs(i);
            ntouched++;
            for (int j = 0; j < cs.size(); j++)
                if (cs[j]->mark() == 0){
                    clauses.push(cs[j]);
                    cs[j]->mark(2);
                }
            touched[i] = 0;
        }

    //fprintf(stderr, "Touched variables %d of %d yields %d clauses to check\n", ntouched, touched.size(), clauses.size());
    for (int i = 0; i < clauses.size(); i++)
        clauses[i]->mark(0);
}


/*_________________________________________________________________________________________________
|
|  subsumes : (_c : ClauseId) (c : Clause&) (_d : ClauseId) (d : Clause&)  ->  bool
|
|  Description:
|     Checks if c subsumes d, and at the same time, if c can be used to simplify d by subsumption
|     resolution.
|    
|  Input:
|     Indices into the 'clauses' vector _c, _d, and references to the corresponding clauses c, d.
|
|  Result:
|     lit_Error  - No subsumption or simplification
|     lit_Undef  - Clause c subsumes d
|     l          - The literal l can be deleted from d
|________________________________________________________________________________________________@*/
//Lit Solver::subsumes(const Clause& c, const Clause& d)
inline Lit Solver::subsumes(const Clause& c, const Clause& d) const
{
    //stats.subsumption_checks++;
    if (d.size() < c.size() || (c.abstraction() & ~d.abstraction()) != 0)
        return lit_Error;

    Lit        ret = lit_Undef;
    const Lit* _c  = (const Lit*)c;
    const Lit* _d  = (const Lit*)d;

    for (int i = 0; i < c.size(); i++) {
        // search for c[i] or ~c[i]
        for (int j = 0; j < d.size(); j++)
            if (_c[i] == _d[j])
                goto ok;
            else if (ret == lit_Undef && _c[i] == ~_d[j]){
                ret = _c[i];
                goto ok;
            }

        // did not find it
        //stats.subsumption_misses++;
        return lit_Error;
    ok:;
    }

    return ret;
}



// Backward subsumption + backward subsumption resolution
bool Solver::backwardSubsumptionCheck(bool verbose)
{
    int cnt = 0;
    int subsumed = 0;
    int deleted_literals = 0;

    while (subsumption_queue.size() > 0 || qhead < trail.size()){

        // if propagation queue is non empty, take the first literal and
        // create a dummy unit clause
        if (qhead < trail.size()){
            Lit l = trail[qhead++];
            (*bwdsub_tmpunit)[0] = l;
            assert(bwdsub_tmpunit->mark() == 0);
            subsumption_queue.push(bwdsub_tmpunit);
        }
        Clause&  c = *subsumption_queue.last(); subsumption_queue.pop();

        if (verbose && verbosity >= 2 && cnt++ % 1000 == 0)
            reportf("subsumption left: %10d (%10d subsumed, %10d deleted literals)\r", subsumption_queue.size(), subsumed, deleted_literals);

        if (c.mark())
            continue;

        if (c.size() == 1 && !enqueue(c[0]))
            return false; 

        // (1) find best variable to scan
        Var best = var(c[0]);
        for (int i = 1; i < c.size(); i++)
            if (occurs[var(c[i])].size() < occurs[best].size())
                best = var(c[i]);

        // (2) search all candidates
        vec<Clause*>& _cs = getOccurs(best);
        Clause** cs = (Clause**)_cs;

        for (int j = 0; j < _cs.size(); j++)
            if (cs[j] != &c){
                if (cs[j]->mark())
                    continue;
                if (c.mark())
                    break;

                Lit l = subsumes(c, *cs[j]);

                if (l == lit_Undef)
                    subsumed++, removeClause(*cs[j], false);
                else if (l != lit_Error){
                    deleted_literals++;
                    subsumption_queue.push(cs[j]);
                    if (!strengthen(*cs[j], ~l))
                        return false;

                    // did current candidate get deleted from cs? then check candidate at index j again
                    if (var(l) == best)
                        j--;
                }
            }

#ifdef CHECK_IMPLIED
        if (satisfied(c))
            continue;

        assert(c.mark() == 0);
        // test if c is implied by other clauses
        c.mark(1);
        bool implied = false;
        trail_lim.push(trail.size());
        for (int i = 0; i < c.size(); i++)
            check(enqueue(~c[i]));
        if (propagate() != NULL)
            implied = true;
        cancelUntil(0);
        c.mark(0);
        if (implied)
            removeClause(c, false);
#endif

    }

    return true;
}


bool Solver::asymm(Var v, Clause& c)
{
    assert(decisionLevel() == 0);

    //fprintf(stderr, "asymmetric branching on clause: "); printClause(c); fprintf(stderr, "\n");
    if (c.mark() || satisfied(c)){
        //fprintf(stderr, "subsumed.\n");
        return true; }

    trail_lim.push(trail.size());
    Lit l = lit_Undef;
    for (int i = 0; i < c.size(); i++)
        if (var(c[i]) != v)
            check(enqueue(~c[i]));
        else
            l = c[i];

    if (propagate() != NULL){
        //fprintf(stderr, " succeeded\n");
        cancelUntil(0);
        stats.asymm_lits++;

        assert(find(c, l));
        if (!strengthen(c, l))
            return false;

        if (c.size() == 1)
            return propagate() == NULL;
        else
            assert(qhead == trail.size());
    }
    else
        cancelUntil(0);

    return true;
}


bool Solver::asymmVar(Var v)
{
    assert(!hasVarProp(v, p_frozen));

    vec<Clause*>  pos, neg;
    const vec<Clause*>& cls = getOccurs(v);

    if (value(v) != l_Undef || cls.size() == 0)
        return true;

    for (int i = 0; i < cls.size(); i++)
        if (!asymm(v, *cls[i]))
            return false;

    return true;
}


bool Solver::eliminateVar(Var v, bool fail)
{
    assert(!hasVarProp(v, p_frozen));

    
    //int before = stats.asymm_lits;
    if (asymm_mode && !asymmVar(v))
        return false;
    //fprintf(stderr, "removed %d literals\n", stats.asymm_lits - before);

    vec<Clause*>  pos, neg;
    const vec<Clause*>& cls = getOccurs(v);

    if (value(v) != l_Undef || cls.size() == 0)
        return true;

    // split the occurrences into positive and negative
    for (int i = 0; i < cls.size(); i++)
        if (find(*cls[i], Lit(v)))
            pos.push(cls[i]);
        else{
            assert(find(*cls[i], ~Lit(v)));
            neg.push(cls[i]);
        }

    // check if number of clauses decreases
    int      cnt = 0;
    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++){
            if (merge(*pos[i], *neg[j], v))
                cnt++;

            if (cnt > cls.size() + grow)
                return true;
        }


    setVarProp(v, p_decisionvar, false);
    setVarProp(v, p_eliminated,  true);

    vec<Lit> resolvent;
    // produce clauses in cross product
    int top = clauses.size();
    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++){
            resolvent.clear();

            if (merge(*pos[i], *neg[j], v, resolvent)){
                int i, j;

                for (i = j = 0; i < resolvent.size(); i++)
                    if (value(resolvent[i]) == l_True)
                        goto next;
                    else if (value(resolvent[i]) == l_Undef)
                        resolvent[j++] = resolvent[i];
                resolvent.shrink(i - j);

                if (resolvent.size() == 1){
                    if (!enqueue(resolvent[0]))
                        return false;
                }else
                    check(newClause(resolvent, false, true));
            }
        next:;
        }

    // DEBUG: For checking that a clause set is saturated with respect to variable elimination.
    //        If the clause set is expected to be saturated at this point, this constitutes an
    //        error.
    if (fail){
        reportf("eliminated var %d, %d <= %d\n", v+1, cnt, cls.size());
        reportf("previous clauses:\n");
        for (int i = 0; i < cls.size(); i++){
            printClause(*cls[i]);
            reportf("\n");
        }
        
        reportf("new clauses:\n");
        for (int i = top; i < clauses.size(); i++){
            printClause(*clauses[i]);
            reportf("\n");
        }

        assert(0); }

    // delete + store old clauses
    elimtable[v].order = elimorder++;
    assert(elimtable[v].eliminated.size() == 0);
    for (int i = 0; i < cls.size(); i++){
        elimtable[v].eliminated.push(Clause_new(*cls[i]));
        removeClause(*cls[i], false); 
    }

    assert(subsumption_queue.size() == 0);
    for (int i = top; i < clauses.size(); i++)
        if (clauses[i]->mark() == 0)
            subsumption_queue.push(clauses[i]);
    
    return backwardSubsumptionCheck();
}


void Solver::remember(Var v)
{
    assert(decisionLevel() == 0);

    if (v >= elimtable.size() || elimtable[v].order == 0)
        return;

    vec<Lit> clause;

    // Re-activate variable
    elimtable[v].order = 0;
    setVarProp(v, p_decisionvar, true);
    setVarProp(v, p_eliminated,  false);
    order.undo(v);

    if (subsumption)
        updateHeap(v);

    // Reintroduce all old clauses which may implicitly remember other clauses
    for (int i = 0; i < elimtable[v].eliminated.size(); i++){
        Clause& c = *elimtable[v].eliminated[i];
        clause.clear();
        for (int j = 0; j < c.size(); j++)
            clause.push(c[j]);

        stats.remembered_clauses++;
        check(addClause(clause));
        free(&c);
    }

    elimtable[v].eliminated.clear();
}


void Solver::extendModel()
{
    vec<Var> vs;

    // NOTE: make sure that the extended assignments are undone
    trail_lim.push(trail.size());

    // NOTE: elimtable.size() might be lower than nVars() at the moment
    for (int v = 0; v < elimtable.size(); v++)
        if (elimtable[v].order > 0)
            vs.push(v);

    sort(vs, ElimOrderLt(elimtable));

    for (int i = 0; i < vs.size(); i++){
        Var v = vs[i];
        Lit l = lit_Undef;

        for (int j = 0; j < elimtable[v].eliminated.size(); j++){
            Clause& c = *elimtable[v].eliminated[j];

            for (int k = 0; k < c.size(); k++)
                if (var(c[k]) == v)
                    l = c[k];
                else if (value(c[k]) != l_False)
                    goto next;

            assert(l != lit_Undef);
            check(enqueue(l));
            break;

        next:;
        }

        if (value(v) == l_Undef)
            check(enqueue(Lit(v)));
    }
}


bool Solver::eliminate()
{
    assert(subsumption);
    assert(subsumption_queue.size() == 0);

    int cnt = 0;
    //reportf("eliminating variables\n");


#ifdef INVARIANTS
    // check that all clauses are simplified
    reportf("Checking that all clauses are normalized prior to variable elimination\n");
    bool failed = false;
    for (int i = 0; i < clauses.size(); i++)
        if (clauses[i]->mark() == 0){
            Clause& c = *clauses[i];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_Undef){
                    reportf("non normalized clause: ");
                    printClause(c);
                    reportf("\n");
                    failed = true;
                }
        }
    assert(!failed);
    reportf("done.\n");
#endif

    for (;;){
        gather(subsumption_queue);

        if (subsumption_queue.size() == 0 && heap.size() == 0)
            break;
        
        //if (verbosity >= 2)
        //    reportf("backwards subsumption: %10d\n", subsumption_queue.size());

        if (!backwardSubsumptionCheck(true))
            return false;

        cnt = 0;
        for (;;){
            assert(!heap.empty() || heap.size() == 0);
            if (heap.empty())
                break;

            Var elim = heap.getmin();

            if (hasVarProp(elim, p_frozen))
                continue;

            if (verbosity >= 2)
                if (cnt++ % 100 == 0) 
                    reportf("elimination left: %10d\r", heap.size());
                
            if (!eliminateVar(elim))
                return false;
        }
    }

#ifdef INVARIANTS
    // check that no more subsumption is possible
    reportf("Checking that no more subsumption is possible\n");
    cnt = 0;
    for (int i = 0; i < clauses.size(); i++){
        if (cnt++ % 1000 == 0)
            reportf("left %10d\r", clauses.size() - i);
        for (int j = 0; j < i; j++)
            assert(clauses[i]->mark() ||
                   clauses[j]->mark() ||
                   subsumes(*clauses[i], *clauses[j]) == lit_Error);
    }
    reportf("done.\n");

    // check that no more elimination is possible
    reportf("Checking that no more elimination is possible\n");
    for (int i = 0; i < nVars(); i++){
        if (!hasVarProp(i, p_frozen))
            eliminateVar(i, true);
    }
    reportf("done.\n");
#endif

    assert(qhead == trail.size());

    return true;
}


//=================================================================================================
// Debug:

void Solver::verifyModel()
{
    bool failed = false;
    for (int i = 0; i < clauses.size(); i++){
        assert(clauses[i]->mark() == 0);
        if (!satisfied(*clauses[i])){
            reportf("unsatisfied clause: ");
            printClause(*clauses[i]);
            reportf("\n");
            failed = true;
        }
    }

    assert(!failed);
    int cnt = 0;
    // NOTE: elimtable.size() might be lower than nVars() at the moment
    for (int i = 0; i < elimtable.size(); i++)
        if (elimtable[i].order > 0)
            for (int j = 0; j < elimtable[i].eliminated.size(); j++){
                cnt++;
                if (!satisfied(*elimtable[i].eliminated[j])){
                    reportf("unsatisfied clause: ");
                    printClause(*elimtable[i].eliminated[j]);
                    reportf("\n");
                    failed = true;
                }
            }

    assert(!failed);
    reportf("Verified %d original and %d eliminated clauses.\n", clauses.size(), cnt);
}

