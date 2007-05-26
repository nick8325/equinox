/**************************************************************************************[VarOrder.h]
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

#ifndef VarOrder_h
#define VarOrder_h

#include "SolverTypes.h"
#include "Heap.h"

//#include <math.h>

//=================================================================================================


struct VarOrder_lt {
    const vec<double>&  activity;
    bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
    //bool operator () (Var x, Var y) { return activity[x] < activity[y]; }
    //bool operator () (Var x, Var y) { 
    //    return fabs(activity[x] - activity[y]) < .5 ? x > y : activity[x] > activity[y]; 
    //}
    VarOrder_lt(const vec<double>&  act) : activity(act) { }
};


enum { p_decisionvar = 0, p_polarity = 1, p_frozen = 2, p_eliminated = 3 };
enum { rnd_any = 0, rnd_nonactive = 1, rnd_leftlinear = 2, rnd_rightlinear = 4, rnd_leftcomplete = 5, rnd_anyheap = 6 };
enum { polarity_true = 0, polarity_false = 1, polarity_user = 2, polarity_rnd = 3 };


class VarOrder {
    SolverStats&        stats;
    const vec<char>&    assigns;     // var->val. Pointer to external assignment table.
    const vec<double>&  activity;    // var->act. Pointer to external activity table.
    vec<char>           properties;
    Heap<VarOrder_lt>   heap;
    double              random_seed; // For the internal random number generator

    //=================================================================================================
    // Random numbers:
    

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }
    
    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }

    friend class VarFilter;
public:
    VarOrder(SolverStats& s, const vec<char>& ass, const vec<double>& act) :
        stats(s), assigns(ass), activity(act), heap(VarOrder_lt(act)), random_seed(91648253)
        { }

    int  size       ()                        { return heap.size(); }
    void setVarProp (Var v, int prop, bool b) { properties[v] = (properties[v] & ~(1 << prop)) | (b << prop); }
    bool hasVarProp (Var v, int prop) const   { return properties[v] & (1 << prop); }
    inline void cleanup    ();

    inline void newVar(bool polarity, bool dvar);
    inline void update(Var x);                  // Called when variable increased in activity.
    inline void undo(Var x);                    // Called when variable is unassigned and may be selected again.
    inline Lit  select(int rnd_mode, int polarity_mode, double random_freq =.0); // Selects a new, unassigned variable (or 'var_Undef' if none exists).
};


struct VarFilter {
    const VarOrder& o;
    VarFilter(const VarOrder& _o) : o(_o) {}
    bool operator()(Var v) const { return toLbool(o.assigns[v]) == l_Undef  && o.hasVarProp(v, p_decisionvar); }
    //bool operator()(Var v) const { return toLbool(o.assigns[v]) == l_Undef; }
};

void VarOrder::cleanup()
{
    VarFilter f(*this);
    heap.filter(f);
}

void VarOrder::newVar(bool polarity, bool dvar)
{
    Var v = assigns.size()-1;
    heap.setBounds(v+1);
    properties.push(0);
    setVarProp(v, p_decisionvar, dvar);
    setVarProp(v, p_polarity, polarity);
    undo(v);
}


void VarOrder::update(Var x)
{
    if (heap.inHeap(x))
        heap.increase(x);
}


void VarOrder::undo(Var x)
{
    if (!heap.inHeap(x) && hasVarProp(x, p_decisionvar))
        heap.insert(x);
}


Lit VarOrder::select(int rnd_mode, int polarity_mode, double random_var_freq)
{
    Var next = var_Undef;

    // Random decision:

    if (drand(random_seed) < random_var_freq && !heap.empty()){
        if (rnd_mode == rnd_any){
            next = irand(random_seed,assigns.size());
        }else if (rnd_mode == rnd_anyheap){
            next = heap[irand(random_seed,heap.size())];
        }else if (rnd_mode == rnd_nonactive){
            next = heap[heap.size() / 2 + irand(random_seed, heap.size()/2)];
        }else if (rnd_mode == rnd_rightlinear){
            for (int i = heap.size()-1; i >= 0; i--){
                next = heap[i];
                if (toLbool(assigns[next]) == l_Undef && hasVarProp(next, p_decisionvar))
                    break;
            }
        }else if (rnd_mode == rnd_leftlinear){
            for (int i = 0; i < heap.size(); i++){
                next = heap[i];
                if (toLbool(assigns[next]) == l_Undef && hasVarProp(next, p_decisionvar))
                    break;
            }
        }else if (rnd_mode == rnd_leftcomplete){
            int index = irand(random_seed,heap.size());
            for (int i = heap.size()-1; i >= 0; i--){
                next = heap[(index + i) % heap.size()];
                if (toLbool(assigns[next]) == l_Undef && hasVarProp(next, p_decisionvar))
                    break;
            }
        }
    }

    if (toLbool(assigns[next]) == l_Undef && hasVarProp(next, p_decisionvar))
        stats.rnd_decisions++;

    // Activity based decision:
    while (next == var_Undef || toLbool(assigns[next]) != l_Undef || !hasVarProp(next, p_decisionvar))
        if (heap.empty()){
            next = var_Undef;
            break;
        }else
            next = heap.getmin();

    //if (next != var_Undef)
    //    fprintf(stderr, "var = %d, prop = %d, decision = %d, polarity = %d, frozen = %d\n", 
    //            next+1, properties[next], hasVarProp(next, p_decisionvar), hasVarProp(next, p_polarity), hasVarProp(next, p_frozen));
    //else
    //    fprintf(stderr, "var = undef\n");

    bool sign = false;
    switch (polarity_mode){
    case polarity_true:  sign = false; break;
    case polarity_false: sign = true;  break;
    case polarity_user:  sign = hasVarProp(next, p_polarity); break;
    case polarity_rnd:   sign = irand(random_seed, 2); break;
    }

    return next == var_Undef ? lit_Undef : Lit(next, sign);
}


//=================================================================================================
#endif
