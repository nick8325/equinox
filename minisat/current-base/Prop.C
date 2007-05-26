/******************************************************************************************[Prop.C]
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

#include "Prop.h"

#define MORESIMP

static void logBinOp (FILE* f, Var x, Lit a, Lit b, char* op)
{
    logLit (f, Lit(x));
    fprintf(f, " = ");
    logLit (f, a);
    fprintf(f, op);
    logLit (f, b);
    fprintf(f, "\n");
    fflush(f);
}

static void logIte (FILE* _f, Var x, Lit c, Lit t, Lit f)
{
    logLit (_f, Lit(x));
    fprintf(_f, " = ");
    logLit (_f, c);
    fprintf(_f, " ? ");
    logLit (_f, t);
    fprintf(_f, " : ");
    logLit (_f, f);
    fprintf(_f, "\n");
    fflush(_f);
}

static void logAdd (FILE* f, Var c, Var s, Lit x, Lit y, Lit z)
{
    fprintf(f, "(");
    logLit (f, Lit(c));
    fprintf(f, ",");
    logLit (f, Lit(s));
    fprintf(f, ") = add(");
    logLit (f, x);
    fprintf(f, ",");
    logLit (f, y);
    fprintf(f, ",");
    logLit (f, z);
    fprintf(f, ")\n");
    fflush(f);
}

Lit PropSolver::mkAnd(Lit f, Lit g)
{
    if (!ok) return lit_False;

    // Normalize
#ifdef MORESIMP
    if (g < f) swap(f, g);
    if      (value(f) == l_False || value(g) == l_False) return lit_False;
    else if (value(f) == l_True)                    return g;
    else if (value(g) == l_True)                    return f;
    else if (f == g  || (value(f) != l_Undef && value(f) == value(g)))              return f;
    else if (f == ~g || (value(f) != l_Undef && value(f) != l_Undef && value(f) != value(g)))              return lit_False;
#else
    if (g < f) swap(f, g);
    if      (f == lit_False || g == lit_False) return lit_False;
    else if (f == lit_True)                    return g;
    else if (g == lit_True)                    return f;
    else if (f ==  g )                         return f;
    else if (f == ~g )                         return lit_False;
#endif
    
    // Clausify
    Node n(node_and, f, g, lit_Undef);
    Var  v;
    if (!unique.peek(n, v)){
        v = mkNode(n);
        unique.insert(n,v);

        if (logfile != NULL)
            logBinOp(logfile, v, f, g, " & ");
            
        Solver::addClause(~Lit(v), f);
        Solver::addClause(~Lit(v), g);
        Solver::addClause(~f, ~g, Lit(v));

        check(okay()); }
    
    return Lit(v);
}


Lit PropSolver::mkEqu(Lit f, Lit g)
{
    if (!ok) return lit_False;

#ifdef MORESIMP
    // Normalize
    if (g < f) swap(f, g);
    if      (value(f) == l_False) return ~g;
    else if (value(f) == l_True)  return g;
    else if (value(g) == l_False) return ~f;
    else if (value(g) == l_True)  return f;
    else if (f == g  || (value(f)!= l_Undef && value(f) == value(g)))        return lit_True;
    else if (f == ~g || (value(f)!= l_Undef && value(f) != l_Undef && value(f) != value(g)))        return lit_False;
#else
    // Normalize
    if (g < f) swap(f, g);
    if      (f == lit_False) return ~g;
    else if (f == lit_True)  return g;
    else if (g == lit_False) return ~f;
    else if (g == lit_True)  return f;
    else if (f == g)         return lit_True;
    else if (f == ~g)        return lit_False;
#endif

    // Clausify
    bool sig     = sign(f) != sign(g);
    f            = Lit(var(f));
    g            = Lit(var(g));

    Node       n(node_equ, f, g, lit_Undef );
    Var        v;
    if (!unique.peek(n, v)){
        v = mkNode(n);

        if (logfile != NULL)
            logBinOp(logfile, v, f, g, " == ");

        Solver::addClause(~Lit(v), ~f,  g);
        Solver::addClause(~Lit(v),  f, ~g);
        Solver::addClause( Lit(v), ~f, ~g);
        Solver::addClause( Lit(v),  f,  g);

        check(okay()); }
    
    return Lit(v, sig);
}


Lit PropSolver::mkIte(Lit c, Lit t, Lit f)
{
    if (!ok) return lit_False;

#ifdef MORESIMP
    // Normalize
    if (t < f) { swap(t, f); c = ~c; }
    if (value(c) == l_False) return f;
    if (value(c) == l_True)  return t;
    if (t ==  f || (value(t) != l_Undef && value(t) == value(f))) return t;
    if (t == ~f || (value(t) != l_Undef && value(f) != l_Undef && value(t) != value(f))) return mkXor(c, f);
    if (value(t) == l_False || t == ~c || (value(t) != l_Undef && value(f) != l_Undef && value(t) != value(c))) return mkAnd(~c, f); 
    if (value(t) == l_True  || t ==  c || (value(t) != l_Undef && value(t) == value(c))) return mkOr ( c, f);
    if (value(f) == l_False || f ==  c || (value(f) != l_Undef && value(f) == value(c))) return mkAnd( c, t); 
    if (value(f) == l_True  || f == ~c || (value(f) != l_Undef && value(f) != l_Undef && value(f) != value(c))) return mkOr (~c, t);
#else
    // Normalize
    if (t < f) { swap(t, f); c = ~c; }
    if (c == lit_False) return f;
    if (c == lit_True)  return t;
    if (t ==  f)        return t;
    if (t == ~f)        return mkXor(c, f);
    if (t == lit_False || t == ~c) return mkAnd(~c, f); 
    if (t == lit_True  || t ==  c) return mkOr ( c, f);
    if (f == lit_False || f ==  c) return mkAnd( c, t); 
    if (f == lit_True  || f == ~c) return mkOr (~c, t);
#endif
    
    // Clausify
    bool sig     = sign(f);
    f            = Lit(var(f));
    t            = Lit(var(t), sign(t) ^ sig);
    Node       n(node_ite, c, t, f);
    Var        v;
    if (!unique.peek(n, v)){
        v = mkNode(n);

        if (logfile != NULL)
            logIte(logfile, v, c, t, f);

        Solver::addClause(~Lit(v), ~c,  t);
        Solver::addClause(~Lit(v),  c,  f);
        Solver::addClause( Lit(v), ~c, ~t);
        Solver::addClause( Lit(v),  c, ~f);
        Solver::addClause(~Lit(v),  t,  f); // implied
        Solver::addClause( Lit(v), ~t, ~f);

        check(okay()); }
    
    return Lit(v, sig);
}

    
void PropSolver::mkAdd(Lit a, Lit b, Lit c, Lit& carry, Lit& sum)
{
    if (!ok) carry = lit_False, sum = lit_False;

#ifdef MORESIMP
    // Normalize
    if (c < b) swap(c, b);
    if (b < a) swap(b, a);
    if (c < b) swap(c, b);
    if      (value(a) == l_False) { carry = mkAnd(b, c); sum = mkXor(b, c); }
    else if (value(a) == l_True)  { carry = mkOr (b, c); sum = mkEqu(b, c); }
    else if (value(b) == l_False) { carry = mkAnd(a, c); sum = mkXor(a, c); }
    else if (value(b) == l_True)  { carry = mkOr (a, c); sum = mkEqu(a, c); }
    else if (value(c) == l_False) { carry = mkAnd(a, b); sum = mkXor(a, b); }
    else if (value(c) == l_True)  { carry = mkOr (a, b); sum = mkEqu(a, b); }
    else {
#else
    // Normalize
    if (c < b) swap(c, b);
    if (b < a) swap(b, a);
    if (c < b) swap(c, b);
    if      (a == lit_False) { carry = mkAnd(b, c); sum = mkXor(b, c); }
    else if (a == lit_True)  { carry = mkOr (b, c); sum = mkEqu(b, c); }
    else if (b == lit_False) { carry = mkAnd(a, c); sum = mkXor(a, c); }
    else if (b == lit_True)  { carry = mkOr (a, c); sum = mkEqu(a, c); }
    else if (c == lit_False) { carry = mkAnd(a, b); sum = mkXor(a, b); }
    else if (c == lit_True)  { carry = mkOr (a, b); sum = mkEqu(a, b); }
    else {
#endif
        // Clausify
        Node ns(node_sum,   a, b, c);
        Node nc(node_carry, a, b, c);

        Var _sum, _carry;
        if (!unique.peek(ns, _sum)){
            sum   = Lit(mkNode(ns));
            carry = Lit(mkNode(nc));
            
            if (logfile != NULL)
                logAdd(logfile, var(carry), var(sum), a, b, c);

            Solver::addClause(~carry,  a,  b);
            Solver::addClause(~carry,  a,  c);
            Solver::addClause(~carry,  b,  c);
            Solver::addClause( carry, ~a, ~b);
            Solver::addClause( carry, ~a, ~c);
            Solver::addClause( carry, ~b, ~c);
            Solver::addClause(~sum, ~a, ~b,  c);
            Solver::addClause(~sum, ~a,  b, ~c);
            Solver::addClause(~sum,  a, ~b, ~c);
            Solver::addClause(~sum,  a,  b,  c);
            Solver::addClause( sum, ~a, ~b, ~c);
            Solver::addClause( sum, ~a,  b,  c);
            Solver::addClause( sum,  a, ~b,  c);
            Solver::addClause( sum,  a,  b, ~c);
            Solver::addClause(~carry, ~sum,  a);  // implied
            Solver::addClause(~carry, ~sum,  b);
            Solver::addClause(~carry, ~sum,  c);
            Solver::addClause( carry,  sum, ~a);
            Solver::addClause( carry,  sum, ~b);
            Solver::addClause( carry,  sum, ~c);

        }else{
            check(unique.peek(nc, _carry));
            sum   = Lit(_sum);
            carry = Lit(_carry);
        }
    }
}

