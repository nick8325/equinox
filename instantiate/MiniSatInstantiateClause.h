#ifndef __INSTANTIATE_CLAUSE__
#define __INSTANTIATE_CLAUSE__


#include <vector>
using std::vector;

#if (__GNUC__ > 2)
#include <ext/hash_map>
//using namespace __gnu_cxx;
#else
#include <hash_map>
#endif

#include <iostream>


#include "minisat.h"

using namespace std;

/**************************************************************************************************/
/*** The type of Literal (Atom) Arguments. An argument is either a constant or a variable. ********/
/**************************************************************************************************/

typedef int Arg;

static inline Arg  varArg(int v) { return v + v + 1; }
static inline Arg  conArg(int c) { return c + c; }
static inline bool isVar(Arg a)  { return a & 1; }
static inline bool isCon(Arg a)  { return !isVar(a); }
static inline int  getArg(Arg a) { return a >> 1; }


typedef unsigned short DomElem;
//typedef unsigned char DomElem;

/**************************************************************************************************/
/*** A Simple Allocator class for argument vectors. ***********************************************/
/**************************************************************************************************/

class ArgAllocator {
  int              arity;
  int              size;
  int              num;
  vector<DomElem*>    chunks;

 public:
  ArgAllocator(int a) : 
    arity(a), size(1000), num(0) { 
    chunks.push_back((DomElem*)malloc(sizeof(DomElem) * size * arity));
  }

  DomElem* alloc(void) {
    if(num == size) {
      num = 0;
      chunks.push_back((DomElem*)malloc(sizeof(DomElem) * size * arity));
    }
    return chunks.back() + (arity * num++);
  }
};

/**************************************************************************************************/
/*** Hash-function + equality of argument arrays. *************************************************/
/**************************************************************************************************/


struct HashArgs {
  int arity;
  size_t operator()(const DomElem* args) const {
    if (arity == 0) return 0;

    int    bits   = (32 / arity) + (32 % arity != 0 ? 1 : 0);
    int    size   = 1;
    size_t sum    = 0;

    for(int i = 0; i < arity; i++) { sum += size * args[i]; size <<= bits; }

    //    cout << "arity : " << arity << endl;
    //    cout << "bits  : " << bits  << endl;
    //    cout << "hash  : " << sum   << endl;

    return sum;
  }
  HashArgs(int a) : arity(a) {}
};

struct EqArgs {
  int arity;
  bool operator()(const DomElem* args1, const DomElem* args2) const {
    for(int i = 0; i < arity; i++) if(args1[i] != args2[i]) return false;
    return true; }
  EqArgs(int a) : arity(a) {}
};

typedef __gnu_cxx::hash_map<DomElem*,minisat_Var,HashArgs,EqArgs> varMap;

/**************************************************************************************************/
/*** a class for representing sets of literals ****************************************************/
/**************************************************************************************************/

class LitSet {
  vector<bool> lset;
 public:
  LitSet(void) : lset(100) {}

  void add(minisat_Lit l) {
    int ind = l, siz;
    if(ind >= (int)lset.size()) {
      for(siz = lset.size() * 2; ind >= siz; siz *= 2); lset.resize(siz); }
    lset[ind] = true;
  }
  void del(minisat_Lit l) { if(l < (int)lset.size()) lset[l] = false; }
  bool member(minisat_Lit l) {
    return l < (int)lset.size() && lset[l];
  }

  bool isCleared() const {
      for (int i = 0; i < lset.size(); i++)
          if (lset[i])
              return false;
      return true;
  }
};


/**************************************************************************************************/
/*** a location is a table of MiniSat-variables for representing a first-order predicate **********/
/**************************************************************************************************/

class Loc {
  static int   n;
  int          myname;
  int          arity;
  ArgAllocator mem;
  varMap       vmap;
 public:
  Loc(int a) : myname(n), arity(a), mem(a), vmap(100, HashArgs(a), EqArgs(a)) { n++; }

  minisat_Var  get(minisat_solver* s, const vector<int>& args, const vector<int>& bindings);
  bool peek(const vector<int>& args, const vector<int>& bindings, minisat_Var& out);

  int  getArity(void) { return arity; }
  int  name(void) { return myname; }
};

/**************************************************************************************************/
/*** The type of literals. ************************************************************************/
/**************************************************************************************************/

class Literal {
  Loc*     loc;
  vector<Arg> args;
 public:
  bool        sign;
  Literal(void) { }
  Literal(Loc* l, bool s) : loc(l), sign(s) { }
 Literal(const Literal& l) : loc(l.loc), args(l.args), sign(l.sign) { }
  void setLoc(Loc* l) { loc = l; };
  void addArg(Arg a)  { args.push_back(a); };
  minisat_Var  get(minisat_solver* s, const vector<int>& bindings) { return loc->get(s,args,bindings); }
  bool peek(const vector<int>& args, const vector<int>& bindings, minisat_Var& out) { return loc->peek(args, bindings, out); }

  void vars(vector<minisat_Var>& vs) const {
    for(int i = 0; i < args.size(); i++)
      if(isVar(args[i])) vs.push_back(getArg(args[i]));
  }

  friend ostream& operator<<(ostream& o, const Literal& l) {
    if(!l.sign) o << '-'; o << 'p' << l.loc->name();
    if(l.args.size() > 0) {
      o << '(';
      if(isVar(l.args[0])) o << 'x'; o << getArg(l.args[0]);
      for(int i = 1; i < l.args.size(); i++) {
	o << ',';
	if(isVar(l.args[i])) o << 'x'; o << getArg(l.args[i]);
      }
      o << ')';
    }
    return o;
  }
  
  void swap(Literal& l) {
      Loc* tmp  = loc;  loc = l.loc;   l.loc = tmp;
      bool tmp2 = sign; sign = l.sign; l.sign = tmp2;
      args.swap(l.args);
  }
};


/**************************************************************************************************/
/*** The type of First-order Clauses **************************************************************/
/**************************************************************************************************/

class FOClause {
  vector<Literal> lits;
  vector<int>     sizes;

  LitSet       lset;
 public:

  void     clear       (void)           { lits.clear(); sizes.clear(); }
  void     clearLits   (void)           { lits.clear(); }
  void     clearSize   (void)           { sizes.clear(); }
  void     addSize     (int s)          { sizes.push_back(s); }
  void     addLit      (Loc* l, bool s) { lits.push_back(Literal()); lits.back().setLoc(l); lits.back().sign = s; }
  Literal& lastLit     (void)           { return lits.back(); }
  bool     instantiate (minisat_solver* s, int fresh);
};



#endif
