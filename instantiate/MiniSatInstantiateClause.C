#include "MiniSatInstantiateClause.h"

/**************************************************************************************************/
/*** Loc implementaion ****************************************************************************/
/**************************************************************************************************/

Var Loc::get(Solver& s, const vec<Arg>& args, const vec<int>& bindings) { 
  assert(args.size() == (int)arity);

  //cout << "get [1] " << arity << args << bindings << endl;

  DomElem                argv[args.size()];
  Var                    result;

  for(int i = 0; i < arity; i++) 
    argv[i] = isVar(args[i]) ? bindings[getArg(args[i])] : getArg(args[i]);

  varMap::const_iterator i = vmap.find(argv);

  if(i == vmap.end()) {
    DomElem* argp = mem.alloc();
    for(int i = 0; i < arity; i++) argp[i] = argv[i];
    result     = s.newVar();
    vmap[argp] = result;
  } else result = (*i).second;

  return result;
}

int nvars(const Literal& l, const vec<bool>& vset) {
  vec<Var> vs; 
  l.vars(vs); 

  int r = 0; 
  for(int i = 0; i < vs.size(); i++) if(!vset[vs[i]]) r++;
  return r;
}

void schedule(vec<Literal>& lits, vec<int>& variables, vec<int>& chunksize)
{
  assert(variables.size() == chunksize.size());
  vec<bool> varset(variables.size(),false);
  int i,j,k;

  vec<Literal> tmp;
  // order literals
  for(i = 0; i < lits.size(); i++) {
    int minindex = i;
    int minvars  = nvars(lits[i],varset);
    for(j = i; j < lits.size(); j++) {
      int nv = nvars(lits[j],varset);
      if(nv < minvars) { minindex = j; minvars = nv; }
    }
    lits[i].swap(lits[minindex]);
//    tmp.clear();
//    lits[i].moveTo(tmp);
//    lits[minindex].moveTo(lits[i]);
//    tmp.moveTo(lits[minindex]);
    
    vec<int> vs; lits[i].vars(vs);
    for(j = 0; j < vs.size(); j++) varset[vs[j]] = true;
  }

  // calculate tables
  k = 0;
  for(i = 0; i < varset.size(); i++) varset[i] = false;
  for(i = 0; i < lits.size(); i++) {
    vec<int> vs; lits[i].vars(vs);
    for(j = 0; j < vs.size(); j++) 
      if(!varset[vs[j]]) { variables[k++] = vs[j]; varset[vs[j]] = true; }
    if(k > 0) chunksize[k-1]++;
  }

}


// print a vector of literals
inline ostream& operator<<(ostream& o, const vec<Literal>& literals) {
  for(int i = 0; i < literals.size(); i++) o << literals[i] << ' ';
  return o; }

int Loc::n = 0;

/**************************************************************************************************/
/*** The implementation of First-order Clauses ****************************************************/
/**************************************************************************************************/

// precondition: fresh >= max(sizes)-1
bool FOClause::instantiate(Solver& s, int fresh) {

  vec<int> bindings(sizes.size(), -1);
  vec<int> variables(sizes.size());
  vec<int> chunksize(sizes.size());

  int maxe = 0;  // the largest domain-size of a variable
  int maxi = -1; // the first largest variable
  int i,j;

  for(i = 0; (int)i < sizes.size(); i++) if(maxe < sizes[i]) { maxe = sizes[i]; maxi = i; } 
  if(maxe > 0) maxe--;

  if(fresh > maxe) { 
      //cout << "satisfied (1) " << endl; 
    return true; 
  }
  assert(fresh == 0 || fresh == maxe);

  //cout << "(" << s.nClauses() << ") clause:    " << lits << endl;
  //cout << "  lits:    " << lits.size() << endl;
  //cout << "  vars:    " << sizes.size() << endl;
  //cout << "  fresh:   " << fresh  << endl;
  //cout << "  max:     " << maxe  << endl;
  //cout << "  sizes:   " << sizes << endl;

  schedule(lits,variables,chunksize);

  //cout << "reordered: " << lits << endl;
//  cout << "variables: " << variables << endl;
//  cout << "chunksize: " << chunksize << endl;

  vec<Lit> cls;
  //  LitSet      lset;
  
  // handle ground prefix
  int lind; { vec<bool> varset(variables.size(),false);
  for(lind = 0; lind < lits.size(); lind++) {
    Literal& l = lits[lind];
    //cout << "lit " << l << endl;
    if(nvars(l,varset) == 0) {
      Lit g = Lit(l.get(s,bindings),!l.sign);
      if(s.value(g) == l_True || lset.member(~g)) {
	//cout << "Done! " << s.get_nof_constraints() - count << endl; return true; }
	//cout << "Done! " << s.get_nof_constraints()  << endl; 
	for(i = 0; (int)i < cls.size(); i++) lset.del(cls[i]);
	return true; }
      else if(s.value(g) == l_Undef && !lset.member(g)) {
	cls.push(g);
	lset.add(g);
      }
      else {
	  // cout << "Literal " << l << "is false!" << endl;
      }
    }
    else break;
  } }
  
  // if whole clause is ground, add it and return
  if(variables.size() == 0) {
    //cout << bindings << " : " << cls << endl;
    //fprintf(stderr, "ground clause (1): [ ");
    //s.printClause(cls);
    //fprintf(stderr, " ]\n");
//    if(cls.size() == 0) { 
//	return false;
//    }
    //bool ret = s.addClause(cls,true);
    s.addClause(cls);
    bool ret = s.okay();
    assert(ret);
    for(i = 0; (int)i < cls.size(); i++) lset.del(cls[i]);
    //cout << "Done! " << s.get_nof_constraints() - count << endl; return ret;
    //cout << "Done! " << s.nClauses() << endl; 
    return ret;
  }
  
  // find last fresh variable
  int fvar = 0;
  if(fresh > 0) 
    for(i = variables.size()-1; i >= 0; i--) {
      //cout << "var" << variables[i] << ':' << sizes[variables[i]] << endl;
      if(sizes[variables[i]]-1 == fresh) { fvar = i; break; }
    }
  //cout << "fresh: " << fresh << endl;
  //cout << "fvar:  " << fvar << endl;

  vec<int> currsize(chunksize.size(),0);

  // enumerate variable substitutions
  int top = 0; // number of variables with the value "fresh"
  for(i = 0; i >= 0;) {

      //cout << "apa" << i << ":" << sizes.size() << endl;
    // full substitution constructed?
    if((int)i == sizes.size()) {
      // check if clause is empty
//      if(cls.size() == 0) {
//	  cout << "Contradictive clause: " << lits;
//	  return false;
//      }
      
      //cout << bindings << " : " << cls << endl;
//      {
//	LitSet      ls;
//	for(size_t k = 0; k < cls.size(); k++) {
//	  Lit l = cls[k];
//	  assert(!s.values(l));
//	  assert(!s.values(neg(l)));
//	  assert(!ls.member(l));
//	  assert(!ls.member(neg(l)));
//	  ls.add(cls[k]);
//	}
//	bool fr = false;
//	for(size_t l = 0; l < bindings.size(); l++)
//	  fr = fr | bindings[l] == maxe;
//	if(fresh > 0) assert(fr);
//      }
      //vector<Lit> cs = cls;
      //sort(cs.begin(), cs.end(), Solver::IndexLitComparator());
#ifndef NDEBUG
      int count2 = s.nClauses();
#endif
      //bool ret = s.addClause(cls,true);
      s.addClause(cls);
      bool ret = s.okay();
      //bool ret = s.unsafe_add_clause(cs);
      //fprintf(stderr, "ground clause (2): [ ");
      //s.printClause(cls);
      //fprintf(stderr, " ]\n");
      //cout << "adding: " << cls << endl;
      if (!s.okay())
          return false;
      assert(ret);
      assert(cls.size() == 1 || s.nClauses() == count2 + 1);
      i--;
      while(currsize[i] > 0) { Lit g = cls.last(); cls.pop(); lset.del(g); currsize[i]--; }
      lind -= chunksize[i];
      continue;
    }

    // not done
    int var = variables[i];
    assert(cls.size() <= lind);
    if(bindings[var] == sizes[var]-1) {
      // backtrack
      if(bindings[var] == fresh) top--;
      bindings[var] = -1; i--;

      if(i >= 0) {
//	cout << "unset x" << var << endl;
//	cout << "backtrack: " << currsize[i] << endl;
//	cout << "    chunk: " << chunksize[i] << endl;
//	cout << "     lind: " << lind << endl;
	while(currsize[i] > 0) { Lit g = cls.last(); cls.pop(); lset.del(g); currsize[i]--; }
	lind -= chunksize[i];
      }
    } else {
      // advance
      if(fresh > 0 && top == 0 && i == fvar) 
	bindings[var] = fresh;
      else
	bindings[var]++;

      if(bindings[var] == fresh) top++;
      //cout << "set x" << var << " = " << bindings[var] << endl;
      //cout << "top: " << top << endl;
      //cout << "advance: " << chunksize[i] << endl;

      currsize[i] = 0;
      int oldind = lind;
      for(j = 0; j < chunksize[i]; j++) {
	//cout << "lind: " << lind << endl;
	Lit g = Lit(lits[lind].get(s,bindings),!lits[lind].sign);
	//cout << "lit: " << g << endl;
	lind++;
	if(s.value(g) == l_True || lset.member(~g)) {
	  while(currsize[i] > 0) { Lit g = cls.last(); cls.pop(); lset.del(g); currsize[i]--; }
	  lind = oldind;
	  goto apa;
	}
	else if(s.value(~g) == l_Undef && !lset.member(g)) {
	  cls.push(g);
	  lset.add(g);
	  currsize[i]++;
	}
      }
      //cout << "curr clause: " << cls << endl;
	
      i++;
    }
  apa:;
    //cout << "Var: " << var << ", Binding: " << bindings[var] << ", Top: " << top << endl;
  }
  //cout << "Done! " << s.get_nof_constraints() - count << endl;
  //cout << "Done! " << s.get_nof_constraints() << endl;
  for(i = 0; (int)i < cls.size(); i++) lset.del(cls[i]);
  return true;
}


#if 0

/**************************************************************************************************/
/*** Main, for testing purposes *******************************************************************/
/**************************************************************************************************/

int main() {
  Solver      s;
  Loc         pr(2);
  FOClause    c;

  // transitivity of p

  #if 1
  c.addLit(&pr, false);
  c.lastLit().addArg(varArg(0));
  c.lastLit().addArg(varArg(1));
  c.addLit(&pr, false);
  c.lastLit().addArg(varArg(1));
  c.lastLit().addArg(varArg(2));
  c.addLit(&pr, true);
  c.lastLit().addArg(varArg(0));
  c.lastLit().addArg(varArg(2));

  cout << "Instantiating all for d = 2:" << endl;
  c.clearSize();
  c.addSize(2);
  c.addSize(2);
  c.addSize(2);
  c.instantiate(s,0);
  s.export_dimacs(cout);


  cout << "Instantiating new for d = 3:" << endl;
  c.clearSize();
  c.addSize(3);
  c.addSize(3);
  c.addSize(3);
  c.instantiate(s,2);
  s.export_dimacs(cout);

  vec<Arg> args; args.push(varArg(0)); args.push(varArg(1)); 
  vec<int> bind(2);

  for(int i = 0; i < 3; i++)
    for(int j = 0; j < 3; j++) {
      bind[0] = i; bind[1] = j;
      cout << "p(" << i << "," << j << ") = " << pr.get(s,args,bind) << endl;
    }
  #endif

  //exit(-1);
  

  c.clearLits();
  
  c.addLit(&pr, true);
  c.lastLit().addArg(varArg(0));
  c.lastLit().addArg(varArg(1));
  c.addLit(&pr, true);
  c.lastLit().addArg(varArg(2));
  c.lastLit().addArg(varArg(3));
  c.addLit(&pr, true);
  c.lastLit().addArg(varArg(4));
  c.lastLit().addArg(varArg(5));

  Loc         qr(6);
  c.addLit(&qr, true);
  c.lastLit().addArg(varArg(0));
  c.lastLit().addArg(varArg(1));
  c.lastLit().addArg(varArg(2));
  c.lastLit().addArg(varArg(3));
  c.lastLit().addArg(varArg(4));
  c.lastLit().addArg(varArg(5));

  c.addLit(&qr, false);
  c.lastLit().addArg(conArg(0));
  c.lastLit().addArg(conArg(0));
  c.lastLit().addArg(conArg(0));
  c.lastLit().addArg(conArg(0));
  c.lastLit().addArg(conArg(0));
  c.lastLit().addArg(conArg(0));

  for(int siz = 1; siz < 11; siz++) {
    cout << "Instantiating a lot! (" << siz << " ^ 6):" << endl;
    c.clearSize();
    c.addSize(siz);
    c.addSize(siz);
    c.addSize(siz);
    c.addSize(siz);
    c.addSize(siz);
    c.addSize(siz);

    c.instantiate(s,siz-1);
    cout << "Number of clauses: " << s.get_nof_constraints() << endl;
    cout << "Number of vars:    " << s.get_nof_vars() << endl;

    //exit(-1);
  }

  return 0;
}

#endif
