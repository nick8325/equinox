Prop.o: Prop.C Prop.h ../mtl/Map.h ../mtl/Vec.h Solver.h ../mtl/Vec.h \
  ../mtl/Alg.h SolverTypes.h VarOrder.h ../mtl/Heap.h
Solver.o: Solver.C Solver.h ../mtl/Vec.h ../mtl/Alg.h SolverTypes.h \
  VarOrder.h ../mtl/Heap.h ../mtl/Vec.h ../mtl/Sort.h
csolver.o: csolver.C Solver.h ../mtl/Vec.h ../mtl/Alg.h SolverTypes.h \
  VarOrder.h ../mtl/Heap.h ../mtl/Vec.h Prop.h ../mtl/Map.h
