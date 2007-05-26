
#-- Variables

MINISAT = minisat/current-base
INST    = instantiate
HASKELL = Haskell

#-- Add this when compiling on Cygwin

export EXTRACFLAGS=-mno-cygwin

#-- Main

main: mk-minisat mk-instantiate mk-haskell

mk-minisat:
	make Solver.or -C $(MINISAT)
	make Prop.or   -C $(MINISAT)

mk-instantiate:
	make MiniSatWrapper.or           -C $(INST)
	make MiniSatInstantiateClause.or -C $(INST)

mk-haskell:
	make -C $(HASKELL)

