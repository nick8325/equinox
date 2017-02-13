.NOTPARALLEL:

#-- Variables

INST    = instantiate
HASKELL = Haskell

#-- Add this when compiling on Cygwin

#-- export EXTRACFLAGS=-mno-cygwin

#-- Main

main: mk-instantiate mk-haskell

mk-instantiate:
	make MiniSatInstantiateClause.o -C $(INST)
	make MiniSatWrapper.o -C $(INST)

mk-haskell:
	make -C $(HASKELL)

