
#-- Variables

MINISAT = ../minisat/current-base
INST    = ../instantiate
OBJS    = $(MINISAT)/Solver.or $(MINISAT)/Prop.or $(INST)/MiniSatWrapper.or $(INST)/MiniSatInstantiateClause.or
HFLAGS  = -optl -static -lstdc++ -fglasgow-exts -O3 -I../instantiate -I$(MINISAT) $(OBJS)
GHC     = ghc

#-- Main

main: paradox.exe equinox.exe

paradox: paradox.exe
equinox: equinox.exe

#-- Paradox

paradox.exe: *.hs Paradox/*.hs ../instantiate/*.or ../minisat/current-base/*.or
	$(GHC) $(HFLAGS) -main-is Paradox.Main.main --make Paradox.Main -o paradox
        
#-- Equinox

equinox.exe: *.hs Equinox/*.hs ../instantiate/*.or ../minisat/current-base/*.or
	$(GHC) $(HFLAGS) -main-is Equinox.Main.main --make Equinox.Main -o equinox
        
#-- Cleaning up

clean:
	rm -f *.o *.hi paradox* equinox* Equinox/*.o Equinox/*.hi Paradox/*.o Paradox/*.hi
