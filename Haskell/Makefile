
#-- Variables

MINISAT = ../minisat/current-base
INST    = ../instantiate
OBJS    = $(MINISAT)/Solver.or $(MINISAT)/Prop.or $(INST)/MiniSatWrapper.or $(INST)/MiniSatInstantiateClause.or
HFLAGS  = -fglasgow-exts -O2 -static
HSAT    = -optl -static -lstdc++ -I../instantiate -I$(MINISAT) $(OBJS)
GHC     = ghc

#-- Main

main: paradox.exe equinox.exe infinox.exe

paradox: paradox.exe
equinox: equinox.exe
infinox: infinox.exe
equiparadox: equiparadox.exe

Sat.o: Sat.hs
	$(GHC) -fglasgow-exts --make Sat.hs

#-- EquiParadox

#equiparadox.exe: Sat.o *.hs Paradox/*.hs Equinox/*.hs EquiParadox/*.hs ../instantiate/*.or ../minisat/current-base/*.or
	$(GHC) $(HSAT) $(HFLAGS) -main-is EquiParadox.Main.main --make EquiParadox.Main -o equiparadox
        
#-- Paradox

paradox.exe: Sat.o *.hs Paradox/*.hs ../instantiate/*.or ../minisat/current-base/*.or
	$(GHC) $(HSAT) $(HFLAGS) -main-is Paradox.Main.main --make Paradox.Main -o paradox
        
#-- Equinox

equinox.exe: Sat.o *.hs Equinox/*.hs ../instantiate/*.or ../minisat/current-base/*.or
	$(GHC) $(HSAT) $(HFLAGS) -main-is Equinox.Main.main --make Equinox.Main -o equinox
                
#-- Infinox

infinox.exe: *.hs Infinox/*.hs
	$(GHC) $(HFLAGS) -main-is Infinox.Main.main --make Infinox.Main -o infinox
                
#-- Cleaning up

clean:
	rm -f *.o *.hi paradox* equinox* Equinox/*.o Equinox/*.hi Paradox/*.o Paradox/*.hi
