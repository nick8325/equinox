
#-- Variables

MINISAT = ../minisat/current-base
INST    = ../instantiate
OBJS    = $(MINISAT)/Solver.or $(MINISAT)/Prop.or $(INST)/MiniSatWrapper.or $(INST)/MiniSatInstantiateClause.or
HFLAGS  = -optl -static -lstdc++ -fglasgow-exts -O3 -I../instantiate -I$(MINISAT) $(OBJS)
GHC     = ghc

#-- Main

main: paradox.exe equinox.exe equiparadox.exe

paradox: paradox.exe
equinox: equinox.exe
equiparadox: equiparadox.exe

Sat.o: Sat.hs
	$(GHC) -fglasgow-exts --make Sat.hs

#-- EquiParadox

equiparadox.exe: Sat.o *.hs Paradox/*.hs Equinox/*.hs EquiParadox/*.hs ../instantiate/*.or ../minisat/current-base/*.or
	$(GHC) $(HFLAGS) -main-is EquiParadox.Main.main --make EquiParadox.Main -o equiparadox
        
#-- Paradox

paradox.exe: Sat.o *.hs Paradox/*.hs ../instantiate/*.or ../minisat/current-base/*.or
	$(GHC) $(HFLAGS) -main-is Paradox.Main.main --make Paradox.Main -o paradox
        
#-- Equinox

equinox.exe: Sat.o *.hs Equinox/*.hs ../instantiate/*.or ../minisat/current-base/*.or
	$(GHC) $(HFLAGS) -main-is Equinox.Main.main --make Equinox.Main -o equinox
        
#-- Roberto

roberto.exe: Sat.o *.hs Equinox/*.hs ../instantiate/*.or ../minisat/current-base/*.or
	$(GHC) $(HFLAGS) --make Roberto -o roberto
        
#-- Cleaning up

clean:
	rm -f *.o *.hi paradox* equinox* Equinox/*.o Equinox/*.hi Paradox/*.o Paradox/*.hi
