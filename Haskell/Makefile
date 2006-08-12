
#-- Variables

MINISAT = ../minisat/current-base
HFLAGS  = -optl -static -lstdc++ -fglasgow-exts -I$(MINISAT) $(MINISAT)/Solver.or $(MINISAT)/Prop.or $(MINISAT)/csolver.or
GHC     = ghc

#-- Main

main: paradox.exe equinox.exe

#-- Paradox

paradox.exe: *.hs Paradox/*.hs
	$(GHC) $(HFLAGS) -main-is Paradox.Main.main --make Paradox.Main -o paradox
        
#-- Equinox

equinox.exe: *.hs Equinox/*.hs
	$(GHC) $(HFLAGS) -main-is Equinox.Main.main --make Equinox.Main -o equinox
        
#-- Cleaning up

clean:
	rm -f *.o *.hi paradox* equinox* Equinox/*.o Equinox/*.hi Paradox/*.o Paradox/*.hi
