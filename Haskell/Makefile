
#-- Variables

MINISAT = ../minisat/current-base
HFLAGS  = -fglasgow-exts -I$(MINISAT) $(MINISAT)/Solver.or $(MINISAT)/Prop.or $(MINISAT)/csolver.or

#-- Main

main: paradox.exe equinox.exe

#-- Paradox

paradox.exe: *.hs Paradox/*.hs
	ghc++ $(HFLAGS) -main-is Paradox.Main.main --make Paradox.Main -o paradox
        
#-- Equinox

equinox.exe: *.hs Equinox/*.hs
	ghc++ $(HFLAGS) -main-is Equinox.Main.main --make Equinox.Main -o equinox
        
#-- Cleaning up

clean:
	rm -f *.o *.hi *.exe Equinox/*.o Equinox/*.hi Paradox/*.o Paradox/*.hi
