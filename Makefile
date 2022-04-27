GHCFLAGS=-Wall -Wno-unused-matches -Wno-unused-local-binds -Wno-missing-signatures -Wno-name-shadowing -Wno-orphans -Wno-type-defaults

all: compiler.exe

compiler.exe: src/*.hs src/*/*.hs
	mkdir -p .objects
	cd src && ghc Main.hs --make -odir ../.objects -hidir ../.objects -o ../compiler.exe $(GHCFLAGS)

tests:
	./run_tests.sh

clean:
	rm -f *.o *.hi *.exe .objects/*.o .objects/*.hi .objects/*/*.o .objects/*/*.hi
