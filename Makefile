GHCFLAGS=-Wunused-do-bind -Wunused-foralls -Wunused-imports -Wunused-pattern-binds -Wunused-top-binds -Wunused-type-patterns

all: compiler.exe

compiler.exe: src/*.hs
	mkdir -p .objects
	cd src && ghc Main.hs --make -odir ../.objects -hidir ../.objects -o ../compiler.exe $(GHCFLAGS)

tests:
	./run_tests.sh

clean:
	rm -f *.o *.hi *.exe .objects/*.o .objects/*.hi
