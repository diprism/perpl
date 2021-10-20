all: compiler.exe

compiler.exe: src/*.hs
	mkdir -p .objects
	cd src && ghc Main.hs --make -odir ../.objects -hidir ../.objects -o ../compiler.exe

tests:
	./run_tests.sh

clean:
	rm -f *.o *.hi *.exe .objects/*.o .objects/*.hi
