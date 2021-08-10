all: compiler.exe

compiler.exe: *.hs
	mkdir -p .objects
	ghc Main.hs --make -odir .objects -hidir .objects -o compiler.exe

tests:
	./run_tests.sh

clean:
	rm -f *.o *.hi *.exe .objects/*.o .objects/*.hi
