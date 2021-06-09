all: compiler.exe

compiler.exe: *.hs
	mkdir -p .objects
	ghc Main.hs --make -odir .objects -hidir .objects -o compiler.exe

parse-test: compiler.exe
	./compiler.exe < example.ppl

clean:
	rm -f *.o *.hi *.exe .objects/*.o .objects/*.hi
