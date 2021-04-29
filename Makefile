
compiler.exe: *.hs
	ghc Main.hs --make -o compiler.exe
	./compiler.exe

parse-test: compiler.exe
	./compiler.exe < example.ppl

all: compiler.exe

clean:
	rm -f *.o *.hi *.exe
