
compiler.exe: Main.hs Parser.hs
	ghc Main.hs --make -o compiler.exe
	./compiler.exe

all: compiler.exe

clean:
	rm -f *.o *.hi *.exe
