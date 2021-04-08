
DiprismCompiler: Main.hs Parser.hs
	ghc Main.hs --make -o DiprismCompiler
	./DiprismCompiler

all: DiprismCompiler

clean:
	rm *.o *.hi DiprismCompiler
