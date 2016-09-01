all: bnfc compiler

compiler:
	ghc -threaded --make lab4.hs -o lab4

bnfc:
	bnfc --haskell Fun.cf
	happy -gca ParFun.y
	alex -g LexFun.x

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DocFun.ps

distclean: clean
	-rm -f DocFun.* 
	-rm -f LexFun.* 
	-rm -f ParFun.* 
	-rm -f LayoutFun.* 
	-rm -f SkelFun.* 
	-rm -f PrintFun.* 
	-rm -f TestFun.* 
	-rm -f AbsFun.* 
	-rm -f TestFun 
	-rm -f ErrM.* 
	-rm -f SharedString.* 
	-rm -f Fun.dtd 
	-rm -f XMLFun.*
