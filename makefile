all:
	rm -rf lingeling*
	tar xf archives/lingeling*.tar.gz
	mv lingeling* lingeling
	cd lingeling && ./configure.sh && make
	rm -rf boolector*
	tar xf archives/boolector*.tar.gz
	mv boolector* boolector
	cd boolector && ./configure && make
clean:
	rm -rf lingeling* boolector*
.PHONY: all clean distclean
