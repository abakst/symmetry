TEST_FILES = $(wildcard *.hs)
EXES       = $(patsubst %.hs,%,$(TEST_FILES))
TESTS      = $(patsubst %,test-%,$(EXES))

all: build-lib $(EXES)

$(EXES): %: %.hs
	@stack ghc -- $< -o $@

.PHONY: build-lib $(TESTS) clean

build-lib:
	@stack install

$(TESTS): test-%: %
	@./test $<

clean:
	rm -f *.hi *.o $(EXES)
	rm -rf .symcheck
