TEST_FILES = $(wildcard *.hs)
EXES       = $(patsubst %.hs,%,$(TEST_FILES))
TESTS      = $(patsubst %,test-%,$(EXES))

SRC_DIR            = $(CURDIR)/../../src/Symmetry
LIBRARY_FILE_NAMES = Language Verify SymbEx
LIBRARY_FILES      = $(patsubst %,$(SRC_DIR)/%.hs,$(LIBRARY_FILE_NAMES))

all: build-lib $(EXES)

$(EXES): %: %.hs $(LIBRARY_FILES)
	stack ghc -- $< -o $@

.PHONY: build-lib clean

build-lib:
	stack install

test: $(TESTS)

$(TESTS): test-%: %
	./test $<

clean:
	rm -f *.hi *.o $(EXES)
	rm -rf .symcheck
