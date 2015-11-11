TEST_FILES = $(wildcard *.hs)
EXES_ALL   = $(patsubst %.hs,%,$(TEST_FILES))
EXES       = $(filter-out SrcPipe DatabaseSample, $(EXES_ALL))
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
	-./$< --verify

clean:
	rm -f *.hi *.o $(EXES)
	rm -rf .symcheck
