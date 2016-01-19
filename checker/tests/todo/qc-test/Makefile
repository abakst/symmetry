LH_INC = $(HOME)/libs/liquidhaskell/include

all:

run:
	stack ghci --ghc-options -i.:$(LH_INC)

test:
	stack runghc -- -i.:$(LH_INC) qc.hs
