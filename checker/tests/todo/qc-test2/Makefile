LH_INC = $(HOME)/libs/liquidhaskell/include

all:

run:
	stack ghci --ghc-options -i.:$(LH_INC)

test:
	stack runghc -- -i.:$(LH_INC) qc.hs

liquid-test:
	liquid SymVerify.hs

simp-ghci:
	stack --stack-yaml ~/.stack/global/stack.yaml --resolver lts-3.8 ghci
