all:

run:
	stack ghci --ghc-options -i.:/home/gokhan/libs/liquidhaskell/include

test:
	stack runghc -- -i.:/home/gokhan/libs/liquidhaskell/include qc.hs

liquid-test:
	liquid SymVerify.hs

simp-ghci:
	stack --stack-yaml ~/.stack/global/stack.yaml --resolver lts-3.8 ghci
