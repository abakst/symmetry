{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}
module Symmetry.IL.Rewrite.Prolog (printProlog) where

import           Symmetry.IL.AST
import           Symmetry.IL.ConfigInfo
import           Text.PrettyPrint
import qualified Text.PrettyPrint.Leijen as P hiding ((<$>))

printProlog :: P.Pretty a => ConfigInfo a -> String  
printProlog ci
  = renderStyle style{mode = LeftMode} (toProlog (config ci))

class Prolog a where
  toProlog :: a -> Doc

tupled :: [Doc] -> Doc
tupled xs
  = parens (hcat (punctuate (text ",") xs))

list :: [Doc] -> Doc
list xs
  = brackets (hcat (punctuate (text ",") xs))

term :: String -> [Doc] -> Doc
term p xs
  = text p <> tupled xs

unhandled :: P.Pretty a => a -> b
unhandled x = error ("prolog " ++ show (P.pretty x))

instance Prolog Pid where
  toProlog (PConc n)
    = text "p" <> int n
  toProlog (PAbs v s)
    = toProlog v <> colon <> toProlog s
  toProlog p
    = unhandled p

instance Prolog Var where
  toProlog (V v) = text v
  toProlog (GV v) = text v
  toProlog v     = unhandled v

instance Prolog Set where
  toProlog (S s) = term "set" [text s]
  toProlog (SV x) = term "set_var" [toProlog x]
  toProlog (SInts n) = term "set_ints" [int 1, int n]

instance Prolog ILExpr where
  toProlog EUnit
    = text "e_tt"
  toProlog (EVar x)
    = term "e_var" [toProlog x]
  toProlog (EPid p)
    = term "e_pid" [toProlog p]
  toProlog e
    = unhandled e

instance P.Pretty a => Prolog (Pid, Stmt a) where
  toProlog (_, Skip{})
    = text "skip"
  toProlog (p, Send{sndPid = q, sndMsg = (_,e)})
    = term "send" [who,to,msg]
    where
      who = toProlog p
      msg = toProlog e
      to  = toProlog q
  toProlog (p, Recv{rcvMsg = (_,v)})
    = term "recv" [who,var]
    where
      var = toProlog v
      who = toProlog p
  toProlog (p, Block{blkBody = body})
    = term "seq" [list (map (toProlog . (p,)) body)]
  toProlog (p, Iter{iterVar = v, iterSet = s, iterBody = b})
    = term "foreach" [i, is, body]
    where
      i = toProlog v
      is = toProlog s
      body = toProlog (p, b)
  toProlog p      = unhandled p

instance P.Pretty a => Prolog (Config a) where
  toProlog Config{ cProcs = ps }
    = term "par" [list (map toProlog ps)]
