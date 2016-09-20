{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}
module Symmetry.IL.Rewrite.Prolog (printProlog) where

import           Symmetry.IL.AST hiding(($$))
import           Symmetry.IL.ConfigInfo
import           Paths_checker
import           Text.PrettyPrint
import qualified Text.PrettyPrint.Leijen as P hiding ((<$>))

import Control.Exception
import Data.Char
import System.FilePath.Posix

import Debug.Trace

data PrologExpr = PLTerm   { pTermName :: String }
                | PLVar    { pVarName :: String }
                | PLString { pString :: String }
                | PLInt    { pInt :: Int }
                | PLQuery  { pQueryTerm :: PrologStmt
                           , pQueryArgs :: [PrologExpr] }
                | PLList   { pStmts :: [PrologExpr] }
                | PLAnd    { pStmts :: [PrologExpr] }
                | PLOr     { pStmts :: [PrologExpr] }
                | PLAsgn   { pLhs :: PrologExpr
                           , pRhs :: PrologExpr }
                | PLNull

data PrologStmt = PLImport { importedFile      :: String
                           , importedFunctions :: [PrologStmt] }
                | PLRule   { pStmtName :: String
                           , pStmtArgs :: [PrologExpr]
                           , ruleBody  :: PrologExpr   }
                | PLFact   { pStmtName :: String
                           , pStmtArgs :: [PrologExpr] }

dummyArg  :: Int -> [PrologExpr]
dummyArg n = replicate n PLNull

mkRule :: String -> Int -> PrologStmt
mkRule name argNo = PLRule name (dummyArg argNo) PLNull

-- imported functions
consult_rule            = mkRule "consult" 1
check_race_freedom_rule = mkRule "check_race_freedom" 2
rewrite_query_rule      = mkRule "rewrite_query" 2
rewrite_rule            = mkRule "rewrite" 6
format_result_rule      = mkRule "format_result" 2
format_rule             = mkRule "format" 2
catch_rule              = mkRule "catch" 3

-- rewrite rules
par_rule     = mkRule "par"    1 -- par([A,B,C])
seq_rule     = mkRule "seq"    1 -- seq([A,B,C])
send_rule    = mkRule "send"   3 -- send(p, x, v)
send_t_rule  = mkRule "send"   4 -- send(p, x, type, v)
recv_rule    = mkRule "recv"   2 -- recv(p, v)
recv_f_rule  = mkRule "recv"   3 -- recv(p, x, v)
recv_ft_rule = mkRule "recv"   4 -- recv(p, x, type, v)
sym_rule     = mkRule "sym"    3 -- sym(P, S, A)
for_rule     = mkRule "for"    4 -- for(m, P, S, A)
iter_rule    = mkRule "iter"   3 -- iter(p, k, A)
while_rule   = mkRule "while"  3 -- while(p, cond, A)
nondet_rule  = mkRule "nondet" 2 -- nondet(P, A)
assign_rule  = mkRule "assign" 3 -- assign(p, x, v)
ite_rule     = mkRule "ite"    4 -- ite(P, Cond, A, B)
if_rule      = mkRule "if"     3 -- if(P, Cond, A)
skip_rule    = mkRule "skip"   0 -- skip
pair_rule    = mkRule "pair"   2 -- pair(x, y)

prolog_main = PLRule "main" [] stmts
  where stmts = PLAnd [con, rewq, rem, ind, crf, rew, prntHdr, prnt]
        con   = PLQuery consult_rule [PLTerm "rewrite"]
        rewq  = PLQuery rewrite_query_rule [PLVar "T", PLVar "Name"]
        rem   = PLAsgn (PLVar "Rem") (PLTerm "skip")
        ind   = PLAsgn (PLVar "Ind") (PLList [])
        crf   =
          PLQuery format_result_rule
                  [ PLQuery catch_rule
                            [ PLQuery check_race_freedom_rule [PLVar "T" , PLNull]
                            , PLNull
                            , PLTerm "fail" ]
                  , PLVar "Race" ]
        rew   =
          PLQuery format_result_rule
                  [ PLQuery rewrite_rule
                            [PLVar "T", PLVar "Rem", PLVar "Ind", PLNull, PLNull, PLNull]
                  , PLVar "Rewrite" ]
        prntHdr =
          PLAnd [ PLQuery format_rule
                         [ PLString "~p:~30|~p~t~10+~p~n"
                         , PLList [PLString "name", PLString "rewrite", PLString "race-check"] ]
                , PLQuery format_rule
                          [ PLString "====================================================~n"
                          , PLList []]]
        prnt  =
          PLQuery format_rule
                  [ PLString "~p:~t~30|~p~t~21+~p~n"
                  , PLList [PLVar "Name", PLVar "Rewrite", PLVar "Race"] ]

printProlog :: P.Pretty a => ConfigInfo a -> String
printProlog ci
  -- = renderStyle style{mode = LeftMode} (protocol $+$ space $+$ prolog)
  = render $ vcat [ protocol
                  , space
                  , prolog]
  where
    prolog = vcat [ toProlog $ rewrite ci
                  , space
                  , toProlog prolog_main ]
    protocol =
      vcat [ text "%%" <+> text l | l <- lines (show (P.pretty (config ci)))]



rewrite :: P.Pretty a => ConfigInfo a -> PrologStmt
rewrite ci
  = PLRule "rewrite_query"
           [PLVar "T", PLVar "Name"]
           $ PLAnd [ PLAsgn (PLVar "T") s0
                   , PLAsgn (PLVar "Name") (PLTerm "verify") ]
  where
    s0 = PLTerm $ renderStyle style{mode = LeftMode} $ toProlog (config ci)
    --s0 = PLNull

class Prolog a where
  toProlog :: a -> Doc

tupled :: [Doc] -> Doc
tupled xs
  = parens (hcat (punctuate (text ",") xs))

list :: [Doc] -> Doc
list xs
  = brackets (hcat (punctuate (text ",") xs))

comment :: Doc -> Doc
comment t = text "/*" <+> t <+> text "*/"

term :: String -> [Doc] -> Doc
term p xs
  = text p <> tupled xs

--unhandled :: P.Pretty a => a -> b
--unhandled x = error ("prolog error " ++ )
unhandled :: P.Pretty a => a -> Doc
unhandled x = trace t (comment $ text t)
              where t = show $ P.pretty x

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

toPrologMsg EUnit    = text "e_tt"
toPrologMsg (EVar x) = term "e_var" [toProlog x]
toPrologMsg (EPid p) = toProlog p
toPrologMsg e        = unhandled e

instance P.Pretty a => Prolog (Pid, Stmt a) where
  toProlog (_, Skip{})
    = text "skip"
  toProlog (p, Send{sndPid = q, sndMsg = (_,e)})
    = term "send" [who,to,msg]
    where
      who = toProlog p
      msg = trace (show e) (toPrologMsg e)
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

instance Prolog PrologStmt where
  toProlog PLImport {..} = text ":- use_module" <>
                           tupled [ quotes $ text importedFile
                                  , list $ (\f -> (text $ pStmtName f) <>
                                                  char '/' <>
                                                  (int $ length $ pStmtArgs f)) <$>
                                    importedFunctions ]
  toProlog PLRule {..} =
    vcat [ text pStmtName <> args <+> text ":-", exprs] <> char '.'
    where
      args   = case pStmtArgs of
                 [] -> empty
                 _  -> parens $ hsep $ punctuate comma (toProlog <$> pStmtArgs)
      exprs  = nest 4 $ toProlog ruleBody

  toProlog PLFact {..} =
    text pStmtName <> args <> char '.'
    where
      args = case pStmtArgs of
               [] -> empty
               _  -> parens $ hsep $ punctuate comma (toProlog <$> pStmtArgs)

instance Prolog PrologExpr where
  toProlog (PLTerm {..}) = assert (length pTermName > 0 && (isLower $ head pTermName) )
                                  (text pTermName)
  toProlog (PLVar {..}) = assert (length pVarName > 0 && (isUpper $ head pVarName) )
                                 (text pVarName)
  toProlog (PLString {..}) = quotes $ text pString
  toProlog (PLInt {..}) = int pInt
  toProlog (PLQuery {..}) =
    assert ((length pQueryArgs) == (length $ pStmtArgs pQueryTerm))
    (text $ pStmtName pQueryTerm )  <> args
    where
      args = case pQueryArgs of
               [] -> empty
               _  -> parens $ hsep $ punctuate comma (toProlog <$> pQueryArgs)
  toProlog (PLList {..}) = brackets $ hsep $ punctuate comma (toProlog <$> pStmts)
  toProlog (PLAnd {..}) = vcat $ punctuate comma (toProlog <$> pStmts)
  toProlog (PLOr {..}) = vcat $ punctuate semi (toProlog <$> pStmts)
  toProlog (PLAsgn {..}) = toProlog pLhs <+> equals <+> toProlog pRhs
  toProlog PLNull = char '_'
