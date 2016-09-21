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
                | PLComment { pInline :: Bool
                            , pLines :: [String] }

data PrologStmt = PLImport { importedFile      :: String
                           , importedFunctions :: [PrologStmt] }
                | PLRule   { pStmtName :: String
                           , pStmtArgs :: [PrologExpr]
                           , ruleBody  :: PrologExpr   }
                | PLFact   { pStmtName :: String
                           , pStmtArgs :: [PrologExpr] }

dummyArg  :: Int -> [PrologExpr]
dummyArg n = replicate n PLNull

mkQuery :: String -> Int -> ([PrologExpr] -> PrologExpr)
mkQuery name argNo args
  = assert (length args == argNo) (PLQuery stmt args)
  where
    stmt = PLRule name (dummyArg argNo) PLNull

-- imported functions
consult_rule            = mkQuery "consult" 1
check_race_freedom_rule = mkQuery "check_race_freedom" 2
rewrite_query_rule      = mkQuery "rewrite_query" 2
rewrite_rule            = mkQuery "rewrite" 6
format_result_rule      = mkQuery "format_result" 2
format_rule             = mkQuery "format" 2
catch_rule              = mkQuery "catch" 3

-- imported rewrite rules
send_rule    = mkQuery "send"   3 -- send(p, x, v)
send_t_rule  = mkQuery "send"   4 -- send(p, x, type, v)
recv_rule    = mkQuery "recv"   2 -- recv(p, v)
recv_f_rule  = mkQuery "recv"   3 -- recv(p, x, v)
recv_ft_rule = mkQuery "recv"   4 -- recv(p, x, type, v)
sym_rule     = mkQuery "sym"    3 -- sym(P, S, A)
for_rule     = mkQuery "for"    4 -- for(m, P, S, A)
iter_rule    = mkQuery "iter"   3 -- iter(p, k, A)
while_rule   = mkQuery "while"  3 -- while(p, cond, A)
nondet_rule  = mkQuery "nondet" 2 -- nondet(P, A)
assign_rule  = mkQuery "assign" 3 -- assign(p, x, v)
ite_rule     = mkQuery "ite"    4 -- ite(P, Cond, A, B)
if_rule      = mkQuery "if"     3 -- if(P, Cond, A)
skip_rule    = mkQuery "skip"   0  -- skip
pair_rule    = mkQuery "pair"   2 -- pair(x, y)

-- make sure that argument is a single list
par_rule l@[PLList _] = mkQuery "par" 1 l -- par([A,B,C])
par_rule _            = error "prolog function 'par' takes a single list as argument"
seq_rule l@[PLList _] = mkQuery "seq" 1 l -- seq([A,B,C])
seq_rule _            = error "prolog function 'seq' takes a single list as argument"

-- other helper functions  
set_rule      = mkQuery "set"      1
set_var_rule  = mkQuery "set_var"  1
set_ints_rule = mkQuery "set_ints" 2
e_var_rule    = mkQuery "e_var"    1
e_pid_rule    = mkQuery "e_pid"    1

-- Glue between generated prolog code and rewrite terms
prolog_main = PLRule "main" [] stmts
  where stmts = PLAnd [con, rewq, rem, ind, crf, rew, prntHdr, prnt]
        con   = consult_rule [PLTerm "rewrite"]
        rewq  = rewrite_query_rule [PLVar "T", PLVar "Name"]
        rem   = PLAsgn (PLVar "Rem") (skip_rule [])
        ind   = PLAsgn (PLVar "Ind") (PLList [])
        crf   =
          format_result_rule [ catch_rule [ check_race_freedom_rule [PLVar "T" , PLNull]
                                          , PLNull
                                          , PLTerm "fail" ]
                             , PLVar "Race" ]
        rew   =
          format_result_rule [ rewrite_rule [ PLVar "T"
                                            , PLVar "Rem"
                                            , PLVar "Ind"
                                            , PLNull, PLNull, PLNull]
                             , PLVar "Rewrite" ]
        prntHdr =
          PLAnd [ format_rule [ PLString "~p:~30|~p~t~10+~p~n"
                              , PLList [PLString "name", PLString "rewrite", PLString "race-check"] ]
                , format_rule [ PLString "====================================================~n"
                              , PLList []]]
        prnt  =
          format_rule [ PLString "~p:~t~30|~p~t~21+~p~n"
                      , PLList [PLVar "Name", PLVar "Rewrite", PLVar "Race"] ]

printProlog :: P.Pretty a => ConfigInfo a -> String
printProlog ci
  = render $ vcat [ protocol
                  , space
                  , prolog]
  where
    prolog = vcat [ encodeProlog $ rewrite ci
                  , space
                  , encodeProlog prolog_main ]
    protocol =
      vcat [ text "%%" <+> text l | l <- lines (show (P.pretty (config ci)))]

rewrite :: P.Pretty a => ConfigInfo a -> PrologStmt
rewrite ci
  = PLRule "rewrite_query"
           [PLVar "T", PLVar "Name"]
           $ PLAnd [ PLAsgn (PLVar "T") $ toPrologExpr (config ci)
                   , PLAsgn (PLVar "Name") (PLTerm "verify") ]

-- -----------------------------------------------------------------------------
-- Symmetry to PrologExpr
-- -----------------------------------------------------------------------------

class ToPrologExpr a where
  toPrologExpr :: a -> PrologExpr

tupled :: [Doc] -> Doc
tupled xs
  = parens (hcat (punctuate (text ",") xs))

list :: [Doc] -> Doc
list xs
  = brackets (hcat (punctuate (text ",") xs))

unhandled :: P.Pretty a => a -> PrologExpr
unhandled x = trace str (PLComment True [str])
              where
                doc  = P.pretty x
                rndr = P.displayS . P.renderCompact
                str  = rndr doc ""

instance ToPrologExpr Var where
  toPrologExpr (V v)  = PLTerm v
  toPrologExpr (GV v) = PLTerm v
  toPrologExpr v      = unhandled v

instance ToPrologExpr Set where
  toPrologExpr (S s)     = set_rule      [PLTerm s]
  toPrologExpr (SV x)    = set_var_rule  [toPrologExpr x]
  toPrologExpr (SInts n) = set_ints_rule [PLInt 1, PLInt n]

instance ToPrologExpr Pid where
  toPrologExpr (PConc n)
    = PLTerm $ "p" ++ show n
  toPrologExpr p@(PAbs v s)
    = unhandled p --toPrologExpr v <> colon <> toPrologExpr s
  toPrologExpr p
    = unhandled p

instance ToPrologExpr ILExpr where
  toPrologExpr EUnit    = PLTerm "e_tt"
  toPrologExpr (EVar x) = e_var_rule [toPrologExpr x]
  toPrologExpr (EPid p) = e_pid_rule [toPrologExpr p]
  toPrologExpr e        = unhandled e

toPrologExprMsg         :: ILExpr -> PrologExpr
toPrologExprMsg EUnit    = PLTerm "e_tt"
toPrologExprMsg (EVar x) =e_var_rule [toPrologExpr x]
toPrologExprMsg (EPid p) = toPrologExpr p -- TODO: Is this really an exception ?
toPrologExprMsg e        = unhandled e

instance P.Pretty a => ToPrologExpr (Pid, Stmt a) where
  toPrologExpr (_, Skip{})
    = skip_rule []
  toPrologExpr (p, Send{sndPid = q, sndMsg = (_,e)})
    = send_rule [who,to,msg]
    where
      who = toPrologExpr p
      msg = toPrologExprMsg e
      to  = toPrologExpr q
  toPrologExpr (p, Recv{rcvMsg = (_,v)})
    = recv_rule [who,var]
    where
      var = toPrologExpr v
      who = toPrologExpr p
  toPrologExpr (p, Block{blkBody = body})
    = seq_rule [PLList $ (toPrologExpr . (p,)) <$> body]

  toPrologExpr stmt@(p, Iter{iterVar = v, iterSet = s, iterBody = b})
    = unhandled stmt
  -- toPrologExpr (p, Iter{iterVar = v, iterSet = s, iterBody = b})
  --   = PLQuery "foreach" [i, is, body]
  --   where
  --     i = toPrologExpr v
  --     is = toPrologExpr s
  --     body = toPrologExpr (p, b)

  toPrologExpr p  = unhandled p

instance P.Pretty a => ToPrologExpr (Config a) where
  toPrologExpr Config{ cProcs = ps }
    = par_rule [PLList (toPrologExpr <$> ps)]

-- -----------------------------------------------------------------------------
-- PrologExpr to Prolog
-- -----------------------------------------------------------------------------

class Prolog a where
  encodeProlog :: a -> Doc

instance Prolog PrologStmt where
  encodeProlog PLImport {..} = text ":- use_module" <>
                           tupled [ quotes $ text importedFile
                                  , list $ (\f -> (text $ pStmtName f) <>
                                                  char '/' <>
                                                  (int $ length $ pStmtArgs f)) <$>
                                    importedFunctions ]
  encodeProlog PLRule {..} =
    vcat [ text pStmtName <> args <+> text ":-", exprs] <> char '.'
    where
      args   = case pStmtArgs of
                 [] -> empty
                 _  -> tupled (encodeProlog <$> pStmtArgs)
      exprs  = nest 4 $ encodeProlog ruleBody

  encodeProlog PLFact {..} =
    text pStmtName <> args <> char '.'
    where
      args = case pStmtArgs of
               [] -> empty
               _  -> tupled (encodeProlog <$> pStmtArgs)

instance Prolog PrologExpr where
  encodeProlog (PLTerm {..})   = assert (length pTermName > 0 && (isLower $ head pTermName) )
                                        (text pTermName)
  encodeProlog (PLVar {..})    = assert (length pVarName > 0 && (isUpper $ head pVarName) )
                                        (text pVarName)
  encodeProlog (PLString {..}) = quotes $ text pString
  encodeProlog (PLInt {..})    = int pInt

  encodeProlog (PLQuery {..}) =
    assert ((length pQueryArgs) == (length $ pStmtArgs pQueryTerm))
    (text $ pStmtName pQueryTerm )  <> args
    where
      args = case pQueryArgs of
               [] -> empty
               _  -> tupled (encodeProlog <$> pQueryArgs)

  encodeProlog (PLList {..}) = list (encodeProlog <$> pStmts)
  encodeProlog (PLAnd {..})  = vcat $ punctuate comma (encodeProlog <$> pStmts)
  encodeProlog (PLOr {..})   = vcat $ punctuate semi (encodeProlog <$> pStmts)
  encodeProlog (PLAsgn {..}) = encodeProlog pLhs <+> equals <+> encodeProlog pRhs
  encodeProlog PLNull        = char '_'

  encodeProlog (PLComment {..}) =
    if pInline
    then text "/*" <+> (hsep $ punctuate space $ text <$> pLines) <+> text "*/"
    else vcat $ (text "%%" <+>) . text <$> pLines

