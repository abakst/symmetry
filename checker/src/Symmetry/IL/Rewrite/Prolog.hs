{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE ScopedTypeVariables     #-}
-- module Symmetry.IL.Rewrite.Prolog (printProlog) where
module Symmetry.IL.Rewrite.Prolog where

import           Symmetry.IL.AST hiding(($$))
import           Paths_checker
import           Text.PrettyPrint
import qualified Text.PrettyPrint.Leijen as P hiding ((<$>))
import           Data.Generics (everywhere, mkT, Data(..), Typeable(..))

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
                | PLEq     { pLhs :: PrologExpr
                           , pRhs :: PrologExpr
                           }
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
rewrite_query_rule      = mkQuery "rewrite_query" 4
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

mkLeft  x = pair_rule [PLTerm "0", x]
mkRight x = pair_rule [PLTerm "1", x]

-- Glue between generated prolog code and rewrite terms
prolog_main = PLRule "main" [] stmts
  where stmts = PLAnd [con, rewq, rem, ind, {- crf, -} tmp, rew, prntHdr, prnt]
        con   = consult_rule [PLTerm "rewrite"]
        rewq  = rewrite_query_rule [PLVar "T",PLVar "Rem", PLVar "Ind", PLVar "Name"]
        rem   = PLAsgn (PLVar "Rem") (skip_rule [])
        ind   = PLAsgn (PLVar "Ind") (PLList [])
        tmp   = PLAsgn (PLVar "Race") (PLTerm "fail")
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

printProlog :: (Data a, P.Pretty a) => Config a -> String
printProlog ci
  = render $ vcat [ protocol
                  , space
                  , prolog]
  where
    prolog = vcat [ encodeProlog $ rewrite ci
                  , space
                  , encodeProlog prolog_main ]
    protocol =
      vcat [ text "%%" <+> text l | l <- lines (show (P.pretty ci))]

rewrite :: (Data a, P.Pretty a) => Config a -> PrologStmt
rewrite ci
  = PLRule "rewrite_query"
           [PLVar "T", PLTerm "skip", PLTerm "[]", PLVar "Name"]
           $ PLAnd [ PLAsgn (PLVar "T") $ toPrologExpr ci
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

debug :: P.Pretty a => a -> a
debug x = trace str x
  where
    str  = rndr doc ""
    rndr = P.displayS . P.renderCompact
    doc  = P.pretty x

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
    = toPrologExpr v
  toPrologExpr p
    = unhandled p

instance ToPrologExpr ILExpr where
  toPrologExpr EUnit      = PLTerm "e_tt"
  toPrologExpr (EVar x)   = toPrologExpr x
  toPrologExpr (EPid p)   = toPrologExpr p
  -- toPrologExpr (EVar x)   = e_var_rule   [toPrologExpr x]
  -- toPrologExpr (EPid p)   = e_pid_rule   [toPrologExpr p]
  toPrologExpr (ELeft e)  = mkLeft  $ toPrologExpr e
  toPrologExpr (ERight e) = mkRight $ toPrologExpr e
  toPrologExpr e          = unhandled e

toPrologExprPid (EVar x) = e_var_rule [toPrologExpr x]                            
toPrologExprPid (EPid x) = e_pid_rule [toPrologExpr x]                            

toPrologExprMsg         :: ILExpr -> PrologExpr
toPrologExprMsg EUnit     = PLTerm "e_tt"
toPrologExprMsg (EVar x)  = toPrologExpr x
toPrologExprMsg (EPid p)  = toPrologExpr p -- TODO: Is this really an exception ?
toPrologExprMsg (ELeft e) = mkLeft   $ toPrologExprMsg e
toPrologExprMsg (ERight e) = mkRight $ toPrologExprMsg e
toPrologExprMsg e         = toPrologExpr e

prologRecv :: (Type, Pat) -> PrologExpr
prologRecv (_, p)
  = toPrologExpr p

instance ToPrologExpr Pat where    
  toPrologExpr (PSum t (PProd x _ _) (PProd y _ _))
    = pair_rule [toPrologExpr t, toPrologExpr x]
  toPrologExpr (PSum t (PBase x) (PBase y))
    = pair_rule [toPrologExpr t, toPrologExpr x]
  toPrologExpr (PProd _ x y)
    = pair_rule [toPrologExpr x, toPrologExpr y]
  toPrologExpr (PBase x)
    = toPrologExpr x

instance ToPrologExpr Type where
  toPrologExpr TUnit        = PLTerm "unit"
  toPrologExpr TInt         = PLTerm "int"
  toPrologExpr TPid         = PLTerm "pid"
  toPrologExpr (TSum t1 t2) = sum [ toPrologExpr t1, toPrologExpr t2 ]
    where
      sum = mkQuery "sum_ty" 2
  toPrologExpr (TProd t1 t2) = pair [ toPrologExpr t1, toPrologExpr t2 ]
    where
      pair = mkQuery "prod_ty" 2

instance P.Pretty a => ToPrologExpr (Pid, Stmt a) where
  toPrologExpr (_, Skip{})
    = skip_rule []
  toPrologExpr (_, Die{})
    = mkQuery "die" 0 []
  toPrologExpr (p, Send{sndPid = q, sndMsg = (t,e)})
    = send_rule [who,to,msg]
    where
      who = toPrologExpr p
      msg = toPrologExpr e
      to  = toPrologExprPid q
      ty  = toPrologExpr t
  toPrologExpr (p, Recv{rcvMsg = (t,pat)})
    = recv_rule [who,var]
    where
      var = prologRecv (t,pat)
      who = toPrologExpr p
  toPrologExpr (p, Block{blkBody = body})
    = seq_rule [PLList $ (toPrologExpr . (p,)) <$> body]

  -- toPrologExpr stmt@(p, Iter{iterVar = v, iterSet = s, iterBody = b})
  toPrologExpr (p, Iter{ iterVar = v
                       , iterSet = s
                       , iterBody = b@Block{ blkBody = bs}
                       })
    = case s of
        SInts k ->
          iter_rule [ toPrologExpr p
                    , toPrologExpr k
                    , body
                    ] -- PLQuery "foreach" [i, is, body]
        SIntParam x ->
          iter_rule [ toPrologExpr p
                    , toPrologExpr x
                    , body
                    ]
        S _ ->
          for_rule [ toPrologExpr p
                   , toPrologExpr v
                   , toPrologExpr s
                   , body
                   ]
    where
      body = toPrologExpr (p, b')
      b'   = b { blkBody = filter (notIncr v) bs }
      notIncr v Assign { assignLhs = v' } = v /= v'
      notIncr _ _                         = True

  toPrologExpr (p, Goto { varVar = x })
    = assign_rule [ toPrologExpr p
                  , toPrologExpr x
                  , PLTerm "1"
                  ]

  toPrologExpr (p, Loop { loopVar  = x
                        , loopBody = b
                        })
    = seq_rule [ PLList [ assign_rule [ toPrologExpr p
                                      , toPrologExpr x
                                      , PLTerm "1"
                                      ]
                        , while_rule [ toPrologExpr p
                                     , cond
                                     , body
                                     ]
                        ]
               ]
      where
        cond  = PLEq (toPrologExpr x) (PLTerm "1")
        body  = seq_rule [ PLList [ assign_rule [ toPrologExpr p
                                                , toPrologExpr x
                                                , PLTerm "0"
                                                ]
                                  , toPrologExpr (p, b)
                                  ]
                         ]
  toPrologExpr (p, Case { caseVar = v
                        , caseLeft = l
                        , caseRight = r })
    = ite_rule [ toPrologExpr p
               , PLEq (toPrologExpr v) (PLTerm "0")
               , toPrologExpr (p, l)
               , toPrologExpr (p, r)
               ]

  toPrologExpr (p, Assign { assignLhs = lhs, assignRhs = rhs })
    = assign_rule [ toPrologExpr p
                  , toPrologExpr lhs
                  , toPrologExpr rhs
                  ]

  toPrologExpr p  = unhandled p

instance ToPrologExpr LVar where
  toPrologExpr (LV v) = PLTerm v

instance ToPrologExpr Int where
  toPrologExpr i = PLTerm (show i)

instance (Data a, P.Pretty a) => ToPrologExpr (Config a) where
  toPrologExpr Config{ cProcs = ps }
    = par_rule [PLList (prologProcess <$> ps'')]
      where
        ps'   = everywhere (mkT toUpperPAbs) <$>  ps
        ps''  = toUpperIterVarProc           <$>  ps'

prologProcess :: (Data a, P.Pretty a) => Process a -> PrologExpr
prologProcess (p@(PConc _), s)
  = toPrologExpr (p, s)
prologProcess (p@(PAbs v vs), s)
  = sym_rule [ toPrologExpr v
             , toPrologExpr vs
             , toPrologExpr (p,s)
             ]

toUpperPAbs :: Pid -> Pid
toUpperPAbs (PAbs v s) = PAbs v' s
  where
    v' = upperV v
toUpperPAbs x          = x

toUpperIterVarProc :: forall a. Data a => Process a -> Process a
toUpperIterVarProc (p, s)
  = (p, everywhere (mkT toUpperIterVar) s)
  where
    toUpperIterVar :: Stmt a -> Stmt a
    toUpperIterVar s @ Iter { iterVar = v }
      = s { iterVar  = upperV v
          , iterBody = everywhere (mkT (go v)) (iterBody s)
          }
    toUpperIterVar s = s
    go :: Var -> Var -> Var
    go v = subVar v (upperV v) 

subVar :: Var -> Var -> Var -> Var
subVar x y v
  | x == v    = y
  | otherwise = v

upperV :: Var -> Var
upperV (V v)  = V  (map toUpper v)
upperV (GV v) = GV (map toUpper v)

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
  encodeProlog (PLTerm {..})   =
    assert (length pTermName > 0 && (isLower $ head pTermName))
           (text pTermName)
  encodeProlog (PLVar {..})    =
    assert (length pVarName > 0 && (isUpper $ head pVarName))
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

  encodeProlog (PLList {..})
    = list (encodeProlog <$> pStmts)
  encodeProlog (PLAnd {..})
    = vcat $ punctuate comma (encodeProlog <$> pStmts)
  encodeProlog (PLOr {..})
    = vcat $ punctuate semi (encodeProlog <$> pStmts)
  encodeProlog (PLAsgn {..})
    = encodeProlog pLhs <+> equals <+> encodeProlog pRhs
  encodeProlog (PLEq {..})
    = encodeProlog pLhs <+> equals <+> encodeProlog pRhs
  encodeProlog PLNull
    = char '_'

  encodeProlog (PLComment {..}) =
    if pInline
    then text "/*" <+> (hsep $ punctuate space $ text <$> pLines) <+> text "*/"
    else vcat $ (text "%%" <+>) . text <$> pLines
