{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module ConfigParser (readConfig) where

import AST

import           Prelude
import           Text.Parsec
import           Text.Parsec.Combinator
import           Text.Parsec.Char
import           Text.Parsec.Error
import           Text.Parsec.String
import           Text.Parsec.Language
import qualified Text.Parsec.Token as Token
import           Control.Applicative hiding ((<|>), many)
import           Data.Functor.Identity
import           Data.Map hiding (foldl')
import           Data.List hiding (insert)
import qualified Data.Text as T
import           System.Directory

-- ####################################################################
-- ### MAIN FUNCTION
-- ####################################################################

readConfig    :: String -> Config ()
readConfig str =
  case runParser configParser Data.Map.empty "" str of
    Left  err -> let pos     = errorPos err
                     lineNo  = sourceLine pos
                     colNo   = sourceColumn pos
                     line    = (T.splitOn "\n" (T.pack str)) !! (lineNo - 1)
                     cursor  = (replicate (colNo - 1) ' ') ++ "^"
                     newMsg  = Message ((T.unpack line) ++ "\n" ++ cursor)
                     newErr  = addErrorMessage newMsg err
                 in error (show newErr)
    Right exp -> exp

-- ####################################################################
-- ### LEXER
-- ####################################################################

stmtDef =
  emptyDef {Token.commentLine     = "#"
           ,Token.identStart      = letter
           ,Token.identLetter     = (alphaNum <|> char '_')
           ,Token.reservedNames   = stmt_tokens ++
                                    stmt_messageTokens ++
                                    stmt_pidTokens ++
                                    stmt_otherTokens
           ,Token.reservedOpNames = ["=>", "="]}
  where stmt_tokens        = ["receive", "send", "end", "skip",
                              "loop", "jump" ,"def"]
        stmt_messageTokens = ["MTApp", "MTyCon"]
        stmt_pidTokens     = ["PConc", "PAbs", "PVar"]
        stmt_otherTokens   = ["S", "V", "LV", "Conc"]
        stmt_configTokens  = ["cTypes", "cSets", "cProcs"]

stmtLexer  = Token.makeTokenParser stmtDef

identifier    = Token.identifier    stmtLexer
reserved      = Token.reserved      stmtLexer
reservedOp    = Token.reservedOp    stmtLexer
parens        = Token.parens        stmtLexer
braces        = Token.braces        stmtLexer
brackets      = Token.brackets      stmtLexer
integer       = Token.integer       stmtLexer
int           = fromIntegral <$> integer
semi          = Token.semi          stmtLexer
whiteSpace    = Token.whiteSpace    stmtLexer
stringLiteral = Token.stringLiteral stmtLexer
semiSep       = Token.semiSep       stmtLexer
commaSep      = Token.commaSep      stmtLexer
comma         = Token.comma         stmtLexer

-- ####################################################################
-- ### PARSER
-- ####################################################################

configParser  = do whiteSpace
                   many s_macroP -- parse all the macros
                                 -- and collect them in the parser state
                   types <- do reserved "cTypes"
                               reservedOp "="
                               withMacro $ s_arrP s_msgP
                   sets  <- do reserved "cSets"
                               reservedOp "="
                               withMacro $ s_arrP s_setP
                   procs <- do reserved "cProcs"
                               reservedOp "="
                               s_procP
                   return Config { cTypes  = types
                                 , cSets   = sets
                                 , cUnfold = []
                                 , cProcs  = procs }

s_procP = withMacro $ s_arrP $ s_tupP s_pidP s_stmtP

s_stmtP = withMacro $ s_skipP <|> s_blockP <|> s_sendP <|> s_recvP <|> s_loopP <|> s_svarP

s_skipP  = reserved "skip" *> return (Skip ())

s_blockP = braces $ do ss <- semiSep s_stmtP
                       return (Block ss ())

s_sendP = do reserved "send"
             pid   <- s_pidP
             pairs <- braces (semiSep pp)
             return (Send pid pairs ())
          where pp = (,) <$> s_msgP <* reservedOp "=>" <*> s_stmtP

s_recvP = do reserved "receive"
             pairs <- braces (semiSep pp)
             return (Recv pairs ())
          where pp = (,) <$> s_msgP <* reservedOp "=>" <*> s_stmtP

s_loopP = do reserved "loop"
             lv <- s_lvarP
             s  <- braces s_stmtP
             return (Loop lv s ())

s_svarP = do reserved "jump"
             lv <- s_lvarP
             return (Goto lv ())

s_msgP  = try s_msgP1 <|> try s_msgPN

s_msgP1 = let csv2 p1 p2 = (,) <$> (p1 <* comma) <*> p2
              prsr   = (\(n,p)-> (MTApp (MTyCon n) [p])) <$> (csv2 identifier s_pidP)
          in withMacro $ braces prsr

s_msgPN = let pidArr = s_arrP s_pidP
              csv2 p1 p2 = (,) <$> p1 <* comma <*> p2
              prsr   = (\(n,ps)-> (MTApp (MTyCon n) ps)) <$> csv2 identifier pidArr
          in withMacro $ braces prsr

s_mtyconP = withMacro $ parens $ reserved "MTyCon" *> (MTyCon <$> stringLiteral)

s_pidP = withMacro $ parens $ (reserved "PConc" *> (PConc <$> int)) <|>
                              (reserved "PAbs"  *> (PAbs <$> s_varP <*> s_setP)) <|>
                              (reserved "PVar"  *> (PVar <$> s_varP))

s_varP  = withMacro $ parens $ reserved "V"  *> (V <$> stringLiteral)
s_setP  = withMacro $ parens $ reserved "S"  *> (S <$> stringLiteral)

s_lvarP = LV <$> identifier

s_unfoldP = withMacro $ parens $ reserved "Conc" *> (Conc <$> s_setP <*> int)

s_arrP p     = brackets $ commaSep p
s_tupP p1 p2 = parens $ (,) <$> p1 <* comma <*> p2

-- ####################################################################
-- ### MACRO
-- ####################################################################

data Macro = MStmt   (Stmt ())
           | MMType  MType
           | MMTyCon MTyCon
           | MPid    Pid
           | MVar    Var
           | MSet    Set
           | MUnfold Unfold
           | MArr    [Macro]
           | MTup    (Macro,Macro)
           deriving (Eq, Show)

type StmtState = Map String Macro

class MacroTransformer a where
  fromMacro :: Macro -> (Maybe a)
  toMacro   :: a -> Macro

instance MacroTransformer (Stmt ()) where
  fromMacro (MStmt s) = Just s
  fromMacro _         = Nothing
  toMacro   s         = MStmt s

instance MacroTransformer MType where
  fromMacro (MMType m) = Just m
  fromMacro _          = Nothing
  toMacro   m          = MMType m

instance MacroTransformer MTyCon where
  fromMacro (MMTyCon m) = Just m
  fromMacro _           = Nothing
  toMacro   m           = MMTyCon m

instance MacroTransformer Pid where
  fromMacro (MPid p) = Just p
  fromMacro _        = Nothing
  toMacro   p        = MPid p

instance MacroTransformer Var where
  fromMacro (MVar v) = Just v
  fromMacro _        = Nothing
  toMacro   v        = MVar v

instance MacroTransformer Set where
  fromMacro (MSet s) = Just s
  fromMacro _        = Nothing
  toMacro   s        = MSet s

instance MacroTransformer Unfold where
  fromMacro (MUnfold u) = Just u
  fromMacro _           = Nothing
  toMacro   u           = MUnfold u

instance (MacroTransformer a) => MacroTransformer [a] where
  fromMacro (MArr ms) = let xs = Prelude.map fromMacro ms
                            helper ([],ys)     = ys
                            helper ((x:xs),ys) = case x of
                                                   (Just a) -> helper (xs,ys ++ [a])
                                                   Nothing  -> []
                            res = helper (xs, [])
                        in case ms of
                             [] -> Just []
                             _  -> case res of
                                     [] -> Nothing
                                     _  -> Just res
  fromMacro _         = Nothing
  toMacro   xs        = MArr (Prelude.map toMacro xs)

instance (MacroTransformer a, MacroTransformer b) => MacroTransformer (a,b) where
  fromMacro (MTup (m1,m2)) = case (fromMacro m1, fromMacro m2) of
                               (Nothing,_)      -> Nothing
                               (_,Nothing)      -> Nothing
                               (Just a, Just b) -> Just (a,b)
  toMacro (a,b) = MTup (toMacro a, toMacro b)

s_macroP = do reserved "def"
              l <- Token.identifier stmtLexer
              reservedOp "="
              r <- try (toMacro <$> s_stmtP)
                     <|> try (toMacro <$> s_msgP)
                     <|> try (toMacro <$> s_mtyconP)
                     <|> try (toMacro <$> s_pidP)
                     <|> try (toMacro <$> s_varP)
                     <|> try (toMacro <$> s_setP)
                     <|> try (toMacro <$> s_arrP s_msgP)
                     <|> try (toMacro <$> s_arrP s_setP)
                     <|> try (toMacro <$> s_procP)
              st <- getState :: ParsecT String StmtState Identity StmtState
              putState $ insert l r st
              return r

lookupMacro name = do st <- getState
                      case Data.Map.lookup name st of
                        (Just m) -> return m
                        Nothing  -> unexpected $ name ++ " not bound to anything"

getMacro name = do m <-lookupMacro name
                   case fromMacro m of
                     (Just a) -> return a
                     Nothing  -> unexpected $ name ++ "is not bound to the right type"

fillMacro :: (MacroTransformer a) => ParsecT String StmtState Identity a
fillMacro  = Token.identifier stmtLexer >>= getMacro

withMacro p = p <|> fillMacro

-- ####################################################################
-- ### TESTING
-- ####################################################################

s_testerS parser str =
  case runParser parser Data.Map.empty "" str of
    Left  err -> print "ERROR:" >> print err
    Right exp -> print exp

s_testerF parser fname =
  let emp   = Data.Map.empty in
  do input <- readFile fname
     case runParser parser emp fname input of
       (Left err) -> print "ERROR" >> print err
       (Right s)  -> print s

s_test = s_testerF configParser "/home/gokhan/Desktop/stmt"

{- poor man's here document -}

here tag file env =
  do txt <- readFile file
     let (_,_:rest) = span (/="{- "++tag++" START") (lines txt)
         (doc,_)    = span (/=tag++" END -}") rest
     return $ unlines $ Prelude.map subst doc
     where
       subst ('$':'(':cs) = case span (/=')') cs of
         (var,')':cs) -> maybe ("$("++var++")") id (Prelude.lookup var env) ++ subst cs
         _ -> '$':'(':subst cs
       subst (c:cs) = c:subst cs
       subst "" = ""

getPoorConfig     :: String -> IO (Config ())
getPoorConfig file = do checker_path <- getCurrentDirectory
                        conf_str <- here "CONFIG" (checker_path ++ file) []
                        return (readConfig conf_str)
