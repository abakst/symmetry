{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module ConfigParser2 (readConfig, getPoorConfig) where

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
import           SimplePreprocessor
import           Control.Monad.IO.Class
import           Text.Printf

-- ####################################################################
-- ### MAIN FUNCTION
-- ####################################################################

readConfig    :: String -> IO (Config ())
readConfig str =
  do p_str <- runPreprocessor str
     case runParser configParser Data.Map.empty "" p_str of
       Left  err -> let pos     = errorPos err
                        lineNo  = sourceLine pos
                        colNo   = sourceColumn pos
                        line    = (T.splitOn "\n" (T.pack p_str)) !! (lineNo - 1)
                        cursor  = (replicate (colNo - 1) ' ') ++ "^"
                        newMsg  = Message ((T.unpack line) ++ "\n" ++ cursor)
                        newErr  = addErrorMessage newMsg err
                    in error (show newErr)
       Right exp -> return exp

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

configParser :: ParsecT String u Identity (Config ())
configParser  = do whiteSpace
                   types <- do reserved "cTypes"
                               reservedOp "="
                               s_arrP s_msgP
                   sets  <- do reserved "cSets"
                               reservedOp "="
                               s_arrP s_setP
                   procs <- do reserved "cProcs"
                               reservedOp "="
                               s_procP
                   return Config { cTypes  = types
                                 , cSets   = sets
                                 , cUnfold = []
                                 , cProcs  = procs }

s_procP = s_arrP $ s_tupP s_pidP s_stmtP

s_stmtP = s_skipP <|> s_blockP <|> s_sendP <|> s_recvP <|> s_loopP <|> s_svarP

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

s_msgP1 = let csv2 p1 p2 = (,) <$> p1 <* comma <*> p2
              prsr   = (\(n,p)-> (MTApp (MTyCon n) [p])) <$> (csv2 identifier s_pidP)
          in braces prsr

s_msgPN = let pidArr = s_arrP s_pidP
              csv2 p1 p2 = (,) <$> p1 <* comma <*> p2
              prsr   = (\(n,ps)-> (MTApp (MTyCon n) ps)) <$> csv2 identifier pidArr
          in braces prsr

s_mtyconP = parens $ reserved "MTyCon" *> (MTyCon <$> stringLiteral)

s_pidP = parens $ (reserved "PConc" *> (PConc <$> int)) <|>
                              (reserved "PAbs"  *> (PAbs <$> s_varP <*> s_setP)) <|>
                              (reserved "PVar"  *> (PVar <$> s_varP))

s_varP  = parens $ reserved "V"  *> (V <$> stringLiteral)
s_setP  = parens $ reserved "S"  *> (S <$> stringLiteral)

s_lvarP = LV <$> identifier

s_unfoldP = parens $ reserved "Conc" *> (Conc <$> s_setP <*> int)

s_arrP p     = brackets $ commaSep p
s_tupP p1 p2 = parens $ (,) <$> p1 <* comma <*> p2

-- ####################################################################
-- ### TESTING
-- ####################################################################

-- s_testerS parser str =
--   case runParser parser Data.Map.empty "" str of
--     Left  err -> print "ERROR:" >> print err
--     Right exp -> print exp

-- s_testerF parser fname =
--   let emp   = Data.Map.empty in
--   do input <- readFile fname
--      case runParser parser emp fname input of
--        (Left err) -> print "ERROR" >> print err
--        (Right s)  -> print s

-- s_test = s_testerF configParser "/home/gokhan/Desktop/stmt"

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
                        readConfig conf_str
