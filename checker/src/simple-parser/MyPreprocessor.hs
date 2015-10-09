{-# LANGUAGE GADTs #-}
module MyPreprocessor where

import           AST

import           Text.Parsec
import           Text.Parsec.Combinator
import           Text.Parsec.Char
import           Text.Parsec.Error
import           Text.Parsec.String
import           Text.Parsec.Language
import qualified Text.Parsec.Token as Token

import           Control.Applicative hiding ((<|>), many)
import           Data.Functor.Identity
import qualified Data.Map.Strict as Map
import           Data.List hiding (insert)
import qualified Data.Text as T

import           System.Directory
import           Text.Printf


-- ####################################################################
-- ### LEXER
-- ####################################################################

-- ### Definition
-- def Func(Var1,Var2,...,VarN) = Replacement;;
-- ### Usage
-- #Func(Arg1,Arg2,...,ArgN)

macroDef =
  emptyDef { Token.commentLine     = "--"
           , Token.identStart      = letter
           , Token.identLetter     = (letter <|> char '_')
           , Token.reservedNames   = ["def"]
           , Token.reservedOpNames = ["=", ";;"]
           }

macroLexer    = Token.makeTokenParser macroDef

identifier    = Token.identifier    macroLexer
reserved      = Token.reserved      macroLexer
reservedOp    = Token.reservedOp    macroLexer
parens        = Token.parens        macroLexer
braces        = Token.braces        macroLexer
brackets      = Token.brackets      macroLexer
semi          = Token.semi          macroLexer
whiteSpace    = Token.whiteSpace    macroLexer
stringLiteral = Token.stringLiteral macroLexer
semiSep       = Token.semiSep       macroLexer
commaSep      = Token.commaSep      macroLexer
comma         = Token.comma         macroLexer

-- ####################################################################
-- ### PARSER
-- ####################################################################

-- macroDefP :: ParsecT String u Identity Macro
-- macroDefP  = do reserved "def"
--                 name <- identifier
--                 args <- parens $ commaSep identifier
--                 reservedOp "="
--                 body <- manyTill anyChar (reservedOp ";;")
--                 return (M name args body)

-- -- first pass over the text to find the macro definitions
-- firstPass :: ParsecT String MacroState Identity String
-- firstPass =
--   do ss <- many1 $ do macros <- many macroDefP
--                       mapM (\m -> modifyState (upd m)) macros
--                       manyTill1 anyChar end
--      return (concat ss)
--    where end     = lookAhead $ (reserved "def" >> return ()) <|> eof
--          upd m s = let name = mname m
--                    in case Map.lookup name s of
--                         Nothing -> Map.insert name m s
--                         _       -> error $ "2nd definition of macro " ++ name

-- ####################################################################
-- ### TESTING
-- ####################################################################

parseWithState parser str =
  case runParser ((,) <$> parser <*> getState) Map.empty "" str of
    Left  err     -> print "ERROR:" >> print err
    Right (exp,s) -> printf exp >> printf "\n" >> print s

-- ####################################################################
-- ### UTILS
-- ####################################################################

manyTill1 p e = do x  <- p
                   xs <- manyTill p e
                   return (x:xs)
