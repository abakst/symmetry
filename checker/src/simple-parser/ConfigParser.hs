{-# LANGUAGE FlexibleContexts #-}

module ConfigParser where

import AST

import           Text.Parsec
import           Text.Parsec.Combinator
import           Text.Parsec.Char
import           Text.Parsec.String
import           Text.Parsec.Language
import qualified Text.Parsec.Token as Token
import           Control.Applicative hiding ((<|>), many)

type MyStmt = Stmt ()

-- ####################################################################
-- ### LEXER
-- ####################################################################
stmtDef =
  emptyDef {Token.commentLine   = "#"
           ,Token.reservedNames = ["receive"
                                  ,"send"
                                  ,"skip"
                                  ,"PConc"
                                  ,"PAbs"
                                  ,"V"
                                  ,"LV"
                                  ,"S"]}

stmtLexer  = Token.makeTokenParser stmtDef

identifier = Token.identifier stmtLexer -- parses an identifier
reserved   = Token.reserved   stmtLexer -- parses a reserved name
reservedOp = Token.reservedOp stmtLexer -- parses an operator
parens     = Token.parens     stmtLexer -- parses surrounding parenthesis:
braces     = Token.braces     stmtLexer -- parses surrounding parenthesis:
integer    = Token.integer    stmtLexer -- parses an integer
semi       = Token.semi       stmtLexer -- parses a semicolon
whiteSpace = Token.whiteSpace stmtLexer -- parses whitespace

-- ####################################################################
-- ### Parser
-- ####################################################################

stmtParser :: Parser MyStmt
stmtParser  = do whiteSpace
                 s_skipP <|> s_blockP <|> s_sendP

s_skipP  = reserved "skip" >> return (SSkip ())

s_blockP = braces $ do ss <- stmt_arrayP stmtParser semi
                       return (SBlock ss ())

s_sendP = do reserved "skip"
             undefined

test = do tester stmtParser "skip"
          tester stmtParser "{skip;skip}"


-- parses "" and "p[,p]*"
stmt_arrayP p sep = option [] (liftA2 (:) p (many $ sep *> p))

tester parser str = case parse parser "" str of
                      Left err   -> print "ERROR:" >> print err
                      Right stmt -> print stmt
