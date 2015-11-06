{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module TrailParser (readConfig) where

import Symmetry.IL.AST

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
import           System.Directory

-- ####################################################################
-- ### MAIN FUNCTION
-- ####################################################################

readConfig    :: String -> [Trail]
readConfig str =
  case runParser trailParser Data.Map.empty "" str of
    Left  err -> error "err.."
    Right exp -> []

-- ####################################################################
-- ### LEXER
-- ####################################################################

stmtDef =
  emptyDef { Token.identStart      = letter
           , Token.identLetter     = (alphaNum <|> char '_')
           }

trailLexer  = Token.makeTokenParser stmtDef

identifier    = Token.identifier    trailLexer
symbol        = Token.symbol        trailLexer
reserved s    = Token.reserved      trailLexer s *> return s
parens        = Token.parens        trailLexer
brackets      = Token.brackets      trailLexer
integer       = Token.integer       trailLexer
int           = fromIntegral <$> integer
colon         = Token.colon         trailLexer
charLiteral   = Token.charLiteral   trailLexer
whiteSpace    = Token.whiteSpace    trailLexer
colonSep p    = p `sepBy` colon

-- ####################################################################
-- ### PARSER
-- ####################################################################

data Trail = Trail { no      :: Int
                   , typ     :: String
                   , spinPid :: Int
                   , fun     :: String
                   , funId   :: Int
                   , procId  :: Pid
                   , stmtId  :: Int
                   , lineNo  :: Int
                   , stateNo :: Int
                   , line    :: String
                   } deriving (Eq, Show)

parser = do whiteSpace
            many trailParser


trailParser :: ParsecT String u Identity Trail
trailParser  = do n       <- int <* colon
                  t       <- symbol "proc"
                  s_pid   <- int
                  (f,fid) <- parens $ (,) <$> identifier <*> (colon *> int)
                  p_id    <- procIdParser
                  sid     <- colon *> int
                  lno     <- colon *> int
                  st_no   <- parens $ symbol "state" *> int
                  l       <- rest
                  return $ Trail n t s_pid f fid p_id sid lno st_no l


procIdParser = (PConc <$> int) <|>
                 do pid_t <- identifier
                    case pid_t of
                      "abs"  -> PAbs <$> (V <$> identifier) <*> (S <$> identifier)
                      "unf"  -> PUnfold <$> (V <$> identifier)
                                        <*> (S <$> identifier)
                                        <*> int
                      "pvar" -> PVar <$> (V <$> identifier)
                      _      -> unexpected "undefined Pid identifier"

rest = (many $ noneOf "\n") <* whiteSpace

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
