module Ping where

import Language.AST

pingProc :: Symantics repr => repr (Process ())
pingProc = recv `bindL` 
           (\p -> self `bindL` send p)

pongProc :: Symantics repr => repr (Process (Pid RSing)) 
pongProc = newRSing (repS "ping") `bindL` (
  \pingr -> spawn pingr pingProc `bindL` (
     \p  -> self `bindL` (
     \me -> send p me `bindL` 
     const recv)))

bindL m = bind m . lam

main :: Symantics repr => repr ()
main = exec (repS "pong") (pongProc `bindL` (\_ -> ret tt))
