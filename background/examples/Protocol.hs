module Protocol where

data Expr b t = Null
              | Send b t
              | Recv t
              | Case (Expr b t) [(Expr b t)]
              | Lam b (Expr b t)
              | Fork (Expr b t)
              | Bind (Expr b t) (Expr b t)


{-
  alloc(x); run (0 || x : e); return x >>= 
-}                


{-
spawn :: P < B > ()
      -> P < in(k).new (x) (k!x | x: B) >
-}
