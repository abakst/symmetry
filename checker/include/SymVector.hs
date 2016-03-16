module SymVector where

data Vec a = V (Int -> a)
{-@
data Vec a <rng :: Int -> a -> Prop>
     = V {a :: i:Int -> a <rng i>}
  @-}

instance Show (Vec a) where
  show _ = "some vector"

{-@ emptyVec :: forall <p :: Int -> a -> Prop>. Vec <p> a @-}
emptyVec     :: Vec  a
emptyVec     = V $ \_ -> (error "Empty array!")


{-@ mkVec :: x:a -> Vec <{\v -> 0=0}, {\i v-> v=x}> a @-}
mkVec     :: a -> Vec  a
mkVec x   = V $ \_ -> x

{-@ getVec :: forall a <r :: x0: Int -> x1: a -> Prop>.
             i: Int ->
             a: Vec<r> a ->
             a<r i> @-}
getVec :: Int -> Vec a -> a
getVec i (V f) = f i

{-@ setVec :: forall a <r :: x0: Int -> x1: a -> Prop>.
      i: Int ->
      x: a<r i> ->
      a: Vec <r> a -> 
      Vec <r> a @-}
setVec :: Int -> a -> Vec a -> Vec a
setVec i v (V f) = V $ \k -> if k == i then v else f k

data Vec2D a = V2D (Int -> Int -> a)
{-@
data Vec2D a <rng :: Int -> Int -> a -> Prop> = V2D (x:Int -> y:Int -> a<rng x y>)
@-}

{-@ emptyVec2D :: forall <p :: Int -> Int -> a -> Prop>. Vec2D <p> a @-}
emptyVec2D :: Vec2D a
emptyVec2D = V2D $ \_ -> error "Empty Vec2D"

{-@ getVec2D :: forall a <r :: Int -> Int -> a -> Prop>.
                x:Int -> y:Int -> Vec2D <r> a -> a<r x y> @-}
getVec2D :: Int -> Int -> Vec2D a -> a
getVec2D x y (V2D f) = f x y

{-@ setVec2D :: forall a <r :: Int -> Int -> a -> Prop>.
                x:Int -> y:Int -> a:a<r x y> -> Vec2D <r> a -> Vec2D <r> a 
@-}
setVec2D :: Int -> Int -> a -> Vec2D a -> Vec2D a
setVec2D x y v (V2D f) = V2D $ \i j -> if i == x && j == y then v else f i j
