{-# Language GADTs #-}
module AST where

data RoleSing  = RS String
data RoleMulti = RM String
data Process a

data Var = V String

data Type t where
  TInt :: Type Int
  TArrow :: Type a -> Type b -> Type (a -> b)
  TRoleSing :: Type RoleSing
  TRoleMulti :: Type RoleMulti
  
class TypeOf t where
  typeOf :: t -> Type t

instance TypeOf Int where
  typeOf = const TInt

instance TypeOf RoleSing where
  typeOf = const TRoleSing

instance TypeOf RoleMulti where
  typeOf = const TRoleMulti

data Expr t where
  ELit   :: TypeOf t => t -> Expr t
  EVar   :: Var -> Type a -> Expr a
  EAbs   :: Var -> Type a -> Expr b -> Expr (a -> b)
  ESpawn :: Expr RoleSing -> Expr (Process a) -> Expr (Process RoleSing)
  ESpawnMany :: Expr RoleMulti -> Expr (Process a) -> Expr (Process RoleMulti)
  EDoMany :: Expr RoleMulti -> Expr (RoleSing -> Process a) -> Expr (Process [a])
  ESend :: Expr RoleSing -> Expr a -> Expr (Process ()) 
  ERecv :: Expr (Process a)
  EBind :: Expr (Process a) -> Expr (a -> Process b) -> Expr (Process b)
  ERet ::  Expr a -> Expr (Process a)
