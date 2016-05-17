{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Exp where

import Control.Applicative
import Control.Arrow
import Control.Monad.State
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String (IsString(..))
import Data.Monoid ((<>))

type Var = String

data Exp
  = Lit Lit
  | Var Var
  | Lam Var Exp
  | App Exp Exp
  | If Exp Exp Exp
  | Op Op
  deriving (Eq,Ord,Show)

data Lit
  = Dbl Double
  | Bool Bool
  deriving (Eq,Ord,Show)

data Op
  -- Numeric Ops
  = Add
  | Sub
  | Mul
  | Div
  | Neg
  | Rec
  -- Comparison Ops
  | Eq
  | Lt
  | Gt
  -- Boolean Ops
  | And
  | Or
  | Not
  deriving (Eq,Ord,Show)

op1 :: Op -> Exp -> Exp
op1 f a = Op f `App` a

op2 :: Op -> Exp -> Exp -> Exp
op2 f a b = Op f `App` a `App` b

data Val
  = F (Val -> Maybe Val)
  | N Double
  | B Bool

instance Show Val where
  show = \case
    F{} -> "<function>"
    N d -> show d
    B b -> show b

data Cxt
  = Hole
  | Lam_  Var Cxt
  | App_L Exp Cxt
  | App_R Exp Cxt
  | If_P Exp Exp Cxt
  | If_T Exp Exp Cxt
  | If_F Exp Exp Cxt
  deriving (Eq,Ord,Show)

-- sugar {{{

instance IsString Exp where
  fromString = Var

instance Num Exp where
  fromInteger = Lit . Dbl . fromInteger
  (+) = op2 Add
  (-) = op2 Sub
  (*) = op2 Mul
  negate = op1 Neg
  abs    = undefined
  signum = undefined

instance Fractional Exp where
  fromRational = Lit . Dbl . fromRational
  (/) = op2 Div
  recip = op1 Rec

-- }}}

plug :: Cxt -> Exp -> Exp
plug = \case
  Hole       -> id
  Lam_ x c   -> (\a -> Lam x a) . plug c
  App_L b c  -> (\a -> App a b) . plug c
  App_R a c  -> (\b -> App a b) . plug c
  If_P t f c -> (\p -> If p t f) . plug c
  If_T p f c -> (\t -> If p t f) . plug c
  If_F p t c -> (\f -> If p t f) . plug c

solveFree :: Exp -> Map Var (Set Cxt)
solveFree = \case
  Var x   -> Map.singleton x $ Set.singleton Hole
  Lam x a -> fmap (Set.map $ Lam_ x) $ Map.delete x $ solveFree a
  App a b -> fmap (Set.map $ App_L b) (solveFree a)
          <> fmap (Set.map $ App_R a) (solveFree b)
  Lit{}   -> mempty
  Op{}    -> mempty

examples :: [Exp]
examples =
  [ Lam "x" "x"
  , Lam "x" $ Lam "y" "x"
  , Lam "x" $ Lam "y" "y"
  , Lam "x" "x" `App` 1
  ]

type Env = Map Var Val

eval :: Env -> Exp -> Maybe Val
eval env = \case
  Lit l -> case l of
    Dbl d  -> Just $ N d
    Bool b -> Just $ B b
  Var x   -> Map.lookup x env
  Lam x a -> Just $ F $ \v -> eval (Map.insert x v env) a
  App a b -> do
    v1 <- eval env a
    v2 <- eval env b
    f <- vFun v1
    f v2
  If p t f -> do
    v1 <- eval env p
    b <- vBool v1
    eval env $ if b then t else f
  Op o -> Just $ opVal o

opVal :: Op -> Val
opVal = \case
  Add  -> vOp2 vNum vNum   (Just . N) (+)
  Sub  -> vOp2 vNum vNum   (Just . N) (-)
  Mul  -> vOp2 vNum vNum   (Just . N) (*)
  Div  -> vOp2 vNum vNum   (Just . N) (/)
  Neg  -> vOp1 vNum        (Just . N) negate
  Rec  -> vOp1 vNum        (Just . N) recip
  And  -> vOp2 vBool vBool (Just . B) (&&)
  Or   -> vOp2 vBool vBool (Just . B) (||)
  Not  -> vOp1 vBool       (Just . B) not
  Eq   -> vOp2 (vNum .|. vBool)
               (vNum .|. vBool) (fmap B)
    $ (Just .: (==)) |.| (Just .: (==))
  Lt   -> vOp2 (vNum .|. vBool)
               (vNum .|. vBool) (fmap B)
    $ (Just .:  (<)) |.| (Just .:  (<))
  Gt   -> vOp2 (vNum .|. vBool)
               (vNum .|. vBool) (fmap B)
    $ (Just .:  (>)) |.| (Just .:  (>))
    

vOp1 :: (Val -> Maybe a) -> (b -> Maybe Val) -> (a -> b) -> Val
vOp1 p f op = F $ \x -> do
  a <- p x
  f $ op a

vOp2 :: (Val -> Maybe a) -> (Val -> Maybe b) -> (c -> Maybe Val) -> (a -> b -> c) -> Val
vOp2 p1 p2 f op = F $ \x -> do
  a <- p1 x
  return $ F $ \y -> do
    b <- p2 y
    f $ op a b

vBool :: Val -> Maybe Bool
vBool = \case
  B b -> Just b
  _   -> Nothing

vNum :: Val -> Maybe Double
vNum = \case
  N d -> Just d
  _   -> Nothing

vFun :: Val -> Maybe (Val -> Maybe Val)
vFun = \case
  F g -> Just g
  _   -> Nothing

(.|.) :: (Val -> Maybe a) -> (Val -> Maybe b) -> Val -> Maybe (Either a b)
(.|.) p1 p2 v = (Left <$> p1 v) <|> (Right <$> p2 v)
infixr 3 .|.

(|.|) :: (a -> a -> Maybe c) -> (b -> b -> Maybe c)
      -> Either a b -> Either a b -> Maybe c
f |.| g = curry $ \case
  (Left  a,Left  b) -> f a b
  (Right a,Right b) -> g a b
  _                 -> Nothing
infixr 3 |.|

(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) = (.) . (.)
infixr 8 .:

