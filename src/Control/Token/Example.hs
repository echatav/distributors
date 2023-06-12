{-# LANGUAGE
FlexibleContexts
, OverloadedStrings
, TemplateHaskell
#-}

module Control.Token.Example where

import Control.Distributor
import Control.Lens
import Control.Token

data SimpleExpression
  = Letters Char Char
  | Digit Char
  -- | Pair SimpleExpression SimpleExpression
  deriving (Show,Eq)
makePrisms ''SimpleExpression

simple' :: PP Maybe String String SimpleExpression SimpleExpression
simple' = mconcat
  [ _Letters <$< token letter >*< token letter
  , _Digit <$< token digit
  -- , _Pair <$< "(" >* simple' >*< "," >* simple' *< ")"
  ]

data Operator
  = AddOp
  | MulOp
  deriving (Show,Eq)
makePrisms ''Operator

data Expression
  = Variable String
  | Literal Integer
  | BinOp Expression Operator Expression
  | IfZero Expression Expression Expression
  deriving (Show,Eq)
makePrisms ''Expression

expression :: PP [] String String Expression Expression
expression = exp2 where
  keywords = ["ifzero","else"]
  identifier
    = (notOneOf keywords . _Cons) <$<
      (token letter >*< several (token letter <> token digit))
  integer = partialIso show' read' <$< several (token digit)
  read' s = case [x | (x,"") <- reads s] of
    [] -> Nothing
    x:_ -> Just (x::Integer)
  show' = Just . show
  parens p = "(" >* p *< ")"
  ops = (_MulOp <$< "*") <> (_AddOp <$< "+")
  spacedOps = optSpace >* ops *< optSpace
  priority MulOp = 1
  priority AddOp = 2
  triple :: Iso (a,b,c) (d,e,f) (a,(b,c)) (d,(e,f))
  triple = dimap (\(a,b,c) -> (a,(b,c))) (fmap (\(a,(b,c)) -> (a,b,c)))
  exp0 = (_Literal <$< integer)
    <> (_Variable <$< identifier)
    <> ((_IfZero . triple) <$< ifzero)
    <> parens (skipSpace >* expression *< skipSpace)
  exp1 = chainl1 exp0 spacedOps (binOpPrio 1)
  exp2 = chainl1 exp1 spacedOps (binOpPrio 2)
  ifzero = "ifzero" >*
    optSpace >* parens expression >*<
    optSpace >* parens expression >*<
    optSpace >* "else" >*
    optSpace >* parens expression
  binOpPrio n = mirrorToken $
    _BinOp . triple . satisfy (\(_,(op,_)) -> priority op == n)
  skipSpace = ignore [] <$< several " "
  optSpace = ignore [()] <$< several " "
  sepSpace = " " *< skipSpace
