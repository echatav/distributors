{-# LANGUAGE
FlexibleContexts
, FlexibleInstances
, LambdaCase
, MultiParamTypeClasses
#-}

module Text.Distributor where

import Control.Applicative
import Control.Distributor
import Data.Bifunctor
import Data.Bool
import Data.Char
import Data.List
import Data.Profunctor

data PP s t a b = PP
  { printer :: a -> s -> Maybe s
  , parser :: t -> [(b, t)]
  }

instance Profunctor (PP s t) where
  dimap f g pp = PP (printer pp . f) (map (first g) . parser pp)

instance Bimodule (PP s t) where
  expel b = PP (\_ -> Just) (\t -> [(b,t)])
  factor f g pp0 pp1 = PP printer' parser'
    where
      printer' a s = do
        let (fa0, fa1) = f a
        s' <- printer pp0 fa0 s
        printer pp1 fa1 s'
      parser' t = do
        (b0, t0) <- parser pp0 t
        (b1, t1) <- first (g b0) <$> parser pp1 t0
        return (b1, t1)

instance Distributor (PP s t) where
  root f = PP (\_ _ -> Nothing) (\_ -> [])
  branch f g pp0 pp1 = PP printer' parser'
    where
      printer' a = either (printer pp0) (printer pp1) (f a)
      parser' t =
        let
          lhs = [(g (Left b0), t0) | (b0,t0) <- parser pp0 t]
          rhs = [(g (Right b1), t1) | (b1,t1) <- parser pp1 t]
        in
          lhs ++ rhs

end :: PP [c] [d] () ()
end = PP (\_ -> Just) (bool [] [((),[])] . null)

class Tokenized s t p where
  tokenized :: (a -> Maybe s) -> (t -> Maybe b) -> p a b
instance Tokenized c d (PP [c] [d]) where
  tokenized f g = PP printer' parser'
    where
      printer' a ts = case f a of
        Nothing -> Nothing
        Just t -> Just (ts <> [t])
      parser' [] = []
      parser' (t:ts) = case g t of
        Nothing -> []
        Just b -> [(b,ts)]

satisfy :: Tokenized a a p => (a -> Bool) -> p a a
satisfy cond = tokenized satiate satiate
  where
    satiate t = bool Nothing (Just t) (cond t)

anyToken :: Tokenized a b p => p a b
anyToken = tokenized Just Just

notToken :: (Eq a, Tokenized a a p) => a -> p a a
notToken c = satisfy (/= c)

token :: (Eq a, Tokenized a a p) => a -> p a a
token c = satisfy (== c)

token_ :: (Eq a, Profunctor p, Tokenized a a p) => a -> p () ()
token_ c = dimap (\_ -> c) (\_ -> ()) (token c)

tokens :: (Eq a, Bimodule p, Tokenized a a p) => [a] -> p [a] [a]
tokens as = dimap (\_ -> ()) (\_ -> as) (tokens_ as)

tokens_ :: (Eq a, Bimodule p, Tokenized a a p) => [a] -> p () ()
tokens_ = \case
  [] -> expel ()
  a:as -> token_ a >* tokens_ as

oneOf :: (Eq a, Tokenized a a p) => [a] -> p a a
oneOf cs = satisfy (`elem` cs)

noneOf :: (Eq a, Tokenized a a p) => [a] -> p a a
noneOf cs = satisfy (`notElem` cs)

control, space
  , lower, upper, alpha, alphaNum, printChar
  , digit, octDigit, hexDigit
  , letter, mark, number, punctuation, symbol, separator
  , ascii, latin1, asciiUpper, asciiLower
  :: Tokenized Char Char p => p Char Char
control = satisfy isControl
space = satisfy isSpace
lower = satisfy isLower
upper = satisfy isUpper
alpha = satisfy isAlpha
alphaNum = satisfy isAlphaNum
printChar = satisfy isPrint
digit = satisfy isDigit
octDigit = satisfy isOctDigit
hexDigit = satisfy isHexDigit
letter = satisfy isLetter
mark = satisfy isMark
number = satisfy isNumber
punctuation = satisfy isPunctuation
symbol = satisfy isSymbol
separator = satisfy isSeparator
ascii = satisfy isAscii
latin1 = satisfy isLatin1
asciiUpper = satisfy isAsciiUpper
asciiLower = satisfy isAsciiLower

-- | CSV example
--
-- >>> let Just txt = printer csv [["foo","bar"],["oof","rab"]] ""
-- >>> putStrLn txt
-- "foo","bar"
-- "oof","rab"
--
-- >>> parser csv txt
-- [([["foo","bar"],["oof","rab"]],"")]
csv :: PP String String [[String]] [[String]]
csv =
  let
    quote = token_ '\"'
    notQuote = notToken '\"'
    newline = token_ '\n'
    comma = token_ ','
    cell = quote >* several notQuote *< quote
    line = sepBy comma cell *< newline
  in
    several line *< end

data Expr = EAdd Expr Expr
          | EInt Int

express :: Expr -> Either (Expr, Expr) String
express = \case
  EAdd x y -> Left (x,y)
  EInt x -> Right (show x)

reexpress :: Either (Expr, Expr) String -> Expr
reexpress = \case
  Left (x,y) -> EAdd x y
  Right x -> EInt (read x)

expr :: PP String String Expr Expr
expr = dimap express reexpress $
  expr >*< expr
  >|< several digit
