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

token :: (a -> Maybe c) -> (d -> Maybe b) -> PP [c] [d] a b
token f g = PP printer' parser'
  where
    printer' a ts = case f a of
      Nothing -> Nothing
      Just t -> Just (ts <> [t])
    parser' [] = []
    parser' (t:ts) = case g t of
      Nothing -> []
      Just b -> [(b,ts)]

satisfy :: (c -> Bool) -> PP [c] [c] c c 
satisfy cond = token satiate satiate
  where
    satiate t = bool Nothing (Just t) (cond t)

char :: Eq c => c -> PP [c] [c] c c
char c = satisfy (== c)

char_ :: Eq c => c -> PP [c] [c] () ()
char_ c = dimap (\_ -> c) (\_ -> ()) (char c)

anyChar :: PP [c] [c] c c
anyChar = token Just Just

string :: Eq c => [c] -> PP [c] [c] [c] [c]
string cs =
  let
    printer' ds es = bool Nothing (Just (cs ++ es)) (cs == ds)
    parser' ds = case stripPrefix cs ds of
      Nothing -> []
      Just es -> [(cs,es)]
  in
    PP printer' parser'

string_ :: Eq c => [c] -> PP [c] [c] () ()
string_ cs = dimap (\_ -> cs) (\_ -> ()) (string cs)

oneOf :: Eq c => [c] -> PP [c] [c] c c
oneOf cs = satisfy (`elem` cs)

noneOf :: Eq c => [c] -> PP [c] [c] c c
noneOf cs = satisfy (`notElem` cs)

control, space
  , lower, upper, alpha, alphaNum, printChar
  , digit, octDigit, hexDigit
  , letter, mark, number, punctuation, symbol, separator
  , ascii, latin1, asciiUpper, asciiLower
  :: PP String String Char Char
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
    quote = '\"'
    newline = '\n'
    comma = ','
    cell = char_ quote >* several (satisfy (/= quote)) *< char_ quote
    line = sepBy (char_ comma) cell *< char_ newline
  in
    several line *< end
