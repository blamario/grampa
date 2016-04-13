{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa where

import Control.Applicative
import Control.Arrow (second)
import Data.Function(fix)
import Data.Monoid (Monoid, mappend, mempty, (<>))
import Data.Monoid.Cancellative (LeftReductiveMonoid (stripPrefix))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(length, splitPrimePrefix, tails))
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Textual as Textual
import Prelude hiding (length, null)

class Functor1 f where
   fmap1 :: (forall a. g a -> h a) -> f g -> f h

class Functor1 f => Foldable1 f where
   foldMap1 :: Monoid m => (forall a. g a -> m) -> f g -> m

class Foldable1 f => Traversable1 f where
   traverse1 :: Applicative m => (forall a. g a -> m (h a)) -> f g -> m (f h)

class Functor1 f => Reassemblable f where
   composePer :: (f g -> f g) -> (f g -> f g) -> (f g -> f g)
   reassemble :: (forall a. (f g -> g a) -> f g -> h a) -> f g -> f h
   reassemble' :: (forall a. (f g -> g a) -> (g a -> f g) -> f g -> h a) -> f g -> f h

data Parser t s r = Failure String
                  | Result [(t (Parser t s), s)] r
                  | Choice (Parser t s r) (Parser t s r)
                  | Delay (Parser t s r) ([(t (Parser t s), s)] -> Parser t s r)
                  | Recursive (Parser t s r)

instance (Show r, Show s, Show (t (Parser t s))) => Show (Parser t s r) where
   showsPrec _ (Failure s) rest = "(Failure " ++ shows s (")" ++ rest)
   showsPrec prec (Result s r) rest
      | prec > 0 = "(Result " ++ foldr (\(t, s)-> showsPrec (prec - 1) t . shows s) (" " ++ shows r (")" ++ rest)) s
      | otherwise = "Result" ++ rest
   showsPrec prec (Choice p1 p2) rest = "(Choice " ++ showsPrec prec p1 (" " ++ showsPrec prec p2 (")" ++ rest))
   showsPrec prec (Recursive p) rest
      | prec > 0 = "(Recursive " ++ showsPrec (prec - 1) p (")" ++ rest)
      | otherwise = "Recursive" ++ rest
   showsPrec prec (Delay e f) rest = "(Delay " ++ showsPrec prec e (")" ++ rest)

type Grammar t s = t (Parser t s) -> t (Parser t s)

fixGrammar :: (MonoidNull s, Reassemblable t) => (t (Parser t s) -> t (Parser t s)) -> t (Parser t s)
fixGrammar gf = tieRecursion $ fix (composePer gf (fmap1 $ Recursive) . reassemble (\f g-> nt f g))

fixGrammar' :: Reassemblable t => (t (Parser t s) -> t (Parser t s)) -> t (Parser t s)
fixGrammar' = fix . (. reassemble nt)

tieRecursion :: (MonoidNull s, Reassemblable t) => t (Parser t s) -> t (Parser t s)
tieRecursion = reassemble' tie

tie :: (MonoidNull s, Functor1 g) =>
        (g (Parser g s) -> Parser g s r)
     -> (Parser g s r -> g (Parser g s))
     -> g (Parser g s)
     -> Parser g s r
tie get set g = case separate (get g)
                of (p, Failure{}) -> p
                   (Failure{}, _) -> Failure "Unlimited left recursion"
                   (nonRecursive, recursive) -> iterateMany nonRecursive (\p-> feed [(set p, mempty)] recursive)
   where separate (Choice p q) = (pn <|> qn, pr <|> qr)
            where (pn, pr) = separate p
                  (qn, qr) = separate q
         separate (Recursive p) = (empty, p)
         separate p = (p, empty)

feedGrammar :: (FactorialMonoid s, Functor1 t) => t (Parser t s) -> s -> t (Parser t s) -> t (Parser t s)
feedGrammar g s = fmap1 (feed $ fixGrammarInput g s)

fixGrammarInput :: forall s t. (FactorialMonoid s, Functor1 t) => t (Parser t s) -> s -> [(t (Parser t s), s)]
fixGrammarInput parsers s = foldr parseTail [] (tails s)
   where parseTail input parsedTail = parsedInput
            where parsedInput = (fmap1 (feed parsedInput) parsers, input):parsedTail

nt :: (t (Parser t s) -> Parser t s r) -> t (Parser t s) -> Parser t s r
nt f g = Delay (f g) (\((t, _):_)-> f t)

feed :: (MonoidNull s, Functor1 t) => [(t (Parser t s), s)] -> Parser t s r -> Parser t s r
feed [] p = p
feed s (Choice p q) = feed s p <|> feed s q
feed s (Delay _ f) = f s
feed s (Failure msg) = Failure msg
feed s (Result t r) = Result (foldr refeed s t) r
   where refeed (t, s') rest
            | null s' = rest
            | otherwise = (fmap1 (feed s) t, s' <> s''):rest
         s'' = snd (head s)
feed s (Recursive p) = feed s p

feedEnd :: (MonoidNull s, Functor1 t) => Parser t s r -> Parser t s r
feedEnd (Choice p q) = feedEnd p <|> feedEnd q
feedEnd (Delay e _) = feedEnd e
feedEnd (Recursive p) = Recursive (feedEnd p)
feedEnd p = p

results :: (FactorialMonoid s, Functor1 t) => Parser t s r -> [(r, [(t (Parser t s), s)])]
results Failure{} = []
results (Result s r) = [(r, s)]
results (Choice p q) = results p <> results q
results (Delay e _) = results e
results (Recursive p) = findFixPoint Nothing 0 p
   where findFixPoint l d p = let r = resultsToDepth d p
                                  l' = Just $ minimum $ (length . inputWith . snd) <$> r
                              in if l == l'
                                 then r
                                 else findFixPoint l' (succ d) p

resultsToDepth :: (MonoidNull s, Functor1 t) => Int -> Parser t s r -> [(r, [(t (Parser t s), s)])]
resultsToDepth _ Failure{} = []
resultsToDepth _ (Result s r) = [(r, s)]
resultsToDepth d (Choice p q) = resultsToDepth d p <> resultsToDepth d q
resultsToDepth d (Recursive p)
   | d > 0 = resultsToDepth (pred d) p
   | otherwise = []
resultsToDepth d (Delay e _) = resultsToDepth d e

resultPart :: (r -> r) -> Parser t s r -> Parser t s r
resultPart f p = f <$> p

instance Functor (Parser t s) where
   fmap f (Choice p q) = Choice (fmap f p) (fmap f q)
   fmap g (Delay e f) = Delay (fmap g e) (fmap g . f)
   fmap f (Failure msg) = Failure msg
   fmap f (Result s r) = Result s (f r)
   fmap f (Recursive p) = Recursive (fmap f p)

instance (MonoidNull s, Functor1 t) => Applicative (Parser t s) where
   pure = Result []
   Choice p q <*> r = p <*> r <|> q <*> r
   Delay e f <*> p = Delay (e <*> p) ((<*> p) . f)
   Failure msg <*> _ = Failure msg
   Result s r <*> p = r <$> feed s p
   Recursive p <*> q = Recursive (p <*> q)

instance (MonoidNull s, Functor1 t) => Alternative (Parser t s) where
   empty = Failure "empty"
   p <|> Failure{} = p
   Failure{} <|> p = p
--   Delay e f <|> p = Delay (e <|> feedEnd p) (\i-> f i <|> feed i p)
--   p <|> Delay e f = Delay (feedEnd p <|> e) (\i-> feed i p <|> f i)
   p <|> q = Choice p q

instance (MonoidNull s, Functor1 t) => Monad (Parser t s) where
   return = pure
   Result s r >>= f = feed s (f r)
   Choice p q >>= f = (p >>= f) <|> (q >>= f)
   Delay e f >>= g = Delay (e >>= g) ((>>= g) . f)
   Failure msg >>= f = Failure msg
   Recursive p >>= f = Recursive (p >>= f)
   (>>) = (*>)
   fail = Failure

iterateMany :: (MonoidNull s, Functor1 t) => Parser t s r -> (Parser t s r -> Parser t s r) -> Parser t s r
iterateMany p f = p >>= (\r-> return r <|> iterateMany (f $ return r) f)

-- | A parser that fails on any input and succeeds at its end
endOfInput :: (MonoidNull s, Functor1 t) => Parser t s ()
endOfInput = Delay (pure ()) (\s-> if null (inputWith s) then endOfInput else Failure "endOfInput")

string :: (Show s, LeftReductiveMonoid s, FactorialMonoid s, Functor1 t) => s -> Parser t s s
string x | null x = pure x
string x = Delay (Failure $ "string " ++ show x) $
           \case i@((_, y):_)-> case (stripPrefix x y, stripPrefix y x)
                                of (Just y', _) -> Result (drop (length x) i) x
                                   (Nothing, Nothing) -> Failure "string"
                                   (Nothing, Just x') -> string x' *> pure x
                 [] -> string x

takeCharsWhile :: (TextualMonoid s, Functor1 t) => (Char -> Bool) -> Parser t s s
takeCharsWhile pred = while
   where while = Delay (pure mempty) f
         f i@((_, s):_) = let (prefix, suffix) = Textual.span (const False) pred s
                          in if null suffix then resultPart (mappend prefix) while
                             else let (prefix', suffix') = Textual.span (const True) (const False) suffix
                                  in if null prefix' then Result (drop (length prefix) i) prefix
                                     else resultPart (mappend prefix . mappend prefix') $
                                          f $ drop (length prefix + length prefix') i

takeCharsWhile1 :: (TextualMonoid s, Functor1 t) => (Char -> Bool) -> Parser t s s
takeCharsWhile1 pred = Delay (Failure "takeWhile1") f
   where f i@((_, s):_) | null s = takeCharsWhile1 pred
                        | otherwise = let (prefix, suffix) = Textual.span (const False) pred s
                                          (prefix', suffix') = Textual.span (const True) (const False) suffix
                                          rest = drop (length prefix + length prefix') i
                                      in if null prefix
                                         then if null prefix' then Failure "takeCharsWhile1"
                                              else mappend prefix' <$> f rest
                                         else if null suffix then resultPart (mappend prefix) (takeCharsWhile pred)
                                              else if null prefix' then Result (drop (length prefix) i) prefix
                                                   else resultPart (mappend prefix . mappend prefix')
                                                                   (feed rest $ takeCharsWhile pred)

satisfyChar :: (TextualMonoid s, Functor1 t) => (Char -> Bool) -> Parser t s s
satisfyChar predicate = p
   where p = Delay (Failure "satisfyChar") f
         f [] = p
         f i@((_, s):tl) = case splitPrimePrefix s
                           of Just (first, rest) ->
                                 case Textual.characterPrefix first
                                 of Just c -> if predicate c then Result tl first else Failure "satisfyChar"
                                    Nothing -> if null rest then p else Failure "satisfyChar"
                              Nothing -> p

inputWith [] = mempty
inputWith ((_, s):_) = s
