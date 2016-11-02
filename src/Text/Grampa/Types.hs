{-# LANGUAGE InstanceSigs, FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa.Types (FailureInfo(..), ResultInfo(..), ResultList(..),
                          Grammar, GrammarDerived(..), Parser(..),
                          concede, gd2rl, fixGrammar, fixGrammarInput)
where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (Monad(..), MonadPlus(..))
import Control.Monad.Trans.State (State, evalState, get, modify)
import Data.Either (either)
import Data.Foldable (asum)
import Data.Function (fix)
import Data.Functor.Classes (Show1(liftShowsPrec))
import Data.Functor.Compose (Compose(Compose, getCompose))
import Data.Monoid (Monoid(mappend, mempty), All(..), (<>))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(spanMaybe', splitPrimePrefix, tails))
import Data.Word (Word64)

import qualified Rank2

import Prelude hiding (iterate, null)


-- | Parser of streams of type `s`, as a part of grammar type `g`, producing a value of type `r`
newtype Parser g s r = P {parseP :: forall r'. Maybe (GrammarResults g s) -> s -> [(GrammarResults g s, s)]
                                 -> (ResultInfo g s r -> GrammarDerived g s (ResultList g s r'))
                                 -> (FailureInfo -> GrammarDerived g s (ResultList g s r'))
                                 -> GrammarDerived g s (ResultList g s r')}
newtype GrammarParseResults g s r = GrammarParseResults {grammarParseResults :: GrammarDerived g s (ResultList g s r)}
newtype ResultList g s r = ResultList {resultList :: Either FailureInfo [ResultInfo g s r]}
data ResultInfo g s r = ResultInfo !(Maybe (GrammarResults g s)) !s ![(GrammarResults g s, s)] !r
data FailureInfo =  FailureInfo !Int Word64 [String] deriving (Eq, Show)
data GrammarDerived g s a = GrammarDerived a (GrammarResults g s -> a)
type Grammar g s = g (Parser g s)
type GrammarResults g s = g (ResultList g s)

concede :: FailureInfo -> GrammarDerived g s (ResultList g s r)
concede a = GrammarDerived (ResultList $ Left a) (const $ ResultList $ Right [])

-- | Tie the knot on a 'GrammarBuilder' and turn it into a 'Grammar'
fixGrammar :: forall g s. (Monoid s, Rank2.Reassemblable g, Rank2.Traversable g) =>
              (Grammar g s -> Grammar g s) -> Grammar g s
fixGrammar gf = fix . (. Rank2.reassemble nt) $ gf
   where nt :: forall r. (forall p. g p -> p r) -> g (Parser g s) -> Parser g s r
         nt f _ = P p
            where p :: forall r'. Maybe (GrammarResults g s) -> s -> [(GrammarResults g s, s)]
                    -> (ResultInfo g s r -> GrammarDerived g s (ResultList g s r'))
                    -> (FailureInfo -> GrammarDerived g s (ResultList g s r'))
                    -> GrammarDerived g s (ResultList g s r')
                  p g s t rc fc = maybe (GrammarDerived mempty f') (continue . resultList . f) g
                     where continue :: Either FailureInfo [ResultInfo g s r] -> GrammarDerived g s (ResultList g s r')
                           continue (Left (FailureInfo strength pos msgs)) = fc (FailureInfo (succ strength) pos msgs)
                           continue (Right rs) = foldMap rc rs
                           f' :: GrammarResults g s -> ResultList g s r'
                           f' gr = case resultList (f gr)
                                   of Left err -> ResultList (Left err)
                                      Right rs -> gd2rl gr (foldMap rc rs)

fixGrammarInput :: forall s g. (FactorialMonoid s, Rank2.Alternative g, Rank2.Traversable g) =>
                   Grammar g s -> s -> [(GrammarResults g s, s)]
fixGrammarInput g s = foldr (parseTail g) [] (tails s)
   where parseTail :: (FactorialMonoid s, Rank2.Alternative g, Rank2.Traversable g) =>
                      Grammar g s -> s -> [(GrammarResults g s, s)] -> [(GrammarResults g s, s)]
         parseTail g input parsedTail = parsedInput
            where parsedInput = (grammarResults' g', input):parsedTail
                  g' :: g (GrammarParseResults g s)
                  g' = Rank2.fmap (\(P p)-> GrammarParseResults $ p Nothing input parsedTail rc fc) g
                  fc = concede
                  rc r = GrammarDerived (ResultList $ Right [r]) (const mempty)
                  grammarResults' :: forall s g. (MonoidNull s, Rank2.Traversable g, Rank2.Alternative g) =>
                                     g (GrammarParseResults g s) -> GrammarResults g s
                  grammarResults' g = foldr1 Rank2.choose (iterate fc [rn])
                     where GrammarDerived rn fc = Rank2.traverse grammarParseResults g

iterate :: Rank2.Foldable g =>
           (GrammarResults g s -> GrammarResults g s) -> [GrammarResults g s] -> [GrammarResults g s]
iterate f ns@(n:_) = if getAll (Rank2.foldMap (either (const mempty) (All . null) . resultList) n')
                     then n':ns else iterate f (n':ns)
   where n' = f n

gd2rl :: GrammarResults g s -> GrammarDerived g s (ResultList g s r) -> ResultList g s r
gd2rl gr (GrammarDerived rl f) = rl

instance Functor (GrammarParseResults g s) where
   fmap f (GrammarParseResults gd) = GrammarParseResults ((f <$>) <$> gd)

instance (Show (g (ResultList g s)), Show s, Show r) => Show (ResultList g s r) where
   show (ResultList l) = "ResultList (" ++ shows l ")"

instance (Show (g (ResultList g s)), Show s, Show r) => Show (ResultInfo g s r) where
   show (ResultInfo g s t r) = "(ResultInfo " ++ show s ++ " " ++ show (length t) ++ " " ++ shows r ")"

instance (Show (g (ResultList g s)), Show s) => Show1 (ResultList g s) where
   liftShowsPrec sp sl prec (ResultList (Left err)) rest =
      "ResultList " ++ showsPrec prec err rest
   liftShowsPrec sp sl prec (ResultList (Right l)) rest =
      "ResultList (Right " ++ showsPrec prec (f <$> l) (")" ++ sl (g <$> l) rest)
      where f (ResultInfo g s t _) = (s, snd <$> take 1 t)
            g (ResultInfo _ _ _ r) = r

instance Functor (ResultInfo g s) where
   fmap f (ResultInfo g s t r) = ResultInfo g s t (f r)

instance Functor (ResultList g s) where
   fmap f (ResultList l) = ResultList ((fourth <$>) <$> l)
      where fourth (ResultInfo a b c d) = ResultInfo a b c (f d)

instance Monoid s => Applicative (ResultList g s) where
   pure r = ResultList (Right [ResultInfo Nothing mempty [] r])
   ResultList a <*> ResultList b = ResultList (apply <$> a <*> b)
      where apply [] _ = []
            apply _ [] = []
            apply (ResultInfo g1 s1 t1 r1 : rest1) (ResultInfo g2 s2 t2 r2 : rest2)
               | length t1 == length t2 = ResultInfo g1 s1 t1 (r1 r2) : apply rest1 rest2

instance Monoid s => Alternative (ResultList g s) where
   empty = ResultList (Left $ FailureInfo 0 maxBound ["empty"])
   rl1@(ResultList (Left (FailureInfo s1 pos1 exp1))) <|> rl2@(ResultList (Left (FailureInfo s2 pos2 exp2)))
      | s1 < s2 = rl2
      | s1 > s2 = rl1
      | otherwise = ResultList (Left $ FailureInfo s1 pos' exp')
      where (pos', exp') | pos1 < pos2 = (pos1, exp1)
                         | pos1 > pos2 = (pos2, exp2)
                         | otherwise = (pos1, exp1 <> exp2)
   ResultList (Right []) <|> rl = rl
   rl <|> ResultList (Right []) = rl
   ResultList Left{} <|> rl = rl
   rl <|> ResultList Left{} = rl
   ResultList (Right a) <|> ResultList (Right b) = ResultList (Right $ a <|> b)

instance Monoid s => Monoid (ResultList g s r) where
   mempty = ResultList (Right [])
   mappend a b = a <|> b

instance Show a => Show (GrammarDerived g s a) where
   show (GrammarDerived a _) = "GrammarDerived (" ++ show a ++ " _)"

instance Monoid a => Monoid (GrammarDerived g s a) where
   mempty = GrammarDerived mempty (const mempty)
   mappend (GrammarDerived a fa) (GrammarDerived b fb) = GrammarDerived (a <> b) (\g-> fa g <> fb g)

instance Functor (GrammarDerived g s) where
   fmap f (GrammarDerived a g) = GrammarDerived (f a) (f . g)

instance Applicative (GrammarDerived g s) where
   pure a = GrammarDerived a (error "There's no pure GrammarDerived")
   GrammarDerived a fa <*> GrammarDerived b fb = GrammarDerived (a b) (\g-> fa g $ fb g)

instance Functor (Parser g s) where
   fmap f (P p) = P (\g s t rc fc-> p g s t (rc . (f <$>)) fc)

instance Monoid s => Applicative (Parser g s) where
   pure a = P (\g s t rc fc-> rc $ ResultInfo g s t a)
   (<*>) :: forall g s a b. Parser g s (a -> b) -> Parser g s a -> Parser g s b
   P p <*> P q = P r
      where r :: forall r'. Maybe (GrammarResults g s) -> s -> [(GrammarResults g s, s)]
               -> (ResultInfo g s b -> GrammarDerived g s (ResultList g s r'))
               -> (FailureInfo -> GrammarDerived g s (ResultList g s r'))
               -> GrammarDerived g s (ResultList g s r')
            r g s t rc fc = p g s t rc' fc
               where rc' :: ResultInfo g s (a -> b) -> GrammarDerived g s (ResultList g s r')
                     rc' (ResultInfo g s t f) = q g s t (rc'' f) fc
                     rc'' :: (a -> b) -> ResultInfo g s a -> GrammarDerived g s (ResultList g s r')
                     rc'' f (ResultInfo g s t a) = rc (ResultInfo g s t $ f a)

instance Monoid s => Alternative (Parser g s) where
   empty = P (\g s t rc fc-> fc $ FailureInfo 0 maxBound [])
   P p <|> P q = P (\g s t rc fc-> p g s t rc fc <> q g s t rc fc)

infixl 3 <<|>
(<<|>) :: Monoid s => Parser g s r -> Parser g s r -> Parser g s r
P p <<|> P q = P (\g s t rc fc-> p g s t rc $
                    \ f1@(FailureInfo strength1 pos1 exp1)-> q g s t rc $
                    \ f2@(FailureInfo strength2 pos2 exp2)-> fc $
                       if strength1 < strength2 then f2
                       else if strength1 > strength2 then f1
                       else let (pos', exp') | pos1 < pos2 = (pos1, exp1)
                                             | pos1 > pos2 = (pos2, exp2)
                                             | otherwise = (pos1, exp1 <> exp2)
                            in FailureInfo strength1 pos' exp')

instance Monoid s => Monad (Parser g s) where
   return = pure
   (>>=) :: forall g s a b. Parser g s a -> (a -> Parser g s b) -> Parser g s b
   P p >>= f = P q
      where q :: forall r'. Maybe (GrammarResults g s) -> s -> [(GrammarResults g s, s)]
               -> (ResultInfo g s b -> GrammarDerived g s (ResultList g s r'))
               -> (FailureInfo -> GrammarDerived g s (ResultList g s r'))
               -> GrammarDerived g s (ResultList g s r')
            q g s t rc fc = p g s t rc' fc
               where rc' (ResultInfo g' s' t' r) = parseP (f r) g' s' t' rc fc
   (>>) = (*>)
   fail msg = P (\g s t rc fc-> fc $ FailureInfo 0 maxBound [msg])

instance Monoid s => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance (Rank2.Functor g, MonoidNull s, Monoid x) => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend
