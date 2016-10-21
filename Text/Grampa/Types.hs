{-# LANGUAGE FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa.Types (FailureInfo(..), ResultInfo(..), ResultList(..), InputStatus(Advanced, Stuck),
                          Grammar, GrammarBuilder, Parser(..),
                          succeed, concede, fixGrammar, fixGrammarInput)
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

import Text.Grampa.Classes

import Prelude hiding (iterate, null)

data InputStatus = Advanced | Stuck deriving (Eq, Show)

-- | Parser of streams of type `s`, as a part of grammar type `g`, producing a value of type `r`
newtype Parser g s r = P {parseP :: s -> [(GrammarResults g s, s)] -> GrammarDerived g s (ResultList g s r)}
newtype GrammarParseResults g s r = GrammarParseResults {grammarParseResults :: GrammarDerived g s (ResultList g s r)}
type Grammar g s = g (Parser g s)
type GrammarBuilder g g' s = g (Parser g' s) -> g (Parser g' s)
type GrammarResults g s = g (ResultList g s)
newtype ResultList g s r = ResultList {resultList :: Either FailureInfo [ResultInfo g s r]}
data ResultInfo g s r = ResultInfo InputStatus [(GrammarResults g s, s)] r
data FailureInfo =  FailureInfo Word64 [String] deriving (Eq, Show)
data GrammarDerived g s a = GrammarDerived a (GrammarResults g s -> a)

succeed :: ResultInfo g s r -> GrammarDerived g s (ResultList g s r)
succeed a = GrammarDerived (ResultList $ Right [a]) (const $ ResultList $ Right [])

concede :: FailureInfo -> GrammarDerived g s (ResultList g s r)
concede a = GrammarDerived (ResultList $ Left a) (const $ ResultList $ Right [])

-- | Tie the knot on a 'GrammarBuilder' and turn it into a 'Grammar'
fixGrammar :: forall g s. (Reassemblable g, Traversable1 g) => (Grammar g s -> Grammar g s) -> Grammar g s
fixGrammar gf = fix . (. reassemble nt) $ gf
   where nt :: (forall p. g p -> p r) -> g (Parser g s) -> Parser g s r
         nt f _ = P (\s t-> GrammarDerived mempty f)

fixGrammarInput :: forall s g. (FactorialMonoid s, Alternative1 g, Traversable1 g) =>
                   Grammar g s -> s -> [(GrammarResults g s, s)]
fixGrammarInput g s = foldr (parseTail g) [] (tails s)
   where parseTail :: (FactorialMonoid s, Alternative1 g, Traversable1 g) =>
                      Grammar g s -> s -> [(GrammarResults g s, s)] -> [(GrammarResults g s, s)]
         parseTail g input parsedTail = parsedInput
            where parsedInput = (grammarResults' g', input):parsedTail
                  g' :: g (GrammarParseResults g s)
                  g' = fmap1 (\(P p)-> GrammarParseResults $ p input parsedTail) g
                  grammarResults' :: forall s g. (MonoidNull s, Traversable1 g, Alternative1 g) =>
                                     g (GrammarParseResults g s) -> GrammarResults g s
                  grammarResults' g = foldr1 choose1 (iterate rf [rn])
                     where GrammarDerived rn rf = traverse1 grammarParseResults g

iterate :: Foldable1 g => (GrammarResults g s -> GrammarResults g s) -> [GrammarResults g s] -> [GrammarResults g s]
iterate f ns@(n:_) = if getAll (foldMap1 (either (const mempty) (All . null) . resultList) n')
                     then n':ns else iterate f (n':ns)
   where n' = f n

gd2rl :: GrammarResults g s -> GrammarDerived g s (ResultList g s r) -> ResultList g s r
gd2rl gr (GrammarDerived rl f) = rl <> f gr

instance Functor (GrammarParseResults g s) where
   fmap f (GrammarParseResults gd) = GrammarParseResults ((f <$>) <$> gd)

instance (Show (g (ResultList g s)), Show s, Show r) => Show (ResultList g s r) where
   show (ResultList l) = "ResultList (" ++ shows l ")"

instance (Show (g (ResultList g s)), Show s, Show r) => Show (ResultInfo g s r) where
   show (ResultInfo is@Advanced i r) = "(ResultInfo " ++ show is ++ " " ++ show (length i) ++ " " ++ shows r ")"
   show (ResultInfo is@Stuck _ r) = "(ResultInfo " ++ show is ++ " " ++ shows r ")"

instance (Show (g (ResultList g s)), Show s) => Show1 (ResultList g s) where
   liftShowsPrec sp sl prec (ResultList (Left err)) rest =
      "ResultList " ++ showsPrec prec err rest
   liftShowsPrec sp sl prec (ResultList (Right l)) rest =
      "ResultList (Right " ++ showsPrec prec (f <$> l) (")" ++ sl (g <$> l) rest)
      where f (ResultInfo is grs _) = (is, snd <$> take 1 grs)
            g (ResultInfo _ _ r) = r

instance Functor (ResultList g s) where
   fmap f (ResultList l) = ResultList ((third <$>) <$> l)
      where third (ResultInfo a b c) = ResultInfo a b (f c)

instance Applicative (ResultList g s) where
   pure r = ResultList (Right [ResultInfo Stuck [] r])
   ResultList a <*> ResultList b = ResultList (apply <$> a <*> b)
      where apply [] _ = []
            apply _ [] = []
            apply (ResultInfo is1 i1 r1 : rest1) (ResultInfo is2 i2 r2 : rest2)
               | is1 == is2 && length i1 == length i2 = ResultInfo is1 i1 (r1 r2) : apply rest1 rest2
   
instance Alternative (ResultList g s) where
   empty = ResultList (Left $ FailureInfo maxBound ["empty"])
   ResultList (Left f1@(FailureInfo pos1 exp1)) <|> ResultList (Left f2@(FailureInfo pos2 exp2))
      | pos1 < pos2 = ResultList (Left f1)
      | pos2 < pos1 = ResultList (Left f2)
      | otherwise = ResultList (Left $ FailureInfo pos1 (exp1 <> exp2))
   ResultList (Right []) <|> rl = rl
   rl <|> ResultList (Right []) = rl
   ResultList Left{} <|> rl = rl
   rl <|> ResultList Left{} = rl
   ResultList (Right a) <|> ResultList (Right b) = ResultList (Right $ a <|> b)

instance Monoid (ResultList g s r) where
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
   pure a = GrammarDerived a (const a)
   GrammarDerived a fa <*> GrammarDerived b fb = GrammarDerived (a b) (\g-> fa g $ fb g)

instance Functor (Parser g s) where
   fmap f (P p) = P (\s t-> (f <$>) <$> p s t)

instance Monoid s => Applicative (Parser g s) where
   pure a = P (\s t-> succeed $ ResultInfo Stuck undefined a)
   P p <*> P q = P r
      where r s t = GrammarDerived pr' (gr' <> gr'')
               where GrammarDerived (ResultList rl) gr = p s t
                     GrammarDerived pr' gr' = case rl
                        of Left f -> GrammarDerived (ResultList $ Left f) (const $ ResultList $ Right [])
                           Right rs -> foldMap cont rs
--                     gr'' :: GrammarResults g s -> ParseResults b
                     gr'' g' = either (ResultList . Left) (foldMap $ gd2rl g' . cont) (resultList $ gr g')
                     cont (ResultInfo Stuck _ r) = (r <$>) <$> q s t
                     cont (ResultInfo Advanced t'@((g', s'):t'') r) =
                        GrammarDerived (ResultList $ ((advance <$>) <$>) $ resultList $ gd2rl g' $ q s' t'')
                                       (const $ ResultList $ Right [])
                        where advance (ResultInfo Stuck _ r') = ResultInfo Advanced t' (r r')
                              advance (ResultInfo Advanced t' r') = ResultInfo Advanced t' (r r')

instance Monoid s => Alternative (Parser g s) where
   empty = P (\s t-> concede $ FailureInfo maxBound [])
   P p <|> P q = P (\s t-> p s t <> q s t)

instance Monoid s => Monad (Parser g s) where
   return = pure
   P p >>= f = P q
      where q s t = GrammarDerived pr' (gr' <> gr'')
               where GrammarDerived (ResultList rl) gr = p s t
                     GrammarDerived pr' gr' = case rl
                        of Left f -> GrammarDerived (ResultList $ Left f) (const $ ResultList $ Right [])
                           Right rs -> foldMap cont rs
--                     gr'' :: GrammarResults g s -> ParseResults b
                     gr'' g' = either (ResultList . Left) (foldMap $ gd2rl g' . cont) (resultList $ gr g')
                     cont (ResultInfo Stuck _ r) = parseP (f r) s t
                     cont (ResultInfo Advanced t'@((g', s'):t'') r) =
                        GrammarDerived (ResultList $ ((advance <$>) <$>) $
                                        resultList $ gd2rl g' $ parseP (f r) s' t'') (const $ ResultList $ Right [])
                        where advance (ResultInfo Stuck _ r) = ResultInfo Advanced t' r
                              advance r = r
   (>>) = (*>)
   fail msg = P (\_ _-> concede $ FailureInfo maxBound [msg])

instance Monoid s => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance (Functor1 g, MonoidNull s, Monoid x) => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend
