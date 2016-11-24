{-# LANGUAGE FlexibleContexts, InstanceSigs, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa.Types (FailureInfo(..), ResultInfo(..), ResultList(..),
                          Grammar, GrammarDerived(..), Parser(..), (<<|>),
                          concede, succeed, gd2rl, fixGrammar, fixGrammarInput, selfReferring)
where

import Control.Applicative
import Control.Monad (Monad(..), MonadPlus(..))
import Data.Either (either)
import Data.Function (fix)
import Data.Functor.Classes (Show1(liftShowsPrec))
import Data.Monoid (Monoid(mappend, mempty), All(..), (<>))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(tails))
import Data.Word (Word64)

import qualified Rank2

import Prelude hiding (iterate, null)


-- | Parser of streams of type `s`, as a part of grammar type `g`, producing a value of type `r`
newtype Parser g s r = P {parseP :: forall r'. Maybe (GrammarResults g s) -> s -> [(GrammarResults g s, s)]
                                 -> (ResultInfo g s r -> GrammarDerived g s (ResultList g s r'))
                                 -> (FailureInfo -> GrammarDerived g s (ResultList g s r'))
                                 -> GrammarDerived g s (ResultList g s r')}
newtype DerivedResultList g s r = DerivedResultList {derivedResultList :: GrammarDerived g s (ResultList g s r)}
newtype ResultList g s r = ResultList {resultList :: Either FailureInfo [ResultInfo g s r]}
data ResultInfo g s r = ResultInfo !(Maybe (GrammarResults g s)) !s ![(GrammarResults g s, s)] !r
data FailureInfo =  FailureInfo !Int Word64 [String] deriving (Eq, Show)
data GrammarDerived g s a = GrammarDerived a (GrammarResults g s -> a)
type Grammar g s = g (Parser g s)
type GrammarResults g s = g (ResultList g s)

concede :: FailureInfo -> GrammarDerived g s (ResultList g s r)
concede a = GrammarDerived rl (const rl)
   where rl = ResultList (Left a)

succeed :: ResultInfo g s r -> GrammarDerived g s (ResultList g s r)
succeed a = GrammarDerived (ResultList $ Right [a]) (const mempty)

-- | Tie the knot on a 'GrammarBuilder' and turn it into a 'Grammar'
fixGrammar :: forall g s. Rank2.Reassemblable g => (Grammar g s -> Grammar g s) -> Grammar g s
fixGrammar gf = fix (gf . selfReferring)

selfReferring :: Rank2.Reassemblable g => Grammar g s -> Grammar g s
selfReferring = Rank2.reassemble nonTerminal
   where nonTerminal :: forall g s r. (forall p. g p -> p r) -> g (Parser g s) -> Parser g s r
         nonTerminal f _ = P p
            where p :: forall r'. Maybe (GrammarResults g s) -> s -> [(GrammarResults g s, s)]
                    -> (ResultInfo g s r -> GrammarDerived g s (ResultList g s r'))
                    -> (FailureInfo -> GrammarDerived g s (ResultList g s r'))
                    -> GrammarDerived g s (ResultList g s r')
                  p g _ _ rc fc = maybe (GrammarDerived mempty f') (continue . resultList . f) g
                     where continue :: Either FailureInfo [ResultInfo g s r] -> GrammarDerived g s (ResultList g s r')
                           continue (Left (FailureInfo strength pos msgs)) = fc (FailureInfo (succ strength) pos msgs)
                           continue (Right rs) = foldMap rc rs
                           f' :: GrammarResults g s -> ResultList g s r'
                           f' gr = case resultList (f gr)
                                   of Left err -> ResultList (Left err)
                                      Right rs -> gd2rl gr (foldMap rc rs)

fixGrammarInput :: forall s g. (FactorialMonoid s, Rank2.Apply g, Rank2.Traversable g) =>
                   Grammar g s -> Grammar g s -> s -> [(GrammarResults g s, s)]
fixGrammarInput final grammar input = parseTailWith input $ foldr parseTail [] (tails input)
   where parseTail :: s -> [(GrammarResults g s, s)] -> [(GrammarResults g s, s)]
         parseTail s parsedTail = (collectGrammarResults gpr, s):parsedTail
            where gpr = Rank2.fmap (\p-> DerivedResultList $ parseP p Nothing s parsedTail succeed concede) grammar
         parseTailWith :: s -> [(GrammarResults g s, s)] -> [(GrammarResults g s, s)]
         parseTailWith s parsed@((gh, _):_) = (collectGrammarResults gpr, input):parsed
            where gpr = Rank2.fmap (\p-> DerivedResultList $ parseP p (Just gh) s parsed succeed concede) final
         parseTailWith _ [] = error "Impossible"

collectGrammarResults :: (Rank2.Apply g, Rank2.Traversable g) => g (DerivedResultList g s) -> GrammarResults g s
collectGrammarResults gpr = foldr1 (Rank2.liftA2 (<>)) (iterate rf rl [])
   where GrammarDerived rl rf = Rank2.traverse derivedResultList gpr

iterate :: Rank2.Foldable g =>
           (GrammarResults g s -> GrammarResults g s) -> GrammarResults g s -> [GrammarResults g s]
        -> [GrammarResults g s]
iterate f n ns = if getAll (Rank2.foldMap (either (const mempty) (All . null) . resultList) n')
                 then n':n:ns else iterate f n' (n:ns)
   where n' = f n

gd2rl :: GrammarResults g s -> GrammarDerived g s (ResultList g s r) -> ResultList g s r
gd2rl gr (GrammarDerived rl rf) = rl <> rf gr

instance Functor (DerivedResultList g s) where
   fmap f (DerivedResultList gd) = DerivedResultList ((f <$>) <$> gd)

instance (Show s, Show r) => Show (ResultList g s r) where
   show (ResultList l) = "ResultList (" ++ shows l ")"

instance (Show s, Show r) => Show (ResultInfo g s r) where
   show (ResultInfo _ s t r) = "(ResultInfo " ++ show s ++ " " ++ show (length t) ++ " " ++ shows r ")"

instance (Show s) => Show1 (ResultList g s) where
   liftShowsPrec _ _ prec (ResultList (Left err)) rest =
      "ResultList " ++ showsPrec prec err rest
   liftShowsPrec _ sl prec (ResultList (Right l)) rest =
      "ResultList (Right " ++ showsPrec prec (f <$> l) (")" ++ sl (g <$> l) rest)
      where f (ResultInfo _ s t _) = (s, snd <$> take 1 t)
            g (ResultInfo _ _ _ r) = r

instance Functor (ResultInfo g s) where
   fmap f (ResultInfo g s t r) = ResultInfo g s t (f r)

instance Functor (ResultList g s) where
   fmap f (ResultList l) = ResultList ((fourth <$>) <$> l)
      where fourth (ResultInfo a b c d) = ResultInfo a b c (f d)

instance Monoid (ResultList g s r) where
   mempty = ResultList (Left $ FailureInfo 0 maxBound ["empty"])
   rl1@(ResultList (Left (FailureInfo s1 pos1 exp1))) `mappend` rl2@(ResultList (Left (FailureInfo s2 pos2 exp2)))
      | s1 < s2 = rl2
      | s1 > s2 = rl1
      | otherwise = ResultList (Left $ FailureInfo s1 pos' exp')
      where (pos', exp') | pos1 < pos2 = (pos1, exp1)
                         | pos1 > pos2 = (pos2, exp2)
                         | otherwise = (pos1, exp1 <> exp2)
   ResultList (Right []) `mappend` rl = rl
   rl `mappend` ResultList (Right []) = rl
   ResultList Left{} `mappend` rl = rl
   rl `mappend` ResultList Left{} = rl
   ResultList (Right a) `mappend` ResultList (Right b) = ResultList (Right $ a `mappend` b)

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

instance Applicative (Parser g s) where
   pure a = P (\g s t rc _fc-> rc $ ResultInfo g s t a)
   (<*>) :: forall a b. Parser g s (a -> b) -> Parser g s a -> Parser g s b
   P p <*> P q = P r
      where r :: forall r'. Maybe (GrammarResults g s) -> s -> [(GrammarResults g s, s)]
               -> (ResultInfo g s b -> GrammarDerived g s (ResultList g s r'))
               -> (FailureInfo -> GrammarDerived g s (ResultList g s r'))
               -> GrammarDerived g s (ResultList g s r')
            r g s t rc fc = p g s t rc' fc
               where rc' :: ResultInfo g s (a -> b) -> GrammarDerived g s (ResultList g s r')
                     rc' (ResultInfo g' s' t' f) = q g' s' t' (rc'' f) fc
                     rc'' :: (a -> b) -> ResultInfo g s a -> GrammarDerived g s (ResultList g s r')
                     rc'' f (ResultInfo g' s' t' a) = rc (ResultInfo g' s' t' $ f a)

instance Alternative (Parser g s) where
   empty = P (\_g _s _t _rc fc-> fc $ FailureInfo 0 maxBound [])
   P p <|> P q = P (\g s t rc fc-> p g s t rc fc <> q g s t rc fc)

infixl 3 <<|>
(<<|>) :: Parser g s r -> Parser g s r -> Parser g s r
P p <<|> P q = P (\g s t rc fc-> p g s t rc $
                    \ f1@(FailureInfo strength1 pos1 exp1)-> q g s t rc $
                    \ f2@(FailureInfo strength2 pos2 exp2)-> fc $
                       if strength1 < strength2 then f2
                       else if strength1 > strength2 then f1
                       else let (pos', exp') | pos1 < pos2 = (pos1, exp1)
                                             | pos1 > pos2 = (pos2, exp2)
                                             | otherwise = (pos1, exp1 <> exp2)
                            in FailureInfo strength1 pos' exp')

instance Monad (Parser g s) where
   return = pure
   (>>=) :: forall a b. Parser g s a -> (a -> Parser g s b) -> Parser g s b
   P p >>= f = P q
      where q :: forall r'. Maybe (GrammarResults g s) -> s -> [(GrammarResults g s, s)]
               -> (ResultInfo g s b -> GrammarDerived g s (ResultList g s r'))
               -> (FailureInfo -> GrammarDerived g s (ResultList g s r'))
               -> GrammarDerived g s (ResultList g s r')
            q g s t rc fc = p g s t rc' fc
               where rc' (ResultInfo g' s' t' r) = parseP (f r) g' s' t' rc fc
   (>>) = (*>)
   fail msg = P (\_ _ _ _ fc-> fc $ FailureInfo 0 maxBound [msg])

instance MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend
