{-# LANGUAGE FlexibleContexts, InstanceSigs, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa.Types (FailureInfo(..), ResultInfo(..), ResultList(..), InitialResultInfo(..), InitialResultList(..),
                          Grammar, GrammarDerived(..), Parser(..), (<<|>),
                          concede, succeed, gd2rl, fixGrammar, fixGrammarInput, primitive, selfReferring)
where

import Control.Applicative
import Control.Monad (Monad(..), MonadPlus(..))
import Data.Either (either)
import Data.Function (fix)
import Data.Functor.Classes (Show1(liftShowsPrec))
import Data.List (genericLength)
import Data.Monoid (Monoid(mappend, mempty), All(..), (<>), Sum(..))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(tails))
import Data.Word (Word64)

import qualified Rank2

import Debug.Trace (trace)

import Prelude hiding (iterate, null)


-- | Parser of streams of type `s`, as a part of grammar type `g`, producing a value of type `r`
data Parser g s r = Parser {continued :: forall r'. [(GrammarResults g s, s)]
                              -> (r -> [(GrammarResults g s, s)] -> ResultList g s r')
                              -> (FailureInfo -> ResultList g s r')
                              -> ResultList g s r',
                            direct :: s -> [(GrammarResults g s, s)] -> InitialResultList g s r,
                            recursive :: g (InitialResultList g s) -> InitialResultList g s r}
newtype DerivedInitialResultList g s r = DerivedInitialResultList {
   derivedInitialResultList :: g (InitialResultList g s) -> InitialResultList g s r}
newtype DerivedResultList g s r = DerivedResultList {derivedResultList :: GrammarResults g s -> ResultList g s r}
newtype InitialResultList g s r = InitialResultList {initialResultList :: Either FailureInfo [InitialResultInfo g s r]}
newtype ResultList g s r = ResultList {resultList :: Either FailureInfo [ResultInfo g s r]}
data ResultInfo g s r = ResultInfo ![(GrammarResults g s, s)] !r
data InitialResultInfo g s r = CompleteResultInfo ![(GrammarResults g s, s)] !r
                             | StuckResultInfo !r
data FailureInfo = FailureInfo !Int Word64 [String] deriving (Eq, Show)
data GrammarDerived g s a = GrammarDerived a (GrammarResults g s -> a)
type Grammar g s = g (Parser g s)
type GrammarResults g s = g (ResultList g s)

concede :: FailureInfo -> ResultList g s r
concede a = ResultList (Left a)

succeed :: r -> [(GrammarResults g s, s)] -> ResultList g s r
succeed r t = ResultList (Right [ResultInfo t r])

uncomplete :: ResultList g s r -> InitialResultList g s r
uncomplete (ResultList (Left err)) = InitialResultList (Left err)
uncomplete (ResultList (Right results)) = InitialResultList (Right $ uncompleteResult <$> results)
   where uncompleteResult (ResultInfo t r) = CompleteResultInfo t r

primitive :: (forall x. s -> [(GrammarResults g s, s)]
                        -> (r -> x)
                        -> (r -> [(GrammarResults g s, s)] -> x)
                        -> (String -> x)
                        -> x)
          -> Parser g s r
primitive parser = Parser{continued= \t@((_, s):t') rc fc ->
                               parser s t' (`rc` t) rc (fc . FailureInfo 0 (genericLength t) . (:[])),
                          direct= \s t-> parser s t rc0 rc (failAt t),
                          recursive= const $ InitialResultList $ Right []}
   where rc0 r = InitialResultList (Right [StuckResultInfo r])
         rc r t' = InitialResultList (Right [CompleteResultInfo t' r])
         failAt t msg = InitialResultList (Left $ FailureInfo 0 (genericLength t) [msg])

-- | Tie the knot on a 'GrammarBuilder' and turn it into a 'Grammar'
fixGrammar :: forall g s. Rank2.Reassemblable g => (Grammar g s -> Grammar g s) -> Grammar g s
fixGrammar gf = fix (gf . selfReferring)

selfReferring :: Rank2.Reassemblable g => Grammar g s -> Grammar g s
selfReferring = Rank2.reassemble nonTerminal
   where nonTerminal :: forall g s r. (forall p. g p -> p r) -> g (Parser g s) -> Parser g s r
         nonTerminal f _ = Parser (continue . resultList . f . fst . head) mempty f
            where continue :: Either FailureInfo [ResultInfo g s r]
                           -> (r -> [(GrammarResults g s, s)] -> ResultList g s r')
                           -> (FailureInfo -> ResultList g s r')
                           -> ResultList g s r'
                  continue (Left (FailureInfo strength pos msgs)) _ fc = fc (FailureInfo (succ strength) pos msgs)
                  continue (Right rs) rc _ = foldMap (\(ResultInfo t r)-> rc r t) rs

fixGrammarInput :: forall s g. (FactorialMonoid s, Rank2.Apply g, Rank2.Traversable g) =>
                   Grammar g s -> Grammar g s -> s -> [(GrammarResults g s, s)]
fixGrammarInput final grammar input = parseTailWith input $ foldr parseTail [] (tails input)
   where parseTail :: s -> [(GrammarResults g s, s)] -> [(GrammarResults g s, s)]
         parseTail s parsedTail = parsed
            where parsed = (Rank2.fmap finalize $ collectGrammarResults gd gr, s):parsedTail
                  gd = Rank2.fmap (\p-> direct p s parsedTail) grammar
                  gr = Rank2.fmap (DerivedInitialResultList . recursive) grammar
                  finalize :: InitialResultList g s r -> ResultList g s r
                  finalize (InitialResultList (Left err)) = ResultList (Left err)
                  finalize (InitialResultList (Right results)) = ResultList (Right $ finalizeResult <$> results)
                  finalizeResult (CompleteResultInfo t r) = ResultInfo t r
                  finalizeResult (StuckResultInfo r) = ResultInfo parsed r
         parseTailWith :: s -> [(GrammarResults g s, s)] -> [(GrammarResults g s, s)]
         parseTailWith s parsed = (gd, s):parsed
            where gd = Rank2.fmap (\p-> continued p parsed succeed concede) final

collectGrammarResults :: (Rank2.Apply g, Rank2.Traversable g) =>
                         g (InitialResultList g s) -> g (DerivedInitialResultList g s) -> g (InitialResultList g s)
collectGrammarResults gd gdr = foldr1 (Rank2.liftA2 (<>)) (iterate rf gd [])
   where rf = Rank2.traverse derivedInitialResultList gdr

iterate :: Rank2.Foldable g =>
           (g (InitialResultList g s) -> g (InitialResultList g s)) -> g (InitialResultList g s)
        -> [g (InitialResultList g s)]
        -> [g (InitialResultList g s)]
iterate f n ns = if getAll (Rank2.foldMap (either (const mempty) (All . null) . initialResultList) n')
                 then n':n:ns else -- trace ("iterate " ++ show (length ns) ++ ": " ++ show (Rank2.foldMap (Sum . length . foldMap id . initialResultList) n')) $
                                   iterate f n' (n:ns)
   where n' = f n

gd2rl :: GrammarResults g s -> GrammarDerived g s (ResultList g s r) -> ResultList g s r
gd2rl gr (GrammarDerived rl rf) = rl <> rf gr

instance Functor (DerivedInitialResultList g s) where
   fmap f (DerivedInitialResultList gd) = DerivedInitialResultList ((f <$>) <$> gd)

instance Functor (DerivedResultList g s) where
   fmap f (DerivedResultList gd) = DerivedResultList ((f <$>) <$> gd)

instance (Show s, Show r) => Show (ResultList g s r) where
   show (ResultList l) = "ResultList (" ++ shows l ")"

instance (Show s, Show r) => Show (ResultInfo g s r) where
   show (ResultInfo t r) = "(ResultInfo @" ++ show (snd $ head t) ++ " " ++ shows r ")"

instance (Show s) => Show1 (ResultList g s) where
   liftShowsPrec _ _ prec (ResultList (Left err)) rest =
      "ResultList " ++ showsPrec prec err rest
   liftShowsPrec _ sl _prec (ResultList (Right l)) rest = "ResultList (Right " ++ sl (result <$> l) (")" ++ rest)
      where result (ResultInfo _ r) = r
--      where f (ResultInfo _ s t _) = (s, snd <$> take 1 t)
--            g (ResultInfo _ _ _ r) = r

instance Functor (ResultInfo g s) where
   fmap f (ResultInfo t r) = ResultInfo t (f r)

instance Functor (InitialResultInfo g s) where
   fmap f (CompleteResultInfo t r) = CompleteResultInfo t (f r)
   fmap f (StuckResultInfo r) = StuckResultInfo (f r)

instance Functor (ResultList g s) where
   fmap f (ResultList l) = ResultList (((f <$>) <$>) <$> l)

instance Functor (InitialResultList g s) where
   fmap f (InitialResultList l) = InitialResultList (((f <$>) <$>) <$> l)

instance Monoid (ResultList g s r) where
--   mempty = ResultList (Left $ FailureInfo 0 maxBound ["empty"])
   mempty = ResultList (Right [])
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

instance Monoid (InitialResultList g s r) where
--   mempty = InitialResultList (Left $ FailureInfo 0 maxBound ["empty"])
   mempty = InitialResultList (Right [])
   rl1@(InitialResultList (Left (FailureInfo s1 pos1 exp1))) `mappend` rl2@(InitialResultList (Left (FailureInfo s2 pos2 exp2)))
      | s1 < s2 = rl2
      | s1 > s2 = rl1
      | otherwise = InitialResultList (Left $ FailureInfo s1 pos' exp')
      where (pos', exp') | pos1 < pos2 = (pos1, exp1)
                         | pos1 > pos2 = (pos2, exp2)
                         | otherwise = (pos1, exp1 <> exp2)
   InitialResultList (Right []) `mappend` rl = rl
   rl `mappend` InitialResultList (Right []) = rl
   InitialResultList Left{} `mappend` rl = rl
   rl `mappend` InitialResultList Left{} = rl
   InitialResultList (Right a) `mappend` InitialResultList (Right b) = InitialResultList (Right $ a `mappend` b)

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
   fmap f p = Parser{continued= \t rc fc-> continued p t (rc . f) fc,
                     direct= \s t-> f <$> direct p s t,
                     recursive= \g-> f <$> recursive p g}

instance Applicative (Parser g s) where
   pure a = Parser (\t rc _fc-> rc a t) (\_ _-> InitialResultList (Right [StuckResultInfo a])) mempty
   (<*>) :: forall a b. Parser g s (a -> b) -> Parser g s a -> Parser g s b
   p <*> q = Parser{continued= \t rc fc-> continued p t (\r t'-> continued q t' (rc . r) fc) fc,
                    direct= \s t-> directly s t $ direct p s t,
                    recursive= \g-> recursively g $ recursive p g}
      where directly :: s -> [(GrammarResults g s, s)] -> InitialResultList g s (a -> b) -> InitialResultList g s b
            directly _s _t (InitialResultList (Left err)) = InitialResultList (Left err)
            directly s t (InitialResultList (Right results)) = foldMap proceedWith results
               where proceedWith (CompleteResultInfo t' r) = uncomplete (continued q t' (succeed . r) concede)
                     proceedWith (StuckResultInfo r) = r <$> direct q s t
            recursively :: g (InitialResultList g s) -> InitialResultList g s (a -> b) -> InitialResultList g s b
            recursively _g (InitialResultList (Left err)) = InitialResultList (Left err)
            recursively g (InitialResultList (Right results)) = foldMap proceedWith results
               where proceedWith (CompleteResultInfo t r) = uncomplete (continued q t (succeed . r) concede)
                     proceedWith (StuckResultInfo r) = r <$> recursive q g

instance Alternative (Parser g s) where
   empty = Parser{continued= \_t _rc fc-> fc $ FailureInfo 0 maxBound [],
                  direct= \_s _t-> InitialResultList (Left $ FailureInfo 0 maxBound []),
                  recursive= mempty}
   p <|> q = Parser{continued= \t rc fc-> continued p t rc fc <> continued q t rc fc,
                    direct= \s t-> direct p s t <> direct q s t,
                    recursive= \g-> recursive p g <> recursive q g}

infixl 3 <<|>
(<<|>) :: Parser g s r -> Parser g s r -> Parser g s r
p <<|> q = Parser{continued= \t rc fc-> continued p t rc (\f1-> continued q t rc $ \f2-> fc $ combine f1 f2),
                  direct= \s t-> redirect s t (direct p s t),
                  recursive= \g-> rerecurse g (recursive p g)}
   where combine f1@(FailureInfo strength1 pos1 exp1)
                 f2@(FailureInfo strength2 pos2 exp2) =
                      if strength1 < strength2 then f2
                      else if strength1 > strength2 then f1
                      else let (pos', exp') | pos1 < pos2 = (pos1, exp1)
                                            | pos1 > pos2 = (pos2, exp2)
                                            | otherwise = (pos1, exp1 <> exp2)
                           in FailureInfo strength1 pos' exp'
         onFailure f (InitialResultList (Left err)) = InitialResultList (Left $ f err)
         onFailure _ rl = rl
         redirect s t (InitialResultList (Left f1)) = onFailure (combine f1) (direct q s t)
         redirect _ _ rl = rl
         rerecurse g (InitialResultList (Left f1)) = onFailure (combine f1) (recursive q g)
         rerecurse _ rl = rl

instance Monad (Parser g s) where
   return = pure
   (>>=) :: forall a b. Parser g s a -> (a -> Parser g s b) -> Parser g s b
   p >>= cont = Parser{continued= \t rc fc-> continued p t (\r t'-> continued (cont r) t' rc fc) fc,
                       direct= \s t-> directly s t $ direct p s t,
                       recursive= \g-> recursively g $ recursive p g}
      where directly :: s -> [(GrammarResults g s, s)] -> InitialResultList g s a -> InitialResultList g s b
            directly _s _t (InitialResultList (Left err)) = InitialResultList (Left err)
            directly s t (InitialResultList (Right results)) = foldMap proceedWith results
               where proceedWith (CompleteResultInfo t' r) = uncomplete (continued (cont r) t' succeed concede)
                     proceedWith (StuckResultInfo r) = direct (cont r) s t
            recursively :: g (InitialResultList g s) -> InitialResultList g s a -> InitialResultList g s b
            recursively _g (InitialResultList (Left err)) = InitialResultList (Left err)
            recursively g (InitialResultList (Right results)) = foldMap proceedWith results
               where proceedWith (CompleteResultInfo t r) = uncomplete (continued (cont r) t succeed concede)
                     proceedWith (StuckResultInfo r) = recursive (cont r) g
   (>>) = (*>)
   fail msg = Parser{continued= \_ _ fc-> fc $ FailureInfo 0 maxBound [msg],
                     direct= \_s _t-> InitialResultList (Left $ FailureInfo 1 maxBound [msg]),
                     recursive= \_g-> InitialResultList (Left $ FailureInfo 1 maxBound [msg])}

instance MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend
