{-# LANGUAGE FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa.Types (ResultList(..), InputStatus(Advanced, Stuck),
                          Grammar, GrammarBuilder, Parser(..),
                          feed, feedEnd, fixGrammar, fixGrammarInput, iterateMany)
where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (Monad(..), MonadPlus(..))
import Control.Monad.Trans.State (State, evalState, get, modify)
import Data.Function(fix)
import Data.Functor.Classes (Show1(liftShowsPrec))
import Data.Functor.Compose (Compose(Compose, getCompose))
import Data.Monoid (Monoid(mappend, mempty), All(..), (<>))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(spanMaybe', splitPrimePrefix, tails))

import Text.Grampa.Classes

import Prelude hiding (iterate, null)

data InputStatus = Advanced | Stuck deriving (Eq, Show)

-- | Parser of streams of type `s`, as a part of grammar type `g`, producing a value of type `r`
data Parser g s r = Failure String
                  | Result InputStatus [(GrammarResults g s, s)] r
                  | Choice (Parser g s r) (Parser g s r)
                  | Delay (Parser g s r) (InputStatus -> [(GrammarResults g s, s)] -> Parser g s r)
                  | forall r'. NonTerminal Int (forall f. g f -> f r') (r' -> r)
                  | forall r'. Bind (Parser g s r') (r' -> Parser g s r)

data ResultInfo g s r = ResultInfo InputStatus [(GrammarResults g s, s)] r

type Grammar g s = g (Parser g s)
type GrammarBuilder g g' s = g (Parser g' s) -> g (Parser g' s)

instance (Show r, Show s, Show (Grammar g s), Show (GrammarResults g s)) => Show (Parser g s r) where
   showsPrec _ (Failure s) rest = "(Failure " ++ shows s (")" ++ rest)
   showsPrec prec (Result is s r) rest
      | prec > 0 = "(Result " ++ show is ++ " "
                   ++ foldr (\(t, s)-> showsPrec (prec - 1) t . shows s) (" " ++ shows r (")" ++ rest)) s
      | otherwise = "Result" ++ rest
   showsPrec prec (Choice p1 p2) rest = "(Choice " ++ showsPrec prec p1 (" " ++ showsPrec prec p2 (")" ++ rest))
   showsPrec prec (Delay e f) rest = "(Delay " ++ showsPrec prec e (")" ++ rest)
   showsPrec prec (Bind p cont) rest = "(Bind " ++ showsPrec prec (const () <$> p) (")" ++ rest)
   showsPrec prec (NonTerminal i get map) rest = "(NonTerminal " ++ show i ++ ")" ++ rest

instance (Show s, Show (Grammar g s), Show (GrammarResults g s)) => Show1 (Parser g s) where
   liftShowsPrec sp _ _ (Failure s) rest = "(Failure " ++ shows s (")" ++ rest)
   liftShowsPrec sp _ prec (Result is s r) rest
      | prec > 0 = "(Result " ++ show is ++ " "
                   ++ foldr (\(t, s)-> showsPrec (prec - 1) t . shows s) (" " ++ sp prec r (")" ++ rest)) s
      | otherwise = "Result" ++ rest
   liftShowsPrec sp sl prec (Choice p1 p2) rest = "(Choice " ++ liftShowsPrec sp sl prec p1 (" " ++ liftShowsPrec sp sl prec p2 (")" ++ rest))
   liftShowsPrec sp sl prec (Delay e f) rest = "(Delay " ++ liftShowsPrec sp sl prec e (")" ++ rest)
   liftShowsPrec sp sl prec (Bind p cont) rest = "(Bind " ++ liftShowsPrec showsPrec showList prec (const () <$> p) (")" ++ rest)
   liftShowsPrec sp sl prec (NonTerminal i get map) rest = "(NonTerminal " ++ show i ++ ")" ++ rest

-- | Tie the knot on a 'GrammarBuilder' and turn it into a 'Grammar'
fixGrammar :: forall g s. (Reassemblable g, Traversable1 g) => (Grammar g s -> Grammar g s) -> Grammar g s
fixGrammar gf = fix . (. mark) $ gf
   where mark :: g (Parser g s) -> g (Parser g s)
         mark g = evalState (traverse1 f $ reassemble nt g) 0
            where nt :: (forall p. g p -> p r) -> g (Parser g s) -> Parser g s r
                  nt f g = NonTerminal 0 f id
         f :: Parser g s r -> State Int (Parser g s r)
         f (NonTerminal 0 getP map) = do modify succ
                                         i <- get
                                         return (NonTerminal i getP map)

fixGrammarInput :: forall s g. (FactorialMonoid s, Alternative1 g, Traversable1 g) =>
                   Grammar g s -> s -> [(GrammarResults g s, s)]
fixGrammarInput g s = foldr (parseTail g) [] (tails s)
   where parseTail :: (FactorialMonoid s, Alternative1 g, Traversable1 g) =>
                      Grammar g s -> s -> [(GrammarResults g s, s)] -> [(GrammarResults g s, s)]
         parseTail g input parsedTail = parsedInput
            where parsedInput = (grammarResults' g', input):parsedTail
                  g' = fmap1 (feedSelf parsedInput) g

grammarResults' :: forall s g. (MonoidNull s, Traversable1 g, Alternative1 g) => Grammar g s -> GrammarResults g s
grammarResults' g = foldr1 choose1 (iterate rf [rn])
   where GrammarDerived rn rf = separate g

iterate :: Foldable1 g => (GrammarResults g s -> GrammarResults g s) -> [GrammarResults g s] -> [GrammarResults g s]
iterate f ns@(n:_) = if getAll (foldMap1 (All . null . resultList) n') then ns else iterate f (n':ns)
   where n' = f n

type GrammarResults g s = g (ResultList g s)
newtype ResultList g s r = ResultList {resultList :: [(InputStatus, [(GrammarResults g s, s)], r)]}
data GrammarDerived g s a = GrammarDerived a (GrammarResults g s -> a)
type ParserResults g s r = GrammarDerived g s (ResultList g s r)

instance (Show (g (ResultList g s)), Show s, Show r) => Show (ResultList g s r) where
   show (ResultList l) = "ResultList " ++ show l

instance (Show (g (ResultList g s)), Show s) => Show1 (ResultList g s) where
   liftShowsPrec sp sl prec (ResultList l) rest = "ResultList " ++ showsPrec prec (f <$> l) (sl (g <$> l) rest)
      where f (is, grs, _) = (is, snd <$> take 1 grs)
            g (_, _, r) = r

instance Functor (ResultList g s) where
   fmap f (ResultList l) = ResultList (third <$> l)
      where third (a, b, c) = (a, b, f c)

instance Applicative (ResultList g s) where
   pure r = ResultList [(Stuck, [], r)]
   ResultList a <*> ResultList b = ResultList (apply a b)
      where apply [] _ = []
            apply _ [] = []
            apply ((is1, i1, r1):rest1) ((is2, i2, r2):rest2)
               | is1 == is2 && length i1 == length i2 = (is1, i1, r1 r2):(apply rest1 rest2)
   
instance Alternative (ResultList g s) where
   empty = ResultList []
   ResultList a <|> ResultList b = ResultList (a <|> b)

instance Monoid (ResultList g s r) where
   mempty = ResultList []
   ResultList a `mappend` ResultList b = ResultList (a <> b)

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

separate :: forall g s. (MonoidNull s, Traversable1 g, Alternative1 g) =>
            Grammar g s -> GrammarDerived g s (GrammarResults g s)
separate g = traverse1 sep1 g
   
sep1 :: forall g s r. (Monoid s, Traversable1 g, Alternative1 g) => Parser g s r -> ParserResults g s r
sep1 Failure{} = GrammarDerived (ResultList []) (const $ ResultList [])
sep1 (Result is s r) = GrammarDerived (ResultList [(is, s, r)]) (const $ ResultList [])
sep1 (Choice p q) = sep1 p <> sep1 q
sep1 (Delay e _) = sep1 e
sep1 (NonTerminal i get map) = GrammarDerived (ResultList []) ((map <$>) . get)
sep1 (Bind p cont) = foldMap f pn <> GrammarDerived (ResultList []) pr'
   where GrammarDerived (ResultList pn) pr = sep1 p
         --f :: ([(Grammar g s, s)], r') -> ParserResults g s r
         f (Stuck, i, r) = sep1 (feedSelf i $ cont r)
         f (Advanced, i, r) = sep1 (feed i $ cont r)
         pr' :: GrammarResults g s -> ResultList g s r
         pr' gr = foldr gr2rl empty (resultList $ pr gr)
            where --gr2rl ([], r) l = pr2rl gr (sep1 $ cont r) <> l
                  gr2rl (Stuck, i, r) l = pr2rl gr (sep1 $ feedSelf i $ cont r) <> l
                  gr2rl (Advanced, i, r) l = pr2rl gr (sep1 $ feed i $ cont r) <> l
                  pr2rl g (GrammarDerived rl rf) = rl <> rf g

feedSelf :: Monoid s => [(GrammarResults g s, s)] -> Parser g s r -> Parser g s r
feedSelf input (Choice p q) = feedSelf input p <|> feedSelf input q
feedSelf input (Delay _ f) = f Stuck input
feedSelf input (Failure msg) = Failure msg
feedSelf input (Result is t r) = Result is (t <> input) r
feedSelf _ p@NonTerminal{} = p
feedSelf input (Bind p cont) = feedSelf input p >>= cont
   
-- | Feeds a chunk of the input to the given parser.
feed :: Monoid s => [(GrammarResults g s, s)] -> Parser g s r -> Parser g s r
feed s (Choice p q) = feed s p <|> feed s q
feed s (Delay _ f) = f Advanced s
feed s (Failure msg) = Failure msg
feed s (Result _ t r) = Result Advanced (t <> s) r
--feed [] p@NonTerminal{} = p
feed ((rs, s):_) (NonTerminal i get map) = foldr (<|>) empty (f <$> resultList (get rs))
   where f (is, i, r) = Result is i (map r)
feed s (Bind p cont) = feed s p >>= cont

-- | Signals the end of the input.
feedEnd :: (MonoidNull s, Functor1 g) => Parser g s r -> Parser g s r
feedEnd (Choice p q) = feedEnd p <|> feedEnd q
feedEnd (Delay e _) = feedEnd e
feedEnd p = p

instance Functor (Parser g s) where
   fmap f (Choice p q) = Choice (fmap f p) (fmap f q)
   fmap g (Delay e f) = Delay (fmap g e) (\is-> fmap g . f is)
   fmap f (Failure msg) = Failure msg
   fmap f (Result is s r) = Result is s (f r)
   fmap f (Bind p cont) = Bind p (fmap f . cont)
   fmap f (NonTerminal i get map) = NonTerminal i get (f . map)

instance Monoid s => Applicative (Parser g s) where
   pure = Result Stuck []
   Choice p q <*> r = p <*> r <|> q <*> r
   Delay e f <*> p = Delay (e <*> p) (\is-> (<*> p) . f is)
   Failure msg <*> _ = Failure msg
   Result Stuck s r <*> p = r <$> feedSelf s p
   Result Advanced s r <*> p = r <$> feed s p
   p <*> q = Bind p (<$> q)

instance Monoid s => Alternative (Parser g s) where
   empty = Failure "empty"
   p <|> Failure{} = p
   Failure{} <|> p = p
--   Delay e f <|> p = Delay (e <|> feedEnd p) (\i-> f i <|> feed i p)
--   p <|> Delay e f = Delay (feedEnd p <|> e) (\i-> feed i p <|> f i)
   Choice p q <|> r = p <|> Choice q r
   p <|> q = Choice p q

instance Monoid s => Monad (Parser g s) where
   return = pure
   Result Stuck s r >>= f = feedSelf s (f r)
   Result Advanced s r >>= f = feed s (f r)
   Choice p q >>= f = (p >>= f) <|> (q >>= f)
   Delay e f >>= g = Delay (e >>= g) (\is-> (>>= g) . f is)
   Failure msg >>= f = Failure msg
   p >>= cont = Bind p cont
   (>>) = (*>)
   fail = Failure

instance Monoid s => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance (Functor1 g, MonoidNull s, Monoid x) => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

iterateMany :: (MonoidNull s, Functor1 g) => Parser g s r -> (Parser g s r -> Parser g s r) -> Parser g s r
iterateMany p f = p >>= (\r-> return r <|> iterateMany (f $ return r) f)
