{-# LANGUAGE FlexibleContexts, GADTs, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Text.Grampa.Types (FailureInfo(..), ResultInfo(..), ResultList(..), InputStatus(Advanced, Stuck),
                          Grammar, GrammarBuilder, Parser(..),
                          feed, feedEnd, fixGrammar, fixGrammarInput, iterateMany)
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
data Parser g s r = Failure {-# UNPACK #-} !FailureInfo
                  | Result {-# UNPACK #-} !(ResultInfo g s r)
                  | Choice (Parser g s r) (Parser g s r)
                  | Delay (Parser g s r) (InputStatus -> [(GrammarResults g s, s)] -> Parser g s r)
                  | forall r'. NonTerminal Int (forall f. g f -> f r') (r' -> r)
                  | forall r'. Bind (Parser g s r') (r' -> Parser g s r)

type Grammar g s = g (Parser g s)
type GrammarBuilder g g' s = g (Parser g' s) -> g (Parser g' s)

instance (Show r, Show s, Show (Grammar g s), Show (GrammarResults g s)) => Show (Parser g s r) where
   showsPrec _ (Failure (FailureInfo pos expectations)) rest =
      "(Failure at " ++ show pos ++ ": " ++ shows expectations (")" ++ rest)
   showsPrec prec (Result (ResultInfo is s r)) rest
      | prec > 0 = "(Result " ++ show is ++ " "
                   ++ foldr (\(t, s)-> showsPrec (prec - 1) t . shows s) (" " ++ shows r (")" ++ rest)) s
      | otherwise = "Result" ++ rest
   showsPrec prec (Choice p1 p2) rest = "(Choice " ++ showsPrec prec p1 (" " ++ showsPrec prec p2 (")" ++ rest))
   showsPrec prec (Delay e f) rest = "(Delay " ++ showsPrec prec e (")" ++ rest)
   showsPrec prec (Bind p cont) rest = "(Bind " ++ showsPrec prec (const () <$> p) (")" ++ rest)
   showsPrec prec (NonTerminal i get map) rest = "(NonTerminal " ++ show i ++ ")" ++ rest

instance (Show s, Show (Grammar g s), Show (GrammarResults g s)) => Show1 (Parser g s) where
   liftShowsPrec sp _ _ (Failure (FailureInfo pos expectations)) rest =
      "(Failure at " ++ show pos ++ ": " ++ shows expectations (")" ++ rest)
   liftShowsPrec sp _ prec (Result (ResultInfo is s r)) rest
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
iterate f ns@(n:_) = if getAll (foldMap1 (either (const mempty) (All . null) . resultList) n')
                     then n':ns else iterate f (n':ns)
   where n' = f n

type GrammarResults g s = g (ResultList g s)
newtype ResultList g s r = ResultList {resultList :: Either FailureInfo [ResultInfo g s r]}
data ResultInfo g s r = ResultInfo InputStatus [(GrammarResults g s, s)] r
data FailureInfo =  FailureInfo Word64 [String] deriving (Eq, Show)
data GrammarDerived g s a = GrammarDerived a (GrammarResults g s -> a)

instance (Show (g (ResultList g s)), Show s, Show r) => Show (ResultList g s r) where
   show (ResultList l) = "ResultList (" ++ shows l ")"

instance (Show (g (ResultList g s)), Show s, Show r) => Show (ResultInfo g s r) where
   show (ResultInfo is i r) = "(ResultInfo " ++ show is ++ " " ++ show (length i) ++ " " ++ shows r ")"

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

separate :: forall g s. (MonoidNull s, Traversable1 g, Alternative1 g) =>
            Grammar g s -> GrammarDerived g s (GrammarResults g s)
separate = traverse1 sep1
   
sep1 :: forall g s r. (Monoid s, Traversable1 g, Alternative1 g) =>
        Parser g s r -> GrammarDerived g s (ResultList g s r)
sep1 (Failure f) = GrammarDerived (ResultList $ Left f) (const mempty)
sep1 (Result ri@(ResultInfo is s r)) = GrammarDerived (ResultList $ Right [ri]) (const mempty)
sep1 (Choice p q) = sep1 p <> sep1 q
sep1 (Delay e _) = sep1 e
sep1 (NonTerminal i get map) =
   GrammarDerived (ResultList $ Left $ FailureInfo maxBound ["NT#" ++ show i]) ((map <$>) . get)
sep1 (Bind p cont) = either (\pair-> GrammarDerived (ResultList $ Left pair) (const mempty)) (foldMap f) pn
                     <> GrammarDerived mempty pr'
   where GrammarDerived (ResultList pn) pr = sep1 p
         --f :: ([(Grammar g s, s)], r') -> GrammarDerived g s (ResultList g s r)
         f (ResultInfo Stuck i r) = sep1 (feedSelf i $ cont r)
         f (ResultInfo Advanced i r) = sep1 (feed i $ cont r)
         pr' :: GrammarResults g s -> ResultList g s r
         pr' gr = either (ResultList . Left) (foldMap gr2rl) (resultList $ pr gr)
            where --gr2rl ([], r) l = pr2rl gr (sep1 $ cont r) <> l
                  gr2rl (ResultInfo Stuck i r) = pr2rl gr (sep1 $ feedSelf i $ cont r)
                  gr2rl (ResultInfo Advanced i r) = pr2rl gr (sep1 $ feed i $ cont r)
                  pr2rl g (GrammarDerived rl rf) = rl <> rf g

feedSelf :: Monoid s => [(GrammarResults g s, s)] -> Parser g s r -> Parser g s r
feedSelf input (Choice p q) = feedSelf input p <|> feedSelf input q
feedSelf input (Delay _ f) = f Stuck input
feedSelf input p@Failure{} = p
feedSelf input (Result (ResultInfo is t r)) = Result (ResultInfo is (t <> input) r)
feedSelf _ p@NonTerminal{} = p
feedSelf input (Bind p cont) = feedSelf input p >>= cont
   
-- | Feeds a chunk of the input to the given parser.
feed :: Monoid s => [(GrammarResults g s, s)] -> Parser g s r -> Parser g s r
feed s (Choice p q) = feed s p <|> feed s q
feed s (Delay _ f) = f Advanced s
feed s p@Failure{} = p
feed s (Result (ResultInfo _ t r)) = Result (ResultInfo Advanced (t <> s) r)
--feed [] p@NonTerminal{} = p
feed ((rs, s):_) (NonTerminal i get map) = either Failure (asum . (f <$>)) (resultList (get rs))
   where f (ResultInfo is i r) = Result (ResultInfo is i (map r))
feed s (Bind p cont) = feed s p >>= cont

-- | Signals the end of the input.
feedEnd :: (MonoidNull s, Functor1 g) => Parser g s r -> Parser g s r
feedEnd (Choice p q) = feedEnd p <|> feedEnd q
feedEnd (Delay e _) = feedEnd e
feedEnd p = p

instance Functor (Parser g s) where
   fmap f (Choice p q) = Choice (fmap f p) (fmap f q)
   fmap g (Delay e f) = Delay (fmap g e) (\is-> fmap g . f is)
   fmap _ (Failure f) = Failure f
   fmap f (Result (ResultInfo is s r)) = Result (ResultInfo is s (f r))
   fmap f (Bind p cont) = Bind p (fmap f . cont)
   fmap f (NonTerminal i get map) = NonTerminal i get (f . map)

instance Monoid s => Applicative (Parser g s) where
   pure = Result . ResultInfo Stuck []
   Choice p q <*> r = p <*> r <|> q <*> r
   Delay e f <*> p = Delay (e <*> p) (\is-> (<*> p) . f is)
   Failure f <*> _ = Failure f
   Result (ResultInfo Stuck s r) <*> p = r <$> feedSelf s p
   Result (ResultInfo Advanced s r) <*> p = r <$> feed s p
   p <*> q = Bind p (<$> q)

instance Monoid s => Alternative (Parser g s) where
   empty = Failure (FailureInfo maxBound [])
   Failure f1@(FailureInfo pos1 exp1) <|> Failure f2@(FailureInfo pos2 exp2)
      | pos1 < pos2 = Failure f1
      | pos2 < pos1 = Failure f2
      | otherwise = Failure (FailureInfo pos1 (exp1 <> exp2))
   Failure{} <|> p@Result{} = p
   p@Result{} <|> Failure{} = p
   Failure{} <|> p@(Choice Result{} _) = p
   p@(Choice Result{} _) <|> Failure{} = p
--   p <|> Failure{} = p
--   Failure{} <|> p = p
--   Delay e f <|> p = Delay (e <|> feedEnd p) (\i-> f i <|> feed i p)
--   p <|> Delay e f = Delay (feedEnd p <|> e) (\i-> feed i p <|> f i)
   Choice p q <|> r = p <|> Choice q r
   p <|> q = Choice p q

instance Monoid s => Monad (Parser g s) where
   return = pure
   Result (ResultInfo Stuck s r) >>= f = feedSelf s (f r)
   Result (ResultInfo Advanced s r) >>= f = feed s (f r)
   Choice p q >>= f = (p >>= f) <|> (q >>= f)
   Delay e f >>= g = Delay (e >>= g) (\is-> (>>= g) . f is)
   Failure f >>= _ = Failure f
   p >>= cont = Bind p cont
   (>>) = (*>)
   fail msg = Failure (FailureInfo maxBound [msg])

instance Monoid s => MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance (Functor1 g, MonoidNull s, Monoid x) => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend

iterateMany :: (MonoidNull s, Functor1 g) => Parser g s r -> (Parser g s r -> Parser g s r) -> Parser g s r
iterateMany p f = p >>= (\r-> return r <|> iterateMany (f $ return r) f)
