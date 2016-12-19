{-# LANGUAGE FlexibleContexts, InstanceSigs, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa.Types (FailureInfo(..), ResultInfo(..), ResultList(..),
                          Grammar, GrammarDerived(..), Parser(..), (<<|>),
                          concede, succeed, gd2rl, fixGrammar, fixGrammarInput, primitive, selfReferring)
where

import Control.Applicative
import Control.Monad (Monad(..), MonadPlus(..))
import Data.Either (either)
import Data.Functor.Classes (Show1(liftShowsPrec))
import Data.List (genericLength)
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid(mappend, mempty), All(..), (<>))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(tails))
import Data.Word (Word64)

import qualified Rank2

import Prelude hiding (iterate, null)


-- | Parser of streams of type `s`, as a part of grammar type `g`, producing a value of type `r`
data Parser g s r = Parser {continued :: forall r'. [(GrammarResults g s, s)]
                              -> (r -> [(GrammarResults g s, s)] -> ResultList g s r')
                              -> (FailureInfo -> ResultList g s r')
                              -> ResultList g s r',
                            direct :: s -> [(GrammarResults g s, s)] -> ResultList g s r,
                            recursive :: Maybe (g (ResultList g s) -> s -> [(GrammarResults g s, s)] -> ResultList g s r),
                            nullable :: Bool,
                            recursivelyNullable :: g (Parser g s) -> Bool}
newtype DerivedResultList g s r = DerivedResultList {
   derivedResultList :: g (ResultList g s) -> ResultList g s r}
newtype ResultList g s r = ResultList {resultList :: Either FailureInfo [ResultInfo g s r]}
data ResultInfo g s r = CompleteResultInfo ![(GrammarResults g s, s)] !r
                      | StuckResultInfo !r
data FailureInfo = FailureInfo !Int Word64 [String] deriving (Eq, Show)
data GrammarDerived g s a = GrammarDerived a (GrammarResults g s -> a)
type Grammar g s = g (Parser g s)
type GrammarResults g s = g (ResultList g s)

concede :: FailureInfo -> ResultList g s r
concede a = ResultList (Left a)

succeed :: r -> [(GrammarResults g s, s)] -> ResultList g s r
succeed r t = ResultList (Right [CompleteResultInfo t r])

primitive :: Bool
          -> (forall x. s -> [(GrammarResults g s, s)]
                        -> (r -> x)
                        -> (r -> [(GrammarResults g s, s)] -> x)
                        -> (String -> x)
                        -> x)
          -> Parser g s r
primitive n parser = Parser{continued= \t@((_, s):t') rc fc ->
                                 parser s t' (`rc` t) rc (fc . FailureInfo 0 (genericLength t) . (:[])),
                            direct= \s t-> parser s t rc0 rc (failAt t),
                            recursive= mempty,
                            nullable= n,
                            recursivelyNullable= const n}
   where rc0 r = ResultList (Right [StuckResultInfo r])
         rc r t' = ResultList (Right [CompleteResultInfo t' r])
         failAt t msg = ResultList (Left $ FailureInfo 0 (genericLength t) [msg])

-- | Tie the knot on a 'GrammarBuilder' and turn it into a 'Grammar'
fixGrammar :: forall g s. (Rank2.Foldable g, Rank2.Apply g, Rank2.Distributive g) =>
              (Grammar g s -> Grammar g s) -> Grammar g s
fixGrammar gf = combine `Rank2.fmap` gf selfReferring `Rank2.ap` fixNullable (gf selfNullable)
   where combine p1 = Rank2.Arrow (\p2-> Parser{continued= continued p1,
                                                direct= direct p1,
                                                recursive= recursive p1,
                                                nullable= nullable p2,
                                                recursivelyNullable= recursivelyNullable p2})

fixNullable :: forall g s. (Rank2.Foldable g, Rank2.Apply g) => Grammar g s -> Grammar g s
fixNullable g = head (iterateNullable iter g [])
   where iter g' = Rank2.fmap (iterP g') g'
         iterP g' p = p{nullable= recursivelyNullable p g'}

iterateNullable :: forall g s. (Rank2.Foldable g, Rank2.Apply g) =>
                   (g (Parser g s) -> g (Parser g s)) -> g (Parser g s)
                -> [g (Parser g s)]
                -> [g (Parser g s)]
iterateNullable f n ns = if getAll (Rank2.foldMap (All . getConst) $ equallyNullable `Rank2.fmap` n `Rank2.ap` n')
                         then n':n:ns else iterateNullable f n' (n:ns)
   where n' = f n
         equallyNullable :: forall x. Parser g s x -> Rank2.Arrow (Parser g s) (Const Bool) x
         equallyNullable p1 = Rank2.Arrow (\p2-> Const $ nullable p1 == nullable p2)

selfNullable :: forall g s. Rank2.Distributive g => Grammar g s
selfNullable = Rank2.distributeWith nonTerminal id
   where nonTerminal :: forall r. (g (Parser g s) -> Parser g s r) -> Parser g s r
         nonTerminal f = Parser{continued= undefined,
                                direct= undefined,
                                recursive= undefined,
                                nullable= True,
                                recursivelyNullable= nullable . f}

selfReferring :: forall g s. Rank2.Distributive g => Grammar g s
selfReferring = Rank2.distributeWith nonTerminal id
   where nonTerminal :: forall r. (g (ResultList g s) -> ResultList g s r) -> Parser g s r
         nonTerminal f = Parser{continued= continue . resultList . f . fst . head,
                                direct= mempty,
                                recursive= Just (const . const . f),
                                nullable= True,
                                recursivelyNullable= error "recursivelyNullable will be initialized by selfNullable"}
            where continue :: Either FailureInfo [ResultInfo g s r]
                           -> (r -> [(GrammarResults g s, s)] -> ResultList g s r')
                           -> (FailureInfo -> ResultList g s r')
                           -> ResultList g s r'
                  continue (Left (FailureInfo strength pos msgs)) _ fc = fc (FailureInfo (succ strength) pos msgs)
                  continue (Right rs) rc _ = foldMap continueFrom rs
                     where continueFrom (CompleteResultInfo t r) = rc r t
                           continueFrom StuckResultInfo{} = error "Can't continue, I'm Stuck."

fixGrammarInput :: forall s g. (FactorialMonoid s, Rank2.Apply g, Rank2.Traversable g) =>
                   Grammar g s -> Grammar g s -> s -> [(GrammarResults g s, s)]
fixGrammarInput final grammar input = parseTailWith input $ foldr parseTail [] (tails input)
   where parseTail :: s -> [(GrammarResults g s, s)] -> [(GrammarResults g s, s)]
         parseTail s parsedTail = parsed
            where parsed = (Rank2.fmap finalize $ collectGrammarResults gd gr, s):parsedTail
                  gd = Rank2.fmap (\p-> direct p s parsedTail) grammar
                  gr = Rank2.fmap (\p-> DerivedResultList $ \g-> fromMaybe mempty (recursive p) g s parsedTail) grammar
                  finalize :: ResultList g s r -> ResultList g s r
                  finalize (ResultList (Left err)) = ResultList (Left err)
                  finalize (ResultList (Right results)) = ResultList (Right $ complete <$> results)
                  complete :: ResultInfo g s r -> ResultInfo g s r
                  complete r@CompleteResultInfo{} = r
                  complete (StuckResultInfo r) = CompleteResultInfo parsed r
         parseTailWith :: s -> [(GrammarResults g s, s)] -> [(GrammarResults g s, s)]
         parseTailWith s parsed = (gd, s):parsed
            where gd = Rank2.fmap (\p-> continued p parsed succeed concede) final

collectGrammarResults :: (Rank2.Apply g, Rank2.Traversable g) =>
                         g (ResultList g s) -> g (DerivedResultList g s) -> g (ResultList g s)
collectGrammarResults gd gdr = foldr1 (Rank2.liftA2 (<>)) (iterate rf gd [])
   where rf = Rank2.traverse derivedResultList gdr

iterate :: Rank2.Foldable g =>
           (g (ResultList g s) -> g (ResultList g s)) -> g (ResultList g s)
        -> [g (ResultList g s)]
        -> [g (ResultList g s)]
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
   show (CompleteResultInfo t r) = "(CompleteResultInfo @" ++ show (snd $ head t) ++ " " ++ shows r ")"
   show (StuckResultInfo r) = "(StuckResultInfo " ++ " " ++ shows r ")"

instance (Show s) => Show1 (ResultList g s) where
   liftShowsPrec _ _ prec (ResultList (Left err)) rest =
      "ResultList " ++ showsPrec prec err rest
   liftShowsPrec _ sl _prec (ResultList (Right l)) rest = "ResultList (Right " ++ sl (result <$> l) (")" ++ rest)
      where result (CompleteResultInfo _ r) = r
            result (StuckResultInfo r) = r
--      where f (ResultInfo _ s t _) = (s, snd <$> take 1 t)
--            g (ResultInfo _ _ _ r) = r

instance Functor (ResultInfo g s) where
   fmap f (CompleteResultInfo t r) = CompleteResultInfo t (f r)
   fmap f (StuckResultInfo r) = StuckResultInfo (f r)

instance Functor (ResultList g s) where
   fmap f (ResultList l) = ResultList (((f <$>) <$>) <$> l)

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
                     recursive= (\r g s t-> f <$> r g s t) <$> recursive p,
                     nullable= nullable p,
                     recursivelyNullable= recursivelyNullable p}

instance Applicative (Parser g s) where
   pure a = Parser{continued= \t rc _fc-> rc a t,
                   direct= \_ _-> ResultList (Right [StuckResultInfo a]),
                   recursive= mempty,
                   nullable= True,
                   recursivelyNullable= const True}
   (<*>) :: forall a b. Parser g s (a -> b) -> Parser g s a -> Parser g s b
   p <*> q = Parser{continued= \t rc fc-> continued p t (\r t'-> continued q t' (rc . r) fc) fc,
                    direct= \s t-> directly s t $ direct p s t,
                    recursive= (if nullable p
                                then (\r g s t-> recursively' (direct p s t) r g s t) <$> recursive q
                                else Nothing)
                               <> ((\r g s t-> recursively g s t $ r g s t) <$> recursive p),
                    nullable= nullable p && nullable q,
                    recursivelyNullable= \g-> recursivelyNullable p g && recursivelyNullable q g}
      where directly :: s -> [(GrammarResults g s, s)] -> ResultList g s (a -> b) -> ResultList g s b
            directly _s _t (ResultList (Left err)) = ResultList (Left err)
            directly s t (ResultList (Right results)) = foldMap proceedWith results
               where proceedWith (CompleteResultInfo t' r) = continued q t' (succeed . r) concede
                     proceedWith (StuckResultInfo r) = r <$> direct q s t
            recursively :: g (ResultList g s) -> s -> [(GrammarResults g s, s)] -> ResultList g s (a -> b)
                        -> ResultList g s b
            recursively _g _s _t (ResultList (Left err)) = ResultList (Left err)
            recursively g s t (ResultList (Right results)) = foldMap proceedWith results
               where proceedWith (CompleteResultInfo t' r) = continued q t' (succeed . r) concede
                     proceedWith (StuckResultInfo r) = maybe mempty (\recurse-> r <$> recurse g s t) (recursive q)
            recursively' :: ResultList g s (a -> b)
                         -> (g (ResultList g s) -> s -> [(GrammarResults g s, s)] -> ResultList g s a)
                         -> g (ResultList g s) -> s -> [(GrammarResults g s, s)]
                         -> ResultList g s b
            recursively' (ResultList Left{}) _qr _g _s _t = mempty
            recursively' (ResultList (Right results)) qr g s t = foldMap proceedWith results
               where proceedWith CompleteResultInfo{} = mempty
                     proceedWith (StuckResultInfo r) = r <$> qr g s t

instance Alternative (Parser g s) where
   empty = Parser{continued= \_t _rc fc-> fc $ FailureInfo 0 maxBound [],
                  direct= \_s _t-> ResultList (Left $ FailureInfo 0 maxBound []),
                  recursive= mempty,
                  nullable= False,
                  recursivelyNullable= const False}
   p <|> q = Parser{continued= \t rc fc-> continued p t rc fc <> continued q t rc fc,
                    direct= \s t-> direct p s t <> direct q s t,
                    recursive= recursive p <> recursive q,
                    nullable= nullable p || nullable q,
                    recursivelyNullable= \g-> recursivelyNullable p g || recursivelyNullable q g}

   -- | One or more. Make sure `nullable` terminates.
   some v = some_v{nullable= nullable v,
                   recursivelyNullable= recursivelyNullable v}
      where many_v = some_v <|> pure []
            some_v = (:) <$> v <*> many_v

   -- | Zero or more. Make sure `nullable` terminates.
   many v = many_v{nullable= True,
                   recursivelyNullable= const True}
      where many_v = some_v <|> pure []
            some_v = (:) <$> v <*> many_v

infixl 3 <<|>
(<<|>) :: Parser g s r -> Parser g s r -> Parser g s r
p <<|> q = Parser{continued= \t rc fc-> continued p t rc (\f1-> continued q t rc $ \f2-> fc $ combine f1 f2),
                  direct= \s t-> choose (direct p s t) (direct q s t),
                  recursive= case (recursive p, recursive q)
                             of (Nothing, r) -> r
                                (r, Nothing) -> r
                                (Just rp, Just rq) -> Just (\g s t-> choose (rp g s t) (rq g s t)),
                  nullable= nullable p || nullable q,
                  recursivelyNullable= \g-> recursivelyNullable p g || recursivelyNullable q g}
   where combine f1@(FailureInfo strength1 pos1 exp1)
                 f2@(FailureInfo strength2 pos2 exp2) =
                      if strength1 < strength2 then f2
                      else if strength1 > strength2 then f1
                      else let (pos', exp') | pos1 < pos2 = (pos1, exp1)
                                            | pos1 > pos2 = (pos2, exp2)
                                            | otherwise = (pos1, exp1 <> exp2)
                           in FailureInfo strength1 pos' exp'
         onFailure f (ResultList (Left err)) = ResultList (Left $ f err)
         onFailure _ rl = rl
         choose (ResultList (Left f1)) rl2 = onFailure (combine f1) rl2
         choose rl _ = rl

instance Monad (Parser g s) where
   return = pure
   (>>=) :: forall a b. Parser g s a -> (a -> Parser g s b) -> Parser g s b
   p >>= cont = Parser{continued= \t rc fc-> continued p t (\r t'-> continued (cont r) t' rc fc) fc,
                       direct= \s t-> directly s t $ direct p s t,
                       recursive= if nullable p
                                  then Just (\g s t-> (if nullable p then recursively' g s t (direct p s t) else mempty)
                                                      <> recursively g s t (fromMaybe mempty (recursive p) g s t))
                                  else (\r g s t-> recursively g s t $ r g s t) <$> recursive p,
                       nullable= nullable p,
                       recursivelyNullable= recursivelyNullable p}
      where directly :: s -> [(GrammarResults g s, s)] -> ResultList g s a -> ResultList g s b
            directly _s _t (ResultList (Left err)) = ResultList (Left err)
            directly s t (ResultList (Right results)) = foldMap proceedWith results
               where proceedWith (CompleteResultInfo t' r) = continued (cont r) t' succeed concede
                     proceedWith (StuckResultInfo r) = direct (cont r) s t
            recursively :: g (ResultList g s) -> s -> [(GrammarResults g s, s)] -> ResultList g s a
                        -> ResultList g s b
            recursively _g _s _t (ResultList (Left err)) = ResultList (Left err)
            recursively g s t (ResultList (Right results)) = foldMap proceedWith results
               where proceedWith (CompleteResultInfo t' r) = continued (cont r) t' succeed concede
                     proceedWith (StuckResultInfo r) = fromMaybe mempty (recursive $ cont r) g s t
            recursively' :: g (ResultList g s) -> s -> [(GrammarResults g s, s)] -> ResultList g s a
                        -> ResultList g s b
            recursively' _g _s _t (ResultList Left{}) = mempty
            recursively' g s t (ResultList (Right results)) = foldMap proceedWith results
               where proceedWith (CompleteResultInfo t' r) = continued (cont r) t' succeed concede
                     proceedWith (StuckResultInfo r) = fromMaybe mempty (recursive $ cont r) g s t
   (>>) = (*>)
   fail msg = Parser{continued= \_ _ fc-> fc $ FailureInfo 0 maxBound [msg],
                     direct= \_s _t-> ResultList (Left $ FailureInfo 1 maxBound [msg]),
                     recursive= Nothing,
                     nullable= False,
                     recursivelyNullable= const False}

instance MonadPlus (Parser g s) where
   mzero = empty
   mplus = (<|>)

instance Monoid x => Monoid (Parser g s x) where
   mempty = pure mempty
   mappend = liftA2 mappend
