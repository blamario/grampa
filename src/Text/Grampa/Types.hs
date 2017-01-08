{-# LANGUAGE FlexibleContexts, InstanceSigs, RankNTypes, ScopedTypeVariables #-}
module Text.Grampa.Types (FailureInfo(..), ResultInfo(..), ResultList(..),
                          Grammar, Parser(..), (<<|>),
                          concede, succeed, 
                          fixGrammar, fixGrammarInput, primitive, selfReferring,
                          endOfInput, satisfyChar, string)
where

import Control.Applicative
import Control.Monad (Monad(..), MonadPlus(..))
import Data.Either (either)
import Data.Functor.Classes (Show1(liftShowsPrec))
import Data.List (genericLength)
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid(mappend, mempty), All(..), (<>))
import Data.Monoid.Cancellative (LeftReductiveMonoid (stripPrefix))
import Data.Monoid.Null (MonoidNull(null))
import Data.Monoid.Factorial (FactorialMonoid(length, tails))
import Data.Monoid.Textual (TextualMonoid)
import qualified Data.Monoid.Textual as Textual
import Data.String (fromString)
import Data.Word (Word64)

import qualified Text.Parser.Char as CharParsing
import Text.Parser.Char (CharParsing(char, notChar, anyChar, text))
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.LookAhead (LookAheadParsing(..))
import Text.Parser.Token (TokenParsing)

import qualified Rank2

import Prelude hiding (iterate, length, null, span, takeWhile)

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
type Grammar g s = g (Parser g s)
type GrammarResults g s = g (ResultList g s)

concede :: FailureInfo -> ResultList g s r
concede a = ResultList (Left a)

succeed :: r -> [(GrammarResults g s, s)] -> ResultList g s r
succeed r t = ResultList (Right [CompleteResultInfo t r])

concatMapResults :: (ResultInfo g s a -> ResultList g s b) -> ResultList g s a -> ResultList g s b
concatMapResults _f (ResultList (Left err)) = ResultList (Left err)
concatMapResults f (ResultList (Right results)) = foldMap f results

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
fixGrammar gf = (Rank2.Arrow . combine) `Rank2.fmap` gf selfReferring `Rank2.ap` fixNullable (gf selfNullable)
   where combine p1 p2 = Parser{continued= continued p1,
                                direct= direct p1,
                                recursive= recursive p1,
                                nullable= nullable p2,
                                recursivelyNullable= recursivelyNullable p2}

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
                    direct= \s t-> concatMapResults (continueFrom s t) $ direct p s t,
                    recursive= (if nullable p
                                then (\r g s t-> concatMapResults (recurseFrom r g s t) $ direct p s t) <$> recursive q
                                else Nothing)
                               <> ((\r g s t-> concatMapResults (continueOrRecurse g s t) $ r g s t) <$> recursive p),
                    nullable= nullable p && nullable q,
                    recursivelyNullable= \g-> recursivelyNullable p g && recursivelyNullable q g}
      where continueFrom _s _t (CompleteResultInfo t' r) = continued q t' (succeed . r) concede
            continueFrom s t (StuckResultInfo r) = r <$> direct q s t
            continueOrRecurse _g _s _t (CompleteResultInfo t' r) = continued q t' (succeed . r) concede
            continueOrRecurse g s t (StuckResultInfo r) = maybe mempty (\recurse-> r <$> recurse g s t) (recursive q)
                                                          <> (r <$> direct q s t)
            recurseFrom _qr _g _s _t CompleteResultInfo{} = mempty
            recurseFrom qr g s t (StuckResultInfo r) = r <$> qr g s t

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

   -- | One or more. The overriding ensures that static fields terminate.
   some :: forall a. Parser g s a -> Parser g s [a]
   some p = some_p
      where many_p = some_p <|> pure []
            some_p = ((:) <$> p <*> many_p){
               nullable= nullable p,
               recursivelyNullable= recursivelyNullable p,
               recursive= (\r g s t-> concatMapResults (proceedWith g s t) $ r g s t) <$> recursive p}
            proceedWith _g _s _t (CompleteResultInfo t' r) = continued many_p t' (succeed . (r:)) concede
            proceedWith g s t (StuckResultInfo r) =
               maybe mempty (\recurse-> (r:) <$> recurse g s t) (recursive many_p)

   -- | Zero or more. The overriding ensures that static fields terminate.
   many p = some p <|> pure []

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
         choose (ResultList (Right [])) rl2 = rl2
         choose rl _ = rl

instance Monad (Parser g s) where
   return = pure
   (>>=) :: forall a b. Parser g s a -> (a -> Parser g s b) -> Parser g s b
   p >>= cont = Parser{continued= \t rc fc-> continued p t (\r t'-> continued (cont r) t' rc fc) fc,
                       direct= \s t-> concatMapResults (continueFrom s t) $ direct p s t,
                       recursive= if nullable p
                                  then Just (\g s t-> (if nullable p
                                                       then concatMapResults (recurseFrom g s t) (direct p s t)
                                                       else mempty)
                                                      <> concatMapResults (continueOrRecurse g s t) (fromMaybe mempty (recursive p) g s t))
                                  else (\r g s t-> concatMapResults (recurseFrom g s t) $ r g s t) <$> recursive p,
                       nullable= nullable p,
                       recursivelyNullable= recursivelyNullable p}
      where continueFrom _s _t (CompleteResultInfo t' r) = continued (cont r) t' succeed concede
            continueFrom s t (StuckResultInfo r) = direct (cont r) s t
            continueOrRecurse _g _s _t (CompleteResultInfo t' r) = continued (cont r) t' succeed concede
            continueOrRecurse g s t (StuckResultInfo r) = fromMaybe mempty (recursive q) g s t <> direct q s t
               where q = cont r
            recurseFrom _g _s _t (CompleteResultInfo t' r) = continued (cont r) t' succeed concede
            recurseFrom g s t (StuckResultInfo r) = fromMaybe mempty (recursive $ cont r) g s t
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

instance MonoidNull s => Parsing (Parser g s) where
   try p = Parser{continued= \t rc fc-> continued p t rc (fc . weaken),
                  direct= \s t-> weakenResults (direct p s t),
                  recursive= (\r g s t-> weakenResults $ r g s t) <$> recursive p,
                  nullable= nullable p,
                  recursivelyNullable= recursivelyNullable p}
      where weaken (FailureInfo s pos msgs) = FailureInfo (pred s) pos msgs
            weakenResults (ResultList (Left err)) = ResultList (Left $ weaken err)
            weakenResults rl = rl
   p <?> msg  = Parser{continued= \t rc fc-> continued p t rc (fc . strengthen),
                       direct= \s t-> strengthenResults (direct p s t),
                       recursive= (\r g s t-> strengthenResults $ r g s t) <$> recursive p,
                       nullable= nullable p,
                       recursivelyNullable= recursivelyNullable p}
      where strengthen (FailureInfo s pos _msgs) = FailureInfo (succ s) pos [msg]
            strengthenResults (ResultList (Left err)) = ResultList (Left $ strengthen err)
            strengthenResults rl = rl
   notFollowedBy p = Parser{continued= \t rc fc-> either
                              (const $ rc () t)
                              (\rs-> if null rs then rc () t
                                     else fc (FailureInfo 1 (genericLength t) ["notFollowedBy"]))
                              (resultList $ continued p t succeed concede),
                            direct= \s t-> either
                              (const $ ResultList $ Right [StuckResultInfo ()])
                              (\rs -> ResultList $
                                      if null rs then Right [StuckResultInfo ()]
                                      else Left (FailureInfo 0 (genericLength t) ["notFollowedBy"]))
                              (resultList $ direct p s t),
                            recursive= (\r g s t-> either
                                          (const $ ResultList $ Right [StuckResultInfo ()])
                                          (\rs -> ResultList $
                                             if null rs then Right []
                                             else Left (FailureInfo 0 (genericLength t) ["notFollowedBy"]))
                                          (resultList $ r g s t))
                                       <$> recursive p,
                            nullable= True,
                            recursivelyNullable= const True}
   skipMany p = go
      where go = pure () <|> p *> go
   unexpected msg = primitive False (\_s _t _ _ fc -> fc msg)
   eof = endOfInput

instance MonoidNull s => LookAheadParsing (Parser g s) where
   lookAhead p = Parser{continued= \t rc fc-> continued p t (\r _-> rc r t) fc,
                        direct= \s t-> restoreResultInputs (direct p s t),
                        recursive= (\r g s t-> restoreResultInputs $ r g s t) <$> recursive p,
                        nullable= True,
                        recursivelyNullable= const True}
               where restoreResultInputs rl@(ResultList Left{}) = rl
                     restoreResultInputs (ResultList (Right rl)) = ResultList (Right $ rewind <$> rl)
                     rewind (CompleteResultInfo _ r) = StuckResultInfo r
                     rewind (StuckResultInfo r) = StuckResultInfo r

instance (Show s, TextualMonoid s) => CharParsing (Parser g s) where
   satisfy = satisfyChar
   string s = Textual.toString (error "unexpected non-character") <$> string (fromString s)
   char = satisfyChar . (==)
   notChar = satisfyChar . (/=)
   anyChar = satisfyChar (const True)
   text t = (fromString . Textual.toString (error "unexpected non-character")) <$> string (Textual.fromText t)

instance (Show s, TextualMonoid s) => TokenParsing (Parser g s)

-- | A parser that fails on any input and succeeds at its end
endOfInput :: (MonoidNull s) => Parser g s ()
endOfInput = primitive True f
   where f s _t rc0 _rc fc
            | null s = rc0 ()
            | otherwise = fc "endOfInput"

-- | Specialization of 'satisfy' on 'TextualMonoid' inputs, accepting an input character only if it satisfies the given
-- predicate.
satisfyChar :: (TextualMonoid s) => (Char -> Bool) -> Parser g s Char
satisfyChar predicate = primitive False f
   where f s t _rc0 rc fc =
            case Textual.splitCharacterPrefix s
            of Just (first, _) | predicate first -> rc first t
               _ -> fc "satisfyChar"

-- | A parser that consumes and returns the given prefix of the input.
string :: (Show s, LeftReductiveMonoid s, FactorialMonoid s) => s -> Parser g s s
string x | null x = pure x
string x = primitive False $ \y t _rc0 rc fc-> 
   case stripPrefix x y
   of Just{} -> rc x (drop (length x - 1) t)
      _ -> fc ("string " ++ show x)
