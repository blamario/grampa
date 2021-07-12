{-# LANGUAGE TypeFamilies #-}

module Text.Grampa.Combinators (moptional, concatMany, concatSome,
                                flag, count, upto,
                                delimiter, operator, keyword) where

import Control.Applicative(Applicative(..), Alternative(..))
import Data.List.NonEmpty (fromList)
import Data.Monoid (Monoid, (<>))
import Data.Monoid.Factorial (FactorialMonoid)
import Data.Semigroup (Semigroup(sconcat))
import Data.Semigroup.Cancellative (LeftReductive)

import Text.Grampa.Class (InputParsing(ParserInput, string), LexicalParsing(lexicalToken, keyword))
import Text.Parser.Combinators (Parsing((<?>)), count)

-- | Attempts to parse a monoidal value, if the argument parser fails returns 'mempty'.
moptional :: (Alternative p, Monoid a) => p a -> p a
moptional p = p <|> pure mempty

-- | Zero or more argument occurrences like 'many', with concatenated monoidal results.
concatMany :: (Alternative p, Monoid a) => p a -> p a
concatMany p = mconcat <$> many p

-- | One or more argument occurrences like 'some', with concatenated monoidal results.
concatSome :: (Alternative p, Semigroup a) => p a -> p a
concatSome p = sconcat . fromList <$> some p

-- | Returns 'True' if the argument parser succeeds and 'False' otherwise.
flag :: Alternative p => p a -> p Bool
flag p = True <$ p <|> pure False

-- | Parses between 0 and N occurrences of the argument parser in sequence and returns the list of results.
upto :: Alternative p => Int -> p a -> p [a]
upto n p
   | n > 0 = (:) <$> p <*> upto (pred n) p 
             <|> pure []
   | otherwise = pure []

-- | Parses the given delimiter, such as a comma or a brace
delimiter :: (Show s, FactorialMonoid s, LeftReductive s, s ~ ParserInput m, LexicalParsing m) => s -> m s
delimiter s = lexicalToken (string s) <?> ("delimiter " <> show s)

-- | Parses the given operator symbol
operator :: (Show s, FactorialMonoid s, LeftReductive s, s ~ ParserInput m, LexicalParsing m) => s -> m s
operator s = lexicalToken (string s) <?> ("operator " <> show s)
