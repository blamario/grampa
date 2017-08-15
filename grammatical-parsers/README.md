Grammatical Parsers
===================

Behold, yet another parser combinator library in Haskell. Except this one is capable of working with grammars rather than mere parsers. A more in-depth description is available in the [paper](../Grampa.lhs.pdf) from Haskell Symposium 2017, what follows is a short tutorial.

You can apply the usual
[Applicative](http://hackage.haskell.org/package/base/docs/Control-Applicative.html#t:Applicative),
[Alternative](http://hackage.haskell.org/package/base/docs/Control-Applicative.html#t:Alternative), and
[Monad](http://hackage.haskell.org/package/base/docs/Control-Monad.html#t:Monad) operators to combine primitive parsers
into larger ones. The combinators from the [parsers](http://hackage.haskell.org/package/parsers) library type classes
are also available. Here are some typical imports you may need:

~~~ {.haskell}
{-# LANGUAGE RecordWildCards, ScopedTypeVariables, TemplateHaskell #-}
module README where
import Control.Applicative
import Data.Char (isDigit)
import Data.Functor.Classes (Show1, showsPrec1)
import Text.Grampa
import Text.Grampa.ContextFree.LeftRecursive (Parser)
import qualified Rank2.TH
~~~

What puts this library apart from most is that these parsers are *grammatical*, just as the library name says. Instead
of writing the parser definitions as top-level bindings, you can and should group them into a grammar record definition,
like this:

~~~ {.haskell}
arithmetic :: GrammarBuilder Arithmetic g Parser String
arithmetic Arithmetic{..} = Arithmetic{
   sum= product
         <|> string "-" *> (negate <$> product)
         <|> (+) <$> sum <* string "+" <*> product
         <|> (-) <$> sum <* string "-" <*> product,
   product= factor
         <|> (*) <$> product <* string "*" <*> factor
         <|> div <$> product <* string "/" <*> factor,
   factor= read <$> number
           <|> string "(" *> sum <* string ")",
   number= takeCharsWhile1 isDigit <?> "number"}
~~~

What on Earth for? One good reason is that these parser definitions can then be left-recursive, which is normally a
death knell for parser libraries. There are other benefits like memoization and grammar composability, and the main
downside is the obligation to declare the grammar record:

~~~ {.haskell}
data Arithmetic f = Arithmetic{sum     :: f Int,
                               product :: f Int,
                               factor  :: f Int,
                               number  :: f String}
~~~

and to make it an instance of several rank 2 type classes:

~~~ {.haskell}
$(Rank2.TH.deriveAll ''Arithmetic)
~~~

Optionally, you may also be inclined to declare a proper ``Show`` instance, as it's often handy:

~~~ {.haskell}
instance Show1 f => Show (Arithmetic f) where
   show Arithmetic{..} =
      "Arithmetic{\n  sum=" ++ showsPrec1 0 sum
           (",\n  product=" ++ showsPrec1 0 factor
           (",\n  factor=" ++ showsPrec1 0 factor
           (",\n  number=" ++ showsPrec1 0 number "}")))
~~~

Once that's done, use [fixGrammar](http://hackage.haskell.org/package/grammatical-parsers/docs/Text-Grampa.html#v:fixGrammar) to, well, fix the grammar

~~~ {.haskell}
grammar = fixGrammar arithmetic
~~~

and then [parseComplete](http://hackage.haskell.org/package/grammatical-parsers/docs/Text-Grampa.html#v:parseComplete)
or [parsePrefix](http://hackage.haskell.org/package/grammatical-parsers/docs/Text-Grampa.html#v:parsePrefix) to parse
some input.

~~~ {.haskell}
-- |
-- >>> parseComplete grammar "42"
-- Arithmetic{
--   sum=Compose (Right [42]),
--   product=Compose (Right [42]),
--   factor=Compose (Right [42]),
--   number=Compose (Right ["42"])}
-- >>> parseComplete grammar "1+2*3"
-- Arithmetic{
--   sum=Compose (Right [7]),
--   product=Compose (Left (ParseFailure 1 ["endOfInput"])),
--   factor=Compose (Left (ParseFailure 1 ["endOfInput"])),
--   number=Compose (Left (ParseFailure 1 ["endOfInput"]))}
-- >>> parsePrefix grammar "1+2*3"
-- Arithmetic{
--   sum=Compose (Compose (Right [("+2*3",1),("*3",3),("",7)])),
--   product=Compose (Compose (Right [("+2*3",1)])),
--   factor=Compose (Compose (Right [("+2*3",1)])),
--   number=Compose (Compose (Right [("+2*3","1")]))}
~~~

To see more grammar examples, go straight to the
[examples](https://github.com/blamario/grampa/tree/master/grammatical-parsers/examples) directory that builds up several
smaller grammars and combines them all together in the
[Combined](https://github.com/blamario/grampa/blob/master/grammatical-parsers/examples/Combined.hs) module.

For more conventional tastes there is a monolithic
[Lua grammar](https://github.com/blamario/language-lua2/blob/master/src/Language/Lua/Grammar.hs) example as well.
