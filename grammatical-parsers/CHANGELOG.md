Version 0.5.2
---------------
* Switched from the deprecated `witherable-class` package to `witherable`
* Deprecated the `ContextFree.Memoizing` module
* Fixed and tested the `<<|>` instance of the `LeftRecursive` parser
* Fixed and tested a with left-recursive monadic empty match
* Fixed an infinite loop in the expected set closure calculation
* Improved documentation
* Added the `TraceableParsing` class for easier debugging, not exposed

Version 0.5.1
---------------
* Fixed the `skipAll` implementation for the `SortedMemoizing.Transformer` parser
* Added the `Filterable` and `MonadFail` instances to all parser types
* Added instances `Monad Ambiguous` and `Functor ParseFailure`
* Generalized the types of `LeftRecursive.Transformer.tmap` and `tbind`
* Incremented dependencies' upper bounds

Version 0.5
---------------
* Replaced `MonoidParsing` by `InputParsing`
* Moved the `InputParsing` and `InputCharParser` classes into the `input-parsers` package
* Added the `Expected` data type to eliminate the `Show` constraint on `string`
* Fixed the signature of `scan` and `scanChars`
* Deprecated `endOfInput` and `satisfyChar`
* Replaced `Lexical g` with `LexicalParsing m`
* Added modules `SortedMemoizing.Transformer` and `LeftRecursive.Transformer`
* Added the `getAmbiguous` destructor

Version 0.4.1.2
---------------
* Fixed the doctests using cabal-doctest
* Fixed a QuickCheck timeout, issue #20

Version 0.4.1.1
---------------
* Fixed the doctests after cabal get

Version 0.4.1
---------------
* Adjustments for monoid-subclasses-1.0

Version 0.4.0.1
---------------
* Added missing markdown-unlit dependency

Version 0.4
---------------
* Added `Position` and related functions
* Renamed `showFailure` to `failureDescription`
* Faster parsing at the cost of slower compilation
* Replaced Word64 source positions by plain Int
* Fixed Haddock-related compilation warnings

Version 0.3.2
---------------
* Improved error reporting
* Updated test suite to work with testing-feat >= 1.1
* Fixed the construction of `Ambiguous` results
* Added Applicative and Traversable instances for Ambiguous

Version 0.3.1
---------------
* Added `Text.Parser.Combinators`
* Improved `try/(<?>)` error reporting
* Added `showFailure`

Version 0.3
---------------
* Eliminated `token` and `whiteSpace`
* Added the `Lexical` class of grammars
* Added `Semigroup` instances to fix compilation with GHC 8.4.1
* More precise calculation of `(>>=)` descendants
* Added the `Ambiguous` results and the `AmbiguousParsing` class
* Added the `SortedMemoizing` module

Version 0.2.2
---------------
* Incremented dependency version bounds

Version 0.2.1
---------------
* Added the `ContextFree.Continued` module
* Fixed `LeftRecursive.Parallel.concatMany`

Version 0.2
---------------
* Numerous performance and documentation improvements
* Fixed the `endOfInput` implementation in `PEG.Backtrack`
* Made `LeftRecursive.Parser` a type synonym, introduced `peg` and `longest`
* Added the `notSatisfy[Char]` methods
* Added `satisfyCharInput`
