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
