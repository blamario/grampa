Version 1.3.2
---------------
* Exported the `$` synonym for `apply`

Version 1.3.1.2
---------------
* Fixed doctest module name issue
* Incremented the lower bound of base dependency

Version 1.3.1.1
---------------
* Fixed the doctests after cabal get

Version 1.3.1
---------------
* Added missing markdown-unlit dependency
* Strictified one argument of Rank2.<$> and Rank2.<*>

Version 1.3
---------------
* Added `newtype Flip` to exports - PR by Jeremy List
* Generating INLINE pragmas from Rank2.TH
* Generating the proper constraints on derived instances where needed

Version 1.2.1
---------------
* Added unsafeDeriveApply

Version 1.2
---------------
* Added the class instances for Data.Functor.Const
* Fixed and optimized the Foldable/Traversable instance code generated for bare fields in Rank2.TH

Version 1.1
---------------
* Replaced own `Product` data type by the one from `Data.Functor.Product`
* Added instances of `Data.Functor.Sum`
* Removed the TH generation of partial Apply and Distributive instances
* Covered more constructor cases in TH code
* Added use-template-haskell flag, true by default - PR by Dridus

Version 1.0.2
---------------
* Fixed the bounds and `Semigroup` to compile with GHC 8.4.1
* Added the ~> type synonym
* Fixed `deriveFunctor` for record fields with concrete types - PR by Tom Smalley

Version 1.0.1
---------------
* Fixed the doctests

Version 1.0
---------------
* Swapped `distributeWith` with `cotraverse`
* Documentation improvements

Version 0.2.1.1
---------------
* Corrected the README

Version 0.2.1
---------------
* Incremented the dependency bounds for GHC 8.2.1

Version 0.2
---------------
* Introduced `DistributiveTraversable` as a generalization of `Distributive`
* Export "cotraverse" and "cotraverseTraversable"
* Added `liftA3`, `liftA4`, `liftA5`
* Added more convienence functions
* Fixed grammatical errors and overlong lines

Version 0.1.1
---------------
* Generalized the classes with `{-# LANGUAGE PolyKinds" #-}`

Version 0.1
---------------
* Initial release
