Version 1.1
---------------
* Replaced own `Product` data type by the one from `Data.Functor.Product`

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
