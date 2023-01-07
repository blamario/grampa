# Revision history for deep-transformations

## 0.2.1 -- 2023-01-07

* Added AG.Dimorphic
* Added combinators `Transformation.Mapped`, `Folded`, and `Traversed`
* Compiling with GHC 9.4

## 0.2 -- 2022-03-27

* Changes necessary to compile with GHC 9.2.2
* Excluded GHC 8.2.2 from `deep-transformations` and GitHub CI
* Increased the `deep-transformations`' bottom bound of base dependency
* Relaxed the bounds of the `generic-lens` dependency
* Fixed `deep-transformations` compilation with GHC 9.0.1
* Added an explicit implementation `mappend = (<>)`
* Used haskell-ci to generate GitHub CI
* Incremented upper dependency bounds
* Added `AG.Generics.Keep`
* Added `knitKeeping` and `applyDefaultWithAttributes` to `AG`
* Dropped `fullMapDefault`
* Switch the README's attribute grammar functor to map upwards
* Removed unused code
* Added `infixl 4` declarations for all `<$>` methods
* Added the `AG.Monomorphic` module
* Fixed `Transformation.Shallow.TH` for repeated type parameters
* Added `Transformation.Deep.Sum`

## 0.1 -- 2020-11-11

First version
