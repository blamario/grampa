# Revision history for deep-transformations

## 0.4 -- 2025-10-26

### **BREAKING**

Major type changes:

* Moved the `attribution` method from the `AG.Attribution` class to the new `AG.At` class
* Changed the kind of the second parameter of the `AG.Atts` type family from `Type` to `(Type -> Type) -> (Type ->
  Type) -> Type`
* As a consequence, removed the two deep&shallow type parameters of the `AG.Attribution` and `AG.At` classes
* Adopted the same naming scheme in `AG.Dimorphic` and `AG.Monomorphic`
* Dropped functions `applyDefault`, and `applyDefaultWithAttributes` from `Transformation.AG`

Major reorganization of the data types around the `Keep` semantics:

* Dropped `PreservingSemantics` from `AG`, `Monomorphic`, and `Dimorphic` modules
* Dropped `AG.knitKeeping`, making `AG.Keep` an attribution wrapper instead
* Dropped `Keep` from `Mono`/`Dimorphic` modules
* Replaced `AG.AllAtts` with the `AG.Kept` data type
* Introduced the `AG.Kept` attribute synthesized by the `AG.Keep` transformation wrapper

Breaking instance changes:

* Strengthened the `Foldable` constraint on the `attribution` method to `Traversable`
* Made the default `Bequether` & `Synthesizer` instances specific to `Auto`
* Dropped the fixed instance `Full.Functor (Transformation.Rank2.Map p q)`

### Additions

* the `AG.Knit` transformation
* `Transformation.Coercion` and `Full.coerce`
* the wrapper `Dimorphic.T` separate from `Dimorphic.Auto`
* the `Origin` associated type
* `mapInherited` and `mapSynthesized`
* `Semigroup` and `Monoid` instances for `Inherited` and `Synthesized`
* `Deep.Const2`
* `instance Attribution (Keep t)`

### Other improvements

* Added `test/RepMinKeep ` and `test/RepMinKeepAG`
* Bumped the lower bound of the `rank2classes` dependency to require the new `Rank2.coerce` method
* Bumped the upper bound of the `generic-lens` dependency
* Expanded documentation
* Fixed the Transformation doctests for docspec
* Turned `doctests` from a testsuite into a named library, dropped `cabal-doctest`
* Updated GitHub CI action

## 0.3 -- 2025-01-01

* **BREAKING**: Changed the definitions of `Deep.Product` and `Deep.Sum`
* Added `Shallow` class instances for all data types declared in the `Rank2` module
* Added `Shallow` class instances for `Proxy`, `Const`, `Product`, and `Sum`
* Bumped the upper bound of the template-haskell dependency to compile with GHC 9.12.1
* Fixed the PolyKinds-related test errors
* Added `Deep.Only` and `Deep.Flip` data types to mirror `Rank2.Only` and `Rank2.Flip`

## 0.2.3 -- 2024-05-18

* Bumped the upper bound of the template-haskell dependency
* Generalized the TH generation code
* Fixed the loopy superclass constraints in instance declarations

## 0.2.2 -- 2023-06-25

* Updated for GHC 9.8.1 and TH 2.22
* Updated TH code to use `DuplicateRecordFields` and `OverloadedRecordDot` when enabled
* Fixed warnings in tests

## 0.2.1.2 -- 2023-06-25

* Bumped the upper bound of the `template-haskell` dependency

## 0.2.1.1 -- 2023-04-02

* Bumped the upper bound of the `rank2classes` dependency

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
