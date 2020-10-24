The Grampa project consists of three related Haskell libraries:

- [`rank2classes`](http://github.com/blamario/grampa/tree/master/rank2classes) is at the lowest level. It provides a
  set of type classes that mirror `Functor` and related type classes but for records.
- [`grammatical-parsers`](http://github.com/blamario/grampa/tree/master/grammatical-parsers) is a parser combinator
  and grammar combinator library than depends on rank2classes
- [`deep-transformations`](http://github.com/blamario/grampa/tree/master/deep-transformations) depends on and extends
  `rank2classes` to operate on trees of mutually-recusive types. This library is independent of grammatical-parsers,
  but can be used to manipulate the parse trees produced by it.
