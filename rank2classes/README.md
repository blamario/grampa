rank2
=====

### The standard constructor type classes in the parallel rank-2 universe ###

The rank2 package exports module `Rank2`, meant to be imported qualified like this:

~~~ {.haskell}
{-# LANGUAGE RankNTypes, TemplateHaskell #-}
module MyModule where
import Data.Functor.Classes (Show1, showsPrec1)
import Data.Functor.Identity (Identity(..))
import Data.Functor.Const (Const(..))
import Data.List (find)
import qualified Rank2
import qualified Rank2.TH
~~~

This import will make available the following type classes:
  * [Rank2.Functor](http://hackage.haskell.org/packages/rank2/doc/html/Rank2.html#t:Functor)
  * [Rank2.Apply](http://hackage.haskell.org/packages/rank2/doc/html/Rank2.html#t:Apply)
  * [Rank2.Applicative](http://hackage.haskell.org/packages/rank2/doc/html/Rank2.html#t:Applicative)
  * [Rank2.Foldable](http://hackage.haskell.org/packages/archive/doc/html/Rank2.html#t:Foldable)
  * [Rank2.Traversable](http://hackage.haskell.org/packages/archive/doc/html/Rank2.html#t:Traversable)
  * [Rank2.Distributive](http://hackage.haskell.org/packages/archive/doc/html/Rank2.html#t:Distributive)

The methods of these type classes all have rank-2 types. They operate on data types of kind `(* -> *) -> *`, which could
be a database record with different field types:

~~~ {.haskell}
data Person f = Person{
   name           :: f String,
   age            :: f Int,
   mother, father :: f (Maybe PersonVerified)
   }
~~~

Here we have a generalized record type that can play different roles by switching the value of the parameter `f`. For
example,

~~~ {.haskell}
type PersonVerified = Person Identity
type PersonText = Person (Const String)
type PersonWithErrors = Person (Either String)
type PersonDatabase = [PersonVerified]
~~~

If you wish to have standard `Eq` and `Show` instances for a record type like `Person`, it's best if they refer to `Eq1`
and `Show1` instances for its parameter `f`:

~~~ {.haskell}
instance Show1 f => Show (Person f) where
   show person = "Person{name=" ++ showsPrec1 0 (name person)
                 (", age=" ++ showsPrec1 0 (age person)
                      (", mother=" ++ showsPrec1 0 (mother person)
                       (", father=" ++ showsPrec1 0 (father person) "}")))
~~~

You can create the rank-2 class instances for your data types manually, or you can generate the instances from the
templates imported from the `Rank2.TH` module with two lines of code like this:

~~~ {.haskell}
$(Rank2.TH.deriveAll ''Person)
~~~

Either way, once you have the rank-2 type class instances, you can use them to easily convert between records with
different parameters `f`. First we need a couple of helper functions:

~~~ {.haskell}
findPerson :: PersonDatabase -> String -> Maybe PersonVerified
findPerson db nameToFind = find ((nameToFind ==) . runIdentity . name) db
   
personByName :: PersonDatabase -> String -> Either String (Maybe PersonVerified)
personByName db personName
   | null personName = Right Nothing
   | otherwise = maybe (Left $ "Nobody by name of " ++ personName) (Right . Just)
                 (findPerson db personName)
~~~

 Now we can start by constructing a `Person` record with rank-2 functions for fields:
 
~~~ {.haskell}
personChecker :: PersonDatabase -> Person (Rank2.Arrow (Const String) (Either String))
personChecker db =
   Person{name= Rank2.Arrow (Right . getConst),
          age= Rank2.Arrow $ \(Const age)->
               case reads age
               of [(n, "")] -> Right n
                  _ -> Left (age ++ " is not an integer"),
          mother= Rank2.Arrow (personByName db . getConst),
          father= Rank2.Arrow (personByName db . getConst)}
~~~

which we can apply using the `Rank1.<*>` method of the `Rank2.Apply` type class to a bunch of textual fields for
`Person`, and get back either errors or proper field values:

~~~ {.haskell}
verify :: PersonDatabase -> PersonText -> PersonWithErrors
verify db person = personChecker db Rank2.<*> person
~~~

If there are no errors, we can get a fully verified record using `Rank2.traverse` on the result:

~~~ {.haskell}
completeVerified :: PersonWithErrors -> Either String PersonVerified
completeVerified = Rank2.traverse (Identity <$>)
~~~

or can go in the oposite direction with `Rank2.fmap`:

~~~ {.haskell}
uncompleteVerified :: PersonVerified -> PersonWithErrors
uncompleteVerified = Rank2.fmap (Right . runIdentity)
~~~

If there are errors, we can collect them using `Rank2.foldMap`:

~~~ {.haskell}
verificationErrors :: PersonWithErrors -> [String]
verificationErrors = Rank2.foldMap (either (:[]) (const []))
~~~

Here is an example GHCi session:

~~~ {.haskell}
-- |
-- >>> let Right alice = completeVerified $ verify [] Person{name= Const "Alice", age= Const "44", mother= Const "", father= Const ""}
-- >>> let Right bob = completeVerified $ verify [] Person{name= Const "Bob", age= Const "45", mother= Const "", father= Const ""}
-- >>> let Right charlie = completeVerified $ verify [alice, bob] Person{name= Const "Charlie", age= Const "19", mother= Const "Alice", father= Const "Bob"}
-- >>> charlie
-- Person{name=Identity "Charlie", age=Identity 19, mother=Identity (Just Person{name=Identity "Alice", age=Identity 44, mother=Identity Nothing, father=Identity Nothing}), father=Identity (Just Person{name=Identity "Bob", age=Identity 45, mother=Identity Nothing, father=Identity Nothing})}
-- >>> let dave = verify [alice, bob, charlie] Person{name= Const "Eve", age= Const "young", mother= Const "Lise", father= Const "Mike"}
-- >>> dave
-- Person{name=Right "Eve", age=Left "young is not an integer", mother=Left "Nobody by name of Lise", father=Left "Nobody by name of Mike"}
-- >>> completeVerified dave
-- Left "young is not an integer"
-- >>> verificationErrors  dave
-- ["young is not an integer","Nobody by name of Lise","Nobody by name of Mike"]
-- >>> Rank2.distribute [alice, bob, charlie]
-- Person{name=Compose [Identity "Alice",Identity "Bob",Identity "Charlie"], age=Compose [Identity 44,Identity 45,Identity 19], mother=Compose [Identity Nothing,Identity Nothing,Identity (Just Person{name=Identity "Alice", age=Identity 44, mother=Identity Nothing, father=Identity Nothing})], father=Compose [Identity Nothing,Identity Nothing,Identity (Just Person{name=Identity "Bob", age=Identity 45, mother=Identity Nothing, father=Identity Nothing})]}
~~~
