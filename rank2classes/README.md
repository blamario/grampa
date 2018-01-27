Rank 2 Classes
==============

### The standard constructor type classes in the parallel rank-2 universe ###

The rank2 package exports module `Rank2`, meant to be imported qualified like this:

~~~ {.haskell}
{-# LANGUAGE RankNTypes, TemplateHaskell, TypeOperators #-}
module MyModule where
import qualified Rank2
import qualified Rank2.TH
~~~

Several more imports for the examples...

~~~ {.haskell}
import Data.Functor.Classes (Show1, showsPrec1)
import Data.Functor.Identity (Identity(..))
import Data.Functor.Const (Const(..))
import Data.List (find)
~~~

The `Rank2` import will make available the following type classes:
  * [Rank2.Functor](http://hackage.haskell.org/packages/rank2/doc/html/Rank2.html#t:Functor)
  * [Rank2.Apply](http://hackage.haskell.org/packages/rank2/doc/html/Rank2.html#t:Apply)
  * [Rank2.Applicative](http://hackage.haskell.org/packages/rank2/doc/html/Rank2.html#t:Applicative)
  * [Rank2.Foldable](http://hackage.haskell.org/packages/archive/doc/html/Rank2.html#t:Foldable)
  * [Rank2.Traversable](http://hackage.haskell.org/packages/archive/doc/html/Rank2.html#t:Traversable)
  * [Rank2.Distributive](http://hackage.haskell.org/packages/archive/doc/html/Rank2.html#t:Distributive)

The methods of these type classes all have rank-2 types. The class instances are data types of kind `(k -> *) -> *`,
one example of which would be a database record with different field types but all wrapped by the same type
constructor:

~~~ {.haskell}
data Person f = Person{
   name           :: f String,
   age            :: f Int,
   mother, father :: f (Maybe PersonVerified)
   }
~~~

By wrapping each field we have declared a generalized record type. It can made to play different roles by switching the
value of the parameter `f`. Some examples would be

~~~ {.haskell}
type PersonVerified = Person Identity
type PersonText = Person (Const String)
type PersonWithErrors = Person (Either String)
type PersonDatabase = [PersonVerified]
type PersonDatabaseByColumns = Person []
~~~

If you wish to have the standard [Eq](http://hackage.haskell.org/package/base/docs/Data-Eq.html#t:Eq) and
[Show](http://hackage.haskell.org/package/base/docs/Text-Show.html#t:Show) instances for a record type like `Person`,
it's best if they refer to the
[Eq1](http://hackage.haskell.org/package/base-4.9.1.0/docs/Data-Functor-Classes.html#t:Eq1) and
[Show1](http://hackage.haskell.org/package/base-4.9.1.0/docs/Data-Functor-Classes.html#t:Show1) instances for its
parameter `f`:

~~~ {.haskell}
instance Show1 f => Show (Person f) where
   showsPrec prec person rest =
       "Person{" ++ separator ++ "name=" ++ showsPrec1 prec' (name person)
            ("," ++ separator ++ "age=" ++ showsPrec1 prec' (age person)
            ("," ++ separator ++ "mother=" ++ showsPrec1 prec' (mother person)
            ("," ++ separator ++ "father=" ++ showsPrec1 prec' (father person)
            ("}" ++ rest))))
        where prec' = succ prec
              separator = "\n" ++ replicate prec' ' '
~~~

You can create the rank-2 class instances for your data types manually, or you can generate the instances using the
templates imported from the `Rank2.TH` module with a single line of code per data type:

~~~ {.haskell}
$(Rank2.TH.deriveAll ''Person)
~~~

Either way, once you have the rank-2 type class instances, you can use them to easily convert between records with
different parameters `f`.

### Record construction and modification examples ###

In case of our `Person` record, a couple of helper functions will prove handy:

~~~ {.haskell}
findPerson :: PersonDatabase -> String -> Maybe PersonVerified
findPerson db nameToFind = find ((nameToFind ==) . runIdentity . name) db
   
personByName :: PersonDatabase -> String -> Either String (Maybe PersonVerified)
personByName db personName
   | null personName = Right Nothing
   | p@Just{} <- findPerson db personName = Right p
   | otherwise = Left ("Nobody by name of " ++ personName)
~~~

Now we can start by constructing a `Person` record with rank-2 functions for fields. This record is not so much a person
as a field-by-field person verifier:
 
~~~ {.haskell}
personChecker :: PersonDatabase -> Person (Const String Rank2.~> Either String)
personChecker db =
   Person{name= Rank2.Arrow (Right . getConst),
          age= Rank2.Arrow $ \(Const age)->
               case reads age
               of [(n, "")] -> Right n
                  _ -> Left (age ++ " is not an integer"),
          mother= Rank2.Arrow (personByName db . getConst),
          father= Rank2.Arrow (personByName db . getConst)}
~~~

We can apply it using the [Rank2.<*>](http://hackage.haskell.org/packages/rank2/doc/html/Rank2.html#v:-60--42--62-)
method of the [Rank2.Apply](http://hackage.haskell.org/packages/rank2/doc/html/Rank2.html#t:Apply) type class to a bunch
of textual fields for `Person`, and get back either errors or proper field values:

~~~ {.haskell}
verify :: PersonDatabase -> PersonText -> PersonWithErrors
verify db person = personChecker db Rank2.<*> person
~~~

If there are no errors, we can get a fully verified record by applying
[Rank2.traverse](http://hackage.haskell.org/packages/rank2/doc/html/Rank2.html#v:traverse) to the result:

~~~ {.haskell}
completeVerified :: PersonWithErrors -> Either String PersonVerified
completeVerified = Rank2.traverse (Identity <$>)
~~~

or we can go in the opposite direction with
[Rank2.<$>](http://hackage.haskell.org/packages/rank2/doc/html/Rank2.html#v:-60--36--62-):

~~~ {.haskell}
uncompleteVerified :: PersonVerified -> PersonWithErrors
uncompleteVerified = Rank2.fmap (Right . runIdentity)
~~~

If on the other hand there *are* errors, we can collect them using
[Rank2.foldMap](http://hackage.haskell.org/packages/rank2/doc/html#v:foldMap):

~~~ {.haskell}
verificationErrors :: PersonWithErrors -> [String]
verificationErrors = Rank2.foldMap (either (:[]) (const []))
~~~

Here is an example GHCi session:

~~~ {.haskell}
-- |
-- >>> :{
--let Right alice = completeVerified $
--                  verify [] Person{name= Const "Alice", age= Const "44",
--                                   mother= Const "", father= Const ""}
--    Right bob = completeVerified $
--                verify [] Person{name= Const "Bob", age= Const "45",
--                                 mother= Const "", father= Const ""}
--    Right charlie = completeVerified $
--                    verify [alice, bob] Person{name= Const "Charlie", age= Const "19",
--                                               mother= Const "Alice", father= Const "Bob"}
-- :}
-- 
-- >>> charlie
-- Person{
--  name=Identity "Charlie",
--  age=Identity 19,
--  mother=Identity (Just Person{
--             name=(Identity "Alice"),
--             age=(Identity 44),
--             mother=(Identity Nothing),
--             father=(Identity Nothing)}),
--  father=Identity (Just Person{
--             name=(Identity "Bob"),
--             age=(Identity 45),
--             mother=(Identity Nothing),
--             father=(Identity Nothing)})}
-- >>> :{
--let dave = verify [alice, bob, charlie]
--           Person{name= Const "Dave", age= Const "young",
--                  mother= Const "Lise", father= Const "Mike"}
-- :}
--
-- >>> dave
-- Person{
--  name=Right "Dave",
--  age=Left "young is not an integer",
--  mother=Left "Nobody by name of Lise",
--  father=Left "Nobody by name of Mike"}
-- >>> completeVerified dave
-- Left "young is not an integer"
-- >>> verificationErrors  dave
-- ["young is not an integer","Nobody by name of Lise","Nobody by name of Mike"]
-- >>> Rank2.distribute [alice, bob, charlie]
-- Person{
--  name=Compose [Identity "Alice",Identity "Bob",Identity "Charlie"],
--  age=Compose [Identity 44,Identity 45,Identity 19],
--  mother=Compose [Identity Nothing,Identity Nothing,Identity (Just Person{
--             name=(Identity "Alice"),
--             age=(Identity 44),
--             mother=(Identity Nothing),
--             father=(Identity Nothing)})],
--  father=Compose [Identity Nothing,Identity Nothing,Identity (Just Person{
--             name=(Identity "Bob"),
--             age=(Identity 45),
--             mother=(Identity Nothing),
--             father=(Identity Nothing)})]}
~~~

Grammars are another use case that is almost, but not quite, completely unlike database records. See
[grammatical-parsers](https://github.com/blamario/grampa/tree/master/grammatical-parsers) about that.
