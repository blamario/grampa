> {-# LANGUAGE TemplateHaskell #-}
> module Doctest where
> 
> import qualified Rank2
> import qualified Rank2.TH
> import Data.Functor.Classes (Show1, showsPrec1)
> import Data.Functor.Const (Const(..))
> import Data.Functor.Identity (Identity(..))
> import Data.List (find)
>
> data Person f = Person{
>    name           :: f String,
>    age            :: f Int,
>    mother, father :: f (Maybe PersonVerified)
>    }
> 
> instance Show1 f => Show (Person f) where
>    show person = "Person{name=" ++ showsPrec1 0 (name person)
>                  (", age=" ++ showsPrec1 0 (age person)
>                       (", mother=" ++ showsPrec1 0 (mother person)
>                        (", father=" ++ showsPrec1 0 (father person) "}")))
> 
> type PersonText = Person (Const String)
> type PersonWithErrors = Person (Either String)
> type PersonVerified = Person Identity
> type PersonDatabase = [PersonVerified]
>
> $(Rank2.TH.deriveAll ''Person)
> 
> findPerson :: PersonDatabase -> String -> Maybe PersonVerified
> findPerson db nameToFind = find ((nameToFind ==) . runIdentity . name) db
>
> personByName :: PersonDatabase -> String -> Either String (Maybe PersonVerified)
> personByName db personName
>    | null personName = Right Nothing
>    | otherwise = maybe (Left $ "Nobody by name of " ++ personName) (Right . Just)
>                  (findPerson db personName)
>
> personChecker :: PersonDatabase -> Person (Rank2.Arrow (Const String) (Either String))
> personChecker db =
>    Person{name= Rank2.Arrow (Right . getConst),
>           age= Rank2.Arrow $ \(Const age)->
>                case reads age
>                of [(n, "")] -> Right n
>                   _ -> Left (age ++ " is not an integer"),
>           mother= Rank2.Arrow (personByName db . getConst),
>           father= Rank2.Arrow (personByName db . getConst)}
>
> verify :: PersonDatabase -> PersonText -> PersonWithErrors
> verify db person = personChecker db Rank2.<*> person
>
> completeVerified :: PersonWithErrors -> Either String PersonVerified
> completeVerified = Rank2.traverse (Identity <$>)
> 
> uncompleteVerified :: PersonVerified -> PersonWithErrors
> uncompleteVerified = Rank2.fmap (Right . runIdentity)
> 
> verificationErrors :: PersonWithErrors -> [String]
> verificationErrors = Rank2.foldMap (either (:[]) (const []))
> 
> -- |
> -- >>> let Right alice = completeVerified $ verify [] Person{name= Const "Alice", age= Const "44", mother= Const "", father= Const ""}
> -- >>> let Right bob = completeVerified $ verify [] Person{name= Const "Bob", age= Const "45", mother= Const "", father= Const ""}
> -- >>> let Right charlie = completeVerified $ verify [alice, bob] Person{name= Const "Charlie", age= Const "19", mother= Const "Alice", father= Const "Bob"}
> -- >>> charlie
> -- Person{name=Identity "Charlie", age=Identity 19, mother=Identity (Just Person{name=Identity "Alice", age=Identity 44, mother=Identity Nothing, father=Identity Nothing}), father=Identity (Just Person{name=Identity "Bob", age=Identity 45, mother=Identity Nothing, father=Identity Nothing})}
> -- >>> let dave = verify [alice, bob, charlie] Person{name= Const "Eve", age= Const "young", mother= Const "Lise", father= Const "Mike"}
> -- >>> dave
> -- Person{name=Right "Eve", age=Left "young is not an integer", mother=Left "Nobody by name of Lise", father=Left "Nobody by name of Mike"}
> -- >>> completeVerified dave
> -- Left "young is not an integer"
> -- >>> verificationErrors  dave
> -- ["young is not an integer","Nobody by name of Lise","Nobody by name of Mike"]
> -- >>> Rank2.distribute [alice, bob, charlie]
> -- Person{name=Compose [Identity "Alice",Identity "Bob",Identity "Charlie"], age=Compose [Identity 44,Identity 45,Identity 19], mother=Compose [Identity Nothing,Identity Nothing,Identity (Just Person{name=Identity "Alice", age=Identity 44, mother=Identity Nothing, father=Identity Nothing})], father=Compose [Identity Nothing,Identity Nothing,Identity (Just Person{name=Identity "Bob", age=Identity 45, mother=Identity Nothing, father=Identity Nothing})]}
