Deep transformations
====================

An abstract syntax tree of a realistic programming language will generally contain more than one node type. In other
 words, its type will involve several mutually recursive data types: the usual suspects would be expression,
 declaration, type, statement, and module.

This library, `deep-transformations`, provides a solution to the problem of traversing and transforming such
 heterogenous trees. It is not the only solution by far. The venerable
 [`multiplate`](http://hackage.haskell.org/package/multiplate) has long offered a very approachable way to traverse and
 fold heterogenous trees, without even depending on any extension to standard Haskell. Multiplate is not as expressive
 as the present library, but if it satisfies your needs go with it. If not, be aware that `deep-transformations` relies
 on quite a number of extensions:

~~~ {.haskell}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses,
             StandaloneDeriving, TypeFamilies, TypeOperators #-}
module README where
~~~

It will also require several imports.

~~~ {.haskell}
import Control.Applicative
import Data.Coerce (coerce)
import Data.Functor.Const
import Data.Functor.Identity
import qualified Rank2
import Transformation (Transformation, At)
import qualified Transformation
import qualified Transformation.AG as AG
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.Shallow as Shallow
~~~

Let us start with the same example handled by [Multiplate](https://wiki.haskell.org/Multiplate). It's a relatively
 simple set of two mutually recursive data types.

    data Expr = Con Int
              | Add Expr Expr
              | Mul Expr Expr
              | EVar Var
              | Let Decl Expr

    data Decl = Var := Expr
              | Seq Decl Decl

    type Var = String

This kind of tree is *not* something that `deep-transformations` can handle. Before you can use this library, you must
parameterize every data type and wrap every recursive field of every constructor as follows:

~~~ {.haskell}
data Expr d s = Con Int
              | Add (s (Expr d d)) (s (Expr d d))
              | Mul (s (Expr d d)) (s (Expr d d))
              | EVar Var
              | Let (s (Decl d d)) (s (Expr d d))

data Decl d s = Var := s (Expr d d)
              | Seq (s (Decl d d)) (s (Decl d d))

type Var = String
~~~

The parameters `d` and `s` stand for the *deep* and *shallow* type constructor. A typical occurrence of the tree will
 instantiate the same type for both parameters. While it may look ugly and annoying, this kind of parameterization
 carries benefits beyond this library's use. The parameters may vary from `Identity`, equivalent to the original
 simple formulation, via `(,) LexicalInfo` to store the source code position and white-space and comments for every
 node, or `[]` if you need some ambiguity, to attribute grammar semantics.

Now, let's declare all the class instances. First make the tree `Show`.

~~~ {.haskell}
deriving instance (Show (f (Expr f' f')), Show (f (Decl f' f'))) => Show (Expr f' f)
deriving instance (Show (f (Expr f' f')), Show (f (Decl f' f'))) => Show (Decl f' f)
~~~

The shallow parameter comes last so that every data type can have instances of
 [`rank2classes`](https://hackage.haskell.org/package/rank2classes). The instances below are written manually, but
 they can be generated automatically using the Template Haskell imports from
 [`Rank2.TH`](https://hackage.haskell.org/package/rank2classes/docs/Rank2-TH.html).

~~~ {.haskell}
instance Rank2.Functor (Decl f') where
  f <$> (v := e) = (v := f e)
  f <$> Seq x y  = Seq (f x) (f y)

instance Rank2.Functor (Expr f') where
  f <$> Con n   = Con n
  f <$> Add x y = Add (f x) (f y)
  f <$> Mul x y = Mul (f x) (f y)
  f <$> Let d e = Let (f d) (f e)
  f <$> EVar v  = EVar v

instance Rank2.Foldable (Decl f') where
  f `foldMap` (v := e) = f e
  f `foldMap` Seq x y  = f x <> f y

instance Rank2.Foldable (Expr f') where
  f `foldMap` Con n   = mempty
  f `foldMap` Add x y = f x <> f y
  f `foldMap` Mul x y = f x <> f y
  f `foldMap` Let d e = f d <> f e
  f `foldMap` EVar v  = mempty
~~~

While the methods declared above can be handy, they are limited in requiring that the function argument `f` must be
 polymorphic in the wrapped field type. In other words, it cannot behave one way for an `Expr` and another for a
 `Decl`. That can be a severe handicap.

The class methods exported by `deep-transformations` therefore work not with polymorphic functions but with
 *tranformations*. The instances of these classes are similar to the instances above. Also as above, they can be
 generated automatically with Template Haskell functions from
 [`Transformation.Deep.TH`](https://hackage.haskell.org/package/deep-transformations/docs/Transformation-Deep-TH.html).

~~~ {.haskell}
instance (Transformation t, Full.Functor t Decl, Full.Functor t Expr) => Deep.Functor t Decl where
  t <$> (v := e)   = (v := (t Full.<$> e))
  t <$> Seq x y = Seq (t Full.<$> x) (t Full.<$> y)

instance (Transformation t, Full.Functor t Decl, Full.Functor t Expr) => Deep.Functor t Expr where
  t <$> Con n   = Con n
  t <$> Add x y = Add (t Full.<$> x) (t Full.<$> y)
  t <$> Mul x y = Mul (t Full.<$> x) (t Full.<$> y)
  t <$> Let d e = Let (t Full.<$> d) (t Full.<$> e)
  t <$> EVar v  = EVar v

instance (Transformation t, Full.Foldable t Decl, Full.Foldable t Expr) => Deep.Foldable t Decl where
  t `foldMap` (v := e) = t `Full.foldMap` e
  t `foldMap` Seq x y  = t `Full.foldMap` x <> t `Full.foldMap` y

instance (Transformation t, Full.Foldable t Decl, Full.Foldable t Expr) => Deep.Foldable t Expr where
  t `foldMap` Con n   = mempty
  t `foldMap` Add x y = t `Full.foldMap` x <> t `Full.foldMap` y
  t `foldMap` Mul x y = t `Full.foldMap` x <> t `Full.foldMap` y
  t `foldMap` Let d e = t `Full.foldMap` d <> t `Full.foldMap` e
  t `foldMap` EVar v  = mempty
~~~

~~~ {.haskell.ignore}
instance (Full.Traversable t Decl, Full.Traversable t Expr) => Deep.Traversable t Decl where
  t `traverse` (v := e)   = (v := (t `Full.traverse` e))
  t `traverse` Seq x y = Seq (t `Full.traverse` x) (t `Full.traverse` y)

instance (Full.Traversable t Decl, Full.Traversable t Expr) => Deep.Traversable t Expr where
  t `traverse` Con n   = pure (Con n)
  t `traverse` Add x y = Add <$> t `Full.traverse` x <*> t `Full.traverse` y
  t `traverse` Mul x y = Mul <$> t `Full.traverse` x <*> t `Full.traverse` y
  t `traverse` Let d e = Let <$> t `Full.traverse` d <*> t `Full.traverse` e
  t `traverse` EVar v  = pure (EVar v)
~~~

Once the above boilerplate code is written or generated, no further boilerplate code need be written.

Generic Programing with deep-transformations
============================================

Folding
-------

Suppose we we want to get a list of all variables used in an expression. To do this we would declare the appropriate
 [`Transformation`](https://hackage.haskell.org/package/deep-transformations/docs/Transformation.html) instance for an
 arbitrary data type. We'll give this data type an evocative name.

~~~ {.haskell}
data GetVariables = GetVariables

instance Transformation GetVariables where
  type Domain GetVariables = Identity
  type Codomain GetVariables = Const [Var]
~~~

The `Transformation` instance for `GetVariables` converts the `Identity` wrapper of a given node into a constant list
 of variables contained within it. To do that, it must behave differently for `Expr` and for `Decl`:

~~~ {.haskell}
instance GetVariables `At` Expr Identity Identity where
  GetVariables $ Identity (EVar v) = Const [v]
  GetVariables $ x = mempty

instance GetVariables `At` Decl Identity Identity where
  GetVariables $ x = mempty
~~~

There is one last decision to make about our transformation: is it a pre-order or a post-order fold? In this case it
 doesn't matter, so let's pick pre-order:

~~~ {.haskell}
instance Full.Foldable GetVariables Decl where
  foldMap = Full.foldMapDownDefault

instance Full.Foldable GetVariables Expr where
  foldMap = Full.foldMapDownDefault
~~~

Now the transformation is ready. We'll try it on this example:

~~~ {.haskell}
e1 :: Expr Identity Identity
e1 = bin Let ("x" := Identity (Con 42)) (bin Add (EVar "x") (EVar "y"))
~~~

with the help of a little combinator to shorten the construction of binary nodes:

~~~ {.haskell}
bin f a b = f (Identity a) (Identity b)
~~~

Folding the entire expression tree is as simple as applying `Deep.foldMap` at its root:

~~~ {.haskell}
-- |
-- >>> Deep.foldMap GetVariables e1
-- ["x","y"]
~~~

Traversing
----------

Suppose we want to recursively evaluate constant expressions in the language. We define another data type with a
 `Transformation` instance for the purpose. This time `Domain` and `Codomain` are both `Identity`, since the
 simplification doesn't change the tree type.

~~~ {.haskell}
data ConstantFold = ConstantFold

instance Transformation ConstantFold where
  type Domain ConstantFold = Identity
  type Codomain ConstantFold = Identity

instance ConstantFold `At` Expr Identity Identity where
  ConstantFold $ Identity (Add (Identity (Con x)) (Identity (Con y))) = Identity (Con (x + y))
  ConstantFold $ Identity (Mul (Identity (Con x)) (Identity (Con y))) = Identity (Con (x * y))
  ConstantFold $ Identity x = Identity x

instance ConstantFold `At` Decl Identity Identity where
  ConstantFold $ Identity x = Identity x
~~~

This transformation has to work bottom-up, so we declare

~~~ {.haskell}
instance Full.Functor ConstantFold Decl where
  (<$>) = Full.mapUpDefault

instance Full.Functor ConstantFold Expr where
  (<$>) = Full.mapUpDefault
~~~

Let's build a declaration to test.

~~~ {.haskell}
d1 :: Decl Identity Identity
d1 = "y" := Identity (bin Add (bin Mul (Con 42) (Con 68)) (Con 7))
~~~

As we're keeping the tree this time, instead of `Deep.foldMap` we can use `Deep.fmap`:

~~~ {.haskell}
-- |
-- >>> Deep.fmap ConstantFold d1
-- "y" := Identity (Con 2863)
~~~

Attribute Grammars
------------------

All right, can we do something more complicated? How about inlining all constant let bindings? And while we're at it,
 removing all unused declarations - also known as dead code elimination?

When it comes to complex transformations like this, the best tool in compiler writer's belt is an attribute
 grammar. We can build one with the tools from
 [`Transformation.AG`](https://hackage.haskell.org/package/deep-transformations/docs/Transformation-AG.html).

First we declare another transformation, just like before. Its `Codomain` will now be something called the attribute
 grammar semantics, and it performs bottom-up.

~~~ {.haskell}
data DeadCodeEliminator = DeadCodeEliminator

type Sem = AG.Semantics DeadCodeEliminator

instance Transformation DeadCodeEliminator where
   type Domain DeadCodeEliminator = Identity
   type Codomain DeadCodeEliminator = AG.Semantics DeadCodeEliminator

instance Full.Functor DeadCodeEliminator Decl where
  (<$>) = AG.fullMapDefault runIdentity

instance Full.Functor DeadCodeEliminator Expr where
  (<$>) = AG.fullMapDefault runIdentity
~~~

We also need another bit of a boilerplate instance that can be automatically generated with Template Haskell functions
 from [`Rank2.TH`](https://hackage.haskell.org/package/rank2classes/docs/Rank2-TH.html):

~~~ {.haskell}
instance Rank2.Apply (Decl f') where
  (v := e1) <*> ~(_ := e2) = v := (Rank2.apply e1 e2)
  Seq x1 y1 <*> ~(Seq x2 y2) = Seq (Rank2.apply x1 x2) (Rank2.apply y1 y2)

instance Rank2.Apply (Expr f') where
  Con n <*> _  = Con n
  EVar v <*> _ = EVar v
  Let d1 e1 <*> ~(Let d2 e2) = Let (Rank2.apply d1 d2) (Rank2.apply e1 e2)
  Add x1 y1 <*> ~(Add x2 y2) = Add (Rank2.apply x1 x2) (Rank2.apply y1 y2)
  Mul x1 y1 <*> ~(Mul x2 y2) = Mul (Rank2.apply x1 x2) (Rank2.apply y1 y2)
~~~

### Attributes

Every type of node can have different inherited and synthesized attributes, so we need to declare what they are. Since
 we want to inline the constant bindings declared in outer scopes, we must keep track of all visible bindings. This
 kind of *environment* is a typical example of an inherited attribute. It is also the only attribute inherited by an
 expression.

~~~ {.haskell}
type Env = Var -> Maybe (Expr Identity Identity)
type instance AG.Atts (AG.Inherited DeadCodeEliminator) (Expr _ _) = Env
~~~

A declaration will also need to inherit the environment, if only to pass it on to the nested expressions. Because we
 want to discard useless assignments, it will also need to know the list of all referenced variables.

~~~ {.haskell}
type instance AG.Atts (AG.Inherited DeadCodeEliminator) (Decl _ _) = (Env, [Var])
~~~

A `Decl` needs to synthesize the environment of constant bindings it generates itself, as well as a modified
 declaration without useless assignments. To cover the case where the whole of synthesized declaration is useless, we
 need to wrap it in a `Maybe`.

~~~ {.haskell}
type instance AG.Atts (AG.Synthesized DeadCodeEliminator) (Decl _ _) = (Env, Maybe (Decl Identity Identity))
~~~

All declarations inside an `Expr` need to be trimmed, so the `Expr` itself may be simplified but never completely
 eliminated. The simplified exression is our one synthesized attribute. The only other thing we need to know about an
 `Expr` is the list of variables it uses. We *could* make the used variable list its synthesized attribute, but it's
 easier to reuse the existing `GetVariables` transformation.

~~~ {.haskell}
type instance AG.Atts (AG.Synthesized DeadCodeEliminator) (Expr _ _) = Expr Identity Identity
~~~

Now we need to describe how to calculate the attributes, by declaring `Attribution` instances of the node types. The
 method `attribution` takes as arguments: the transformation - in this case `DeadCodeEliminator`, the node, the node's
 inherited attributes, and the synthesized attributes of all the node's children grouped under the node
 constructor. The last two inputs are grouped in a pair for symmetry with the function result, which is a pair of the
 node's synthesized attributes and the inherited attributes for all the node's children grouped under the node
 constructor. Perhaps this can be more succintly illustrated by the method's type signature:

~~~ {.haskell.ignore}
class Attribution t g deep shallow where
   attribution :: sem ~ (Inherited t Rank2.~> Synthesized t)
               => t -> shallow (g deep deep)
               -> (Inherited   t (g sem sem), g sem (Synthesized t))
               -> (Synthesized t (g sem sem), g sem (Inherited t))
~~~

### Expression rules

Let's see a few simple `attribution` rules first. The rules for leaf nodes can ignore their childrens' attributes
because they don't have any children.

~~~ {.haskell}
instance AG.Attribution DeadCodeEliminator Expr Identity Identity where
  attribution DeadCodeEliminator (Identity e@(EVar v)) (AG.Inherited env, _) = (AG.Synthesized (maybe e id $ env v), EVar v)
  attribution DeadCodeEliminator (Identity e@(Con n)) (AG.Inherited env, _) = (AG.Synthesized e, Con n)
~~~

The `Add` and `Mul` nodes' rules need only to pass their inheritance down and to re-join the synthesized child expressions.

~~~ {.haskell}
  attribution DeadCodeEliminator (Identity Add{}) (inh, (Add (AG.Synthesized e1') (AG.Synthesized e2'))) =
    (AG.Synthesized (bin Add e1' e2'),
     Add inh inh)
  attribution DeadCodeEliminator (Identity Mul{}) (inh, Mul (AG.Synthesized e1') (AG.Synthesized e2')) =
    (AG.Synthesized (bin Mul e1' e2'),
     Mul inh inh)
~~~

The only non-trivial rule is for the `Let` node. It needs to pass the list of variables used in its expression child
 as an inherited attribute of its declaration child. Furthermore, in case its declaration is useless the `Let` node
 should disappear from the synthesized expression.

~~~ {.haskell}
  attribution DeadCodeEliminator (Identity (Let _decl expr))
              (AG.Inherited env, (Let (AG.Synthesized ~(env', decl')) (AG.Synthesized expr'))) =
    (AG.Synthesized (maybe id (bin Let) decl' expr'),
     Let (AG.Inherited (env, Full.foldMap GetVariables expr)) (AG.Inherited $ \v-> maybe (env v) Just (env' v)))
~~~

### Declaration rules

The rules for `Decl` are a bit more involved.

~~~ {.haskell}
instance AG.Attribution DeadCodeEliminator Decl Identity Identity where
~~~

A single variable binding can be in three distinct situations. If the variable is not referenced at all, we can just
erase the declaration. If the variable is referenced but the value assigned to it is constant, we can again erase the
declaration and store the constant binding in the environment instead. Finally, if nothing else works we must preserve
the declaration.

~~~ {.haskell}
  attribution DeadCodeEliminator (Identity (v := e)) (AG.Inherited ~(env, used), (_ := AG.Synthesized e')) =
    (AG.Synthesized (if null (Deep.foldMap GetVariables e')
                     then (\var-> if var == v then Just e' else Nothing, Nothing)  -- constant binding
                     else (const Nothing, if v `elem` used
                                          then Just (v := Identity e')             -- used binding
                                          else Nothing)),                          -- unused binding
     v := AG.Inherited env)
~~~

The rule for a sequence of declarations is much simpler: we only need to combine the two synthesized environments into
their union and to reconstruct the simplified sequence from its simplified children. Note that the sequence becomes
unnecessary if either of its children disappears.

~~~ {.haskell}
  attribution DeadCodeEliminator (Identity Seq{}) (inh, (Seq (AG.Synthesized (env1, d1')) (AG.Synthesized (env2, d2')))) =
    (AG.Synthesized (\v-> maybe (env2 v) Just (env1 v),
                     bin Seq <$> d1' <*> d2' <|> d1' <|> d2'),
     Seq inh inh)
~~~

### Test

Here is the attribute grammar finally in action:

~~~ {.haskell}
-- |
-- >>> let s = Full.fmap DeadCodeEliminator (Identity $ bin Let d1 e1) `Rank2.apply` AG.Inherited (const Nothing)
-- >>> s
-- Synthesized {syn = Add (Identity (Con 42)) (Identity (Add (Identity (Mul (Identity (Con 42)) (Identity (Con 68)))) (Identity (Con 7))))}
-- >>> Full.fmap ConstantFold $ Identity $ AG.syn s
-- Identity (Con 2905)
~~~

~~~ {.haskell}
main = print $ Full.fmap ConstantFold $ Identity $ AG.syn
     $ Full.fmap DeadCodeEliminator (Identity $ bin Let d1 e1) Rank2.$ AG.Inherited (const Nothing)
~~~
