An abstract syntax tree of a realistic programming language will generally contain more than one node type. In other
 words, its type will involve several mutually recursive data types: the usual suspects would be expression,
 declaration, type, statement, and module.

This library, `deep-transformations`, provides a solution to the problem of traversing and transforming such
 heterogenous trees. It is not the only solution by far. The venerable
 [`multiplate`](http://hackage.haskell.org/package/multiplate) has long offered a very approachable way to traverse and
 fold heterogenous trees, without even depending on any extension to standard Haskell. Multiplate is not as expressive
 as the present library, but if it satisfies your needs go with it. If not, be aware that `deep-transformations` relies
 on quite a number of extensions:

> {-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses,
>              StandaloneDeriving, TypeFamilies, TypeOperators #-}

It will also require several imports.

> import Control.Applicative
> import Data.Coerce (coerce)
> import Data.Functor.Const
> import Data.Functor.Identity
> import qualified Rank2
> import Transformation (Transformation, At)
> import qualified Transformation
> import qualified Transformation.AG as AG
> import qualified Transformation.Deep as Deep
> import qualified Transformation.Full as Full
> import qualified Transformation.Shallow as Shallow

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

> data Expr d s = Con Int
>               | Add (s (Expr d d)) (s (Expr d d))
>               | Mul (s (Expr d d)) (s (Expr d d))
>               | EVar Var
>               | Let (s (Decl d d)) (s (Expr d d))
> 
> data Decl d s = Var := s (Expr d d)
>               | Seq (s (Decl d d)) (s (Decl d d))
> 
> type Var = String

The parameters `d` and `s` stand for the *deep* and *shallow* type constructor. A typical occurrence of the tree will
 instantiate the same type for both parameters. While it may look ugly and annoying, this kind of parameterization
 carries benefits beyond this library's use. The parameters may vary from `Identity`, equivalent to the original
 simple formulation, via `(,) LexicalInfo` to store the source code position and white-space and comments for every
 node, or `[]` if you need some ambiguity, to attribute grammar semantics.

Now, let's declare all the class instances. First make the tree `Show`.

> deriving instance (Show (f (Expr f' f')), Show (f (Decl f' f'))) => Show (Expr f' f)
> deriving instance (Show (f (Expr f' f')), Show (f (Decl f' f'))) => Show (Decl f' f)

The shallow parameter comes last so that every data type can have instances of
 [`rank2classes`](https://hackage.haskell.org/package/rank2classes). The instances below are written manually, but
 they can be generated automatically using the Template Haskell imports from
 [`Rank2.TH`](https://hackage.haskell.org/package/rank2classes/docs/Rank2-TH.html).

> instance Rank2.Functor (Decl f') where
>   f <$> (v := e) = (v := f e)
>   f <$> Seq x y  = Seq (f x) (f y)
> 
> instance Rank2.Functor (Expr f') where
>   f <$> Con n   = Con n
>   f <$> Add x y = Add (f x) (f y)
>   f <$> Mul x y = Mul (f x) (f y)
>   f <$> Let d e = Let (f d) (f e)
>   f <$> EVar v  = EVar v
> 
> instance Rank2.Foldable (Decl f') where
>   f `foldMap` (v := e) = f e
>   f `foldMap` Seq x y  = f x <> f y
> 
> instance Rank2.Foldable (Expr f') where
>   f `foldMap` Con n   = mempty
>   f `foldMap` Add x y = f x <> f y
>   f `foldMap` Mul x y = f x <> f y
>   f `foldMap` Let d e = f d <> f e
>   f `foldMap` EVar v  = mempty

While the methods declared above can be handy, they are limited in requiring that the function argument `f` must be
 polymorphic in the wrapped field type. In other words, it cannot behave one way for an `Expr` and another for a
 `Decl`. That can be a severe handicap.

The class methods exported by `deep-transformations` therefore work not with polymorphic functions but with
 *tranformations*. The instances of these classes are similar to the instances above. Also as above, they can be
 generated automatically with Template Haskell functions from
 [`Transformation.Deep.TH`](https://hackage.haskell.org/package/deep-transformations/docs/Transformation-Deep-TH.html).

> instance (Transformation t, Full.Functor t Decl, Full.Functor t Expr) => Deep.Functor t Decl where
>   t <$> (v := e)   = (v := (t Full.<$> e))
>   t <$> Seq x y = Seq (t Full.<$> x) (t Full.<$> y)
> 
> instance (Transformation t, Full.Functor t Decl, Full.Functor t Expr) => Deep.Functor t Expr where
>   t <$> Con n   = Con n
>   t <$> Add x y = Add (t Full.<$> x) (t Full.<$> y)
>   t <$> Mul x y = Mul (t Full.<$> x) (t Full.<$> y)
>   t <$> Let d e = Let (t Full.<$> d) (t Full.<$> e)
>   t <$> EVar v  = EVar v
>
> instance (Transformation t, Full.Foldable t Decl, Full.Foldable t Expr) => Deep.Foldable t Decl where
>   t `foldMap` (v := e) = t `Full.foldMap` e
>   t `foldMap` Seq x y  = t `Full.foldMap` x <> t `Full.foldMap` y
> 
> instance (Transformation t, Full.Foldable t Decl, Full.Foldable t Expr) => Deep.Foldable t Expr where
>   t `foldMap` Con n   = mempty
>   t `foldMap` Add x y = t `Full.foldMap` x <> t `Full.foldMap` y
>   t `foldMap` Mul x y = t `Full.foldMap` x <> t `Full.foldMap` y
>   t `foldMap` Let d e = t `Full.foldMap` d <> t `Full.foldMap` e
>   t `foldMap` EVar v  = mempty

instance (Full.Traversable t Decl, Full.Traversable t Expr) => Deep.Traversable t Decl where
  t `traverse` (v := e)   = (v := (t `Full.traverse` e))
  t `traverse` Seq x y = Seq (t `Full.traverse` x) (t `Full.traverse` y)

instance (Full.Traversable t Decl, Full.Traversable t Expr) => Deep.Traversable t Expr where
  t `traverse` Con n   = pure (Con n)
  t `traverse` Add x y = Add <$> t `Full.traverse` x <*> t `Full.traverse` y
  t `traverse` Mul x y = Mul <$> t `Full.traverse` x <*> t `Full.traverse` y
  t `traverse` Let d e = Let <$> t `Full.traverse` d <*> t `Full.traverse` e
  t `traverse` EVar v  = pure (EVar v)

Once the above boilerplate code is written or generated, no further boilerplate code need be written.

Generic Programing with deep-transformations
============================================

Folding
-------

Suppose we we want to get a list of all variables used in an expression. To do this we would decalre the appropriate
 [`Transformation`](https://hackage.haskell.org/package/deep-transformations/docs/Transformation.html) instance for an
 arbitrary data type. We'll give this data type an evocative name.

> data GetVariables = GetVariables
>
> instance Transformation GetVariables where
>   type Domain GetVariables = Identity
>   type Codomain GetVariables = Const [Var]

The `Transformation` instance for `GetVariables` converts the `Identity` wrapper of a given node into a constant list
 of variables contained within it. To do that, it must behave differently for `Expr` and for `Decl`:

> instance GetVariables `At` Expr Identity Identity where
>   GetVariables $ Identity (EVar v) = Const [v]
>   GetVariables $ x = mempty
>
> instance GetVariables `At` Decl Identity Identity where
>   GetVariables $ x = mempty

There is one last decision to make on our transformation: is it a pre-order or a post-order fold? In this case it
 doesn't matter, so let's pick pre-order:

> instance Full.Foldable GetVariables Decl where
>   foldMap = Full.foldMapDownDefault
> 
> instance Full.Foldable GetVariables Expr where
>   foldMap = Full.foldMapDownDefault

Now the transformation is ready. We'll try it on this example:

> e1 :: Expr Identity Identity
> e1 = Let (Identity $ "x" := Identity (Con 42)) (Identity $ Add (Identity $ EVar "x") (Identity $ EVar "x"))

Traversing
----------

Suppose we want to recursively evaluate constant expressions in the language. We define another data type with a
 `Transformation` instance for the purpose. This time `Domain` and `Codomain` are both `Identity`, since the
 simplification doesn't change the tree type.

> data ConstantFold = ConstantFold
> 
> instance Transformation ConstantFold where
>   type Domain ConstantFold = Identity
>   type Codomain ConstantFold = Identity
>
> instance ConstantFold `At` Expr Identity Identity where
>   ConstantFold $ Identity (Add (Identity (Con x)) (Identity (Con y))) = Identity (Con (x + y))
>   ConstantFold $ Identity (Mul (Identity (Con x)) (Identity (Con y))) = Identity (Con (x * y))
>   ConstantFold $ Identity x = Identity x
>
> instance ConstantFold `At` Decl Identity Identity where
>   ConstantFold $ Identity x = Identity x

This transformation has to work bottom-up, so we declare

> instance Full.Functor ConstantFold Decl where
>   (<$>) = Full.mapUpDefault
> 
> instance Full.Functor ConstantFold Expr where
>   (<$>) = Full.mapUpDefault

Let's build a declaration to test.

> d1 :: Decl Identity Identity
> d1 = "x" := Identity (Add (Identity $ Mul (Identity $ Con 42) (Identity $ Con 68)) (Identity $ Con 7))

Attribute Grammars
------------------

Shall we eliminate dead code, /i.e./, useless let assignments from a given expression? This is tougher than the
 previous examples. We have to first fold the body of each `Let` expression to find which variables it uses, then
 traverse its declaration and eliminate the useless ones. When it comes to situations like this, the best tool in
 compiler writer's belt is an attribute grammar. We can build one with the tools from
 [`Transformation.AG`](https://hackage.haskell.org/package/deep-transformations/docs/Transformation-AG.html).

First we declare another transformation, just like before. Its `Codomain` will now be something called the attribute
 grammar semantics, and it performs bottom-up.

> data DeadCodeEliminator = DeadCodeEliminator
>
> type Sem = AG.Semantics DeadCodeEliminator
>
> instance Transformation DeadCodeEliminator where
>    type Domain DeadCodeEliminator = Identity
>    type Codomain DeadCodeEliminator = AG.Semantics DeadCodeEliminator
>
> instance Full.Functor DeadCodeEliminator Decl where
>   (<$>) = AG.fullMapDefault runIdentity
> 
> instance Full.Functor DeadCodeEliminator Expr where
>   (<$>) = AG.fullMapDefault runIdentity

We also need another bit of a boilerplate instance that can be generated

> instance Rank2.Apply (Decl f') where
>   (v := e1) <*> (_ := e2) = v := (Rank2.apply e1 e2)
>   Seq x1 y1 <*> Seq x2 y2 = Seq (Rank2.apply x1 x2) (Rank2.apply y1 y2)
> 
> instance Rank2.Apply (Expr f') where
>   Con n <*> _  = Con n
>   EVar v <*> _ = EVar v
>   Let d1 e1 <*> Let d2 e2 = Let (Rank2.apply d1 d2) (Rank2.apply e1 e2)
>   Add x1 y1 <*> Add x2 y2 = Add (Rank2.apply x1 x2) (Rank2.apply y1 y2)
>   Mul x1 y1 <*> Mul x2 y2 = Mul (Rank2.apply x1 x2) (Rank2.apply y1 y2)
>

instance Transformation t => Shallow.Foldable t (Expr d) where
  t `foldMap` Con n   = mempty
  t `foldMap` Add x y = t Transformation.$ x <> t Transformation.$ y
  t `foldMap` Mul x y = t Transformation.$ x <> t Transformation.$ y
  t `foldMap` Let d e = t Transformation.$ d <> t Transformation.$ e
  t `foldMap` EVar v  = mempty

instance (Transformation t, Full.Functor t Decl, Full.Functor t Expr) => Deeper.Functor t Decl where
  t <$> (v := e) = v := ((t Deep.<$>) <$> e)
  t <$> Seq x y  = Seq ((t Deep.<$>) <$> x) ((t Deep.<$>) <$> y)

instance (Transformation t, Full.Functor t Decl, Full.Functor t Expr) => Deeper.Functor t Expr where
  t <$> Con n   = Con n
  t <$> Add x y = Add ((t Deep.<$>) <$> x) ((t Deep.<$>) <$> y)
  t <$> Mul x y = Mul ((t Deep.<$>) <$> x) ((t Deep.<$>) <$> y)
  t <$> Let d e = Let ((t Deep.<$>) <$> d) ((t Deep.<$>) <$> e)
  t <$> EVar v  = EVar v

data FromSem t = FromSem

instance Transformation (FromSem t) where
  type Domain (FromSem t) = AG.Semantics t
  type Codomain (FromSem t) = AG.Synthesized t

instance FromSem t `Deeper.Functor` Expr where
  t <$> e = coerce e

data FromSyn t (f :: * -> *) = FromSyn

instance Transformation (FromSyn t f) where
  type Domain (FromSyn t f) = AG.Synthesized t
  type Codomain (FromSyn t f) = f

instance FromSyn DeadCodeEliminator Identity `Full.Functor` Expr where
  _ <$> AG.Synthesized e = Identity e

instance FromSyn DeadCodeEliminator Identity `Full.Functor` Decl where
  _ <$> AG.Synthesized (Just d) = Identity d

instance DeadCodeEliminator `At` Expr (AG.Semantics DeadCodeEliminator) (AG.Semantics DeadCodeEliminator) where
  ($) = AG.applyDefault runIdentity
instance DeadCodeEliminator `At` Decl (AG.Semantics DeadCodeEliminator) (AG.Semantics DeadCodeEliminator) where
  ($) = AG.applyDefault runIdentity

Every type of node can have different inherited and synthesized attributes, so we need to declare what they are.
A `Decl` needs to synthesize a modified declaration without useless assignments, and to do that it must inherit the
 list of used variables. To cover the case where the whole of synthesized declaration is useless, we need to wrap it
 in a `Maybe`.

> type instance AG.Atts (AG.Inherited DeadCodeEliminator) (Decl _ _) = [Var]
> type instance AG.Atts (AG.Synthesized DeadCodeEliminator) (Decl _ _) = Maybe (Decl Identity Identity)

All declarations inside an `Expr` need to be trimmed, so the `Expr` itself may be simplified but never completely
 eliminated. The simplified exression is our one synthesized attribute. The only other thing we need to know about an
 `Expr` is the list of variables it uses. It won't need any inherited attributes to tell us that. We *could* make the
 used variable list its synththesized attribute, but it's easier to reuse the existing `GetVariables`
 transformation.

> type instance AG.Atts (AG.Inherited DeadCodeEliminator) (Expr _ _) = ()
> type instance AG.Atts (AG.Synthesized DeadCodeEliminator) (Expr _ _) = Expr Identity Identity

Now we need to describe how to calculate the attributes, by declaring `Attribution` instances of the node types.

> instance AG.Attribution DeadCodeEliminator Expr Identity Identity where
>   bequest DeadCodeEliminator (Identity (Let decl expr)) _ _ = Let (AG.Inherited $ Deep.foldMap GetVariables $ runIdentity expr) (AG.Inherited ())
>   bequest DeadCodeEliminator _expr _inh _syn = error "no inheritance to bequest"
>   synthesis _ (Identity Let{}) () (Let (AG.Synthesized decl) (AG.Synthesized expr)) = case decl of
>     Just d -> Let (Identity d) (Identity expr)
>     Nothing -> expr
>   synthesis _ _ () (Add (AG.Synthesized e1) (AG.Synthesized e2)) = Add (Identity e1) (Identity e2)
>   synthesis _ _ () (Mul (AG.Synthesized e1) (AG.Synthesized e2)) = Mul (Identity e1) (Identity e2)
>   synthesis _ _ () (EVar v) = EVar v
>   synthesis _ _ () (Con n) = Con n
> 
> instance AG.Attribution DeadCodeEliminator Decl Identity Identity where
>   bequest _ (Identity (v := e)) _ _ = v := AG.Inherited ()
>   bequest _ (Identity (Seq d1 d2)) used _ = Seq (AG.Inherited used) (AG.Inherited used)
>   synthesis _ (Identity (_ := _)) used (v := AG.Synthesized e)
>     | v `elem` used = Just (v := Identity e)
>     | otherwise = Nothing
>   synthesis _ (Identity Seq{}) used (Seq (AG.Synthesized d1') (AG.Synthesized d2')) =
>     Seq <$> (Identity <$> d1') <*> (Identity <$> d2') <|> d1' <|> d2'


> main = do
>  print (Deep.foldMap GetVariables e1)
>  print (Deep.fmap ConstantFold d1)
>  print (Full.fmap DeadCodeEliminator (Identity $ Let (Identity d1) (Identity $ Con 42)) `Rank2.apply` AG.Inherited ())

["x","x"]
"x" := Identity (Con 2863)
