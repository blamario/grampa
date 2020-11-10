-- | This module exports the templates for automatic instance deriving of "Transformation.Full" type classes. The most
-- common way to use it would be
--
-- > import qualified Transformation.Full.TH
-- > data MyDataType f' f = ...
-- > $(Transformation.Full.TH.deriveUpFunctor (conT ''MyTransformation) (conT ''MyDataType))
--

{-# Language TemplateHaskell #-}

module Transformation.Full.TH (deriveDownFunctor, deriveDownFoldable, deriveDownTraversable,
                               deriveUpFunctor, deriveUpFoldable, deriveUpTraversable)
where

import Language.Haskell.TH

import qualified Transformation
import qualified Transformation.Deep
import qualified Transformation.Full

deriveDownFunctor :: Q Type -> Q Type -> Q [Dec]
deriveDownFunctor transformation node = do
   let domain = conT ''Transformation.Domain `appT` transformation
       deepConstraint = conT ''Transformation.Deep.Functor `appT` transformation `appT` node
       fullConstraint = conT ''Transformation.Full.Functor `appT` transformation `appT` node
       shallowConstraint = conT ''Transformation.At `appT` transformation `appT` (node `appT` domain `appT` domain)
   sequence [instanceD (cxt [deepConstraint, shallowConstraint])
             fullConstraint
             [funD '(Transformation.Full.<$>) [clause [] (normalB $ varE 'Transformation.Full.mapDownDefault) []]]]

deriveUpFunctor :: Q Type -> Q Type -> Q [Dec]
deriveUpFunctor transformation node = do
   let codomain = conT ''Transformation.Codomain `appT` transformation
       deepConstraint = conT ''Transformation.Deep.Functor `appT` transformation `appT` node
       fullConstraint = conT ''Transformation.Full.Functor `appT` transformation `appT` node
       shallowConstraint = conT ''Transformation.At `appT` transformation `appT` (node `appT` codomain `appT` codomain)
   sequence [instanceD (cxt [deepConstraint, shallowConstraint])
             fullConstraint
             [funD '(Transformation.Full.<$>) [clause [] (normalB $ varE 'Transformation.Full.mapUpDefault) []]]]

deriveDownFoldable :: Q Type -> Q Type -> Q [Dec]
deriveDownFoldable transformation node = do
   let domain = conT ''Transformation.Domain `appT` transformation
       deepConstraint = conT ''Transformation.Deep.Foldable `appT` transformation `appT` node
       fullConstraint = conT ''Transformation.Full.Foldable `appT` transformation `appT` node
       shallowConstraint = conT ''Transformation.At `appT` transformation `appT` (node `appT` domain `appT` domain)
   sequence [instanceD (cxt [deepConstraint, shallowConstraint])
             fullConstraint
             [funD 'Transformation.Full.foldMap [clause [] (normalB $ varE 'Transformation.Full.foldMapDownDefault) []]]]

deriveUpFoldable :: Q Type -> Q Type -> Q [Dec]
deriveUpFoldable transformation node = do
   let codomain = conT ''Transformation.Codomain `appT` transformation
       deepConstraint = conT ''Transformation.Deep.Foldable `appT` transformation `appT` node
       fullConstraint = conT ''Transformation.Full.Foldable `appT` transformation `appT` node
       shallowConstraint = conT ''Transformation.At `appT` transformation `appT` (node `appT` codomain `appT` codomain)
   sequence [instanceD (cxt [deepConstraint, shallowConstraint])
             fullConstraint
             [funD 'Transformation.Full.foldMap [clause [] (normalB $ varE 'Transformation.Full.foldMapUpDefault) []]]]

deriveDownTraversable :: Q Type -> Q Type -> Q [Dec]
deriveDownTraversable transformation node = do
   let domain = conT ''Transformation.Domain `appT` transformation
       deepConstraint = conT ''Transformation.Deep.Traversable `appT` transformation `appT` node
       fullConstraint = conT ''Transformation.Full.Traversable `appT` transformation `appT` node
       shallowConstraint = conT ''Transformation.At `appT` transformation `appT` (node `appT` domain `appT` domain)
   sequence [instanceD (cxt [deepConstraint, shallowConstraint])
             fullConstraint
             [funD 'Transformation.Full.traverse [clause [] (normalB $ varE 'Transformation.Full.traverseDownDefault) []]]]

deriveUpTraversable :: Q Type -> Q Type -> Q [Dec]
deriveUpTraversable transformation node = do
   let codomain = conT ''Transformation.Codomain `appT` transformation
       deepConstraint = conT ''Transformation.Deep.Traversable `appT` transformation `appT` node
       fullConstraint = conT ''Transformation.Full.Traversable `appT` transformation `appT` node
       shallowConstraint = conT ''Transformation.At `appT` transformation `appT` (node `appT` codomain `appT` codomain)
   sequence [instanceD (cxt [deepConstraint, shallowConstraint])
             fullConstraint
             [funD 'Transformation.Full.traverse [clause [] (normalB $ varE 'Transformation.Full.traverseUpDefault) []]]]
