-- | This module exports the templates for automatic instance deriving of "Transformation.Shallow" type classes. The most
-- common way to use it would be
--
-- > import qualified Transformation.Shallow.TH
-- > data MyDataType f' f = ...
-- > $(Transformation.Shallow.TH.deriveFunctor ''MyDataType)
--

{-# Language TemplateHaskell #-}
-- Adapted from https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial

module Transformation.Shallow.TH (deriveAll, deriveFunctor, deriveTraversable)
where

import Control.Applicative (liftA2)
import Control.Monad (replicateM)
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (BangType, VarBangType, getQ, putQ)

import qualified Transformation
import qualified Transformation.Shallow
import qualified Rank2.TH


data Deriving = Deriving { _constructor :: Name, _variable :: Name }

deriveAll :: Name -> Q [Dec]
deriveAll ty = foldr f (pure []) [Transformation.Shallow.TH.deriveFunctor, Transformation.Shallow.TH.deriveTraversable]
   where f derive rest = (<>) <$> derive ty <*> rest

deriveFunctor :: Name -> Q [Dec]
deriveFunctor ty = do
   t <- varT <$> newName "t"
   (instanceType, cs) <- reifyConstructors ty
   let shallowConstraint ty = conT ''Transformation.Shallow.Functor `appT` t `appT` ty
       baseConstraint ty = conT ''Transformation.Functor `appT` t `appT` ty
   (constraints, dec) <- genShallowmap shallowConstraint baseConstraint instanceType cs
   sequence [instanceD (cxt $ appT (conT ''Transformation.Transformation) t : map pure constraints)
                       (shallowConstraint instanceType)
                       [pure dec]]

deriveTraversable :: Name -> Q [Dec]
deriveTraversable ty = do
   t <- varT <$> newName "t"
   (instanceType, cs) <- reifyConstructors ty
   let shallowConstraint ty = conT ''Transformation.Shallow.Traversable `appT` t `appT` ty
       baseConstraint ty = conT ''Transformation.Traversable `appT` t `appT` ty
   (constraints, dec) <- genTraverse shallowConstraint baseConstraint instanceType cs
   sequence [instanceD (cxt (appT (conT ''Transformation.TraversableTransformation) t :
                             appT (conT ''Monad) (appT (conT ''Transformation.Algebra) t) : map pure constraints))
                       (shallowConstraint instanceType)
                       [pure dec]]

substitute :: Type -> Q Type -> Q Type -> Q Type
substitute resultType = liftA2 substitute'
   where substitute' instanceType argumentType =
            substituteVars (substitutions resultType instanceType) argumentType
         substitutions (AppT t1 (VarT name1)) (AppT t2 (VarT name2)) = (name1, name2) : substitutions t1 t2
         substitutions _t1 _t2 = []
         substituteVars subs (VarT name) = VarT (fromMaybe name $ lookup name subs)
         substituteVars subs (AppT t1 t2) = AppT (substituteVars subs t1) (substituteVars subs t2)
         substituteVars _ t = t

reifyConstructors :: Name -> Q (TypeQ, [Con])
reifyConstructors ty = do
   (TyConI tyCon) <- reify ty
   (tyConName, tyVars, _kind, cs) <- case tyCon of
      DataD _ nm tyVars kind cs _   -> return (nm, tyVars, kind, cs)
      NewtypeD _ nm tyVars kind c _ -> return (nm, tyVars, kind, [c])
      _ -> fail "deriveApply: tyCon may not be a type synonym."

   let (KindedTV tyVar  (AppT (AppT ArrowT StarT) StarT) : _) = reverse tyVars
       instanceType           = foldl apply (conT tyConName) (reverse $ drop 1 $ reverse tyVars)
       apply t (PlainTV name)    = appT t (varT name)
       apply t (KindedTV name _) = appT t (varT name)

   putQ (Deriving tyConName tyVar)
   return (instanceType, cs)

genShallowmap :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> [Con] -> Q ([Type], Dec)
genShallowmap shallowConstraint baseConstraint instanceType cs = do
   (constraints, clauses) <- unzip <$> mapM (genShallowmapClause shallowConstraint baseConstraint instanceType) cs
   return (concat constraints, FunD '(Transformation.Shallow.<$>) clauses)

genTraverse :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> [Con] -> Q ([Type], Dec)
genTraverse shallowConstraint baseConstraint instanceType cs = do
   (constraints, clauses) <- unzip
     <$> mapM (genTraverseClause genTraverseField shallowConstraint baseConstraint instanceType) cs
   return (concat constraints, FunD 'Transformation.Shallow.traverse clauses)

genShallowmapClause :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> Con -> Q ([Type], Clause)
genShallowmapClause shallowConstraint baseConstraint instanceType (NormalC name fieldTypes) = do
   t          <- newName "t"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP t, parensP (conP name $ map varP fieldNames)]
       constraintsAndFields = zipWith newField fieldNames fieldTypes
       newFields = map (snd <$>) constraintsAndFields
       body = normalB $ appsE $ conE name : newFields
       newField :: Name -> BangType -> Q ([Type], Exp)
       newField x (_, fieldType) = genShallowmapField (varE t) fieldType shallowConstraint baseConstraint (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause pats body []
genShallowmapClause shallowConstraint baseConstraint instanceType (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newNamedField fields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>)
          <$> genShallowmapField (varE f) fieldType shallowConstraint baseConstraint (appE (varE fieldName) (varE x)) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP f, varP x] body []
genShallowmapClause shallowConstraint baseConstraint instanceType
                 (GadtC [name] fieldTypes (AppT (AppT resultType (VarT tyVar')) (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genShallowmapClause (shallowConstraint . substitute resultType instanceType)
                       (baseConstraint . substitute resultType instanceType)
                       instanceType (NormalC name fieldTypes)
genShallowmapClause shallowConstraint baseConstraint instanceType
                 (RecGadtC [name] fields (AppT (AppT resultType (VarT tyVar')) (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genShallowmapClause (shallowConstraint . substitute resultType instanceType)
                       (baseConstraint . substitute resultType instanceType)
                       instanceType (RecC name fields)
genShallowmapClause shallowConstraint baseConstraint instanceType (ForallC _vars _cxt con) =
   genShallowmapClause shallowConstraint baseConstraint instanceType con

type GenTraverseFieldType = Q Exp -> Type -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Exp -> (Q Exp -> Q Exp)
                            -> Q ([Type], Exp)

genTraverseClause :: GenTraverseFieldType -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> Con
                  -> Q ([Type], Clause)
genTraverseClause genTraverseField shallowConstraint baseConstraint instanceType (NormalC name fieldTypes) = do
   t          <- newName "t"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP t, parensP (conP name $ map varP fieldNames)]
       constraintsAndFields = zipWith newField fieldNames fieldTypes
       newFields = map (snd <$>) constraintsAndFields
       body | null fieldTypes = [| pure $(conE name) |]
            | otherwise = fst $ foldl apply (conE name, False) newFields
       apply (a, False) b = ([| $(a) <$> $(b) |], True)
       apply (a, True) b = ([| $(a) <*> $(b) |], True)
       newField :: Name -> BangType -> Q ([Type], Exp)
       newField x (_, fieldType) = genTraverseField (varE t) fieldType shallowConstraint baseConstraint (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause pats (normalB body) []
genTraverseClause genTraverseField shallowConstraint baseConstraint instanceType (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let constraintsAndFields = map newNamedField fields
       body | null fields = [| pure $(conE name) |]
            | otherwise = fst (foldl apply (conE name, False) $ map (snd . snd <$>) constraintsAndFields)
       apply (a, False) b = ([| $(a) <$> $(b) |], True)
       apply (a, True) b = ([| $(a) <*> $(b) |], True)
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>)
          <$> genTraverseField (varE f) fieldType shallowConstraint baseConstraint (appE (varE fieldName) (varE x)) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP f, varP x] (normalB body) []
genTraverseClause genTraverseField shallowConstraint baseConstraint instanceType
                  (GadtC [name] fieldTypes (AppT (AppT resultType (VarT tyVar')) (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genTraverseClause genTraverseField
        (shallowConstraint . substitute resultType instanceType)
        (baseConstraint . substitute resultType instanceType)
        instanceType (NormalC name fieldTypes)
genTraverseClause genTraverseField shallowConstraint baseConstraint instanceType
                  (RecGadtC [name] fields (AppT (AppT resultType (VarT tyVar')) (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genTraverseClause genTraverseField
                        (shallowConstraint . substitute resultType instanceType)
                        (baseConstraint . substitute resultType instanceType)
                        instanceType (RecC name fields)
genTraverseClause genTraverseField shallowConstraint baseConstraint instanceType (ForallC _vars _cxt con) =
   genTraverseClause genTraverseField shallowConstraint baseConstraint instanceType con

genShallowmapField :: Q Exp -> Type -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Exp -> (Q Exp -> Q Exp)
                -> Q ([Type], Exp)
genShallowmapField trans fieldType shallowConstraint baseConstraint fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty a | ty == VarT typeVar ->
        (,) <$> ((:[]) <$> baseConstraint (pure a))
            <*> (wrap (varE 'Transformation.fmap `appE` trans) `appE` fieldAccess)
     AppT t1 t2 | t1 /= VarT typeVar ->
        genShallowmapField trans t2 shallowConstraint baseConstraint fieldAccess (wrap . appE (varE '(<$>)))
     SigT ty _kind -> genShallowmapField trans ty shallowConstraint baseConstraint fieldAccess wrap
     ParensT ty -> genShallowmapField trans ty shallowConstraint baseConstraint fieldAccess wrap
     _ -> (,) [] <$> fieldAccess

genTraverseField :: GenTraverseFieldType
genTraverseField trans fieldType shallowConstraint baseConstraint fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty a  | ty == VarT typeVar ->
        (,) <$> ((:[]) <$> baseConstraint (pure a))
            <*> (wrap (varE 'Transformation.traverse `appE` trans) `appE` fieldAccess)
     AppT t1 t2 | t1 /= VarT typeVar ->
        genTraverseField trans t2 shallowConstraint baseConstraint fieldAccess (wrap . appE (varE 'traverse))
     SigT ty _kind -> genTraverseField trans ty shallowConstraint baseConstraint fieldAccess wrap
     ParensT ty -> genTraverseField trans ty shallowConstraint baseConstraint fieldAccess wrap
     _ -> (,) [] <$> [| pure $fieldAccess |]
