-- | This module exports the templates for automatic instance deriving of "Transformation.Shallow" type classes. The most
-- common way to use it would be
--
-- > import qualified Transformation.Shallow.TH
-- > data MyDataType f' f = ...
-- > $(Transformation.Shallow.TH.deriveFunctor ''MyDataType)
--

{-# Language CPP, TemplateHaskell #-}
-- Adapted from https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial

module Transformation.Shallow.TH (deriveAll, deriveFunctor, deriveFoldable, deriveTraversable)
where

import Control.Applicative (liftA2)
import Control.Monad (replicateM)
import Data.Functor.Compose (Compose(getCompose))
import Data.Functor.Const (Const(getConst))
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid, (<>))
import Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax (BangType, VarBangType, getQ, putQ)

import qualified Transformation
import qualified Transformation.Shallow


data Deriving = Deriving { _constructor :: Name, _variable :: Name }

deriveAll :: Name -> Q [Dec]
deriveAll ty = foldr f (pure []) [deriveFunctor, deriveFoldable, deriveTraversable]
   where f derive rest = (<>) <$> derive ty <*> rest

deriveFunctor :: Name -> Q [Dec]
deriveFunctor typeName = do
   t <- varT <$> newName "t"
   (instanceType, cs) <- reifyConstructors typeName
   let shallowConstraint ty = conT ''Transformation.Shallow.Functor `appT` t `appT` ty
       baseConstraint ty = conT ''Transformation.At `appT` t `appT` ty
   (constraints, dec) <- genShallowmap shallowConstraint baseConstraint instanceType cs
   sequence [instanceD (cxt $ appT (conT ''Transformation.Transformation) t : map pure constraints)
                       (shallowConstraint instanceType)
                       [pure dec]]

deriveFoldable :: Name -> Q [Dec]
deriveFoldable typeName = do
   t <- varT <$> newName "t"
   m <- varT <$> newName "m"
   (instanceType, cs) <- reifyConstructors typeName
   let shallowConstraint ty = conT ''Transformation.Shallow.Foldable `appT` t `appT` ty
       baseConstraint ty = conT ''Transformation.At `appT` t `appT` ty
   (constraints, dec) <- genFoldMap shallowConstraint baseConstraint instanceType cs
   sequence [instanceD (cxt (appT (conT ''Transformation.Transformation) t :
                             appT (appT equalityT (conT ''Transformation.Codomain `appT` t))
                                  (conT ''Const `appT` m) :
                             appT (conT ''Monoid) m : map pure constraints))
                       (shallowConstraint instanceType)
                       [pure dec]]

deriveTraversable :: Name -> Q [Dec]
deriveTraversable typeName = do
   t <- varT <$> newName "t"
   m <- varT <$> newName "m"
   f <- varT <$> newName "f"
   (instanceType, cs) <- reifyConstructors typeName
   let shallowConstraint ty = conT ''Transformation.Shallow.Traversable `appT` t `appT` ty
       baseConstraint ty = conT ''Transformation.At `appT` t `appT` ty
   (constraints, dec) <- genTraverse shallowConstraint baseConstraint instanceType cs
   sequence [instanceD (cxt (appT (conT ''Transformation.Transformation) t :
                             appT (appT equalityT (conT ''Transformation.Codomain `appT` t))
                                  (conT ''Compose `appT` m `appT` f) :
                             appT (conT ''Applicative) m : map pure constraints))
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

   let reifySynonyms (ConT name) = TH.reify name >>= reifySynonymInfo name
       reifySynonyms (AppT t1 t2) = AppT <$> reifySynonyms t1 <*> reifySynonyms t2
       reifySynonyms t = pure t
       reifySynonymInfo _ (TyConI (TySynD _ [] t)) = reifySynonyms t
       reifySynonymInfo name _ = pure (ConT name)
#if MIN_VERSION_template_haskell(2,17,0)
       reifyTVKindSynonyms (KindedTV v s k) = KindedTV v s <$> reifySynonyms k
#else
       reifyTVKindSynonyms (KindedTV v k) = KindedTV v <$> reifySynonyms k
#endif
       reifyTVKindSynonyms tv = pure tv
   tyVars' <- traverse reifyTVKindSynonyms tyVars

#if MIN_VERSION_template_haskell(2,17,0)
   let (KindedTV tyVar _ (AppT (AppT ArrowT StarT) StarT) : _) = reverse tyVars'
       instanceType           = foldl apply (conT tyConName) (reverse $ drop 1 $ reverse tyVars')
       apply t (PlainTV name _)    = appT t (varT name)
       apply t (KindedTV name _ _) = appT t (varT name)
#else
   let (KindedTV tyVar  (AppT (AppT ArrowT StarT) StarT) : _) = reverse tyVars'
       instanceType           = foldl apply (conT tyConName) (reverse $ drop 1 $ reverse tyVars')
       apply t (PlainTV name)    = appT t (varT name)
       apply t (KindedTV name _) = appT t (varT name)
#endif

   putQ (Deriving tyConName tyVar)
   return (instanceType, cs)

genShallowmap :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> [Con] -> Q ([Type], Dec)
genShallowmap shallowConstraint baseConstraint instanceType cs = do
   (constraints, clauses) <- unzip <$> mapM (genShallowmapClause shallowConstraint baseConstraint instanceType) cs
   return (concat constraints, FunD '(Transformation.Shallow.<$>) clauses)

genFoldMap :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> [Con] -> Q ([Type], Dec)
genFoldMap shallowConstraint baseConstraint instanceType cs = do
   (constraints, clauses) <- unzip <$> mapM (genFoldMapClause shallowConstraint baseConstraint instanceType) cs
   return (concat constraints, FunD 'Transformation.Shallow.foldMap clauses)

genTraverse :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> [Con] -> Q ([Type], Dec)
genTraverse shallowConstraint baseConstraint instanceType cs = do
   (constraints, clauses) <- unzip
     <$> mapM (genTraverseClause genTraverseField shallowConstraint baseConstraint instanceType) cs
   return (concat constraints, FunD 'Transformation.Shallow.traverse clauses)

genShallowmapClause :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> Con -> Q ([Type], Clause)
genShallowmapClause shallowConstraint baseConstraint _instanceType (NormalC name fieldTypes) = do
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
genShallowmapClause shallowConstraint baseConstraint _instanceType (RecC name fields) = do
   t <- newName "t"
   x <- newName "x"
   let body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newNamedField fields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>)
          <$> genShallowmapField (varE t) fieldType shallowConstraint baseConstraint (getFieldOf x fieldName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP t, x `asP` recP name []] body []
genShallowmapClause shallowConstraint baseConstraint instanceType
                    (GadtC [name] fieldTypes (AppT resultType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genShallowmapClause (shallowConstraint . substitute resultType instanceType)
                       (baseConstraint . substitute resultType instanceType)
                       instanceType (NormalC name fieldTypes)
genShallowmapClause shallowConstraint baseConstraint instanceType
                    (RecGadtC [name] fields (AppT resultType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genShallowmapClause (shallowConstraint . substitute resultType instanceType)
                       (baseConstraint . substitute resultType instanceType)
                       instanceType (RecC name fields)
genShallowmapClause shallowConstraint baseConstraint instanceType (ForallC _vars _cxt con) =
   genShallowmapClause shallowConstraint baseConstraint instanceType con

genFoldMapClause :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> Con -> Q ([Type], Clause)
genFoldMapClause shallowConstraint baseConstraint _instanceType (NormalC name fieldTypes) = do
   t          <- newName "t"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP t, conP name (map varP fieldNames)]
       constraintsAndFields = zipWith newField fieldNames fieldTypes
       body | null fieldNames = [| mempty |]
            | otherwise = foldr1 append $ (snd <$>) <$> constraintsAndFields
       append a b = [| $(a) <> $(b) |]
       newField :: Name -> BangType -> Q ([Type], Exp)
       newField x (_, fieldType) = genFoldMapField (varE t) fieldType shallowConstraint baseConstraint (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause pats (normalB body) []
genFoldMapClause shallowConstraint baseConstraint _instanceType (RecC name fields) = do
   t <- newName "t"
   x <- newName "x"
   let body | null fields = [| mempty |]
            | otherwise = foldr1 append $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newField fields
       append a b = [| $(a) <> $(b) |]
       newField :: VarBangType -> Q ([Type], Exp)
       newField (fieldName, _, fieldType) =
          genFoldMapField (varE t) fieldType shallowConstraint baseConstraint (getFieldOf x fieldName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP t, x `asP` recP name []] (normalB body) []
genFoldMapClause shallowConstraint baseConstraint instanceType
                 (GadtC [name] fieldTypes (AppT resultType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genFoldMapClause (shallowConstraint . substitute resultType instanceType)
                       (baseConstraint . substitute resultType instanceType)
                       instanceType (NormalC name fieldTypes)
genFoldMapClause shallowConstraint baseConstraint instanceType
                 (RecGadtC [name] fields (AppT resultType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genFoldMapClause (shallowConstraint . substitute resultType instanceType)
                       (baseConstraint . substitute resultType instanceType)
                       instanceType (RecC name fields)
genFoldMapClause shallowConstraint baseConstraint instanceType (ForallC _vars _cxt con) =
   genFoldMapClause shallowConstraint baseConstraint instanceType con

type GenTraverseFieldType = Q Exp -> Type -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Exp -> (Q Exp -> Q Exp)
                            -> Q ([Type], Exp)

genTraverseClause :: GenTraverseFieldType -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> Con
                  -> Q ([Type], Clause)
genTraverseClause genField shallowConstraint baseConstraint _instanceType (NormalC name fieldTypes) = do
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
       newField x (_, fieldType) = genField (varE t) fieldType shallowConstraint baseConstraint (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause pats (normalB body) []
genTraverseClause genField shallowConstraint baseConstraint _instanceType (RecC name fields) = do
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
          <$> genField (varE f) fieldType shallowConstraint baseConstraint (getFieldOf x fieldName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP f, x `asP` recP name []] (normalB body) []
genTraverseClause genField shallowConstraint baseConstraint instanceType
                  (GadtC [name] fieldTypes (AppT resultType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genTraverseClause genField
        (shallowConstraint . substitute resultType instanceType)
        (baseConstraint . substitute resultType instanceType)
        instanceType (NormalC name fieldTypes)
genTraverseClause genField shallowConstraint baseConstraint instanceType
                  (RecGadtC [name] fields (AppT resultType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genTraverseClause genField
                        (shallowConstraint . substitute resultType instanceType)
                        (baseConstraint . substitute resultType instanceType)
                        instanceType (RecC name fields)
genTraverseClause genField shallowConstraint baseConstraint instanceType (ForallC _vars _cxt con) =
   genTraverseClause genField shallowConstraint baseConstraint instanceType con

genShallowmapField :: Q Exp -> Type -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Exp -> (Q Exp -> Q Exp)
                -> Q ([Type], Exp)
genShallowmapField trans fieldType shallowConstraint baseConstraint fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty a | ty == VarT typeVar ->
        (,) <$> ((:[]) <$> baseConstraint (pure a))
            <*> (wrap (varE '(Transformation.$) `appE` trans) `appE` fieldAccess)
     AppT t1 t2 | t2 == VarT typeVar -> (,) <$> traverse shallowConstraint [pure t1]
                                            <*> appE (wrap [| ($trans Transformation.Shallow.<$>) |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar ->
        genShallowmapField trans t2 shallowConstraint baseConstraint fieldAccess (wrap . appE (varE '(<$>)))
     SigT ty _kind -> genShallowmapField trans ty shallowConstraint baseConstraint fieldAccess wrap
     ParensT ty -> genShallowmapField trans ty shallowConstraint baseConstraint fieldAccess wrap
     _ -> (,) [] <$> fieldAccess

genFoldMapField :: Q Exp -> Type -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Exp -> (Q Exp -> Q Exp)
                -> Q ([Type], Exp)
genFoldMapField trans fieldType shallowConstraint baseConstraint fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty a | ty == VarT typeVar ->
        (,) <$> ((:[]) <$> baseConstraint (pure a))
            <*> (wrap (varE '(.) `appE` varE 'getConst `appE` (varE '(Transformation.$) `appE` trans))
                 `appE` fieldAccess)
     AppT t1 t2 | t2 == VarT typeVar -> (,) <$> traverse shallowConstraint [pure t1]
                                            <*> appE (wrap [| (Transformation.Shallow.foldMap $trans) |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar ->
                  genFoldMapField trans t2 shallowConstraint baseConstraint fieldAccess (wrap . appE (varE 'foldMap))
     SigT ty _kind -> genFoldMapField trans ty shallowConstraint baseConstraint fieldAccess wrap
     ParensT ty -> genFoldMapField trans ty shallowConstraint baseConstraint fieldAccess wrap
     _ -> (,) [] <$> [| mempty |]

genTraverseField :: GenTraverseFieldType
genTraverseField trans fieldType shallowConstraint baseConstraint fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty a  | ty == VarT typeVar ->
        (,) <$> ((:[]) <$> baseConstraint (pure a))
            <*> (wrap (varE '(.) `appE` varE 'getCompose `appE` (varE '(Transformation.$) `appE` trans))
                 `appE` fieldAccess)
     AppT t1 t2 | t2 == VarT typeVar -> (,) <$> traverse shallowConstraint [pure t1]
                                            <*> appE (wrap [| (Transformation.Shallow.traverse $trans) |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar ->
        genTraverseField trans t2 shallowConstraint baseConstraint fieldAccess (wrap . appE (varE 'traverse))
     SigT ty _kind -> genTraverseField trans ty shallowConstraint baseConstraint fieldAccess wrap
     ParensT ty -> genTraverseField trans ty shallowConstraint baseConstraint fieldAccess wrap
     _ -> (,) [] <$> [| pure $fieldAccess |]

getFieldOf :: Name -> Name -> Q Exp
getFieldOf = getFieldOfE . varE

getFieldOfE :: Q Exp -> Name -> Q Exp
getFieldOfE record field = do
#if MIN_VERSION_template_haskell(2,19,0)
  dotty <- TH.isExtEnabled TH.OverloadedRecordDot
  if dotty
     then TH.getFieldE record (TH.nameBase field)
     else appE (varE field) record
#else
  appE (varE field) record
#endif
