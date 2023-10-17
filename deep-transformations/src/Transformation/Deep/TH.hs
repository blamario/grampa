-- | This module exports the templates for automatic instance deriving of "Transformation.Deep" type classes. The most
-- common way to use it would be
--
-- > import qualified Transformation.Deep.TH
-- > data MyDataType f' f = ...
-- > $(Transformation.Deep.TH.deriveFunctor ''MyDataType)
--

{-# Language CPP, TemplateHaskell #-}
-- Adapted from https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial

module Transformation.Deep.TH (deriveAll, deriveFunctor, deriveTraversable)
where

import Control.Applicative (liftA2)
import Control.Monad (replicateM)
import Data.Functor.Compose (Compose(getCompose))
import Data.Functor.Const (Const(getConst))
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax (BangType, VarBangType, getQ, putQ)

import qualified Transformation
import qualified Transformation.Deep
import qualified Transformation.Full


data Deriving = Deriving { _constructor :: Name, _variableN :: Name, _variable1 :: Name }

deriveAll :: Name -> Q [Dec]
deriveAll ty = foldr f (pure []) [deriveFunctor, deriveFoldable, deriveTraversable]
   where f derive rest = (<>) <$> derive ty <*> rest

deriveFunctor :: Name -> Q [Dec]
deriveFunctor typeName = do
   t <- varT <$> newName "t"
   (instanceType, cs) <- reifyConstructors typeName
   let deepConstraint ty = conT ''Transformation.Deep.Functor `appT` t `appT` ty
       fullConstraint ty = conT ''Transformation.Full.Functor `appT` t `appT` ty
       baseConstraint ty = conT ''Transformation.At `appT` t `appT` ty
   (constraints, dec) <- genDeepmap baseConstraint deepConstraint fullConstraint instanceType cs
   sequence [instanceD (cxt $ appT (conT ''Transformation.Transformation) t : map pure constraints)
                       (deepConstraint instanceType)
                       [pure dec]]

deriveFoldable :: Name -> Q [Dec]
deriveFoldable typeName = do
   t <- varT <$> newName "t"
   m <- varT <$> newName "m"
   (instanceType, cs) <- reifyConstructors typeName
   let deepConstraint ty = conT ''Transformation.Deep.Foldable `appT` t `appT` ty
       fullConstraint ty = conT ''Transformation.Full.Foldable `appT` t `appT` ty
       baseConstraint ty = conT ''Transformation.At `appT` t `appT` ty
   (constraints, dec) <- genFoldMap baseConstraint deepConstraint fullConstraint instanceType cs
   sequence [instanceD (cxt (appT (conT ''Transformation.Transformation) t :
                             appT (appT equalityT (conT ''Transformation.Codomain `appT` t))
                                  (conT ''Const `appT` m) :
                             appT (conT ''Monoid) m : map pure constraints))
                       (deepConstraint instanceType)
                       [pure dec]]

deriveTraversable :: Name -> Q [Dec]
deriveTraversable typeName = do
   t <- varT <$> newName "t"
   m <- varT <$> newName "m"
   f <- varT <$> newName "f"
   (instanceType, cs) <- reifyConstructors typeName
   let deepConstraint ty = conT ''Transformation.Deep.Traversable `appT` t `appT` ty
       fullConstraint ty = conT ''Transformation.Full.Traversable `appT` t `appT` ty
       baseConstraint ty = conT ''Transformation.At `appT` t `appT` ty
   (constraints, dec) <- genTraverse baseConstraint deepConstraint fullConstraint instanceType cs
   sequence [instanceD (cxt (appT (conT ''Transformation.Transformation) t :
                             appT (appT equalityT (conT ''Transformation.Codomain `appT` t))
                                  (conT ''Compose `appT` m `appT` f) :
                             appT (conT ''Applicative) m : map pure constraints))
                       (deepConstraint instanceType)
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
   let (KindedTV tyVar _ (AppT (AppT ArrowT StarT) StarT) :
        KindedTV tyVar' _ (AppT (AppT ArrowT StarT) StarT) : _) = reverse tyVars'
       apply t (PlainTV name _)    = appT t (varT name)
       apply t (KindedTV name _ _) = appT t (varT name)
#else
   let (KindedTV tyVar  (AppT (AppT ArrowT StarT) StarT) :
        KindedTV tyVar' (AppT (AppT ArrowT StarT) StarT) : _) = reverse tyVars'
       apply t (PlainTV name)    = appT t (varT name)
       apply t (KindedTV name _) = appT t (varT name)
#endif
       instanceType           = foldl apply (conT tyConName) (reverse $ drop 2 $ reverse tyVars')

   putQ (Deriving tyConName tyVar' tyVar)
   return (instanceType, cs)

genDeepmap :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> [Con] -> Q ([Type], Dec)
genDeepmap baseConstraint deepConstraint fullConstraint instanceType cs = do
   (constraints, clauses) <- unzip <$> mapM (genDeepmapClause baseConstraint deepConstraint
                                                              fullConstraint instanceType) cs
   return (concat constraints, FunD '(Transformation.Deep.<$>) clauses)

genFoldMap :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> [Con] -> Q ([Type], Dec)
genFoldMap baseConstraint deepConstraint fullConstraint instanceType cs = do
   (constraints, clauses) <- unzip <$> mapM (genFoldMapClause baseConstraint deepConstraint
                                                              fullConstraint instanceType) cs
   return (concat constraints, FunD 'Transformation.Deep.foldMap clauses)

genTraverse :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> [Con] -> Q ([Type], Dec)
genTraverse baseConstraint deepConstraint fullConstraint instanceType cs = do
   (constraints, clauses) <- unzip
     <$> mapM (genTraverseClause genTraverseField baseConstraint deepConstraint fullConstraint instanceType) cs
   return (concat constraints, FunD 'Transformation.Deep.traverse clauses)

genDeepmapClause :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> Con
                 -> Q ([Type], Clause)
genDeepmapClause baseConstraint deepConstraint fullConstraint _instanceType (NormalC name fieldTypes) = do
   t          <- newName "t"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP t, parensP (conP name $ map varP fieldNames)]
       constraintsAndFields = zipWith newField fieldNames fieldTypes
       newFields = map (snd <$>) constraintsAndFields
       body = normalB $ appsE $ conE name : newFields
       newField :: Name -> BangType -> Q ([Type], Exp)
       newField x (_, fieldType) =
          genDeepmapField (varE t) fieldType baseConstraint deepConstraint fullConstraint (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause pats body []
genDeepmapClause baseConstraint deepConstraint fullConstraint _instanceType (RecC name fields) = do
   t <- newName "t"
   x <- newName "x"
   let body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newNamedField fields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>)
          <$> genDeepmapField (varE t) fieldType baseConstraint deepConstraint fullConstraint
                              (getFieldOf x fieldName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP t, x `asP` recP name []] body []
genDeepmapClause baseConstraint deepConstraint fullConstraint instanceType
                 (GadtC [name] fieldTypes (AppT (AppT resultType (VarT tyVar')) (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar' _tyVar) <- getQ
      putQ (Deriving tyConName tyVar' tyVar)
      genDeepmapClause (baseConstraint . substitute resultType instanceType)
                       (deepConstraint . substitute resultType instanceType)
                       (fullConstraint . substitute resultType instanceType)
                       instanceType (NormalC name fieldTypes)
genDeepmapClause baseConstraint deepConstraint fullConstraint instanceType
                 (RecGadtC [name] fields (AppT (AppT resultType (VarT tyVar')) (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar' _tyVar) <- getQ
      putQ (Deriving tyConName tyVar' tyVar)
      genDeepmapClause (baseConstraint . substitute resultType instanceType)
                       (deepConstraint . substitute resultType instanceType)
                       (fullConstraint . substitute resultType instanceType)
                       instanceType (RecC name fields)
genDeepmapClause baseConstraint deepConstraint fullConstraint instanceType (ForallC _vars _cxt con) =
   genDeepmapClause baseConstraint deepConstraint fullConstraint instanceType con

genFoldMapClause :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Type -> Con
                 -> Q ([Type], Clause)
genFoldMapClause baseConstraint deepConstraint fullConstraint _instanceType (NormalC name fieldTypes) = do
   t          <- newName "t"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP t, conP name (map varP fieldNames)]
       constraintsAndFields = zipWith newField fieldNames fieldTypes
       body | null fieldNames = [| mempty |]
            | otherwise = foldr1 append $ (snd <$>) <$> constraintsAndFields
       append a b = [| $(a) <> $(b) |]
       newField :: Name -> BangType -> Q ([Type], Exp)
       newField x (_, fieldType) = genFoldMapField (varE t) fieldType baseConstraint deepConstraint fullConstraint
                                                   (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause pats (normalB body) []
genFoldMapClause baseConstraint deepConstraint fullConstraint _instanceType (RecC name fields) = do
   t <- newName "t"
   x <- newName "x"
   let body | null fields = [| mempty |]
            | otherwise = foldr1 append $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newField fields
       append a b = [| $(a) <> $(b) |]
       newField :: VarBangType -> Q ([Type], Exp)
       newField (fieldName, _, fieldType) =
          genFoldMapField (varE t) fieldType baseConstraint deepConstraint fullConstraint (getFieldOf x fieldName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP t, x `asP` recP name []] (normalB body) []
genFoldMapClause baseConstraint deepConstraint fullConstraint instanceType
                 (GadtC [name] fieldTypes (AppT (AppT resultType (VarT tyVar')) (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar' _tyVar) <- getQ
      putQ (Deriving tyConName tyVar' tyVar)
      genFoldMapClause (baseConstraint . substitute resultType instanceType)
                       (deepConstraint . substitute resultType instanceType)
                       (fullConstraint . substitute resultType instanceType)
                       instanceType (NormalC name fieldTypes)
genFoldMapClause baseConstraint deepConstraint fullConstraint instanceType
                 (RecGadtC [name] fields (AppT (AppT resultType (VarT tyVar')) (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar' _tyVar) <- getQ
      putQ (Deriving tyConName tyVar' tyVar)
      genFoldMapClause (baseConstraint . substitute resultType instanceType)
                       (deepConstraint . substitute resultType instanceType)
                       (fullConstraint . substitute resultType instanceType)
                       instanceType (RecC name fields)
genFoldMapClause baseConstraint deepConstraint fullConstraint instanceType (ForallC _vars _cxt con) =
   genFoldMapClause baseConstraint deepConstraint fullConstraint instanceType con

type GenTraverseFieldType = Q Exp -> Type -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> (Q Type -> Q Type)
                            -> Q Exp -> (Q Exp -> Q Exp)
                            -> Q ([Type], Exp)

genTraverseClause :: GenTraverseFieldType -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> (Q Type -> Q Type)
                  -> Q Type -> Con
                  -> Q ([Type], Clause)
genTraverseClause genField baseConstraint deepConstraint fullConstraint _instanceType (NormalC name fieldTypes) =
   do t          <- newName "t"
      fieldNames <- replicateM (length fieldTypes) (newName "x")
      let pats = [varP t, parensP (conP name $ map varP fieldNames)]
          constraintsAndFields = zipWith newField fieldNames fieldTypes
          newFields = map (snd <$>) constraintsAndFields
          body | null fieldTypes = [| pure $(conE name) |]
               | otherwise = fst $ foldl apply (conE name, False) newFields
          apply (a, False) b = ([| $(a) <$> $(b) |], True)
          apply (a, True) b = ([| $(a) <*> $(b) |], True)
          newField :: Name -> BangType -> Q ([Type], Exp)
          newField x (_, fieldType) =
             genField (varE t) fieldType baseConstraint deepConstraint fullConstraint (varE x) id
      constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
      (,) constraints <$> clause pats (normalB body) []
genTraverseClause genField baseConstraint deepConstraint fullConstraint _instanceType (RecC name fields) = do
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
          <$> genField (varE f) fieldType baseConstraint deepConstraint fullConstraint (getFieldOf x fieldName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP f, x `asP` recP name []] (normalB body) []
genTraverseClause genField baseConstraint deepConstraint fullConstraint instanceType
                  (GadtC [name] fieldTypes (AppT (AppT resultType (VarT tyVar')) (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar' _tyVar) <- getQ
      putQ (Deriving tyConName tyVar' tyVar)
      genTraverseClause genField
                        (baseConstraint . substitute resultType instanceType)
                        (deepConstraint . substitute resultType instanceType)
                        (fullConstraint . substitute resultType instanceType)
                        instanceType (NormalC name fieldTypes)
genTraverseClause genField baseConstraint deepConstraint fullConstraint instanceType
                  (RecGadtC [name] fields (AppT (AppT resultType (VarT tyVar')) (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar' _tyVar) <- getQ
      putQ (Deriving tyConName tyVar' tyVar)
      genTraverseClause genField
                        (baseConstraint . substitute resultType instanceType)
                        (deepConstraint . substitute resultType instanceType)
                        (fullConstraint . substitute resultType instanceType)
                        instanceType (RecC name fields)
genTraverseClause genField baseConstraint deepConstraint fullConstraint instanceType (ForallC _vars _cxt con) =
   genTraverseClause genField baseConstraint deepConstraint fullConstraint instanceType con

genDeepmapField :: Q Exp -> Type -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> (Q Type -> Q Type)
                -> Q Exp -> (Q Exp -> Q Exp)
                -> Q ([Type], Exp)
genDeepmapField trans fieldType baseConstraint deepConstraint fullConstraint fieldAccess wrap = do
   Just (Deriving _ typeVarN typeVar1) <- getQ
   case fieldType of
     AppT ty (AppT (AppT con v1) v2) | ty == VarT typeVar1, v1 == VarT typeVarN, v2 == VarT typeVarN ->
        (,) <$> ((:[]) <$> fullConstraint (pure con))
            <*> appE (wrap [| ($trans Transformation.Full.<$>) |]) fieldAccess
     AppT ty a | ty == VarT typeVar1 ->
        (,) <$> ((:[]) <$> baseConstraint (pure a))
            <*> (wrap (varE '(Transformation.$) `appE` trans) `appE` fieldAccess)
     AppT (AppT con v1) v2 | v1 == VarT typeVarN, v2 == VarT typeVar1 ->
        (,) <$> ((:[]) <$> deepConstraint (pure con))
            <*> appE (wrap [| Transformation.Deep.fmap $trans |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar1 ->
        genDeepmapField trans t2 baseConstraint deepConstraint fullConstraint fieldAccess (wrap . appE (varE '(<$>)))
     SigT ty _kind -> genDeepmapField trans ty baseConstraint deepConstraint fullConstraint fieldAccess wrap
     ParensT ty -> genDeepmapField trans ty baseConstraint deepConstraint fullConstraint fieldAccess wrap
     _ -> (,) [] <$> fieldAccess

genFoldMapField :: Q Exp -> Type -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> (Q Type -> Q Type)
                -> Q Exp -> (Q Exp -> Q Exp)
                -> Q ([Type], Exp)
genFoldMapField trans fieldType baseConstraint deepConstraint fullConstraint fieldAccess wrap = do
   Just (Deriving _ typeVarN typeVar1) <- getQ
   case fieldType of
     AppT ty (AppT (AppT con v1) v2) | ty == VarT typeVar1, v1 == VarT typeVarN, v2 == VarT typeVarN ->
        (,) <$> ((:[]) <$> fullConstraint (pure con))
            <*> appE (wrap [| Transformation.Full.foldMap $trans |]) fieldAccess
     AppT ty a | ty == VarT typeVar1 ->
        (,) <$> ((:[]) <$> baseConstraint (pure a))
            <*> (wrap (varE '(.) `appE` varE 'getConst `appE` (varE '(Transformation.$) `appE` trans))
                 `appE` fieldAccess)
     AppT (AppT con v1) v2 | v1 == VarT typeVarN, v2 == VarT typeVar1 ->
        (,) <$> ((:[]) <$> deepConstraint (pure con))
            <*> appE (wrap [| Transformation.Deep.foldMap $trans |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar1 ->
        genFoldMapField trans t2 baseConstraint deepConstraint fullConstraint fieldAccess (wrap . appE (varE 'foldMap))
     SigT ty _kind -> genFoldMapField trans ty baseConstraint deepConstraint fullConstraint fieldAccess wrap
     ParensT ty -> genFoldMapField trans ty baseConstraint deepConstraint fullConstraint fieldAccess wrap
     _ -> (,) [] <$> [| mempty |]

genTraverseField :: GenTraverseFieldType
genTraverseField trans fieldType baseConstraint deepConstraint fullConstraint fieldAccess wrap = do
   Just (Deriving _ typeVarN typeVar1) <- getQ
   case fieldType of
     AppT ty (AppT (AppT con v1) v2) | ty == VarT typeVar1, v1 == VarT typeVarN, v2 == VarT typeVarN ->
        (,) <$> ((:[]) <$> fullConstraint (pure con))
            <*> appE (wrap [| Transformation.Full.traverse $trans |]) fieldAccess
     AppT ty a  | ty == VarT typeVar1 ->
        (,) <$> ((:[]) <$> baseConstraint (pure a))
            <*> (wrap (varE '(.) `appE` varE 'getCompose `appE` (varE '(Transformation.$) `appE` trans))
                 `appE` fieldAccess)
     AppT (AppT con v1) v2 | v1 == VarT typeVarN, v2 == VarT typeVar1 ->
        (,) <$> ((:[]) <$> deepConstraint (pure con))
            <*> appE (wrap [| Transformation.Deep.traverse $trans |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar1 -> genTraverseField trans t2 baseConstraint deepConstraint fullConstraint
                                                          fieldAccess (wrap . appE (varE 'traverse))
     SigT ty _kind -> genTraverseField trans ty baseConstraint deepConstraint fullConstraint fieldAccess wrap
     ParensT ty -> genTraverseField trans ty baseConstraint deepConstraint fullConstraint fieldAccess wrap
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
