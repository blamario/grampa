-- | This module exports the templates for automatic instance deriving of "Rank2" type classes. The most common way to
-- use it would be
--
-- > import qualified Rank2.TH
-- > data MyDataType f = ...
-- > $(Rank2.TH.deriveAll ''MyDataType)
--
-- or, if you're picky, you can invoke only 'deriveFunctor' and whichever other instances you need instead.

{-# Language CPP #-}
{-# Language TemplateHaskell #-}
{-# Language TypeOperators #-}
-- Adapted from https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial

module Rank2.TH (deriveAll, deriveFunctor, deriveApply, unsafeDeriveApply, deriveApplicative,
                 deriveFoldable, deriveTraversable,
                 deriveDistributive, deriveDistributiveTraversable, deriveLogistic)
where

import Control.Applicative (liftA2, liftA3)
import Control.Monad (replicateM)
import Data.Bifunctor (first)
import Data.Distributive (cotraverse)
import Data.Functor.Compose (Compose (Compose))
import Data.Functor.Contravariant (Contravariant, contramap)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH (Q, TypeQ, Name, TyVarBndr(KindedTV, PlainTV), Clause, Dec(..), Con(..), Type(..), Exp(..),
                            Inline(Inlinable, Inline), RuleMatch(FunLike), Phases(AllPhases),
                            appE, conE, conP, conT, instanceD, varE, varP, varT, normalB, pragInlD, recConE, wildP)
import Language.Haskell.TH.Syntax (BangType, VarBangType, Info(TyConI), getQ, putQ, newName)

import qualified Rank2

data Deriving = Deriving { _derivingConstructor :: Name, _derivingVariable :: Name } deriving Show

deriveAll :: Name -> Q [Dec]
deriveAll ty = foldr f (pure []) [deriveFunctor, deriveApply, deriveApplicative,
                                  deriveFoldable, deriveTraversable,
                                  deriveDistributive, deriveDistributiveTraversable, deriveLogistic]
   where f derive rest = (<>) <$> derive ty <*> rest

deriveFunctor :: Name -> Q [Dec]
deriveFunctor ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Functor ty
   (constraints, dec) <- genFmap instanceType cs
   sequence [instanceD (TH.cxt $ map pure constraints) instanceType
             [pure dec, pragInlD '(Rank2.<$>) Inline FunLike AllPhases]]

deriveApply :: Name -> Q [Dec]
deriveApply ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Apply ty
   (constraints, dec) <- genAp instanceType cs
   sequence [instanceD (TH.cxt $ map pure constraints) instanceType
             [pure dec, genLiftA2 cs, genLiftA3 cs,
              pragInlD '(Rank2.<*>) Inlinable FunLike AllPhases,
              pragInlD 'Rank2.liftA2 Inlinable FunLike AllPhases]]

-- | This function always succeeds, but the methods it generates may be partial. Use with care.
unsafeDeriveApply :: Name -> Q [Dec]
unsafeDeriveApply ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Apply ty
   (constraints, dec) <- genApUnsafely instanceType cs
   sequence [instanceD (TH.cxt $ map pure constraints) instanceType
             [pure dec, genLiftA2Unsafely cs, genLiftA3Unsafely cs,
              pragInlD '(Rank2.<*>) Inlinable FunLike AllPhases,
              pragInlD 'Rank2.liftA2 Inlinable FunLike AllPhases]]

deriveApplicative :: Name -> Q [Dec]
deriveApplicative ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Applicative ty
   (constraints, dec) <- genPure cs
   sequence [instanceD (TH.cxt $ map pure constraints) instanceType
             [pure dec, pragInlD 'Rank2.pure Inline FunLike AllPhases]]

deriveFoldable :: Name -> Q [Dec]
deriveFoldable ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Foldable ty
   (constraints, dec) <- genFoldMap instanceType cs
   sequence [instanceD (TH.cxt $ map pure constraints) instanceType
             [pure dec, pragInlD 'Rank2.foldMap Inlinable FunLike AllPhases]]

deriveTraversable :: Name -> Q [Dec]
deriveTraversable ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Traversable ty
   (constraints, dec) <- genTraverse instanceType cs
   sequence [instanceD (TH.cxt $ map pure constraints) instanceType
             [pure dec, pragInlD 'Rank2.traverse Inlinable FunLike AllPhases]]

deriveDistributive :: Name -> Q [Dec]
deriveDistributive ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Distributive ty
   (constraints, dec) <- genCotraverse cs
   sequence [instanceD (TH.cxt $ map pure constraints) instanceType
             [pure dec, pragInlD 'Rank2.cotraverse Inline FunLike AllPhases]]

deriveDistributiveTraversable :: Name -> Q [Dec]
deriveDistributiveTraversable ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.DistributiveTraversable ty
   (constraints, dec) <- genCotraverseTraversable cs
   sequence [instanceD (TH.cxt $ map pure constraints) instanceType [pure dec]]

deriveLogistic :: Name -> Q [Dec]
deriveLogistic ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Logistic ty
   (constraints, decs) <- genDeliver instanceType cs
   sequence [instanceD (TH.cxt $ map pure constraints) instanceType
              (map pure decs <> [pragInlD 'Rank2.deliver Inline FunLike AllPhases])]

reifyConstructors :: Name -> Name -> Q (TypeQ, [Con])
reifyConstructors cls ty = do
   (TyConI tyCon) <- TH.reify ty
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
   lastVar <- reifyTVKindSynonyms (last tyVars)

#if MIN_VERSION_template_haskell(2,17,0)
   let (KindedTV tyVar () (AppT (AppT ArrowT _) resultKind)) = lastVar
       instanceType           = conT cls `TH.appT` foldl apply (conT tyConName) (init tyVars)
       apply t (PlainTV name _)    = TH.appT t (varT name)
       apply t (KindedTV name _ _) = TH.appT t (varT name)
#else
   let (KindedTV tyVar (AppT (AppT ArrowT _) resultKind)) = lastVar
       instanceType           = conT cls `TH.appT` foldl apply (conT tyConName) (init tyVars)
       apply t (PlainTV name)    = TH.appT t (varT name)
       apply t (KindedTV name _) = TH.appT t (varT name)
#endif

   case resultKind of
      StarT -> pure ()
      _ -> fail ("Unexpected result kind: " <> show resultKind)
   putQ (Deriving tyConName tyVar)
   return (instanceType, cs)

genFmap :: TypeQ -> [Con] -> Q ([Type], Dec)
genFmap instanceType cs = do
   it <- instanceType
   (constraints, clauses) <- unzip <$> mapM (genFmapClause it) cs
   return (concat constraints, FunD '(Rank2.<$>) clauses)

genAp :: TypeQ -> [Con] -> Q ([Type], Dec)
genAp instanceType [con] = do
   it <- instanceType
   (constraints, clause) <- genApClause False it con
   return (constraints, FunD '(Rank2.<*>) [clause])

genLiftA2 :: [Con] -> Q Dec
genLiftA2 [con] = TH.funD 'Rank2.liftA2 [genLiftA2Clause False con]

genLiftA3 :: [Con] -> Q Dec
genLiftA3 [con] = TH.funD 'Rank2.liftA3 [genLiftA3Clause False con]

genApUnsafely :: TypeQ -> [Con] -> Q ([Type], Dec)
genApUnsafely instanceType cons = do
   it <- instanceType
   (constraints, clauses) <- unzip <$> mapM (genApClause True it) cons
   return (concat constraints, FunD '(Rank2.<*>) clauses)

genLiftA2Unsafely :: [Con] -> Q Dec
genLiftA2Unsafely cons = TH.funD 'Rank2.liftA2 (genLiftA2Clause True <$> cons)

genLiftA3Unsafely :: [Con] -> Q Dec
genLiftA3Unsafely cons = TH.funD 'Rank2.liftA3 (genLiftA3Clause True <$> cons)

genPure :: [Con] -> Q ([Type], Dec)
genPure cs = do (constraints, clauses) <- unzip <$> mapM genPureClause cs
                return (concat constraints, FunD 'Rank2.pure clauses)

genFoldMap :: TypeQ -> [Con] -> Q ([Type], Dec)
genFoldMap instanceType cs = do
   it <- instanceType
   (constraints, clauses) <- unzip <$> mapM (genFoldMapClause it) cs
   return (concat constraints, FunD 'Rank2.foldMap clauses)

genTraverse :: TypeQ -> [Con] -> Q ([Type], Dec)
genTraverse instanceType cs = do
   it <- instanceType
   (constraints, clauses) <- unzip <$> mapM (genTraverseClause it) cs
   return (concat constraints, FunD 'Rank2.traverse clauses)

genCotraverse :: [Con] -> Q ([Type], Dec)
genCotraverse [con] = do (constraints, clause) <- genCotraverseClause con
                         return (constraints, FunD 'Rank2.cotraverse [clause])

genCotraverseTraversable :: [Con] -> Q ([Type], Dec)
genCotraverseTraversable [con] = do (constraints, clause) <- genCotraverseTraversableClause con
                                    return (constraints, FunD 'Rank2.cotraverseTraversable [clause])

genDeliver :: TypeQ -> [Con] -> Q ([Type], [Dec])
genDeliver instanceType [con] = do
   it <- instanceType
   let AppT _classType rt = it
       recType = pure rt
   signable <- TH.isExtEnabled TH.InstanceSigs
   scopable <- TH.isExtEnabled TH.ScopedTypeVariables
   if signable && scopable then do
      p <- newName "p"
      q <- newName "q"
      (constraints, clause) <- genDeliverClause recType (Just q) con
      ctx <- [t| Contravariant $(varT p) |]
      methodType <- [t| $(varT p) ($(recType) $(varT q) -> $(recType) $(varT q)) -> $(recType) (Compose $(varT p) ($(varT q) Rank2.~> $(varT q))) |]
      return (constraints,
              [SigD 'Rank2.deliver (ForallT [binder p, binder q] [ctx] methodType),
               FunD 'Rank2.deliver [clause]])
   else do
      (constraints, clause) <- genDeliverClause recType Nothing con
      return (constraints, [FunD 'Rank2.deliver [clause]])


genFmapClause :: Type -> Con -> Q ([Type], Clause)
genFmapClause _ (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP f, conP name (map varP fieldNames)]
       constraintsAndFields = zipWith newField fieldNames fieldTypes
       newFields = map (snd <$>) constraintsAndFields
       body = normalB $ TH.appsE $ conE name : newFields
       newField :: Name -> BangType -> Q ([Type], Exp)
       newField x (_, fieldType) = genFmapField (varE f) fieldType (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause pats body []
genFmapClause _ (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newNamedField fields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>)
          <$> genFmapField (varE f) fieldType (getFieldOf x fieldName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause [varP f, x `TH.asP` TH.recP name []] body []
genFmapClause instanceType (GadtC [name] fieldTypes _resultType@(AppT initType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      let AppT classType t = instanceType
      first (renameConstraintVars t initType <$>) <$> genFmapClause instanceType (NormalC name fieldTypes)
genFmapClause instanceType (RecGadtC [name] fields _resultType@(AppT initType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      let AppT classType t = instanceType
      first (renameConstraintVars t initType <$>) <$> genFmapClause instanceType (RecC name fields)
genFmapClause instanceType (ForallC _vars _cxt con) = genFmapClause instanceType con

genFmapField :: Q Exp -> Type -> Q Exp -> (Q Exp -> Q Exp) -> Q ([Type], Exp)
genFmapField fun fieldType fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _  | ty == VarT typeVar -> (,) [] <$> appE (wrap fun) fieldAccess
     AppT t1 t2 | t2 == VarT typeVar -> (,) (constrain ''Rank2.Functor t1) <$> appE (wrap [| ($fun Rank2.<$>) |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar -> genFmapField fun t2 fieldAccess (wrap . appE (varE '(<$>)))
     SigT ty _kind -> genFmapField fun ty fieldAccess wrap
     ParensT ty -> genFmapField fun ty fieldAccess wrap
     _ -> (,) [] <$> fieldAccess

genLiftA2Clause :: Bool -> Con -> Q Clause
genLiftA2Clause unsafely (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames1 <- replicateM (length fieldTypes) (newName "x")
   y <- newName "y"
   fieldNames2 <- replicateM (length fieldTypes) (newName "y")
   let pats = [varP f, conP name (map varP fieldNames1), varP y]
       body = normalB $ TH.appsE $ conE name : zipWith newField (zip fieldNames1 fieldNames2) fieldTypes
       newField :: (Name, Name) -> BangType -> Q Exp
       newField (x, y) (_, fieldType) = genLiftA2Field unsafely (varE f) fieldType (varE x) (varE y) id
   TH.clause pats body [TH.valD (conP name $ map varP fieldNames2) (normalB $ varE y) []]
genLiftA2Clause unsafely (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   y <- newName "y"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          TH.fieldExp fieldName $
             genLiftA2Field unsafely (varE f) fieldType (getFieldOf x fieldName) (getFieldOf y fieldName) id
   TH.clause [varP f, x `TH.asP` TH.recP name [], varP y] body []
genLiftA2Clause unsafely (GadtC [name] fieldTypes _resultType@(AppT _ (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genLiftA2Clause unsafely (NormalC name fieldTypes)
genLiftA2Clause unsafely (RecGadtC [name] fields _resultType@(AppT _ (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genLiftA2Clause unsafely (RecC name fields)
genLiftA2Clause unsafely (ForallC _vars _cxt con) = genLiftA2Clause unsafely con

genLiftA2Field :: Bool -> Q Exp -> Type -> Q Exp -> Q Exp -> (Q Exp -> Q Exp) -> Q Exp
genLiftA2Field unsafely fun fieldType field1Access field2Access wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> [| $(wrap fun) $field1Access $field2Access |]
     AppT _ ty | ty == VarT typeVar -> [| $(wrap $ appE (varE 'Rank2.liftA2) fun) $field1Access $field2Access |]
     AppT t1 t2 
        | t1 /= VarT typeVar -> genLiftA2Field unsafely fun t2 field1Access field2Access (appE (varE 'liftA2) . wrap)
     SigT ty _kind -> genLiftA2Field unsafely fun ty field1Access field2Access wrap
     ParensT ty -> genLiftA2Field unsafely fun ty field1Access field2Access wrap
     _ | unsafely -> field1Access
       | otherwise -> error ("Cannot apply liftA2 to field of type " <> show fieldType)

genLiftA3Clause :: Bool -> Con -> Q Clause
genLiftA3Clause unsafely (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames1 <- replicateM (length fieldTypes) (newName "x")
   y <- newName "y"
   z <- newName "z"
   fieldNames2 <- replicateM (length fieldTypes) (newName "y")
   fieldNames3 <- replicateM (length fieldTypes) (newName "z")
   let pats = [varP f, conP name (map varP fieldNames1), varP y, varP z]
       body = normalB $ TH.appsE $ conE name : zipWith newField (zip3 fieldNames1 fieldNames2 fieldNames3) fieldTypes
       newField :: (Name, Name, Name) -> BangType -> Q Exp
       newField (x, y, z) (_, fieldType) = genLiftA3Field unsafely (varE f) fieldType (varE x) (varE y) (varE z) id
   TH.clause pats body [TH.valD (conP name $ map varP fieldNames2) (normalB $ varE y) [],
                        TH.valD (conP name $ map varP fieldNames3) (normalB $ varE z) []]
genLiftA3Clause unsafely (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   y <- newName "y"
   z <- newName "z"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          TH.fieldExp fieldName
             (genLiftA3Field unsafely (varE f) fieldType (getFieldOf x fieldName) (getFieldOf y fieldName) (getFieldOf z fieldName) id)
   TH.clause [varP f, x `TH.asP` TH.recP name [], varP y, varP z] body []
genLiftA3Clause unsafely (GadtC [name] fieldTypes _resultType@(AppT _ (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genLiftA3Clause unsafely (NormalC name fieldTypes)
genLiftA3Clause unsafely (RecGadtC [name] fields _resultType@(AppT _ (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genLiftA3Clause unsafely (RecC name fields)
genLiftA3Clause unsafely (ForallC _vars _cxt con) = genLiftA3Clause unsafely con

genLiftA3Field :: Bool -> Q Exp -> Type -> Q Exp -> Q Exp -> Q Exp -> (Q Exp -> Q Exp) -> Q Exp
genLiftA3Field unsafely fun fieldType field1Access field2Access field3Access wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _
        | ty == VarT typeVar -> [| $(wrap fun) $(field1Access) $(field2Access) $(field3Access) |]
     AppT _ ty
        | ty == VarT typeVar -> [| $(wrap $ appE (varE 'Rank2.liftA3) fun) $(field1Access) $(field2Access) $(field3Access) |]
     AppT t1 t2
        | t1 /= VarT typeVar
          -> genLiftA3Field unsafely fun t2 field1Access field2Access field3Access (appE (varE 'liftA3) . wrap)
     SigT ty _kind -> genLiftA3Field unsafely fun ty field1Access field2Access field3Access wrap
     ParensT ty -> genLiftA3Field unsafely fun ty field1Access field2Access field3Access wrap
     _ | unsafely -> field1Access
       | otherwise -> error ("Cannot apply liftA3 to field of type " <> show fieldType)

genApClause :: Bool -> Type -> Con -> Q ([Type], Clause)
genApClause unsafely _ (NormalC name fieldTypes) = do
   fieldNames1 <- replicateM (length fieldTypes) (newName "x")
   fieldNames2 <- replicateM (length fieldTypes) (newName "y")
   rhsName <- newName "rhs"
   let pats = [conP name (map varP fieldNames1), varP rhsName]
       constraintsAndFields = zipWith newField (zip fieldNames1 fieldNames2) fieldTypes
       newFields = map (snd <$>) constraintsAndFields
       body = normalB $ TH.appsE $ conE name : newFields
       newField :: (Name, Name) -> BangType -> Q ([Type], Exp)
       newField (x, y) (_, fieldType) = genApField unsafely fieldType (varE x) (varE y) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause pats body [TH.valD (conP name $ map varP fieldNames2) (normalB $ varE rhsName) []]
genApClause unsafely _ (RecC name fields) = do
   x <- newName "x"
   y <- newName "y"
   let body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newNamedField fields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>) <$> genApField unsafely fieldType (getFieldOf x fieldName) (getFieldOf y fieldName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause [x `TH.asP` TH.recP name [], varP y] body []
genApClause unsafely instanceType (GadtC [name] fieldTypes _resultType@(AppT initType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      let AppT classType t = instanceType
      first (renameConstraintVars t initType <$>) <$> genApClause unsafely instanceType (NormalC name fieldTypes)
genApClause unsafely instanceType (RecGadtC [name] fields _resultType@(AppT initType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      let AppT classType t = instanceType
      first (renameConstraintVars t initType <$>) <$> genApClause unsafely instanceType (RecC name fields)
genApClause unsafely instanceType (ForallC _vars _cxt con) = genApClause unsafely instanceType con

genApField :: Bool -> Type -> Q Exp -> Q Exp -> (Q Exp -> Q Exp) -> Q ([Type], Exp)
genApField unsafely fieldType field1Access field2Access wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> (,) [] <$> [| $(wrap (varE 'Rank2.apply)) $(field1Access) $(field2Access) |]
     AppT t1 t2 | t2 == VarT typeVar ->
                  (,) (constrain ''Rank2.Apply t1) <$> [| $(wrap (varE 'Rank2.ap)) $(field1Access) $(field2Access) |]
     AppT t1 t2 | t1 /= VarT typeVar -> genApField unsafely t2 field1Access field2Access (appE (varE 'liftA2) . wrap)
     SigT ty _kind -> genApField unsafely ty field1Access field2Access wrap
     ParensT ty -> genApField unsafely ty field1Access field2Access wrap
     _ | unsafely -> (,) [] <$> field1Access
       | otherwise -> error ("Cannot apply ap to field of type " <> show fieldType)

genPureClause :: Con -> Q ([Type], Clause)
genPureClause (NormalC name fieldTypes) = do
   argName <- newName "f"
   let body = normalB $ TH.appsE $ conE name : ((snd <$>) <$> constraintsAndFields)
       constraintsAndFields = map newField fieldTypes
       newField :: BangType -> Q ([Type], Exp)
       newField (_, fieldType) = genPureField fieldType (varE argName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause [varP argName] body []
genPureClause (RecC name fields) = do
   argName <- newName "f"
   let body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newNamedField fields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) = ((,) fieldName <$>) <$> genPureField fieldType (varE argName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause [varP argName] body []

genPureField :: Type -> Q Exp -> (Q Exp -> Q Exp) -> Q ([Type], Exp)
genPureField fieldType pureValue wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> (,) [] <$> wrap pureValue
     AppT t1 t2 | t2 == VarT typeVar -> (,) (constrain ''Rank2.Applicative t1) <$> wrap (appE (varE 'Rank2.pure) pureValue)
     AppT t1 t2 | t1 /= VarT typeVar -> genPureField t2 pureValue (wrap . appE (varE 'pure))
     SigT ty _kind -> genPureField ty pureValue wrap
     ParensT ty -> genPureField ty pureValue wrap
     _ -> error ("Cannot create a pure field of type " <> show fieldType)

genFoldMapClause :: Type -> Con -> Q ([Type], Clause)
genFoldMapClause _ (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP f, conP name (map varP fieldNames)]
       constraintsAndFields = zipWith newField fieldNames fieldTypes
       body | null fieldNames = [| mempty |]
            | otherwise = foldr1 append $ (snd <$>) <$> constraintsAndFields
       append a b = [| $(a) <> $(b) |]
       newField :: Name -> BangType -> Q ([Type], Exp)
       newField x (_, fieldType) = genFoldMapField f fieldType (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause pats (normalB body) []
genFoldMapClause _ (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body | null fields = [| mempty |]
            | otherwise = foldr1 append $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newField fields
       append a b = [| $(a) <> $(b) |]
       newField :: VarBangType -> Q ([Type], Exp)
       newField (fieldName, _, fieldType) = genFoldMapField f fieldType (getFieldOf x fieldName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause [varP f, x `TH.asP` TH.recP name []] (normalB body) []
genFoldMapClause instanceType (GadtC [name] fieldTypes _resultType@(AppT initType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      let AppT classType t = instanceType
      first (renameConstraintVars t initType <$>) <$> genFoldMapClause instanceType (NormalC name fieldTypes)
genFoldMapClause instanceType (RecGadtC [name] fields _resultType@(AppT initType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      let AppT classType t = instanceType
      first (renameConstraintVars t initType <$>) <$> genFoldMapClause instanceType (RecC name fields)
genFoldMapClause instanceType (ForallC _vars _cxt con) = genFoldMapClause instanceType con

genFoldMapField :: Name -> Type -> Q Exp -> (Q Exp -> Q Exp) -> Q ([Type], Exp)
genFoldMapField funcName fieldType fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> (,) [] <$> appE (wrap $ varE funcName) fieldAccess
     AppT t1 t2 | t2 == VarT typeVar ->
                  (,) (constrain ''Rank2.Foldable t1) <$> appE (wrap $ appE (varE 'Rank2.foldMap) (varE funcName)) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar -> genFoldMapField funcName t2 fieldAccess (wrap . appE (varE 'foldMap))
     SigT ty _kind -> genFoldMapField funcName ty fieldAccess wrap
     ParensT ty -> genFoldMapField funcName ty fieldAccess wrap
     _ -> (,) [] <$> [| mempty |]

genTraverseClause :: Type -> Con -> Q ([Type], Clause)
genTraverseClause _ (NormalC name []) =
   (,) [] <$> TH.clause [wildP, conP name []] (normalB [| pure $(conE name) |]) []
genTraverseClause _ (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP f, conP name (map varP fieldNames)]
       constraintsAndFields = zipWith newField fieldNames fieldTypes
       newFields = map (snd <$>) constraintsAndFields
       body = normalB $ fst $ foldl apply (conE name, False) newFields
       apply (a, False) b = ([| $(a) <$> $(b) |], True)
       apply (a, True) b = ([| $(a) <*> $(b) |], True)
       newField :: Name -> BangType -> Q ([Type], Exp)
       newField x (_, fieldType) = genTraverseField (varE f) fieldType (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause pats body []
genTraverseClause _ (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let constraintsAndFields = map newField fields
       body = normalB $ fst $ foldl apply (conE name, False) $ (snd <$>) <$> constraintsAndFields
       apply (a, False) b = ([| $(a) <$> $(b) |], True)
       apply (a, True) b = ([| $(a) <*> $(b) |], True)
       newField :: VarBangType -> Q ([Type], Exp)
       newField (fieldName, _, fieldType) = genTraverseField (varE f) fieldType (getFieldOf x fieldName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause [varP f, x `TH.asP` TH.recP name []] body []
genTraverseClause instanceType (GadtC [name] fieldTypes _resultType@(AppT initType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      let AppT classType t = instanceType
      first (renameConstraintVars t initType <$>) <$> genTraverseClause instanceType (NormalC name fieldTypes)
genTraverseClause instanceType (RecGadtC [name] fields _resultType@(AppT initType (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      let AppT classType t = instanceType
      first (renameConstraintVars t initType <$>) <$> genTraverseClause instanceType (RecC name fields)
genTraverseClause instanceType (ForallC _vars _cxt con) = genTraverseClause instanceType con

genTraverseField :: Q Exp -> Type -> Q Exp -> (Q Exp -> Q Exp) -> Q ([Type], Exp)
genTraverseField fun fieldType fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> (,) [] <$> appE (wrap fun) fieldAccess
     AppT t1 t2 | t2 == VarT typeVar ->
                  (,) (constrain ''Rank2.Traversable t1) <$> appE (wrap [| Rank2.traverse $fun |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar -> genTraverseField fun t2 fieldAccess (wrap . appE (varE 'traverse))
     SigT ty _kind -> genTraverseField fun ty fieldAccess wrap
     ParensT ty -> genTraverseField fun ty fieldAccess wrap
     _ -> (,) [] <$> [| pure $fieldAccess |]

genCotraverseClause :: Con -> Q ([Type], Clause)
genCotraverseClause (NormalC name []) = genCotraverseClause (RecC name [])
genCotraverseClause (RecC name fields) = do
   withName <- newName "w"
   argName <- newName "f"
   let constraintsAndFields = map newNamedField fields
       body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>) <$> (genCotraverseField ''Rank2.Distributive (varE 'Rank2.cotraverse) (varE withName)
                                   fieldType [| $(projectField fieldName) <$> $(varE argName) |] id)
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause [varP withName, varP argName] body []

genCotraverseTraversableClause :: Con -> Q ([Type], Clause)
genCotraverseTraversableClause (NormalC name []) = genCotraverseTraversableClause (RecC name [])
genCotraverseTraversableClause (RecC name fields) = do
   withName <- newName "w"
   argName <- newName "f"
   let constraintsAndFields = map newNamedField fields
       body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>) <$> (genCotraverseField ''Rank2.DistributiveTraversable
                                   (varE 'Rank2.cotraverseTraversable) (varE withName) fieldType
                                   [| $(projectField fieldName) <$> $(varE argName) |] id)
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause [varP withName, varP argName] body []

genDeliverClause :: TypeQ -> Maybe Name -> Con -> Q ([Type], Clause)
genDeliverClause recType typeVar (NormalC name []) = genDeliverClause recType typeVar (RecC name [])
genDeliverClause recType typeVar (RecC name fields) = do
   argName <- newName "f"
   let constraintsAndFields = map newNamedField fields
       body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       recExp g = maybe g (\v-> [|($g :: $(recType) $(varT v))|]) typeVar
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>)
          <$> (genDeliverField ''Rank2.Logistic fieldType
               (\wrap-> [| \set g-> $(TH.recUpdE (recExp [|g|]) [(,) fieldName <$> appE (wrap [| Rank2.apply set |]) (getFieldOfE [|g|] fieldName)]) |])
               (\wrap-> [| \set g-> $(TH.recUpdE (recExp [|g|]) [(,) fieldName <$> appE (wrap [| set |]) (getFieldOfE [|g|] fieldName)]) |])
               (varE argName)
               id
               id)
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> TH.clause [varP argName] body []

genCotraverseField :: Name -> Q Exp -> Q Exp -> Type -> Q Exp -> (Q Exp -> Q Exp) -> Q ([Type], Exp)
genCotraverseField className method fun fieldType fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> (,) [] <$> appE (wrap fun) fieldAccess
     AppT t1 t2 | t2 == VarT typeVar -> (,) (constrain className t1) <$> appE (wrap $ appE method fun) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar ->
                  genCotraverseField className method fun t2 fieldAccess (wrap . appE (varE 'cotraverse))
     SigT ty _kind -> genCotraverseField className method fun ty fieldAccess wrap
     ParensT ty -> genCotraverseField className method fun ty fieldAccess wrap

genDeliverField :: Name
                -> Type
                -> ((Q Exp -> Q Exp) -> Q Exp)
                -> ((Q Exp -> Q Exp) -> Q Exp)
                -> Q Exp
                -> (Q Exp -> Q Exp)
                -> (Q Exp -> Q Exp)
                -> Q ([Type], Exp)
genDeliverField className fieldType fieldUpdate subRecordUpdate arg outer inner = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> (,) [] <$> outer (appE [|Compose|] ([|contramap|] `appE` fieldUpdate inner `appE` arg))
     AppT t1 t2 | t2 == VarT typeVar ->
                  (,) (constrain className t1) <$> outer (appE [| Rank2.deliver |] ([|contramap|] `appE` subRecordUpdate inner `appE` arg))
     AppT t1 t2 | t1 /= VarT typeVar ->
                  genDeliverField className t2 fieldUpdate subRecordUpdate arg (outer . appE (varE 'pure)) (inner . appE (varE 'fmap))
     SigT ty _kind -> genDeliverField className ty fieldUpdate subRecordUpdate arg outer inner
     ParensT ty -> genDeliverField className ty fieldUpdate subRecordUpdate arg outer inner

renameConstraintVars :: Type -> Type -> Type -> Type
renameConstraintVars (AppT instanceType (VarT instanceVar)) (AppT returnType (VarT returnVar)) constrainedType =
   renameConstraintVars instanceType returnType (renameConstraintVar returnVar instanceVar constrainedType)
renameConstraintVars (AppT instanceType _) (AppT returnType _) constrainedType =
   renameConstraintVars instanceType returnType constrainedType
renameConstraintVars _ _ constrainedType = constrainedType

renameConstraintVar :: Name -> Name -> Type -> Type
renameConstraintVar from to (VarT name)
   | name == from = VarT to
   | otherwise = VarT name
renameConstraintVar from to (AppT a b) = AppT (renameConstraintVar from to a) (renameConstraintVar from to b)
#if MIN_VERSION_template_haskell(2,15,0)
renameConstraintVar from to (AppKindT t k) = AppT (renameConstraintVar from to t) (renameConstraintVar from to k)
#endif
renameConstraintVar from to (InfixT a op b) = InfixT (renameConstraintVar from to a) op (renameConstraintVar from to b)
renameConstraintVar from to (UInfixT a op b) = UInfixT (renameConstraintVar from to a) op (renameConstraintVar from to b)
renameConstraintVar from to (SigT t k) = SigT (renameConstraintVar from to t) (renameConstraintVar from to k)
renameConstraintVar from to (ParensT t) = ParensT (renameConstraintVar from to t)
renameConstraintVar _ _ t = t

projectField :: Name -> Q Exp
projectField field = do
#if MIN_VERSION_template_haskell(2,19,0)
  dotty <- TH.isExtEnabled TH.OverloadedRecordDot
  if dotty
     then TH.projectionE (pure $ TH.nameBase field)
     else varE field
#else
  varE field
#endif

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

constrain :: Name -> Type -> [Type]
constrain _ ConT{} = []
constrain cls t = [ConT cls `AppT` t]

#if MIN_VERSION_template_haskell(2,17,0)
binder :: Name -> TyVarBndr TH.Specificity
binder name = TH.PlainTV name TH.SpecifiedSpec
#else
binder :: Name -> TyVarBndr
binder = TH.PlainTV
#endif
