-- | This module exports the templates for automatic instance deriving of "Rank2" type classes. The most common way to
-- use it would be
--
-- > import qualified Rank2.TH
-- > data MyDataType f = ...
-- > $(Rank2.TH.deriveAll ''MyDataType)
--
-- or, if you're picky, you can invoke only 'deriveFunctor' and whichever other instances you need instead.

{-# Language TemplateHaskell #-}
-- Adapted from https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial

module Rank2.TH (deriveAll, deriveFunctor, deriveApply, unsafeDeriveApply, deriveApplicative,
                 deriveFoldable, deriveTraversable, deriveDistributive, deriveDistributiveTraversable)
where

import Control.Applicative (liftA2, liftA3)
import Control.Monad (replicateM)
import Data.Distributive (cotraverse)
import Data.Monoid ((<>))
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (BangType, VarBangType, getQ, putQ)

import qualified Rank2

data Deriving = Deriving { _derivingConstructor :: Name, _derivingVariable :: Name } deriving Show

deriveAll :: Name -> Q [Dec]
deriveAll ty = foldr f (pure []) [deriveFunctor, deriveApply, deriveApplicative,
                                  deriveFoldable, deriveTraversable, deriveDistributive, deriveDistributiveTraversable]
   where f derive rest = (<>) <$> derive ty <*> rest

deriveFunctor :: Name -> Q [Dec]
deriveFunctor ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Functor ty
   (constraints, dec) <- genFmap cs
   sequence [instanceD (cxt $ map pure constraints) instanceType
             [pure dec, pragInlD '(Rank2.<$>) Inline FunLike AllPhases]]

deriveApply :: Name -> Q [Dec]
deriveApply ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Apply ty
   (constraints, dec) <- genAp cs
   sequence [instanceD (cxt $ map pure constraints) instanceType
             [pure dec, genLiftA2 cs, genLiftA3 cs,
              pragInlD '(Rank2.<*>) Inlinable FunLike AllPhases,
              pragInlD 'Rank2.liftA2 Inlinable FunLike AllPhases]]

unsafeDeriveApply :: Name -> Q [Dec]
unsafeDeriveApply ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Apply ty
   (constraints, dec) <- genApUnsafely cs
   sequence [instanceD (cxt $ map pure constraints) instanceType
             [pure dec, genLiftA2Unsafely cs, genLiftA3Unsafely cs,
              pragInlD '(Rank2.<*>) Inlinable FunLike AllPhases,
              pragInlD 'Rank2.liftA2 Inlinable FunLike AllPhases]]

deriveApplicative :: Name -> Q [Dec]
deriveApplicative ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Applicative ty
   (constraints, dec) <- genPure cs
   sequence [instanceD (cxt $ map pure constraints) instanceType
             [pure dec, pragInlD 'Rank2.pure Inline FunLike AllPhases]]

deriveFoldable :: Name -> Q [Dec]
deriveFoldable ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Foldable ty
   (constraints, dec) <- genFoldMap cs
   sequence [instanceD (cxt $ map pure constraints) instanceType
             [pure dec, pragInlD 'Rank2.foldMap Inlinable FunLike AllPhases]]

deriveTraversable :: Name -> Q [Dec]
deriveTraversable ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Traversable ty
   (constraints, dec) <- genTraverse cs
   sequence [instanceD (cxt $ map pure constraints) instanceType
             [pure dec, pragInlD 'Rank2.traverse Inlinable FunLike AllPhases]]

deriveDistributive :: Name -> Q [Dec]
deriveDistributive ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Distributive ty
   (constraints, dec) <- genCotraverse cs
   sequence [instanceD (cxt $ map pure constraints) instanceType
             [pure dec, pragInlD 'Rank2.cotraverse Inline FunLike AllPhases]]

deriveDistributiveTraversable :: Name -> Q [Dec]
deriveDistributiveTraversable ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.DistributiveTraversable ty
   (constraints, dec) <- genCotraverseTraversable cs
   sequence [instanceD (cxt $ map pure constraints) instanceType [pure dec]]

reifyConstructors :: Name -> Name -> Q (TypeQ, [Con])
reifyConstructors cls ty = do
   (TyConI tyCon) <- reify ty
   (tyConName, tyVars, _kind, cs) <- case tyCon of
      DataD _ nm tyVars kind cs _   -> return (nm, tyVars, kind, cs)
      NewtypeD _ nm tyVars kind c _ -> return (nm, tyVars, kind, [c])
      _ -> fail "deriveApply: tyCon may not be a type synonym."
 
   let (KindedTV tyVar (AppT (AppT ArrowT StarT) StarT)) = last tyVars
       instanceType           = conT cls `appT` foldl apply (conT tyConName) (init tyVars)
       apply t (PlainTV name)    = appT t (varT name)
       apply t (KindedTV name _) = appT t (varT name)
 
   putQ (Deriving tyConName tyVar)
   return (instanceType, cs)

genFmap :: [Con] -> Q ([Type], Dec)
genFmap cs = do (constraints, clauses) <- unzip <$> mapM genFmapClause cs
                return (concat constraints, FunD '(Rank2.<$>) clauses)

genAp :: [Con] -> Q ([Type], Dec)
genAp [con] = do (constraints, clause) <- genApClause False con
                 return (constraints, FunD '(Rank2.<*>) [clause])

genLiftA2 :: [Con] -> Q Dec
genLiftA2 [con] = funD 'Rank2.liftA2 [genLiftA2Clause False con]

genLiftA3 :: [Con] -> Q Dec
genLiftA3 [con] = funD 'Rank2.liftA3 [genLiftA3Clause False con]

genApUnsafely :: [Con] -> Q ([Type], Dec)
genApUnsafely cons = do (constraints, clauses) <- unzip <$> mapM (genApClause True) cons
                        return (concat constraints, FunD '(Rank2.<*>) clauses)

genLiftA2Unsafely :: [Con] -> Q Dec
genLiftA2Unsafely cons = funD 'Rank2.liftA2 (genLiftA2Clause True <$> cons)

genLiftA3Unsafely :: [Con] -> Q Dec
genLiftA3Unsafely cons = funD 'Rank2.liftA3 (genLiftA3Clause True <$> cons)

genPure :: [Con] -> Q ([Type], Dec)
genPure cs = do (constraints, clauses) <- unzip <$> mapM genPureClause cs
                return (concat constraints, FunD 'Rank2.pure clauses)

genFoldMap :: [Con] -> Q ([Type], Dec)
genFoldMap cs = do (constraints, clauses) <- unzip <$> mapM genFoldMapClause cs
                   return (concat constraints, FunD 'Rank2.foldMap clauses)

genTraverse :: [Con] -> Q ([Type], Dec)
genTraverse cs = do (constraints, clauses) <- unzip <$> mapM genTraverseClause cs
                    return (concat constraints, FunD 'Rank2.traverse clauses)

genCotraverse :: [Con] -> Q ([Type], Dec)
genCotraverse [con] = do (constraints, clause) <- genCotraverseClause con
                         return (constraints, FunD 'Rank2.cotraverse [clause])

genCotraverseTraversable :: [Con] -> Q ([Type], Dec)
genCotraverseTraversable [con] = do (constraints, clause) <- genCotraverseTraversableClause con
                                    return (constraints, FunD 'Rank2.cotraverseTraversable [clause])

genFmapClause :: Con -> Q ([Type], Clause)
genFmapClause (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP f, conP name (map varP fieldNames)]
       constraintsAndFields = zipWith newField fieldNames fieldTypes
       newFields = map (snd <$>) constraintsAndFields
       body = normalB $ appsE $ conE name : newFields
       newField :: Name -> BangType -> Q ([Type], Exp)
       newField x (_, fieldType) = genFmapField (varE f) fieldType (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause pats body []
genFmapClause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newNamedField fields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>)
          <$> genFmapField (varE f) fieldType (appE (varE fieldName) (varE x)) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP f, bangP (varP x)] body []
genFmapClause (GadtC [name] fieldTypes _resultType@(AppT _ (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genFmapClause (NormalC name fieldTypes)
genFmapClause (RecGadtC [name] fields _resultType@(AppT _ (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genFmapClause (RecC name fields)
genFmapClause (ForallC _vars _cxt con) = genFmapClause con

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
       body = normalB $ appsE $ conE name : zipWith newField (zip fieldNames1 fieldNames2) fieldTypes
       newField :: (Name, Name) -> BangType -> Q Exp
       newField (x, y) (_, fieldType) = genLiftA2Field unsafely (varE f) fieldType (varE x) (varE y) id
   clause pats body [valD (conP name $ map varP fieldNames2) (normalB $ varE y) []]
genLiftA2Clause unsafely (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   y <- newName "y"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          fieldExp fieldName (genLiftA2Field unsafely (varE f) fieldType (getFieldOf x) (getFieldOf y) id)
          where getFieldOf = appE (varE fieldName) . varE
   clause [varP f, bangP (varP x), varP y] body []
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
     _ | unsafely -> [| error "Cannot apply liftA2 to field" |]
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
       body = normalB $ appsE $ conE name : zipWith newField (zip3 fieldNames1 fieldNames2 fieldNames3) fieldTypes
       newField :: (Name, Name, Name) -> BangType -> Q Exp
       newField (x, y, z) (_, fieldType) = genLiftA3Field unsafely (varE f) fieldType (varE x) (varE y) (varE z) id
   clause pats body [valD (conP name $ map varP fieldNames2) (normalB $ varE y) [],
                     valD (conP name $ map varP fieldNames3) (normalB $ varE z) []]
genLiftA3Clause unsafely (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   y <- newName "y"
   z <- newName "z"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          fieldExp fieldName (genLiftA3Field unsafely (varE f) fieldType (getFieldOf x) (getFieldOf y) (getFieldOf z) id)
          where getFieldOf = appE (varE fieldName) . varE
   clause [varP f, bangP (varP x), varP y, varP z] body []
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
     _ | unsafely -> [| error "Cannot apply liftA3 to field" |]
       | otherwise -> error ("Cannot apply liftA3 to field of type " <> show fieldType)

genApClause :: Bool -> Con -> Q ([Type], Clause)
genApClause unsafely (NormalC name fieldTypes) = do
   fieldNames1 <- replicateM (length fieldTypes) (newName "x")
   fieldNames2 <- replicateM (length fieldTypes) (newName "y")
   rhsName <- newName "rhs"
   let pats = [conP name (map varP fieldNames1), varP rhsName]
       constraintsAndFields = zipWith newField (zip fieldNames1 fieldNames2) fieldTypes
       newFields = map (snd <$>) constraintsAndFields
       body = normalB $ appsE $ conE name : newFields
       newField :: (Name, Name) -> BangType -> Q ([Type], Exp)
       newField (x, y) (_, fieldType) = genApField unsafely fieldType (varE x) (varE y) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause pats body [valD (conP name $ map varP fieldNames2) (normalB $ varE rhsName) []]
genApClause unsafely (RecC name fields) = do
   x <- newName "x"
   y <- newName "y"
   let body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newNamedField fields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>) <$> genApField unsafely fieldType (getFieldOf x) (getFieldOf y) id
          where getFieldOf = appE (varE fieldName) . varE
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP x, bangP (varP y)] body []
genApClause unsafely (GadtC [name] fieldTypes _resultType@(AppT _ (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genApClause unsafely (NormalC name fieldTypes)
genApClause unsafely (RecGadtC [name] fields _resultType@(AppT _ (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genApClause unsafely (RecC name fields)
genApClause unsafely (ForallC _vars _cxt con) = genApClause unsafely con

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
     _ | unsafely -> (,) [] <$> [| error ("Cannot apply ap to field" <> $(pure $ LitE $ StringL $ show fieldType)) |]
       | otherwise -> error ("Cannot apply ap to field of type " <> show fieldType)

genPureClause :: Con -> Q ([Type], Clause)
genPureClause (NormalC name fieldTypes) = do
   argName <- newName "f"
   let body = normalB $ appsE $ conE name : ((snd <$>) <$> constraintsAndFields)
       constraintsAndFields = map newField fieldTypes
       newField :: BangType -> Q ([Type], Exp)
       newField (_, fieldType) = genPureField fieldType (varE argName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP argName] body []
genPureClause (RecC name fields) = do
   argName <- newName "f"
   let body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newNamedField fields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) = ((,) fieldName <$>) <$> genPureField fieldType (varE argName) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP argName] body []

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

genFoldMapClause :: Con -> Q ([Type], Clause)
genFoldMapClause (NormalC name fieldTypes) = do
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
   (,) constraints <$> clause pats (normalB body) []
genFoldMapClause (RecC _name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body | null fields = [| mempty |]
            | otherwise = foldr1 append $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newField fields
       append a b = [| $(a) <> $(b) |]
       newField :: VarBangType -> Q ([Type], Exp)
       newField (fieldName, _, fieldType) = genFoldMapField f fieldType (appE (varE fieldName) (varE x)) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP f, bangP (varP x)] (normalB body) []
genFoldMapClause (GadtC [name] fieldTypes _resultType@(AppT _ (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genFoldMapClause (NormalC name fieldTypes)
genFoldMapClause (RecGadtC [name] fields _resultType@(AppT _ (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genFoldMapClause (RecC name fields)
genFoldMapClause (ForallC _vars _cxt con) = genFoldMapClause con

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

genTraverseClause :: Con -> Q ([Type], Clause)
genTraverseClause (NormalC name []) =
   (,) [] <$> clause [wildP, wildP] (normalB [| pure $(conE name) |]) []
genTraverseClause (NormalC name fieldTypes) = do
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
   (,) constraints <$> clause pats body []
genTraverseClause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let constraintsAndFields = map newField fields
       body = normalB $ fst $ foldl apply (conE name, False) $ (snd <$>) <$> constraintsAndFields
       apply (a, False) b = ([| $(a) <$> $(b) |], True)
       apply (a, True) b = ([| $(a) <*> $(b) |], True)
       newField :: VarBangType -> Q ([Type], Exp)
       newField (fieldName, _, fieldType) = genTraverseField (varE f) fieldType (appE (varE fieldName) (varE x)) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP f, bangP (varP x)] body []
genTraverseClause (GadtC [name] fieldTypes _resultType@(AppT _ (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genTraverseClause (NormalC name fieldTypes)
genTraverseClause (RecGadtC [name] fields _resultType@(AppT _ (VarT tyVar))) =
   do Just (Deriving tyConName _tyVar) <- getQ
      putQ (Deriving tyConName tyVar)
      genTraverseClause (RecC name fields)
genTraverseClause (ForallC _vars _cxt con) = genTraverseClause con

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
                                   fieldType [| $(varE fieldName) <$> $(varE argName) |] id)
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP withName, varP argName] body []

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
                                   [| $(varE fieldName) <$> $(varE argName) |] id)
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP withName, varP argName] body []

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

constrain :: Name -> Type -> [Type]
constrain _ ConT{} = []
constrain cls t = [ConT cls `AppT` t]
