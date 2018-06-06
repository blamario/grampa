-- | This module exports the templates for automatic instance deriving of "Rank2" type classes. The most common way to
-- use it would be
--
-- > import qualified Rank2.TH
-- > data MyDataType = ...
-- > $(Rank2.TH.deriveAll ''MyDataType)
--
-- or, if you're picky, you can invoke only 'deriveFunctor' and whichever other instances you need instead.

{-# Language TemplateHaskell #-}
-- Adapted from https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial

module Rank2.TH (deriveAll, deriveFunctor, deriveApply, deriveApplicative,
                 deriveFoldable, deriveTraversable, deriveDistributive, deriveDistributiveTraversable)
where

import Control.Applicative (liftA2, liftA3)
import Control.Monad (replicateM)
import Data.Distributive (cotraverse)
import Data.Monoid ((<>))
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (BangType, VarBangType, getQ, putQ)

import qualified Rank2

data Deriving = Deriving { _derivingConstructor :: Name, _derivingVariable :: Name }

deriveAll :: Name -> Q [Dec]
deriveAll ty = foldr f (pure []) [deriveFunctor, deriveApply, deriveApplicative,
                                  deriveFoldable, deriveTraversable, deriveDistributive, deriveDistributiveTraversable]
   where f derive rest = (<>) <$> derive ty <*> rest

deriveFunctor :: Name -> Q [Dec]
deriveFunctor ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Functor ty
   sequence [instanceD (return []) instanceType [genFmap cs]]

deriveApply :: Name -> Q [Dec]
deriveApply ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Apply ty
   sequence [instanceD (return []) instanceType [genAp cs, genLiftA2 cs, genLiftA3 cs]]

deriveApplicative :: Name -> Q [Dec]
deriveApplicative ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Applicative ty
   sequence [instanceD (return []) instanceType [genPure cs]]

deriveFoldable :: Name -> Q [Dec]
deriveFoldable ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Foldable ty
   sequence [instanceD (return []) instanceType [genFoldMap cs]]

deriveTraversable :: Name -> Q [Dec]
deriveTraversable ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Traversable ty
   sequence [instanceD (return []) instanceType [genTraverse cs]]

deriveDistributive :: Name -> Q [Dec]
deriveDistributive ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.Distributive ty
   sequence [instanceD (return []) instanceType [genCotraverse cs]]

deriveDistributiveTraversable :: Name -> Q [Dec]
deriveDistributiveTraversable ty = do
   (instanceType, cs) <- reifyConstructors ''Rank2.DistributiveTraversable ty
   sequence [instanceD (return []) instanceType [genCotraverseTraversable cs]]

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

genFmap :: [Con] -> Q Dec
genFmap cs = funD '(Rank2.<$>) (map genFmapClause cs)

genAp :: [Con] -> Q Dec
genAp [con] = funD '(Rank2.<*>) [genApClause con]

genLiftA2 :: [Con] -> Q Dec
genLiftA2 [con] = funD 'Rank2.liftA2 [genLiftA2Clause con]

genLiftA3 :: [Con] -> Q Dec
genLiftA3 [con] = funD 'Rank2.liftA3 [genLiftA3Clause con]

genPure :: [Con] -> Q Dec
genPure cs = funD 'Rank2.pure (map genPureClause cs)

genFoldMap :: [Con] -> Q Dec
genFoldMap cs = funD 'Rank2.foldMap (map genFoldMapClause cs)

genTraverse :: [Con] -> Q Dec
genTraverse cs = funD 'Rank2.traverse (map genTraverseClause cs)

genCotraverse :: [Con] -> Q Dec
genCotraverse [con] = funD 'Rank2.cotraverse [genCotraverseClause con]

genCotraverseTraversable :: [Con] -> Q Dec
genCotraverseTraversable [con] = funD 'Rank2.cotraverseTraversable [genCotraverseTraversableClause con]

genFmapClause :: Con -> Q Clause
genFmapClause (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP f, tildeP (conP name $ map varP fieldNames)]
       body = normalB $ appsE $ conE name : zipWith newField fieldNames fieldTypes
       newField :: Name -> BangType -> Q Exp
       newField x (_, fieldType) = genFmapField (varE f) fieldType (varE x) id
   clause pats body []
genFmapClause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          fieldExp fieldName (genFmapField (varE f) fieldType (appE (varE fieldName) (varE x)) id)
   clause [varP f, varP x] body []

genFmapField :: Q Exp -> Type -> Q Exp -> (Q Exp -> Q Exp) -> Q Exp
genFmapField fun fieldType fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _  | ty == VarT typeVar -> appE (wrap fun) fieldAccess
     AppT _ ty  | ty == VarT typeVar -> appE (wrap [| ($fun Rank2.<$>) |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar -> genFmapField fun t2 fieldAccess (wrap . appE (varE '(<$>)))
     SigT ty _kind -> genFmapField fun ty fieldAccess wrap
     ParensT ty -> genFmapField fun ty fieldAccess wrap
     _ -> fieldAccess

genLiftA2Clause :: Con -> Q Clause
genLiftA2Clause (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames1 <- replicateM (length fieldTypes) (newName "x")
   fieldNames2 <- replicateM (length fieldTypes) (newName "y")
   let pats = [varP f, tildeP (conP name $ map varP fieldNames1), tildeP (conP name $ map varP fieldNames2)]
       body = normalB $ appsE $ conE name : zipWith newField (zip fieldNames1 fieldNames2) fieldTypes
       newField :: (Name, Name) -> BangType -> Q Exp
       newField (x, y) (_, fieldType) = genLiftA2Field (varE f) fieldType (varE x) (varE y) id
   clause pats body []
genLiftA2Clause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   y <- newName "y"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          fieldExp fieldName (genLiftA2Field (varE f) fieldType (getFieldOf x) (getFieldOf y) id)
          where getFieldOf = appE (varE fieldName) . varE
   clause [varP f, varP x, varP y] body []

genLiftA2Field :: Q Exp -> Type -> Q Exp -> Q Exp -> (Q Exp -> Q Exp) -> Q Exp
genLiftA2Field fun fieldType field1Access field2Access wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> [| $(wrap fun) $field1Access $field2Access |]
     AppT _ ty | ty == VarT typeVar -> [| $(wrap $ appE (varE 'Rank2.liftA2) fun) $field1Access $field2Access |]
     AppT t1 t2 | t1 /= VarT typeVar -> genLiftA2Field fun t2 field1Access field2Access (appE (varE 'liftA2) . wrap)
     SigT ty _kind -> genLiftA2Field fun ty field1Access field2Access wrap
     ParensT ty -> genLiftA2Field fun ty field1Access field2Access wrap
     _ -> error ("Cannot apply liftA2 to field of type " <> show fieldType)

genLiftA3Clause :: Con -> Q Clause
genLiftA3Clause (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames1 <- replicateM (length fieldTypes) (newName "x")
   fieldNames2 <- replicateM (length fieldTypes) (newName "y")
   fieldNames3 <- replicateM (length fieldTypes) (newName "z")
   let pats = [varP f, tildeP (conP name $ map varP fieldNames1), tildeP (conP name $ map varP fieldNames2), 
               tildeP (conP name $ map varP fieldNames3)]
       body = normalB $ appsE $ conE name : zipWith newField (zip3 fieldNames1 fieldNames2 fieldNames3) fieldTypes
       newField :: (Name, Name, Name) -> BangType -> Q Exp
       newField (x, y, z) (_, fieldType) = genLiftA3Field (varE f) fieldType (varE x) (varE y) (varE z) id
   clause pats body []
genLiftA3Clause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   y <- newName "y"
   z <- newName "z"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          fieldExp fieldName (genLiftA3Field (varE f) fieldType (getFieldOf x) (getFieldOf y) (getFieldOf z) id)
          where getFieldOf = appE (varE fieldName) . varE
   clause [varP f, varP x, varP y, varP z] body []

genLiftA3Field :: Q Exp -> Type -> Q Exp -> Q Exp -> Q Exp -> (Q Exp -> Q Exp) -> Q Exp
genLiftA3Field fun fieldType field1Access field2Access field3Access wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _
        | ty == VarT typeVar -> [| $(wrap fun) $(field1Access) $(field2Access) $(field3Access) |]
     AppT _ ty
        | ty == VarT typeVar -> [| $(wrap $ appE (varE 'Rank2.liftA3) fun) $(field1Access) $(field2Access) $(field3Access) |]
     AppT t1 t2
        | t1 /= VarT typeVar
          -> genLiftA3Field fun t2 field1Access field2Access field3Access (appE (varE 'liftA3) . wrap)
     SigT ty _kind -> genLiftA3Field fun ty field1Access field2Access field3Access wrap
     ParensT ty -> genLiftA3Field fun ty field1Access field2Access field3Access wrap
     _ -> error ("Cannot apply liftA3 to field of type " <> show fieldType)

genApClause :: Con -> Q Clause
genApClause (NormalC name fieldTypes) = do
   fieldNames1 <- replicateM (length fieldTypes) (newName "x")
   fieldNames2 <- replicateM (length fieldTypes) (newName "y")
   let pats = [tildeP (conP name $ map varP fieldNames1), tildeP (conP name $ map varP fieldNames2)]
       body = normalB $ appsE $ conE name : zipWith newField (zip fieldNames1 fieldNames2) fieldTypes
       newField :: (Name, Name) -> BangType -> Q Exp
       newField (x, y) (_, fieldType) = genApField fieldType (varE x) (varE y) id
   clause pats body []
genApClause (RecC name fields) = do
   x <- newName "x"
   y <- newName "y"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          fieldExp fieldName (genApField fieldType (getFieldOf x) (getFieldOf y) id)
          where getFieldOf = appE (varE fieldName) . varE
   clause [varP x, varP y] body []

genApField :: Type -> Q Exp -> Q Exp -> (Q Exp -> Q Exp) -> Q Exp
genApField fieldType field1Access field2Access wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> [| $(wrap (varE 'Rank2.apply)) $(field1Access) $(field2Access) |]
     AppT _ ty | ty == VarT typeVar -> [| $(wrap (varE 'Rank2.ap)) $(field1Access) $(field2Access) |]
     AppT t1 t2 | t1 /= VarT typeVar -> genApField t2 field1Access field2Access (appE (varE 'liftA2) . wrap)
     SigT ty _kind -> genApField ty field1Access field2Access wrap
     ParensT ty -> genApField ty field1Access field2Access wrap
     _ -> error ("Cannot apply ap to field of type " <> show fieldType)

genPureClause :: Con -> Q Clause
genPureClause (NormalC name fieldTypes) = do
   argName <- newName "f"
   let body = normalB $ appsE $ conE name : map newField fieldTypes
       newField :: BangType -> Q Exp
       newField (_, fieldType) = genPureField fieldType (varE argName) id
   clause [varP argName] body []
genPureClause (RecC name fields) = do
   argName <- newName "f"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) = fieldExp fieldName (genPureField fieldType (varE argName) id)
   clause [varP argName] body []

genPureField :: Type -> Q Exp -> (Q Exp -> Q Exp) -> Q Exp
genPureField fieldType pureValue wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> wrap pureValue
     AppT _ ty | ty == VarT typeVar -> wrap (appE (varE 'Rank2.pure) pureValue)
     AppT t1 t2 | t1 /= VarT typeVar -> genPureField t2 pureValue (wrap . appE (varE 'pure))
     SigT ty _kind -> genPureField ty pureValue wrap
     ParensT ty -> genPureField ty pureValue wrap
     _ -> error ("Cannot create a pure field of type " <> show fieldType)

genFoldMapClause :: Con -> Q Clause
genFoldMapClause (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP f, tildeP (conP name $ map varP fieldNames)]
       body = normalB $ foldr1 append $ zipWith newField fieldNames fieldTypes
       append a b = [| $(a) <> $(b) |]
       newField :: Name -> BangType -> Q Exp
       newField x (_, fieldType) = genFoldMapField f fieldType (varE x) id
   clause pats body []
genFoldMapClause (RecC _name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ foldr1 append $ map newField fields
       append a b = [| $(a) <> $(b) |]
       newField :: VarBangType -> Q Exp
       newField (fieldName, _, fieldType) = genFoldMapField f fieldType (appE (varE fieldName) (varE x)) id
   clause [varP f, varP x] body []

genFoldMapField :: Name -> Type -> Q Exp -> (Q Exp -> Q Exp) -> Q Exp
genFoldMapField funcName fieldType fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> appE (wrap $ varE funcName) fieldAccess
     AppT _ ty | ty == VarT typeVar -> appE (wrap $ appE (varE 'Rank2.foldMap) (varE funcName)) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar -> genFoldMapField funcName t2 fieldAccess (wrap . appE (varE 'foldMap))
     SigT ty _kind -> genFoldMapField funcName ty fieldAccess wrap
     ParensT ty -> genFoldMapField funcName ty fieldAccess wrap
     _ -> fieldAccess

genTraverseClause :: Con -> Q Clause
genTraverseClause (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP f, tildeP (conP name $ map varP fieldNames)]
       body = normalB $ fst $ foldl apply (conE name, False) $ zipWith newField fieldNames fieldTypes
       apply (a, False) b = ([| $(a) <$> $(b) |], True)
       apply (a, True) b = ([| $(a) <*> $(b) |], True)
       newField :: Name -> BangType -> Q Exp
       newField x (_, fieldType) = genTraverseField (varE f) fieldType (varE x) id
   clause pats body []
genTraverseClause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ fst $ foldl apply (conE name, False) $ map newField fields
       apply (a, False) b = ([| $(a) <$> $(b) |], True)
       apply (a, True) b = ([| $(a) <*> $(b) |], True)
       newField :: VarBangType -> Q Exp
       newField (fieldName, _, fieldType) = genTraverseField (varE f) fieldType (appE (varE fieldName) (varE x)) id
   clause [varP f, varP x] body []

genTraverseField :: Q Exp -> Type -> Q Exp -> (Q Exp -> Q Exp) -> Q Exp
genTraverseField fun fieldType fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> appE (wrap fun) fieldAccess
     AppT _ ty | ty == VarT typeVar -> appE (wrap [| Rank2.traverse $fun |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar -> genTraverseField fun t2 fieldAccess (wrap . appE (varE 'traverse))
     SigT ty _kind -> genTraverseField fun ty fieldAccess wrap
     ParensT ty -> genTraverseField fun ty fieldAccess wrap
     _ -> fieldAccess

genCotraverseClause :: Con -> Q Clause
genCotraverseClause (RecC name fields) = do
   withName <- newName "w"
   argName <- newName "f"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          fieldExp fieldName (genCotraverseField (varE 'Rank2.cotraverse) (varE withName) fieldType
                              [| $(varE fieldName) <$> $(varE argName) |] id)
   clause [varP withName, varP argName] body []

genCotraverseTraversableClause :: Con -> Q Clause
genCotraverseTraversableClause (RecC name fields) = do
   withName <- newName "w"
   argName <- newName "f"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          fieldExp fieldName (genCotraverseField (varE 'Rank2.cotraverseTraversable) (varE withName) fieldType
                              [| $(varE fieldName) <$> $(varE argName) |] id)
   clause [varP withName, varP argName] body []

genCotraverseField :: Q Exp -> Q Exp -> Type -> Q Exp -> (Q Exp -> Q Exp) -> Q Exp
genCotraverseField method fun fieldType fieldAccess wrap = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> appE (wrap fun) fieldAccess
     AppT _ ty | ty == VarT typeVar -> appE (wrap $ appE method fun) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar -> genCotraverseField method fun t2 fieldAccess (wrap . appE (varE 'cotraverse))
     SigT ty _kind -> genCotraverseField method fun ty fieldAccess wrap
     ParensT ty -> genCotraverseField method fun ty fieldAccess wrap
