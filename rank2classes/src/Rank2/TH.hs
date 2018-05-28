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

import Control.Monad (replicateM)
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
       newField x (_, fieldType) = genFmapField f fieldType (varE x) id
   clause pats body []
genFmapClause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          genFmapField f fieldType (appE (varE fieldName) (varE x)) (fieldExp fieldName)
   clause [varP f, varP x] body []

genFmapField :: Name -> Type -> Q Exp -> (Q Exp -> Q a) -> Q a
genFmapField funcName fieldType fieldAccess cont = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> cont (appE (varE funcName) fieldAccess)
     AppT _ ty | ty == VarT typeVar -> cont [| Rank2.fmap $(varE funcName) $(fieldAccess) |]
     _ -> cont fieldAccess

genLiftA2Clause :: Con -> Q Clause
genLiftA2Clause (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames1 <- replicateM (length fieldTypes) (newName "x")
   fieldNames2 <- replicateM (length fieldTypes) (newName "y")
   let pats = [varP f, tildeP (conP name $ map varP fieldNames1), tildeP (conP name $ map varP fieldNames2)]
       body = normalB $ appsE $ conE name : zipWith newField (zip fieldNames1 fieldNames2) fieldTypes
       newField :: (Name, Name) -> BangType -> Q Exp
       newField (x, y) (_, fieldType) = genLiftA2Field f fieldType (varE x) (varE y) id
   clause pats body []
genLiftA2Clause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   y <- newName "y"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          genLiftA2Field f fieldType (getFieldOf x) (getFieldOf y) (fieldExp fieldName)
          where getFieldOf = appE (varE fieldName) . varE
   clause [varP f, varP x, varP y] body []

genLiftA2Field :: Name -> Type -> Q Exp -> Q Exp -> (Q Exp -> Q a) -> Q a
genLiftA2Field funcName fieldType field1Access field2Access cont = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _
        | ty == VarT typeVar -> cont [| $(varE funcName) $(field1Access) $(field2Access) |]
     AppT _ ty
        | ty == VarT typeVar -> cont [| Rank2.liftA2 $(varE funcName) $(field1Access) $(field2Access) |]
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
       newField (x, y, z) (_, fieldType) = genLiftA3Field f fieldType (varE x) (varE y) (varE z) id
   clause pats body []
genLiftA3Clause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   y <- newName "y"
   z <- newName "z"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) =
          genLiftA3Field f fieldType (getFieldOf x) (getFieldOf y) (getFieldOf z) (fieldExp fieldName)
          where getFieldOf = appE (varE fieldName) . varE
   clause [varP f, varP x, varP y, varP z] body []

genLiftA3Field :: Name -> Type -> Q Exp -> Q Exp -> Q Exp -> (Q Exp -> Q a) -> Q a
genLiftA3Field funcName fieldType field1Access field2Access field3Access cont = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _
        | ty == VarT typeVar -> cont [| $(varE funcName) $(field1Access) $(field2Access) $(field3Access) |]
     AppT _ ty
        | ty == VarT typeVar -> cont [| Rank2.liftA3 $(varE funcName) $(field1Access) $(field2Access) $(field3Access) |]
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
       newNamedField (fieldName, _, fieldType) = genApField fieldType (getFieldOf x) (getFieldOf y) (fieldExp fieldName)
          where getFieldOf = appE (varE fieldName) . varE
   clause [varP x, varP y] body []

genApField :: Type -> Q Exp -> Q Exp -> (Q Exp -> Q a) -> Q a
genApField fieldType field1Access field2Access cont = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _
        | ty == VarT typeVar -> cont [| Rank2.apply $(field1Access) $(field2Access) |]
     AppT _ ty
        | ty == VarT typeVar -> cont [| Rank2.ap $(field1Access) $(field2Access) |]
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
       newNamedField (fieldName, _, fieldType) = genPureField fieldType (varE argName) (fieldExp fieldName)
   clause [varP argName] body []

genPureField :: Type -> Q Exp -> (Q Exp -> Q a) -> Q a
genPureField fieldType pureValue cont = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> cont pureValue
     AppT _ ty | ty == VarT typeVar -> cont (appE (varE 'Rank2.pure) pureValue)
     _ -> error ("Cannot create a pure field of type " <> show fieldType)

genFoldMapClause :: Con -> Q Clause
genFoldMapClause (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP f, tildeP (conP name $ map varP fieldNames)]
       body = normalB $ foldr1 append $ zipWith newField fieldNames fieldTypes
       append a b = [| $(a) <> $(b) |]
       newField :: Name -> BangType -> Q Exp
       newField x (_, fieldType) = genFoldMapField f fieldType (varE x)
   clause pats body []
genFoldMapClause (RecC _name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ foldr1 append $ map newField fields
       append a b = [| $(a) <> $(b) |]
       newField :: VarBangType -> Q Exp
       newField (fieldName, _, fieldType) = genFoldMapField f fieldType (appE (varE fieldName) (varE x))
   clause [varP f, varP x] body []

genFoldMapField :: Name -> Type -> Q Exp -> Q Exp
genFoldMapField funcName fieldType fieldAccess = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> appE (varE funcName) fieldAccess
     AppT _ ty | ty == VarT typeVar -> [| Rank2.foldMap $(varE funcName) $(fieldAccess) |]
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
       newField x (_, fieldType) = genTraverseField f fieldType (varE x)
   clause pats body []
genTraverseClause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ fst $ foldl apply (conE name, False) $ map newField fields
       apply (a, False) b = ([| $(a) <$> $(b) |], True)
       apply (a, True) b = ([| $(a) <*> $(b) |], True)
       newField :: VarBangType -> Q Exp
       newField (fieldName, _, fieldType) = genTraverseField f fieldType (appE (varE fieldName) (varE x))
   clause [varP f, varP x] body []

genTraverseField :: Name -> Type -> Q Exp -> Q Exp
genTraverseField funcName fieldType fieldAccess = do
   Just (Deriving _ typeVar) <- getQ
   case fieldType of
     AppT ty _ | ty == VarT typeVar -> appE (varE funcName) fieldAccess
     AppT _ ty | ty == VarT typeVar -> [| Rank2.traverse $(varE funcName) $(fieldAccess) |]
     _ -> fieldAccess

genCotraverseClause :: Con -> Q Clause
genCotraverseClause (RecC name fields) = do
   withName <- newName "w"
   argName <- newName "f"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _
                | ty == VarT typeVar -> fieldExp fieldName [| $(varE withName) ($(varE fieldName) <$> $(varE argName)) |]
             AppT _ ty
                | ty == VarT typeVar ->
                  fieldExp fieldName [| Rank2.cotraverse $(varE withName) ($(varE fieldName) <$> $(varE argName)) |]
   clause [varP withName, varP argName] body []

genCotraverseTraversableClause :: Con -> Q Clause
genCotraverseTraversableClause (RecC name fields) = do
   withName <- newName "w"
   argName <- newName "f"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _
                | ty == VarT typeVar -> fieldExp fieldName [| $(varE withName) ($(varE fieldName) <$> $(varE argName)) |]
             AppT _ ty
                | ty == VarT typeVar ->
                  fieldExp fieldName [| Rank2.cotraverseTraversable $(varE withName) ($(varE fieldName) <$> $(varE argName)) |]
   clause [varP withName, varP argName] body []
