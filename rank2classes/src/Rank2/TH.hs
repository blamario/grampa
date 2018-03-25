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
genAp cs = funD '(Rank2.<*>) (map genApClause cs)

genLiftA2 :: [Con] -> Q Dec
genLiftA2 cs = funD 'Rank2.liftA2 (map genLiftA2Clause cs)

genLiftA3 :: [Con] -> Q Dec
genLiftA3 cs = funD 'Rank2.liftA3 (map genLiftA3Clause cs)

genPure :: [Con] -> Q Dec
genPure cs = funD 'Rank2.pure (map genPureClause cs)

genFoldMap :: [Con] -> Q Dec
genFoldMap cs = funD 'Rank2.foldMap (map genFoldMapClause cs)

genTraverse :: [Con] -> Q Dec
genTraverse cs = funD 'Rank2.traverse (map genTraverseClause cs)

genCotraverse :: [Con] -> Q Dec
genCotraverse cs = funD 'Rank2.cotraverse (map genCotraverseClause cs)

genCotraverseTraversable :: [Con] -> Q Dec
genCotraverseTraversable cs = funD 'Rank2.cotraverseTraversable (map genCotraverseTraversableClause cs)

genFmapClause :: Con -> Q Clause
genFmapClause (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP f, tildeP (conP name $ map varP fieldNames)]
       body = normalB $ appsE $ conE name : zipWith newField fieldNames fieldTypes
       newField :: Name -> BangType -> Q Exp
       newField x (_, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _ | ty == VarT typeVar -> [| $(varE f) $(varE x) |]
             AppT _ ty | ty == VarT typeVar -> [| Rank2.fmap $(varE f) $(varE x) |]
             _ -> [| $(varE x) |]
   clause pats body []
genFmapClause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _
                | ty == VarT typeVar -> fieldExp fieldName [| $(varE f) ($(varE fieldName) $(varE x)) |]
             AppT _ ty
                | ty == VarT typeVar -> fieldExp fieldName [| Rank2.fmap $(varE f) ($(varE fieldName) $(varE x)) |]
             _ -> fieldExp fieldName [| $(varE fieldName) $(varE x) |]
   clause [varP f, varP x] body []

genLiftA2Clause :: Con -> Q Clause
genLiftA2Clause (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames1 <- replicateM (length fieldTypes) (newName "x")
   fieldNames2 <- replicateM (length fieldTypes) (newName "y")
   let pats = [varP f, tildeP (conP name $ map varP fieldNames1), tildeP (conP name $ map varP fieldNames2)]
       body = normalB $ appsE $ conE name : zipWith newField (zip fieldNames1 fieldNames2) fieldTypes
       newField :: (Name, Name) -> BangType -> Q Exp
       newField (x, y) (_, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _ | ty == VarT typeVar -> [| $(varE f) $(varE x) $(varE y) |]
             AppT _ ty | ty == VarT typeVar -> [| Rank2.liftA2 $(varE f) $(varE x) $(varE y) |]
   clause pats body []
genLiftA2Clause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   y <- newName "y"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _
                | ty == VarT typeVar -> fieldExp fieldName [| $(varE f) ($(varE fieldName) $(varE x)) 
                                                                        ($(varE fieldName) $(varE y)) |]
             AppT _ ty
                | ty == VarT typeVar -> fieldExp fieldName [| Rank2.liftA2 $(varE f) ($(varE fieldName) $(varE x)) 
                                                                                     ($(varE fieldName) $(varE y)) |]
   clause [varP f, varP x, varP y] body []

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
       newField (x, y, z) (_, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _ | ty == VarT typeVar -> [| $(varE f) $(varE x) $(varE y) $(varE z) |]
             AppT _ ty | ty == VarT typeVar -> [| Rank2.liftA3 $(varE f) $(varE x) $(varE y) $(varE z) |]
   clause pats body []
genLiftA3Clause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   y <- newName "y"
   z <- newName "z"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _
                | ty == VarT typeVar -> fieldExp fieldName [| $(varE f) ($(varE fieldName) $(varE x))
                                                                        ($(varE fieldName) $(varE y))
                                                                        ($(varE fieldName) $(varE z)) |]
             AppT _ ty
                | ty == VarT typeVar -> fieldExp fieldName [| Rank2.liftA3 $(varE f) ($(varE fieldName) $(varE x))
                                                                                     ($(varE fieldName) $(varE y))
                                                                                     ($(varE fieldName) $(varE z)) |]
   clause [varP f, varP x, varP y, varP z] body []

genApClause :: Con -> Q Clause
genApClause (NormalC name fieldTypes) = do
   fieldNames1 <- replicateM (length fieldTypes) (newName "x")
   fieldNames2 <- replicateM (length fieldTypes) (newName "y")
   let pats = [tildeP (conP name $ map varP fieldNames1), tildeP (conP name $ map varP fieldNames2)]
       body = normalB $ appsE $ conE name : zipWith newField (zip fieldNames1 fieldNames2) fieldTypes
       newField :: (Name, Name) -> BangType -> Q Exp
       newField (x, y) (_, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _ | ty == VarT typeVar -> [| Rank2.apply $(varE x) $(varE y) |]
             AppT _ ty | ty == VarT typeVar -> [| Rank2.ap $(varE x) $(varE y) |]
   clause pats body []
genApClause (RecC name fields) = do
   x <- newName "x"
   y <- newName "y"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _ | ty == VarT typeVar -> fieldExp fieldName [| $(varE fieldName) $(varE x) `Rank2.apply`
                                                                       $(varE fieldName) $(varE y) |]
             AppT _ ty | ty == VarT typeVar -> fieldExp fieldName [| $(varE fieldName) $(varE x) `Rank2.ap`
                                                                       $(varE fieldName) $(varE y) |]
   clause [varP x, varP y] body []

genPureClause :: Con -> Q Clause
genPureClause (NormalC name fieldTypes) = do
   argName <- newName "f"
   let body = normalB $ appsE $ conE name : map newField fieldTypes
       newField :: BangType -> Q Exp
       newField (_, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _ | ty == VarT typeVar -> varE argName
             AppT _ ty | ty == VarT typeVar -> appE (varE 'Rank2.pure) (varE argName)
   clause [varP argName] body []
genPureClause (RecC name fields) = do
   argName <- newName "f"
   let body = normalB $ recConE name $ map newNamedField fields
       newNamedField :: VarBangType -> Q (Name, Exp)
       newNamedField (fieldName, _, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _ | ty == VarT typeVar -> fieldExp fieldName (varE argName)
             AppT _ ty | ty == VarT typeVar -> fieldExp fieldName (appE (varE 'Rank2.pure) $ varE argName)
   clause [varP argName] body []

genFoldMapClause :: Con -> Q Clause
genFoldMapClause (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP f, tildeP (conP name $ map varP fieldNames)]
       body = normalB $ foldr1 append $ zipWith newField fieldNames fieldTypes
       append a b = [| $(a) <> $(b) |]
       newField :: Name -> BangType -> Q Exp
       newField x (_, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _ | ty == VarT typeVar -> [| $(varE f) $(varE x) |]
             AppT _ ty | ty == VarT typeVar -> [| Rank2.foldMap $(varE f) $(varE x) |]
             _ -> [| $(varE x) |]
   clause pats body []
genFoldMapClause (RecC _name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ foldr1 append $ map newField fields
       append a b = [| $(a) <> $(b) |]
       newField :: VarBangType -> Q Exp
       newField (fieldName, _, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _ | ty == VarT typeVar -> [| $(varE f) ($(varE fieldName) $(varE x)) |]
             AppT _ ty | ty == VarT typeVar -> [| Rank2.foldMap $(varE f) ($(varE fieldName) $(varE x)) |]
             _ -> [| $(varE x) |]
   clause [varP f, varP x] body []

genTraverseClause :: Con -> Q Clause
genTraverseClause (NormalC name fieldTypes) = do
   f          <- newName "f"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP f, tildeP (conP name $ map varP fieldNames)]
       body = normalB $ fst $ foldl apply (conE name, False) $ zipWith newField fieldNames fieldTypes
       apply (a, False) b = ([| $(a) <$> $(b) |], True)
       apply (a, True) b = ([| $(a) <*> $(b) |], True)
       newField :: Name -> BangType -> Q Exp
       newField x (_, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _ | ty == VarT typeVar -> [| $(varE f) $(varE x) |]
             AppT _ ty | ty == VarT typeVar -> [| Rank2.traverse $(varE f) $(varE x) |]
             _ -> [| $(varE x) |]
   clause pats body []
genTraverseClause (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ fst $ foldl apply (conE name, False) $ map newField fields
       apply (a, False) b = ([| $(a) <$> $(b) |], True)
       apply (a, True) b = ([| $(a) <*> $(b) |], True)
       newField :: VarBangType -> Q Exp
       newField (fieldName, _, fieldType) = do
          Just (Deriving _ typeVar) <- getQ
          case fieldType of
             AppT ty _ | ty == VarT typeVar -> [| $(varE f) ($(varE fieldName) $(varE x)) |]
             AppT _ ty | ty == VarT typeVar -> [| Rank2.traverse $(varE f) ($(varE fieldName) $(varE x)) |]
             _ -> [| $(varE x) |]
   clause [varP f, varP x] body []

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
