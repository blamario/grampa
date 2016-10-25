{-# Language TemplateHaskell #-}

module Rank2.TH where

import Control.Monad (replicateM)
import Data.Functor
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (BangType, VarBangType, getQ, putQ)

import qualified Rank2

data Deriving = Deriving { tyCon :: Name, tyVar :: Name }

-- Adapted from https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial
deriveFunctor :: Name -> Q [Dec]
deriveFunctor ty
  = do (TyConI tyCon) <- reify ty
       (tyConName, tyVars, kind, cs) <- case tyCon of
         DataD _ nm tyVars kind cs _   -> return (nm, tyVars, kind, cs)
         NewtypeD _ nm tyVars kind c _ -> return (nm, tyVars, kind, [c])
         _ -> fail "deriveFunctor: tyCon may not be a type synonym."
 
       let (KindedTV tyVar (AppT (AppT ArrowT StarT) StarT)) = last tyVars
           instanceType           = conT ''Rank2.Functor `appT`
             foldl apply (conT tyConName) (init tyVars)
 
       putQ (Deriving tyConName tyVar)
       sequence [instanceD (return []) instanceType [genFmap cs]]
  where
    apply t (PlainTV name)    = appT t (varT name)
    apply t (KindedTV name _) = appT t (varT name)

genFmap :: [Con] -> Q Dec
genFmap cs = funD 'Rank2.fmap (map genFmapClause cs)
 
genFmapClause :: Con -> Q Clause
genFmapClause (NormalC name fieldTypes)
  = do f          <- newName "f"
       fieldNames <- replicateM (length fieldTypes) (newName "x")
       let pats = varP f:[conP name (map varP fieldNames)]
           body = normalB $ appsE $ conE name : map (newField f) (zip fieldNames fieldTypes)
       clause pats body []
genFmapClause (RecC name fields)
  = do f <- newName "f"
       x <- newName "x"
       let body = normalB $ recConE name $ map (newNamedField f x) fields
       clause [varP f, varP x] body []
 
newField :: Name -> (Name, BangType) -> Q Exp
newField f (x, (_, fieldType))
  = do Just (Deriving typeCon typeVar) <- getQ
       case fieldType of
         AppT ty _
            | ty == VarT typeVar -> [| $(varE f) $(varE x) |]
         _ -> [| $(varE x) |]
 
newNamedField :: Name -> Name -> VarBangType -> Q (Name, Exp)
newNamedField f x (fieldName, _, fieldType)
  = do Just (Deriving typeCon typeVar) <- getQ
       case fieldType of
         AppT ty _
            | ty == VarT typeVar -> fieldExp fieldName [| $(varE f) ($(varE fieldName) $(varE x)) |]
         _ -> fieldExp fieldName [| $(varE x) |]
 
