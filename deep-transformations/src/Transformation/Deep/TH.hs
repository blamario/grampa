-- | This module exports the templates for automatic instance deriving of "Transformation.Deep" type classes. The most
-- common way to use it would be
--
-- > import qualified Transformation.Deep.TH
-- > data MyDataType f' f = ...
-- > $(Transformation.Deep.TH.deriveFunctor ''MyDataType)
--

{-# Language TemplateHaskell #-}
-- Adapted from https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial

module Transformation.Deep.TH (deriveAll, deriveFunctor, deriveFoldable, deriveDownTraversable, deriveUpTraversable)
where

import Control.Monad (replicateM)
import Data.Monoid ((<>))
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (BangType, VarBangType, getQ, putQ)

import qualified Transformation
import qualified Transformation.Deep
import qualified Rank2.TH


data Deriving = Deriving { _constructor :: Name, _variableN :: Name, _variable1 :: Name }

deriveAll :: Name -> Q [Dec]
deriveAll ty = foldr f (pure []) [Rank2.TH.deriveFunctor, Rank2.TH.deriveFoldable, Rank2.TH.deriveTraversable,
                                  Transformation.Deep.TH.deriveFunctor, Transformation.Deep.TH.deriveFoldable,
                                  Transformation.Deep.TH.deriveDownTraversable,
                                  Transformation.Deep.TH.deriveUpTraversable]
   where f derive rest = (<>) <$> derive ty <*> rest

deriveFunctor :: Name -> Q [Dec]
deriveFunctor ty = do
   t <- varT <$> newName "t"
   p <- varT <$> newName "p"
   q <- varT <$> newName "q"
   let deepConstraint ty = conT ''Transformation.Deep.Functor `appT` t `appT` ty `appT` p `appT` q
       shallowConstraint ty =
          conT ''Transformation.Functor `appT` t `appT` p `appT` q `appT` (ty `appT` q `appT` q)
   (instanceType, cs) <- reifyConstructors ty
   (constraints, dec) <- genDeepmap deepConstraint shallowConstraint cs
   sequence [instanceD (cxt (appT (conT ''Functor) p : map pure constraints))
                       (deepConstraint instanceType)
                       [pure dec]]

deriveFoldable :: Name -> Q [Dec]
deriveFoldable ty = do
   t <- varT <$> newName "t"
   f <- varT <$> newName "f"
   m <- varT <$> newName "m"
   let deepConstraint ty = conT ''Transformation.Deep.Foldable `appT` t `appT` ty `appT` f `appT` m
       shallowConstraint ty =
          conT ''Transformation.Foldable `appT` t `appT` f `appT` m `appT` (ty `appT` f `appT` f)
   (instanceType, cs) <- reifyConstructors ty
   (constraints, dec) <- genFoldMap deepConstraint shallowConstraint cs
   sequence [instanceD (cxt (appT (conT ''Monoid) m : appT (conT ''Foldable) f : map pure constraints))
                       (deepConstraint instanceType)
                       [pure dec]]

deriveDownTraversable :: Name -> Q [Dec]
deriveDownTraversable ty = do
   t <- varT <$> newName "t"
   p <- varT <$> newName "p"
   q <- varT <$> newName "q"
   m <- varT <$> newName "m"
   let deepConstraint ty = conT ''Transformation.Deep.DownTraversable `appT` t `appT` ty `appT` p `appT` q `appT` m
       shallowConstraint ty =
          conT ''Transformation.Traversable `appT` t `appT` p `appT` q `appT` m `appT` (ty `appT` p `appT` p)
   (instanceType, cs) <- reifyConstructors ty
   (constraints, dec) <- genTraverseDown deepConstraint shallowConstraint cs
   sequence [instanceD (cxt (appT (conT ''Monad) m : appT (conT ''Traversable) q : map pure constraints))
                       (deepConstraint instanceType)
                       [pure dec]]

deriveUpTraversable :: Name -> Q [Dec]
deriveUpTraversable ty = do
   t <- varT <$> newName "t"
   p <- varT <$> newName "p"
   q <- varT <$> newName "q"
   m <- varT <$> newName "m"
   let deepConstraint ty = conT ''Transformation.Deep.UpTraversable `appT` t `appT` ty `appT` p `appT` q `appT` m
       shallowConstraint ty =
          conT ''Transformation.Traversable `appT` t `appT` p `appT` q `appT` m `appT` (ty `appT` q `appT` q)
   (instanceType, cs) <- reifyConstructors ty
   (constraints, dec) <- genTraverseUp deepConstraint shallowConstraint cs
   sequence [instanceD (cxt (appT (conT ''Monad) m : appT (conT ''Traversable) p : map pure constraints))
                       (deepConstraint instanceType)
                       [pure dec]]

reifyConstructors :: Name -> Q (TypeQ, [Con])
reifyConstructors ty = do
   (TyConI tyCon) <- reify ty
   (tyConName, tyVars, _kind, cs) <- case tyCon of
      DataD _ nm tyVars kind cs _   -> return (nm, tyVars, kind, cs)
      NewtypeD _ nm tyVars kind c _ -> return (nm, tyVars, kind, [c])
      _ -> fail "deriveApply: tyCon may not be a type synonym."

   let (KindedTV tyVar  (AppT (AppT ArrowT StarT) StarT) :
        KindedTV tyVar' (AppT (AppT ArrowT StarT) StarT) : _) = reverse tyVars
       instanceType           = foldl apply (conT tyConName) (reverse $ drop 2 $ reverse tyVars)
       apply t (PlainTV name)    = appT t (varT name)
       apply t (KindedTV name _) = appT t (varT name)

   putQ (Deriving tyConName tyVar' tyVar)
   return (instanceType, cs)

genDeepmap :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> [Con] -> Q ([Type], Dec)
genDeepmap deepConstraint shallowConstraint cs = do
   (constraints, clauses) <- unzip <$> mapM (genDeepmapClause deepConstraint shallowConstraint) cs
   return (concat constraints, FunD '(Transformation.Deep.<$>) clauses)

genFoldMap :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> [Con] -> Q ([Type], Dec)
genFoldMap deepConstraint shallowConstraint cs = do
   (constraints, clauses) <- unzip <$> mapM (genFoldMapClause deepConstraint shallowConstraint) cs
   return (concat constraints, FunD 'Transformation.Deep.foldMap clauses)

genTraverseDown :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> [Con] -> Q ([Type], Dec)
genTraverseDown deepConstraint shallowConstraint cs = do
   (constraints, clauses) <- unzip <$> mapM (genTraverseClause genTraverseDownField deepConstraint shallowConstraint) cs
   return (concat constraints, FunD 'Transformation.Deep.traverseDown clauses)

genTraverseUp :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> [Con] -> Q ([Type], Dec)
genTraverseUp deepConstraint shallowConstraint cs = do
   (constraints, clauses) <- unzip <$> mapM (genTraverseClause genTraverseUpField deepConstraint shallowConstraint) cs
   return (concat constraints, FunD 'Transformation.Deep.traverseUp clauses)

genDeepmapClause :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> Con -> Q ([Type], Clause)
genDeepmapClause deepConstraint shallowConstraint (NormalC name fieldTypes) = do
   t          <- newName "t"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP t, parensP (conP name $ map varP fieldNames)]
       constraintsAndFields = zipWith newField fieldNames fieldTypes
       newFields = map (snd <$>) constraintsAndFields
       body = normalB $ appsE $ conE name : newFields
       newField :: Name -> BangType -> Q ([Type], Exp)
       newField x (_, fieldType) = genDeepmapField (varE t) fieldType deepConstraint shallowConstraint (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause pats body []
genDeepmapClause deepConstraint shallowConstraint (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newNamedField fields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>)
          <$> genDeepmapField (varE f) fieldType deepConstraint shallowConstraint (appE (varE fieldName) (varE x)) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP f, varP x] body []

genFoldMapClause :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> Con -> Q ([Type], Clause)
genFoldMapClause deepConstraint shallowConstraint (NormalC name fieldTypes) = do
   t          <- newName "t"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP t, parensP (conP name $ map varP fieldNames)]
       constraintsAndFields = zipWith newField fieldNames fieldTypes
       newFields = map (snd <$>) constraintsAndFields
       body | null newFields = [| mempty |]
            | otherwise = foldr1 append newFields
       append a b = [| $(a) <> $(b) |]
       newField :: Name -> BangType -> Q ([Type], Exp)
       newField x (_, fieldType) = genFoldMapField (varE t) fieldType deepConstraint shallowConstraint (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause pats (normalB body) []
genFoldMapClause deepConstraint shallowConstraint (RecC _name fields) = do
   t <- newName "t"
   x <- newName "x"
   let body | null fields = [| mempty |]
            | otherwise = foldr1 append $ (snd <$>) <$> constraintsAndFields
       append a b = [| $(a) <> $(b) |]
       constraintsAndFields = map newNamedField fields
       newNamedField :: VarBangType -> Q ([Type], Exp)
       newNamedField (fieldName, _, fieldType) =
          genFoldMapField (varE t) fieldType deepConstraint shallowConstraint (appE (varE fieldName) (varE x)) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP t, varP x] (normalB body) []

type GenTraverseFieldType = Q Exp -> Type -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Exp -> (Q Exp -> Q Exp)
                            -> Q ([Type], Exp)

genTraverseClause :: GenTraverseFieldType -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Con -> Q ([Type], Clause)
genTraverseClause genTraverseField deepConstraint shallowConstraint (NormalC name fieldTypes) = do
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
       newField x (_, fieldType) = genTraverseField (varE t) fieldType deepConstraint shallowConstraint (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause pats (normalB body) []
genTraverseClause genTraverseField deepConstraint shallowConstraint (RecC name fields) = do
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
          <$> genTraverseField (varE f) fieldType deepConstraint shallowConstraint (appE (varE fieldName) (varE x)) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP f, varP x] (normalB body) []

genDeepmapField :: Q Exp -> Type -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Exp -> (Q Exp -> Q Exp)
                -> Q ([Type], Exp)
genDeepmapField trans fieldType deepConstraint shallowConstraint fieldAccess wrap = do
   Just (Deriving _ typeVarN typeVar1) <- getQ
   case fieldType of
     AppT ty (AppT (AppT con v1) v2) | ty == VarT typeVar1, v1 == VarT typeVarN, v2 == VarT typeVarN ->
        (,) <$> ((:) <$> deepConstraint (pure con) <*> ((:[]) <$> shallowConstraint (pure con)))
            <*> appE (wrap [| (Transformation.fmap $trans . (Transformation.Deep.fmap $trans <$>)) |]) fieldAccess
     AppT ty _  | ty == VarT typeVar1 ->
                  (,) [] <$> (wrap (varE 'Transformation.fmap `appE` trans) `appE` fieldAccess)
     AppT (AppT con v1) v2 | v1 == VarT typeVarN, v2 == VarT typeVar1 ->
        (,) <$> ((:[]) <$> deepConstraint (pure con))
            <*> appE (wrap [| Transformation.Deep.fmap $trans |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar1 ->
        genDeepmapField trans t2 deepConstraint shallowConstraint fieldAccess (wrap . appE (varE '(<$>)))
     SigT ty _kind -> genDeepmapField trans ty deepConstraint shallowConstraint fieldAccess wrap
     ParensT ty -> genDeepmapField trans ty deepConstraint shallowConstraint fieldAccess wrap
     _ -> (,) [] <$> fieldAccess

genFoldMapField :: Q Exp -> Type -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Exp -> (Q Exp -> Q Exp)
                -> Q ([Type], Exp)
genFoldMapField trans fieldType deepConstraint shallowConstraint fieldAccess wrap = do
   Just (Deriving _ typeVarN typeVar1) <- getQ
   case fieldType of
     AppT ty (AppT (AppT con v1) v2) | ty == VarT typeVar1, v1 == VarT typeVarN, v2 == VarT typeVarN ->
        (,) <$> ((:) <$> deepConstraint (pure con) <*> ((:[]) <$> shallowConstraint (pure con)))
            <*> appE (wrap [| foldMap (Transformation.Deep.foldMap $trans) |]) fieldAccess
     AppT ty _  | ty == VarT typeVar1 ->
                  (,) [] <$> (wrap (varE 'Transformation.foldMap `appE` trans) `appE` fieldAccess)
     AppT (AppT con v1) v2 | v1 == VarT typeVarN, v2 == VarT typeVar1 ->
        (,) <$> ((:[]) <$> deepConstraint (pure con))
            <*> appE (wrap [| Transformation.Deep.foldMap $trans |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar1 ->
        genFoldMapField trans t2 deepConstraint shallowConstraint fieldAccess (wrap . appE (varE 'foldMap))
     SigT ty _kind -> genFoldMapField trans ty deepConstraint shallowConstraint fieldAccess wrap
     ParensT ty -> genFoldMapField trans ty deepConstraint shallowConstraint fieldAccess wrap
     _ -> (,) [] <$> [| mempty |]

genTraverseDownField :: GenTraverseFieldType
genTraverseDownField trans fieldType deepConstraint shallowConstraint fieldAccess wrap = do
   Just (Deriving _ typeVarN typeVar1) <- getQ
   case fieldType of
     AppT ty (AppT (AppT con v1) v2) | ty == VarT typeVar1, v1 == VarT typeVarN, v2 == VarT typeVarN ->
        (,) <$> ((:) <$> deepConstraint (pure con) <*> ((:[]) <$> shallowConstraint (pure con)))
            <*> appE (wrap [| (>>= traverse (Transformation.Deep.traverseDown $trans)) . Transformation.traverse $trans |])
                     fieldAccess
     AppT ty _  | ty == VarT typeVar1 ->
                  (,) [] <$> (wrap (varE 'Transformation.traverse `appE` trans) `appE` fieldAccess)
     AppT (AppT con v1) v2 | v1 == VarT typeVarN, v2 == VarT typeVar1 ->
        (,) <$> ((:[]) <$> deepConstraint (pure con))
            <*> appE (wrap [| Transformation.Deep.traverseDown $trans |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar1 ->
        genTraverseDownField trans t2 deepConstraint shallowConstraint fieldAccess (wrap . appE (varE 'traverse))
     SigT ty _kind -> genTraverseDownField trans ty deepConstraint shallowConstraint fieldAccess wrap
     ParensT ty -> genTraverseDownField trans ty deepConstraint shallowConstraint fieldAccess wrap
     _ -> (,) [] <$> [| pure $fieldAccess |]

genTraverseUpField :: GenTraverseFieldType
genTraverseUpField trans fieldType deepConstraint shallowConstraint fieldAccess wrap = do
   Just (Deriving _ typeVarN typeVar1) <- getQ
   case fieldType of
     AppT ty (AppT (AppT con v1) v2) | ty == VarT typeVar1, v1 == VarT typeVarN, v2 == VarT typeVarN ->
        (,) <$> ((:) <$> deepConstraint (pure con) <*> ((:[]) <$> shallowConstraint (pure con)))
            <*> appE (wrap [| (>>= Transformation.traverse $trans) . traverse (Transformation.Deep.traverseUp $trans) |])
                     fieldAccess
     AppT ty _  | ty == VarT typeVar1 ->
                  (,) [] <$> (wrap (varE 'Transformation.traverse `appE` trans) `appE` fieldAccess)
     AppT (AppT con v1) v2 | v1 == VarT typeVarN, v2 == VarT typeVar1 ->
        (,) <$> ((:[]) <$> deepConstraint (pure con))
            <*> appE (wrap [| Transformation.Deep.traverseUp $trans |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar1 ->
        genTraverseUpField trans t2 deepConstraint shallowConstraint fieldAccess (wrap . appE (varE 'traverse))
     SigT ty _kind -> genTraverseUpField trans ty deepConstraint shallowConstraint fieldAccess wrap
     ParensT ty -> genTraverseUpField trans ty deepConstraint shallowConstraint fieldAccess wrap
     _ -> (,) [] <$> [| pure $fieldAccess |]
