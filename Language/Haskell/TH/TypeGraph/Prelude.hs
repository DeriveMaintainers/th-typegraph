{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module Language.Haskell.TH.TypeGraph.Prelude
    ( pprint'
    , OverTypes(overTypes)
    , unlifted
    , constructorName
    , declarationName
    , declarationType
    , unReify
    , unReifyName
    , adjacent'
    , reachable'
    , L(L)
    , friendlyNames
    ) where

import Control.Lens hiding (cons)
import Control.Monad (foldM)
import Data.Generics (Data, everywhere, mkT)
import Data.Graph as Graph
import Data.List (intersperse)
import Data.Map as Map (Map, fromList, toList)
import Data.Maybe (fromMaybe)
import Data.Set as Set (fromList, Set, toList)
import Language.Haskell.TH
import Language.Haskell.TH.PprLib (ptext, hcat)
import Language.Haskell.TH.Syntax (Lift(lift), Name(Name), NameFlavour(NameS), Quasi(qReify), StrictType, VarStrictType)

instance Ppr () where
    ppr () = ptext "()"

newtype L a = L a

instance Ppr a => Ppr (L [a]) where
    ppr (L l) = hcat ([ptext "["] ++ intersperse (ptext ", ") (map ppr l) ++ [ptext "]"])

-- | Pretty print a 'Ppr' value on a single line with each block of
-- white space (newlines, tabs, etc.) converted to a single space, and
-- all the module qualifiers removed from the names.
pprint' :: (Ppr a, Data a) => a -> [Char]
pprint' typ = unwords $ words $ pprint $ friendlyNames $ typ

-- | Perform a fold over the Type and Info values embedded in t
class OverTypes t where
    overTypes :: Quasi m => (a -> Either Info Type -> m a) -> a -> t -> m a

instance OverTypes Dec where
    overTypes f a (DataD _ _ _ cons _) = foldM (overTypes f) a cons
    overTypes f a (NewtypeD _ _ _ con _) = overTypes f a con
    overTypes f a (TySynD _ _ typ) = overTypes f a typ
    overTypes _ a _ = return a

instance OverTypes StrictType where
    overTypes f a (_, t) = overTypes f a t

instance OverTypes VarStrictType where
    overTypes f a (_, _, t) = overTypes f a t

instance OverTypes Con where
    overTypes f a (ForallC _ _ con) = overTypes f a con
    overTypes f a (NormalC _ ts) = foldM (overTypes f) a ts
    overTypes f a (RecC _ ts) = foldM (overTypes f) a ts
    overTypes f a (InfixC t1 _ t2) = overTypes f a t1 >>= flip (overTypes f) t2

instance OverTypes Type where
    overTypes f a t@(AppT t1 t2) = f a (Right t) >>= flip (overTypes f) t1 >>= flip (overTypes f) t2
    overTypes f a (ConT name) = qReify name >>= overTypes f a
    overTypes f a t@(ForallT _ _ typ) = f a (Right t) >>= flip (overTypes f) typ
    overTypes f a t = f a (Right t)

instance OverTypes Info where
    overTypes f a x = f a (Left x)

-- | Does the type or the declaration to which it refers contain a
-- primitive (aka unlifted) type?  This will traverse down any 'Dec'
-- to the named types, and then check whether any of their 'Info'
-- records are 'PrimTyConI' values.
unlifted :: (OverTypes t, Quasi m) => t -> m Bool
unlifted x = overTypes f False x
    where
      f _ (Left (PrimTyConI _ _ _)) = return True
      f r _ = return r

constructorName :: Con -> Name
constructorName (ForallC _ _ con) = constructorName con
constructorName (NormalC name _) = name
constructorName (RecC name _) = name
constructorName (InfixC _ name _) = name

declarationName :: Dec -> Maybe Name
declarationName (FunD name _) = Just name
declarationName (ValD _pat _body _decs) = Nothing
declarationName (DataD _ name _ _ _) = Just name
declarationName (NewtypeD _ name _ _ _) = Just name
declarationName (TySynD name _ _) = Just name
declarationName (ClassD _ name _ _ _) = Just name
declarationName (InstanceD _ _ _) = Nothing
declarationName (SigD name _) = Just name
declarationName (ForeignD _) = Nothing
declarationName (InfixD _ name) = Just name
declarationName (PragmaD _) = Nothing
declarationName (FamilyD _ _name _ _) = Nothing
declarationName (DataInstD _ name _ _ _) = Just name
declarationName (NewtypeInstD _ name _ _ _) = Just name
declarationName (TySynInstD name _) = Just name
declarationName (ClosedTypeFamilyD name _ _ _) = Just name
declarationName (RoleAnnotD name _) = Just name
declarationName (StandaloneDerivD _ _) = Nothing
declarationName (DefaultSigD name _) = Just name

declarationType :: Dec -> Maybe Type
declarationType = fmap ConT . declarationName

instance Lift a => Lift (Set a) where
    lift s = [|Set.fromList $(lift (Set.toList s))|]

instance (Lift a, Lift b) => Lift (Map a b) where
    lift mp = [|Map.fromList $(lift (Map.toList mp))|]

unReify :: Data a => a -> a
unReify = everywhere (mkT unReifyName)

unReifyName :: Name -> Name
unReifyName = mkName . nameBase

-- | Return a key's list of adjacent keys
adjacent' :: forall node key. (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex) -> key -> [key]
adjacent' (_, vf, kf) k =
    view _3 $ vf v
    where
      v = fromMaybe (error "Language.Haskell.TH.TypeGraph.Prelude.adjacent") (kf k)

-- | Return a key's list of reachable keys
reachable' :: forall node key. (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex) -> key -> [key]
reachable' (g, vf, kf) k =
    map (view _2 . vf) $ reachableVerts
    where
      reachableVerts = Graph.reachable g v
      v = fromMaybe (error "Language.Haskell.TH.TypeGraph.Prelude.reachable") (kf k)

-- | Make a template haskell value more human reader friendly.  The
-- result almost certainly won't be compilable.  That's ok, though,
-- because the input is usually uncompilable - it imports hidden modules,
-- uses infix operators in invalid positions, puts module qualifiers in
-- places where they are not allowed, and maybe other things.
friendlyNames :: Data a => a -> a
friendlyNames =
    everywhere (mkT friendlyName)
    where
      friendlyName (Name x _) = Name x NameS -- Remove all module qualifiers
