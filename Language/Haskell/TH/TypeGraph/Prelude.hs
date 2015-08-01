{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module Language.Haskell.TH.TypeGraph.Prelude
    ( pprint'
    , unlifted
    , constructorName
    , declarationName
    , declarationType
    , unReify
    , unReifyName
    , adjacent'
    , reachable'
    , L(L)
    ) where

import Control.Lens
import Data.Generics (Data, everywhere, mkT)
import Data.Graph as Graph
import Data.List (intersperse)
import Data.Map as Map (Map, fromList, toList)
import Data.Maybe (fromMaybe)
import Data.Set as Set (fromList, Set, toList)
import Language.Haskell.TH
import Language.Haskell.TH.PprLib (ptext, hcat)
import Language.Haskell.TH.Syntax (Lift(lift), Quasi(qReify))

instance Ppr () where
    ppr () = ptext "()"

newtype L a = L a

instance Ppr a => Ppr (L [a]) where
    ppr (L l) = hcat ([ptext "["] ++ intersperse (ptext ", ") (map ppr l) ++ [ptext "]"])

-- | Pretty print a 'Ppr' value on a single line with each block of
-- white space (newlines, tabs, etc.) converted to a single space.
pprint' :: Ppr a => a -> [Char]
pprint' typ = unwords $ words $ pprint typ

-- | Does the type or the declaration to which it refers contain a
-- primitive (aka unlifted) type?  This will traverse down any 'Dec'
-- to the named types, and then check whether any of their 'Info'
-- records are 'PrimTyConI' values.
class IsUnlifted t where
    unlifted :: Quasi m => t -> m Bool

instance IsUnlifted Dec where
    unlifted (DataD _ _ _ cons _) = or <$> mapM unlifted cons
    unlifted (NewtypeD _ _ _ con _) = unlifted con
    unlifted (TySynD _ _ typ) = unlifted typ
    unlifted _ = return False

instance IsUnlifted Con where
    unlifted (ForallC _ _ con) = unlifted con
    unlifted (NormalC _ ts) = or <$> mapM (unlifted . snd) ts
    unlifted (RecC _ ts) = or <$> mapM (\ (_, _, t) -> unlifted t) ts
    unlifted (InfixC t1 _ t2) = or <$> mapM (unlifted . snd) [t1, t2]

instance IsUnlifted Type where
    unlifted (ForallT _ _ typ) = unlifted typ
    unlifted (ConT name) = qReify name >>= unlifted
    unlifted (AppT t1 t2) = (||) <$> unlifted t1 <*> unlifted t2
    unlifted _ = return False

instance IsUnlifted Info where
    unlifted (PrimTyConI _ _ _) = return True
    unlifted _ = return False -- traversal stops here

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
