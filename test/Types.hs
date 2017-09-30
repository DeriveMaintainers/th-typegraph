{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Types where

import Data.Aeson
import Data.Generics
import Language.Haskell.TH
import Network.URI

class {- (ToJSON (ValueType t), FromJSON (ValueType t),
       ToJSON (KeyType t), FromJSON (KeyType t),
       ToJSON (ProxyType t), FromJSON (ProxyType t)
      )
         => -} Paths t where

    data ValueType t
    data ProxyType t
    data KeyType t

data TestPaths = TestPaths deriving Data

instance Paths TestPaths where
  data ValueType TestPaths
      = V_Eitherz20UURIz20UInteger (Either URI Integer)
      | V_Int Int
      | V_Integer Integer
      | V_Loc Loc
      | V_Maybez20UURIAuth (Maybe URIAuth)
      | V_Maybez20UZLEitherz20UURIz20UIntegerZR (Maybe (Either URI Integer))
      | V_Name Name
      | V_TyLit TyLit
      | V_TyVarBndr TyVarBndr
      | V_Type Type
      | V_URI URI
      | V_URIAuth URIAuth
      | V_ZLIntz2cUz20UIntZR ((Int, Int))
      | V_ZLIntz2cUz20UTyVarBndrZR ((Int, TyVarBndr))
      | V_ZLIntz2cUz20UTypeZR ((Int, Type))
      | V_ZLIntz2cUz20UZMCharZNZR ((Int, [Char]))
      | V_ZMCharZN ([Char])
      | V_ZMIntZN ([Int])
      | V_ZMTyVarBndrZN ([TyVarBndr])
      | V_ZMTypeZN ([Type])
      | V_ZMZMCharZNZN ([[Char]])
        deriving (Eq, Ord, Data, Show)
  data ProxyType TestPaths
      = P_Eitherz20UURIz20UInteger
      | P_Int | P_Integer
      | P_Loc | P_Maybez20UURIAuth
      | P_Maybez20UZLEitherz20UURIz20UIntegerZR | P_Name
      | P_TyLit | P_TyVarBndr
      | P_Type | P_URI
      | P_URIAuth | P_ZLIntz2cUz20UIntZR
      | P_ZLIntz2cUz20UTyVarBndrZR | P_ZLIntz2cUz20UTypeZR
      | P_ZLIntz2cUz20UZMCharZNZR | P_ZMCharZN
      | P_ZMIntZN | P_ZMTyVarBndrZN
      | P_ZMTypeZN | P_ZMZMCharZNZN
        deriving (Eq, Ord, Data, Show)
  data KeyType TestPaths = K_Int Int deriving (Eq, Ord, Data, Show)

data Hop key
    = NamedField {_cct :: Int, _cpos :: Int, _fct :: Int, _fpos :: Int, _tname :: String, _cname :: String, _fname :: String} -- ^ Name of a field accessor function
    | AnonField {_cct :: Int, _cpos :: Int, _fct :: Int, _fpos :: Int, _tname :: String, _cname :: String} -- ^ Constructor name and arity, field position
    | TupleHop {_tpos :: Int} -- ^ Hop to nth element of a tuple
    | IndexHop {_key :: key} -- ^ Hop from an instance of 'Index', such as Map, via some key value
    | ViewHop  -- ^ Hop due to an instance of View
    | IxViewHop {_key :: key} -- ^ Hop due to an instance of IxView
    deriving Show

data TraversalPath t s a = TraversalPath (ProxyType t) [Hop (KeyType t)] (ProxyType t)
