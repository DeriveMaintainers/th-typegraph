{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

-- import Data.Aeson
-- import Language.Haskell.TH.TypeGraph.Aeson (deriveJSON)
import Language.Haskell.TH.Lift (lift)
import Language.Haskell.TH.TypeGraph.Constraints (monomorphize)
import Language.Haskell.TH.TypeGraph.Serialize (deriveSerialize)
import Language.Haskell.TH.TypeGraph.TypeTraversal (pprint1)
import Language.Haskell.TH.TypeGraph.WebRoutesTH (derivePathInfo)
import Prelude hiding (concat)
import Data.Aeson.TH
import Data.Generics
import Data.Monoid (mconcat)
import Test.HUnit

import Types

-- The deriveJSON function provided by aeson puts constraints ToJSON
-- t, ToJSON s, ToJSON a on the instances.  The ToJSON t constraint is
-- unnecessary because it doesn't actually appear in the value, and we
-- need constraints ToJSON (KeyType t) but they are omitted.

-- $(deriveJSON defaultOptions ''Hop)
-- $(deriveJSON defaultOptions ''TraversalPath)



tests = do
  TestList
    [ TestCase
        (assertEqual "deriveSerialize Hop"
           (concat ["instance Serialize key => Serialize (Hop key) where ",
                    "put (NamedField a1 a2 a3 a4 a5 a6 a7) = ((((((putWord8 0 >> put a1) >> put a2) >> put a3) >> put a4) >> put a5) >> put a6) >> put a7 ",
                    "put (AnonField a1 a2 a3 a4 a5 a6) = (((((putWord8 1 >> put a1) >> put a2) >> put a3) >> put a4) >> put a5) >> put a6 ",
                    "put (TupleHop a1) = putWord8 2 >> put a1 put (IndexHop a1) = putWord8 3 >> put a1 ",
                    "put (ViewHop) = putWord8 4 ",
                    "put (IxViewHop a1) = putWord8 5 >> put a1 ",
                    "get = getWord8 >>= (\\i -> case i of ",
                                                   "0 -> ((((((pure NamedField <*> get) <*> get) <*> get) <*> get) <*> get) <*> get) <*> get ",
                                                   "1 -> (((((pure AnonField <*> get) <*> get) <*> get) <*> get) <*> get) <*> get ",
                                                   "2 -> pure TupleHop <*> get ",
                                                   "3 -> pure IndexHop <*> get ",
                                                   "4 -> pure ViewHop ",
                                                   "5 -> pure IxViewHop <*> get)"])
           $(deriveSerialize [t|Hop|] >>= lift . pprint1))
    , TestCase (assertEqual "deriveSerialize TraversalPath"
                  "instance (Serialize (KeyType t), Serialize (ProxyType t)) => Serialize (TraversalPath t s a) where put (TraversalPath a1 a2 a3) = (put a1 >> put a2) >> put a3 get = ((pure TraversalPath <*> get) <*> get) <*> get"
                  $(deriveSerialize [t|TraversalPath|] >>= lift . pprint1))
    , TestCase
        (assertEqual "deriveSerialize (ValueType TestPaths)"
           (concat ["instance Serialize (ValueType TestPaths) where ",
                    "put (V_Eitherz20UURIz20UInteger a1) = putWord8 0 >> put a1 ",
                    "put (V_Int a1) = putWord8 1 >> put a1 ",
                    "put (V_Integer a1) = putWord8 2 >> put a1 ",
                    "put (V_Loc a1) = putWord8 3 >> put a1 ",
                    "put (V_Maybez20UURIAuth a1) = putWord8 4 >> put a1 ",
                    "put (V_Maybez20UZLEitherz20UURIz20UIntegerZR a1) = putWord8 5 >> put a1 ",
                    "put (V_Name a1) = putWord8 6 >> put a1 ",
                    "put (V_TyLit a1) = putWord8 7 >> put a1 ",
                    "put (V_TyVarBndr a1) = putWord8 8 >> put a1 ",
                    "put (V_Type a1) = putWord8 9 >> put a1 ",
                    "put (V_URI a1) = putWord8 10 >> put a1 ",
                    "put (V_URIAuth a1) = putWord8 11 >> put a1 ",
                    "put (V_ZLIntz2cUz20UIntZR a1) = putWord8 12 >> put a1 ",
                    "put (V_ZLIntz2cUz20UTyVarBndrZR a1) = putWord8 13 >> put a1 ",
                    "put (V_ZLIntz2cUz20UTypeZR a1) = putWord8 14 >> put a1 ",
                    "put (V_ZLIntz2cUz20UZMCharZNZR a1) = putWord8 15 >> put a1 ",
                    "put (V_ZMCharZN a1) = putWord8 16 >> put a1 ",
                    "put (V_ZMIntZN a1) = putWord8 17 >> put a1 ",
                    "put (V_ZMTyVarBndrZN a1) = putWord8 18 >> put a1 ",
                    "put (V_ZMTypeZN a1) = putWord8 19 >> put a1 ",
                    "put (V_ZMZMCharZNZN a1) = putWord8 20 >> put a1 ",
                    "get = getWord8 >>= (\\i -> case i of ",
                    "0 -> pure V_Eitherz20UURIz20UInteger <*> get ",
                    "1 -> pure V_Int <*> get ",
                    "2 -> pure V_Integer <*> get ",
                    "3 -> pure V_Loc <*> get ",
                    "4 -> pure V_Maybez20UURIAuth <*> get ",
                    "5 -> pure V_Maybez20UZLEitherz20UURIz20UIntegerZR <*> get ",
                    "6 -> pure V_Name <*> get ",
                    "7 -> pure V_TyLit <*> get ",
                    "8 -> pure V_TyVarBndr <*> get ",
                    "9 -> pure V_Type <*> get ",
                    "10 -> pure V_URI <*> get ",
                    "11 -> pure V_URIAuth <*> get ",
                    "12 -> pure V_ZLIntz2cUz20UIntZR <*> get ",
                    "13 -> pure V_ZLIntz2cUz20UTyVarBndrZR <*> get ",
                    "14 -> pure V_ZLIntz2cUz20UTypeZR <*> get ",
                    "15 -> pure V_ZLIntz2cUz20UZMCharZNZR <*> get ",
                    "16 -> pure V_ZMCharZN <*> get ",
                    "17 -> pure V_ZMIntZN <*> get ",
                    "18 -> pure V_ZMTyVarBndrZN <*> get ",
                    "19 -> pure V_ZMTypeZN <*> get ",
                    "20 -> pure V_ZMZMCharZNZN <*> get)"])
           $(deriveSerialize [t|ValueType TestPaths|] >>= lift . pprint1))
    , TestCase
        (assertEqual "derivePathInfo Hop"
           (concat ["instance PathInfo key => PathInfo (Hop key) where ",
                    (concat ["toPathSegments inp = case inp of NamedField arg arg arg arg arg arg arg -> (++) [pack ['n', 'a', 'm', 'e', 'd', '-', 'f', 'i', 'e', 'l', 'd']] ((++) (toPathSegments arg) ((++) (toPathSegments arg) ((++) (toPathSegments arg) ((++) (toPathSegments arg) ((++) (toPathSegments arg) ((++) (toPathSegments arg) (toPathSegments arg))))))) AnonField arg arg arg arg arg arg -> (++) [pack ['a', 'n', 'o', 'n', '-', 'f', 'i', 'e', 'l', 'd']] ((++) (toPathSegments arg) ((++) (toPathSegments arg) ((++) (toPathSegments arg) ((++) (toPathSegments arg) ((++) (toPathSegments arg) (toPathSegments arg)))))) TupleHop arg -> (++) [pack ['t', 'u', 'p', 'l', 'e', '-', 'h', 'o', 'p']] (toPathSegments arg) IndexHop arg -> (++) [pack ['i', 'n', 'd', 'e', 'x', '-', 'h', 'o', 'p']] (toPathSegments arg) ViewHop -> [pack ['v', 'i', 'e', 'w', '-', 'h', 'o', 'p']] IxViewHop arg -> (++) [pack ['i', 'x', '-', 'v', 'i', 'e', 'w', '-', 'h', 'o', 'p']] (toPathSegments arg) ",
                             "fromPathSegments = (<|>) ((<|>) ((<|>) ((<|>) ((<|>) (ap (ap (ap (ap (ap (ap (ap (segment (pack \"named-field\") >> return NamedField) fromPathSegments) fromPathSegments) fromPathSegments) fromPathSegments) fromPathSegments) fromPathSegments) fromPathSegments) (ap (ap (ap (ap (ap (ap (segment (pack \"anon-field\") >> return AnonField) fromPathSegments) fromPathSegments) fromPathSegments) fromPathSegments) fromPathSegments) fromPathSegments)) (ap (segment (pack \"tuple-hop\") >> return TupleHop) fromPathSegments)) (ap (segment (pack \"index-hop\") >> return IndexHop) fromPathSegments)) (segment (pack \"view-hop\") >> return ViewHop)) (ap (segment (pack \"ix-view-hop\") >> return IxViewHop) fromPathSegments)"])])
           $(derivePathInfo [t|Hop|] >>= lift . pprint1))
    , TestCase
        (assertEqual "derivePathInfo (ProxyType TestPaths)"
           "instance PathInfo (ProxyType t) where toPathSegments inp = case inp of P_Eitherz20UURIz20UInteger -> [pack ['p', '_', '-', 'e', 'i', 't', 'h', 'e', 'r', 'z', '2', '0', '-', 'u', '-', 'u', '-', 'r', '-', 'i', 'z', '2', '0', '-', 'u', '-', 'i', 'n', 't', 'e', 'g', 'e', 'r']] P_Int -> [pack ['p', '_', '-', 'i', 'n', 't']] P_Integer -> [pack ['p', '_', '-', 'i', 'n', 't', 'e', 'g', 'e', 'r']] P_Loc -> [pack ['p', '_', '-', 'l', 'o', 'c']] P_Maybez20UURIAuth -> [pack ['p', '_', '-', 'm', 'a', 'y', 'b', 'e', 'z', '2', '0', '-', 'u', '-', 'u', '-', 'r', '-', 'i', '-', 'a', 'u', 't', 'h']] P_Maybez20UZLEitherz20UURIz20UIntegerZR -> [pack ['p', '_', '-', 'm', 'a', 'y', 'b', 'e', 'z', '2', '0', '-', 'u', '-', 'z', '-', 'l', '-', 'e', 'i', 't', 'h', 'e', 'r', 'z', '2', '0', '-', 'u', '-', 'u', '-', 'r', '-', 'i', 'z', '2', '0', '-', 'u', '-', 'i', 'n', 't', 'e', 'g', 'e', 'r', '-', 'z', '-', 'r']] P_Name -> [pack ['p', '_', '-', 'n', 'a', 'm', 'e']] P_TyLit -> [pack ['p', '_', '-', 't', 'y', '-', 'l', 'i', 't']] P_TyVarBndr -> [pack ['p', '_', '-', 't', 'y', '-', 'v', 'a', 'r', '-', 'b', 'n', 'd', 'r']] P_Type -> [pack ['p', '_', '-', 't', 'y', 'p', 'e']] P_URI -> [pack ['p', '_', '-', 'u', '-', 'r', '-', 'i']] P_URIAuth -> [pack ['p', '_', '-', 'u', '-', 'r', '-', 'i', '-', 'a', 'u', 't', 'h']] P_ZLIntz2cUz20UIntZR -> [pack ['p', '_', '-', 'z', '-', 'l', '-', 'i', 'n', 't', 'z', '2', 'c', '-', 'u', 'z', '2', '0', '-', 'u', '-', 'i', 'n', 't', '-', 'z', '-', 'r']] P_ZLIntz2cUz20UTyVarBndrZR -> [pack ['p', '_', '-', 'z', '-', 'l', '-', 'i', 'n', 't', 'z', '2', 'c', '-', 'u', 'z', '2', '0', '-', 'u', '-', 't', 'y', '-', 'v', 'a', 'r', '-', 'b', 'n', 'd', 'r', '-', 'z', '-', 'r']] P_ZLIntz2cUz20UTypeZR -> [pack ['p', '_', '-', 'z', '-', 'l', '-', 'i', 'n', 't', 'z', '2', 'c', '-', 'u', 'z', '2', '0', '-', 'u', '-', 't', 'y', 'p', 'e', '-', 'z', '-', 'r']] P_ZLIntz2cUz20UZMCharZNZR -> [pack ['p', '_', '-', 'z', '-', 'l', '-', 'i', 'n', 't', 'z', '2', 'c', '-', 'u', 'z', '2', '0', '-', 'u', '-', 'z', '-', 'm', '-', 'c', 'h', 'a', 'r', '-', 'z', '-', 'n', '-', 'z', '-', 'r']] P_ZMCharZN -> [pack ['p', '_', '-', 'z', '-', 'm', '-', 'c', 'h', 'a', 'r', '-', 'z', '-', 'n']] P_ZMIntZN -> [pack ['p', '_', '-', 'z', '-', 'm', '-', 'i', 'n', 't', '-', 'z', '-', 'n']] P_ZMTyVarBndrZN -> [pack ['p', '_', '-', 'z', '-', 'm', '-', 't', 'y', '-', 'v', 'a', 'r', '-', 'b', 'n', 'd', 'r', '-', 'z', '-', 'n']] P_ZMTypeZN -> [pack ['p', '_', '-', 'z', '-', 'm', '-', 't', 'y', 'p', 'e', '-', 'z', '-', 'n']] P_ZMZMCharZNZN -> [pack ['p', '_', '-', 'z', '-', 'm', '-', 'z', '-', 'm', '-', 'c', 'h', 'a', 'r', '-', 'z', '-', 'n', '-', 'z', '-', 'n']] fromPathSegments = (<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) ((<|>) (segment (pack \"p_-eitherz20-u-u-r-iz20-u-integer\") >> return P_Eitherz20UURIz20UInteger) (segment (pack \"p_-int\") >> return P_Int)) (segment (pack \"p_-integer\") >> return P_Integer)) (segment (pack \"p_-loc\") >> return P_Loc)) (segment (pack \"p_-maybez20-u-u-r-i-auth\") >> return P_Maybez20UURIAuth)) (segment (pack \"p_-maybez20-u-z-l-eitherz20-u-u-r-iz20-u-integer-z-r\") >> return P_Maybez20UZLEitherz20UURIz20UIntegerZR)) (segment (pack \"p_-name\") >> return P_Name)) (segment (pack \"p_-ty-lit\") >> return P_TyLit)) (segment (pack \"p_-ty-var-bndr\") >> return P_TyVarBndr)) (segment (pack \"p_-type\") >> return P_Type)) (segment (pack \"p_-u-r-i\") >> return P_URI)) (segment (pack \"p_-u-r-i-auth\") >> return P_URIAuth)) (segment (pack \"p_-z-l-intz2c-uz20-u-int-z-r\") >> return P_ZLIntz2cUz20UIntZR)) (segment (pack \"p_-z-l-intz2c-uz20-u-ty-var-bndr-z-r\") >> return P_ZLIntz2cUz20UTyVarBndrZR)) (segment (pack \"p_-z-l-intz2c-uz20-u-type-z-r\") >> return P_ZLIntz2cUz20UTypeZR)) (segment (pack \"p_-z-l-intz2c-uz20-u-z-m-char-z-n-z-r\") >> return P_ZLIntz2cUz20UZMCharZNZR)) (segment (pack \"p_-z-m-char-z-n\") >> return P_ZMCharZN)) (segment (pack \"p_-z-m-int-z-n\") >> return P_ZMIntZN)) (segment (pack \"p_-z-m-ty-var-bndr-z-n\") >> return P_ZMTyVarBndrZN)) (segment (pack \"p_-z-m-type-z-n\") >> return P_ZMTypeZN)) (segment (pack \"p_-z-m-z-m-char-z-n-z-n\") >> return P_ZMZMCharZNZN)"
           $(derivePathInfo [t|ProxyType TestPaths|] >>= lift . pprint1))
    , TestCase
        (assertEqual "deriveJSON TraversalPath"
           (concat ["instance (ToJSON (KeyType (t :: *)), ToJSON (ProxyType (t :: *))) => ToJSON (TraversalPath t s a) where ",
                      "toJSON = \\value -> case value of TraversalPath arg1 arg2 arg3 -> Array (create (do {mv <- unsafeNew 3; unsafeWrite mv 0 (toJSON arg1); unsafeWrite mv 1 (toJSON arg2); unsafeWrite mv 2 (toJSON arg3); return mv})) ",
                      "toEncoding = \\value -> case value of TraversalPath arg1 arg2 arg3 -> Encoding (char7 '[' <> ((builder arg1 <> (char7 ',' <> (builder arg2 <> (char7 ',' <> builder arg3)))) <> char7 ']')) ",
                    "instance (FromJSON (KeyType (t :: *)), FromJSON (ProxyType (t :: *))) => FromJSON (TraversalPath t s a) where ",
                      "parseJSON = \\value -> case value of ",
                                                "Array arr -> if length arr == 3 then ((TraversalPath <$> parseJSON (arr `unsafeIndex` 0)) <*> parseJSON (arr `unsafeIndex` 1)) <*> parseJSON (arr `unsafeIndex` 2) else parseTypeMismatch' \"TraversalPath\" \"Types.TraversalPath\" \"Array of length 3\" (\"Array of length \" ++ (show . length) arr) ",
                                                "other -> parseTypeMismatch' \"TraversalPath\" \"Types.TraversalPath\" \"Array\" (valueConName other)"])
           $(deriveJSON defaultOptions ''TraversalPath >>= lift . pprint1))
    , TestCase
        (assertEqual "derivePathInfo TraversalPath"
           "instance (PathInfo (KeyType t), PathInfo (ProxyType t)) => PathInfo (TraversalPath t s a) where toPathSegments inp = case inp of TraversalPath arg arg arg -> (++) [pack ['t', 'r', 'a', 'v', 'e', 'r', 's', 'a', 'l', '-', 'p', 'a', 't', 'h']] ((++) (toPathSegments arg) ((++) (toPathSegments arg) (toPathSegments arg))) fromPathSegments = ap (ap (ap (segment (pack \"traversal-path\") >> return TraversalPath) fromPathSegments) fromPathSegments) fromPathSegments"
           $(derivePathInfo [t|TraversalPath|] >>= lift . pprint1))
    , TestCase (assertEqual "monomorphize Hop" "Hop key" $(monomorphize [t|Hop|] >>= lift . pprint1))
    , TestCase (assertEqual "monomorphize TraversalPath" "TraversalPath t s a" $(monomorphize [t|TraversalPath|] >>= lift . pprint1))
    , TestCase (assertEqual "monomorphize TraversalPath" "TraversalPath TestPaths s a" $(monomorphize [t|TraversalPath TestPaths|] >>= lift . pprint1))
    ]

-- | Without a specialized concat the text values come out as @pack ['a', 'b', 'c']@
concat :: [String] -> String
concat = mconcat

main = runTestTT tests
