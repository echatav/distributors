module Json.Distributor where

import Data.Aeson qualified as A
import Language.TypeScript qualifed as TS

type ValueCodec :: Type -> Type -> Type
newtype ValueCodec a b = ValueCodec
  {unJsonCodec :: Codec (ReaderT A.Value A.Parser) (Op A.Value) a b}

type ObjectCodec :: Type -> Type -> Type
newtype ObjectCodec a b = ObjectCodec
  {unJsonCodec :: Codec (ReaderT (A.KeyMap A.Value) A.Parser) (Op (A.KeyMap A.Value)) a b}

type ValueType :: Type -> Type -> Type
newtype ValueType a b = ValueType {unValueType :: TS.Type}

type ObjectType :: Type -> Type -> Type
newtype ObjectType a b = ObjectType {unObjectType :: TS.TypeBody}
