module DynamicStatic.Type ( ) where

import Data.Foldable (any, all)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Poset as Poset

data Type =
    | Bottom --"subclass" of everything
    | Atom
    | Unit
    | True | False
    | TypeId String
    | List Type
    | Func OverloadSet
    | Union UnionSet
    | Not Type
    deriving (Eq, Ord, Show)

instance Monoid Type where
    mempty = Bottom
    mappend = unionTypes

instance Poset Type where
    compare = isSubtypeOf

type FuncSignature = (Type, Type)
type OverloadSet = Set FuncSignature
type UnionSet = Set Type


invertOrd :: Poset.Ordering -> Poset.Ordering
invertOrd LT = GT
invertOrd GT = LT
invertOrd o  = o

both :: (a -> b) -> (a, a) -> (b, b)
both f (x, y) = (f x, f y)


bool :: Type
bool = Union $ Set.fromList [True, False]


containsId :: String -> Type -> Bool
containsId id = lookupId
    where lookupId TypeId id' = id == id'
          lookupId List t     = lookupId t
          lookupId Func oset  = any (both lookupId) oset
          lookupId Union uset = any lookupId uset
          lookupId Not t      = lookupId t
          lookupId _          = False


isSubtypeOf :: Type -> Type -> Poset.Ordering
Bottom       `isSubtypeOf` _              = Poset.LT
(Func _)     `isSubtypeOf` Atom           = Poset.LT

(TypeId id1) `isSubtypeOf` (TypeId id2)   = if id1 == id2 then Poset.EQ else Poset.NC
(TypeId _)   `isSubtypeOf` _              = Poset.GT
_            `isSubtypeOf` (TypeId _)     = Poset.LT

(Not sub)    `isSubtypeOf` (Not super)    = sub `isSubtypeOf` super
(List sub)   `isSubtypeOf` (List super)   = sub `isSubtypeOf` super

sub          `isSubtypeOf` (Not super)    = invertOrd $ sub `isSubtypeOf` super
(Not sub)    `isSubtypeOf` super          = invertOrd $ sub `isSubtypeOf` super

(Union subs) `isSubtypeOf` super          = all (`isSubtypeOf` super) subs
sub          `isSubtypeOf` (Union supers) = any (isSubtypeOf sub) supers

(Func subs)  `isSubtypeOf` (Func supers)  = all (subs `anyAreSubtypeOf`) supers
    where anyAreSubtypeOf subs super = any (flip overloadUnifies super) subs

sub `isSubtypeOf` super
    | sub == super = Poset.EQ 
    | otherwise    = Poset.NC


overloadUnifies :: FuncSignature -> FuncSignature -> Bool
overloadUnifies (subArg, subReturn) (superArg, superReturn) = 
    isSubtypeOf superArg subArg && isSubtypeOf subReturn superReturn


unionTypes :: Type -> Type -> Type
unionTypes (Func os1) (Func os2) = undefined
unionTypes (Union ts1) t2 =


unionTypes t1 t2
    | t1 `isSubtypeOf` t2 = t2
    | t2 `isSubtypeOf` t1 = t1
    | otherwise           = Union $ Set.fromList [t1, t2]

addToUnion :: Type -> UnionSet -> UnionSet
addToUnion t set = undefined


addToOverloads :: FuncSignature -> OverloadSet -> OverloadSet
addToOverloads = undefined