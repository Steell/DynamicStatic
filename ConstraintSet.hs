module DynamicStatic.ConstraintSet ( ) where

import Data.Map

import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Identity

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import qualified DynamicStatic.Type as Type
import qualified DynamicStatic.Expression as Expr


type IdGen = [String]

freshId :: IdGen -> State IdGen String
freshId = State $ \(id:gen) -> (id, gen)


type Constraint = (String, Type)
type ConstraintSet = Map String Type

constructConstraintSet :: Type -> Environment -> ConstraintSet -> Expression -> State IdGen (Either String [(Type, ConstraintSet)])
constructConstraintSet expectedType env cset = constrainExpr
    where
        constrainTypeToExpected :: Type -> State IdGen (Either String [(Type, ConstraintSet)])
        constrainTypeToExpected = (flip . constrainType) cset $ expectedType

        constrainExpr Expr.Atom = constrainTypeToExpected Type.Atom
        constrainExpr Expr.True = constrainTypeToExpected Type.True
        constrainExpr Expr.False = constrainTypeToExpected Type.False

        constrainExpr (Expr.Id id) =
            case Map.lookup id env of
                Just typeId -> constrainTypeToExpected $ TypeId typeId
                Nothing -> fail "Unbound identifier: " ++ id

        constrainExpr (Let id bound body) = constrainExpr $ Call (Fun id body) bound

        constrainExpr (Fun param body) = do --State monad
            pid <- freshId
            rid <- freshId
            let paramVar = TypeId pid
            let returnVar = TypeId rid
            constraintResult <- constructConstraintSet returnVar (Map.insert param paramVar env) cset