module DynamicStatic.ConstraintSet ( ) where

import Data.Map

import Control.Monad.Trans.State
import Control.Monad.Trans.Except

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import qualified DynamicStatic.Type as Type
import qualified DynamicStatic.Expression as Expr


type IdGen = [String]

idGen :: IdGen
idGen = [ 't' : show x | x <- [0..] ]

freshId :: IdGen -> State IdGen String
freshId = State $ \(id:gen) -> (id, gen)


type Constraint = (String, Type)
type ConstraintSet = Map String Type

constructConstraintSet :: Type -> Expression -> Except String [(Type, ConstraintSet)]
constructConstraintSet expectedType = 
    flip evalStateT idGen . constrain expectedType Map.empty Map.empty

    where
        constrain :: Type -> Environment -> ConstraintSet -> Expression -> StateT IdGen (Except String) [(Type, ConstraintSet)]
        constrain expectedType env cset = constrainExpr

        constrainTypeToExpected = flip (constrainType cset) expectedType

        constrainExpr :: Expression -> StateT IdGen (Except String) [(Type, ConstraintSet)]
        constrainExpr Expr.Atom  = constrainTypeToExpected Type.Atom
        constrainExpr Expr.True  = constrainTypeToExpected Type.True
        constrainExpr Expr.False = constrainTypeToExpected Type.False

        constrainExpr (Expr.Id id) =
            case Map.lookup id env of
                Just typeId -> constrainTypeToExpected $ Type.TypeId typeId
                Nothing     -> lift $ throwE "Unbound identifier: " ++ id

        constrainExpr (Expr.Let id bound body) = constrainExpr $ Expr.Call (Expr.Fun id body) bound

        constrainExpr (Expr.Fun param body) = do
            paramVar  <- Type.TypeId `liftM` freshId
            returnVar <- Type.TypeId `liftM` freshId
            branches  <- lift $ constrain returnVar (Map.insert param paramVar env) cset body
            lift $ throwE "Not Implemented: constrainExpr.Fun"

        constrainExpr (Expr.Call fun arg) = do
            argVar <- Type.TypeId `liftM` freshId
            lift $ throwE "Not Implmented: constrainExpr.Call"

        constrainExpr (Expr.Begin []) = return [(Type.Unit, cset)]
        constrainExpr (Expr.Begin exprs) = lift $ throwE "Not Implemented: constrainExpr.Begin"

        constrainExpr (Expr.If test true false) = return $ fail "Not Implemented: constrainExpr.If"


constrainType :: ConstraintSet -> Type -> Type -> StateT IdGen (Except String) [(Type, ConstraintSet)]
constrainType cset toConstrain constrainTo = undefined