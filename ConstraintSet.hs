module DynamicStatic.ConstraintSet ( ) where

import Data.Map
import qualified DynamicStatic.Type as Type

type Constraint = (String, Type)
type ConstraintSet = Map String Type

