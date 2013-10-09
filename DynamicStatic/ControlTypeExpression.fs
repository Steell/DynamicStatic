module DynamicStatic.ControlTypeExpression

open Type

type ControlTypeExpression =
    | CAtom_E
    | CType_E of Type
    | CLet of string list * ControlTypeExpression list * ControlTypeExpression
    | CFun of string * ControlTypeExpression
    | CCall of ControlTypeExpression * ControlTypeExpression * string
    | CIf of ControlTypeExpression * (int * ControlTypeExpression) * (int * ControlTypeExpression) * string
    | CBegin of ControlTypeExpression list