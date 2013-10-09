module DynamicStatic.TypeExpression

open Type


///AST for FScheme expressions
type TypeExpression =
    | Atom_E
    | Type_E of Type
    | Let of string list * TypeExpression list * TypeExpression
    | Fun of string * TypeExpression
    | Call of TypeExpression * TypeExpression
    | If of TypeExpression * TypeExpression * TypeExpression
    | Begin of TypeExpression list