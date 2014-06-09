module DynamicStatic.Expression () where


data Expression =
    | Atom
    | True | False
    | Id String
    | Let String Expression Expression
    | Fun String Expression
    | Call Expression Expression
    | Begin [Expression]
    | If Expression Expression Expression
