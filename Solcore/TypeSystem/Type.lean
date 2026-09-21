import Solcore.Resolved.Identity

/-! A small source-level type language.

`Core.Ty` remains the concrete runtime type language.  This language lives in
front of it and distinguishes flexible inference variables from rigid source
generic parameters. -/

set_option autoImplicit false

namespace Solcore.TypeSystem

/-- A flexible metavariable allocated by type inference. -/
structure TypeVarId where
  index : Nat
  deriving Repr, DecidableEq

/-- A rigid generic parameter owned by one resolved declaration. -/
structure TypeParameterId where
  owner : Resolved.DeclarationId
  index : Nat
  deriving Repr, DecidableEq

/-- Built-ins which do not need declaration identities in the first slice. -/
inductive BuiltinType where
  | unit
  | bool
  | word
  | integer
  deriving Repr, DecidableEq

/-- The stable identity at the head of a type application. -/
inductive TypeConstructorId where
  | builtin (type : BuiltinType)
  | declaration (id : Resolved.DeclarationId)
  deriving Repr, DecidableEq

/--
Semantic source types.  `variable` is flexible; `parameter` is rigid.
Nominal arguments are represented by left-associated `application` nodes.
-/
inductive Ty where
  | variable (id : TypeVarId)
  | parameter (id : TypeParameterId)
  | constructor (id : TypeConstructorId)
  | application (function argument : Ty)
  | function (parameter result : Ty)
  | product (left right : Ty)
  | mapping (key value : Ty)
  | proxy (inner : Ty)
  | comptime (inner : Ty)
  | error
  deriving Repr, DecidableEq

namespace Ty

def unit : Ty := .constructor (.builtin .unit)

def bool : Ty := .constructor (.builtin .bool)

def word : Ty := .constructor (.builtin .word)

/-- The arbitrary-precision source integer type.  It is staged and therefore
does not by itself acquire a `Core.Ty` projection. -/
def integer : Ty := .constructor (.builtin .integer)

/-- Left-associated type application. -/
def applyMany (head : Ty) (arguments : List Ty) : Ty :=
  arguments.foldl Ty.application head

/-- A nominal declaration applied to zero or more type arguments. -/
def nominal (declaration : Resolved.DeclarationId) (arguments : List Ty := []) : Ty :=
  applyMany (.constructor (.declaration declaration)) arguments

/-- Right-associated products, with the conventional zero/singleton cases. -/
def productMany : List Ty → Ty
  | [] => unit
  | [type] => type
  | type :: types => .product type (productMany types)

private def insertVariable (variables : List TypeVarId) (metavariable : TypeVarId) :
    List TypeVarId :=
  if metavariable ∈ variables then variables else variables ++ [metavariable]

private def unionVariables (left right : List TypeVarId) : List TypeVarId :=
  right.foldl insertVariable left

/-- Flexible variables occurring in a type, in stable left-to-right order. -/
def freeVariables : Ty → List TypeVarId
  | .variable metavariable => [metavariable]
  | .parameter _
  | .constructor _
  | .error => []
  | .application leftPart rightPart
  | .function leftPart rightPart
  | .product leftPart rightPart
  | .mapping leftPart rightPart =>
      unionVariables leftPart.freeVariables rightPart.freeVariables
  | .proxy inner
  | .comptime inner => inner.freeVariables

/-- Whether a flexible metavariable occurs in a type. -/
def containsVariable (type : Ty) (metavariable : TypeVarId) : Bool :=
  type.freeVariables.contains metavariable

/-- A fresh-variable lower bound strictly above every flexible variable. -/
def nextVariable (type : Ty) : Nat :=
  type.freeVariables.foldl (fun next metavariable => max next (metavariable.index + 1)) 0

/-- Constructor-node size, used to choose a conservative unification budget. -/
def size : Ty → Nat
  | .variable _
  | .parameter _
  | .constructor _
  | .error => 1
  | .application left right
  | .function left right
  | .product left right
  | .mapping left right => left.size + right.size + 1
  | .proxy inner
  | .comptime inner => inner.size + 1

end Ty

end Solcore.TypeSystem
