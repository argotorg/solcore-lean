import Solcore.Core.Syntax
import Solcore.Resolved.Expr
import Solcore.TypeSystem.Type

/-!
Closed source values supported by the first general staged-value evaluator.

The carrier is intentionally smaller than `Core.Value`: compile-time source
evaluation cannot accidentally manufacture closures, host functions, cells,
sum injections, or nominal data.  Products retain their exact binary tree, so
right-associated source tuples remain right-associated through Core and
resolved-expression projection.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceStagedValue

/-- Pure, Core-representable values admitted at the staged source boundary. -/
inductive Value where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | product (left right : Value)
  deriving Repr, BEq, DecidableEq

/-- Recover the exact source type represented by a staged value. -/
def sourceType : Value → TypeSystem.Ty
  | .unit => .unit
  | .bool _ => .bool
  | .word _ => .word
  | .product left right => .product (sourceType left) (sourceType right)

/-- Recover the exact Semantic Core type represented by a staged value. -/
def coreType : Value → Core.Ty
  | .unit => .unit
  | .bool _ => .bool
  | .word _ => .word
  | .product left right => .product (coreType left) (coreType right)

/-- Embed a staged value into the corresponding closed Core value. -/
def toCore : Value → Core.Value
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .product left right => .pair (toCore left) (toCore right)

/-- Reification to Core preserves the carrier's exact structural type. -/
@[simp] theorem toCore_type (value : Value) :
    (toCore value).type = coreType value := by
  induction value <;> simp_all [toCore, coreType, Core.Value.type]

/-- Reify the same carrier as a closed Semantic Core expression. -/
def toCoreExpr : Value → Core.Expr
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .product left right => .pair (toCoreExpr left) (toCoreExpr right)

/-- Reify a staged value as a closed resolved expression. -/
def toResolved : Value → Resolved.Expr
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .product left right => .pair (toResolved left) (toResolved right)

/-- Resolved reification lowers to the corresponding closed Core expression
in every surrounding scope; staged values contain no local references. -/
@[simp] theorem toResolved_lower (value : Value)
    (scope : List Resolved.LocalId) :
    (toResolved value).lower? scope = some (toCoreExpr value) := by
  induction value <;>
    simp_all [toResolved, toCoreExpr, Resolved.Expr.lower?]

end Solcore.Frontend.SourceStagedValue
