import Solcore.Syntax.Operator
import Solcore.TypeSystem.Type

/-!
# Foundations: the assignment profile

The operators and targets that the meaning proofs of an assignment take, named once.

Main declarations:
- `AssignmentProfile`, plain assignment or a compound one at a `Word` or an `integer` target;
- `NumericAssignment`, its compound part.

Both are reducible, so a proof takes them apart with `rcases` and builds them with `.inl` and
`.inr`, as it would the disjunction they name.
-/

section
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering

/-- The assignment profile: plain assignment at any target, or a compound one at a `Word`
target, or at an `integer` target when the operator is not Word-only
(`Syntax.ValueAssignOp.wordOnly`). Statements over the metadata view apply it to the target type's
`SourceCoreRawMetadata.runtimeType`. Compound assignments at the twelve fixed-width integer types
are compiled but outside it. -/
abbrev AssignmentProfile (operator : Syntax.ValueAssignOp) (target : TypeSystem.Ty) : Prop :=
  operator = .equal ∨ target = .word ∨ target = .integer ∧ operator.wordOnly = false

/-- The profile's compound part: a `Word` target, or an `integer` one when the operator is not
Word-only. -/
abbrev NumericAssignment (operator : Syntax.ValueAssignOp) (target : TypeSystem.Ty) : Prop :=
  target = .word ∨ target = .integer ∧ operator.wordOnly = false

end Solcore.SourceSemantics.CoreLowering
end
