import Solcore.Frontend.SourceCoreControl
import Solcore.Core.LocalAssignment
import Solcore.Core.IntegerAssignment
import Solcore.Frontend.SourceCoreScalar

/-! Assignment policy for bare scalar/product equal assignments and builtin
Word/Integer compound/unary assignments. Requirements and projections are
rejected; method evidence remains separate lowering work. The caller
supplies each assignment's diagnostic reason and a lexical continuation. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreAssignments

open SourceInference

abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr

/-- Close the expression reason provider before passing this policy. -/
abbrev ExpressionLowerer := Nat → TypedSource → Scope → ExpressionId → Except Error LoweredExpr

def operator? : Syntax.ValueAssignOp → Option Core.LocalAssignment.Operator
  | .equal => none
  | .add => some .add
  | .subtract => some .subtract
  | .multiply => some .multiply
  | .divide => some .divide
  | .modulo => some .modulo
  | .bitAnd => some .bitAnd
  | .bitOr => some .bitOr
  | .bitXor => some .bitXor

/-- Scalar target validation checks the owner, binding, declared payload type,
empty requirements and absence of projections. Equal function assignments
continue through the enclosing function profile's own callback. -/
def target (source : TypedSource) (scope : Scope) (assignment : AssignmentResolution) :
    Except Error (Nat × Core.Ty) := do
  let binder := assignment.target.root
  if binder.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.owner)
  unless assignment.requirements.isEmpty do throw (.assignmentRequirementsPresent binder)
  unless assignment.target.projections.isEmpty do throw (.projectedAssignment binder)
  let (index, type) ← match SourceCoreLocalCell.lookup? scope binder with
    | some slot => pure slot
    | none => .error (.missingBinding binder)
  let projected ← (SourceCoreScalar.lowerType (.binder binder) assignment.target.type).mapError SourceCoreBasic.Error.typeProjection
  SourceCoreBasic.ensureType (.binder binder) type projected
  pure (index, type)

private def integerOperator : Core.LocalAssignment.Operator → Core.IntegerAssignment.Operator
  | .add => .add
  | .subtract => .subtract
  | .multiply => .multiply
  | .divide => .divide
  | .modulo => .modulo
  | .bitAnd => .bitAnd
  | .bitOr => .bitOr
  | .bitXor => .bitXor

def assignValue (lowerExpression : ExpressionLowerer) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (outputType : Core.Ty)
    (next : Core.Expr) (invalidReason : Core.Word) : Except Error Core.Expr := do
  let (index, payloadType) ← target source scope assignment
  match operator? operator with
  | none =>
      let rhs ← lowerExpression fuel source scope rhs
      SourceCoreBasic.ensureType (.binder assignment.target.root) payloadType rhs.type
      pure (Core.LocalSequence.assign outputType (.var index) rhs.expression next)
  | some operator =>
      if payloadType = .integer then
        let rhs ← lowerExpression fuel source scope rhs
        SourceCoreBasic.ensureType (.binder assignment.target.root) .integer rhs.type
        pure (Core.IntegerAssignment.compound outputType (integerOperator operator) (.var index)
          rhs.expression next invalidReason)
      else
        SourceCoreBasic.ensureType (.binder assignment.target.root) .word payloadType
        let rhs ← lowerExpression fuel source scope rhs
        SourceCoreBasic.ensureType (.binder assignment.target.root) .word rhs.type
        pure (Core.LocalAssignment.compound outputType operator (.var index) rhs.expression next invalidReason)

def assignValueWithReasons (lowerExpression : SourceCoreControl.ExpressionLowerer) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (outputType : Core.Ty)
    (next : Core.Expr) (invalidReason : Core.Word) (reasonAt : ExpressionId → Core.Word) :
    Except Error Core.Expr :=
  assignValue (fun fuel source scope id => lowerExpression fuel source scope id reasonAt)
    fuel source scope assignment operator rhs outputType next invalidReason

def assignBitNot (source : TypedSource) (scope : Scope) (assignment : AssignmentResolution)
    (outputType : Core.Ty) (next : Core.Expr) (invalidReason : Core.Word) : Except Error Core.Expr := do
  let (index, payloadType) ← target source scope assignment
  if payloadType = .integer then
    pure (Core.IntegerAssignment.bitNot outputType (.var index) next invalidReason)
  else
    SourceCoreBasic.ensureType (.binder assignment.target.root) .word payloadType
    pure (Core.LocalAssignment.bitNot outputType (.var index) next invalidReason)

end Solcore.Frontend.SourceCoreAssignments
