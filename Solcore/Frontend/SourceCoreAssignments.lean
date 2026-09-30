import Solcore.Frontend.SourceCoreControl
import Solcore.Core.LocalAssignment

/-! Assignment policy for bare scalar/product equal assignments and builtin
Word compound/unary assignments. Requirements and projections are rejected;
method evidence and Integer operations are separate lowering work. The caller
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

/-- The equal-assignment validator already checks the target owner, binding,
declared payload type, empty requirements and absence of projections. -/
def target (source : TypedSource) (scope : Scope) (assignment : AssignmentResolution) :
    Except Error (Nat × Core.Ty) :=
  SourceCoreBasic.lowerAssignment source scope assignment .equal

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
  SourceCoreBasic.ensureType (.binder assignment.target.root) .word payloadType
  pure (Core.LocalAssignment.bitNot outputType (.var index) next invalidReason)

end Solcore.Frontend.SourceCoreAssignments
