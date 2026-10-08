import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNotLowering
import Solcore.SourceSemantics.CoreLowering.TypedImperativeAssignmentMeaning

/-! A bare unary assignment has no source RHS or key child. Its head retains
only actual place layout, lexical lookup, numeric source profile and token. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

structure Head (context : SourceSemantics.Context) (scope : Scope) (assignment : AssignmentResolution) where
  prepared : Prepared
  index : Nat
  invalid : Word
  bare : assignment.target.projections = []
  layout : CompatibleBareBitNotCertificates.Layout prepared
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType)
  writable : WritableLocal context assignment.target.root prepared.route.rootSourceType
  profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
    SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer

namespace Head
variable {context : SourceSemantics.Context} {scope : Scope} {assignment : AssignmentResolution}

def emit (head : Head context scope assignment) (next : Expr) (output : Ty) : Expr :=
  execute head.prepared (.var head.index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
    next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid

def writtenContext (head : Head context scope assignment) (actual : Core.Context) : Core.Context :=
  CompatibleRenamedBareBitNot.writtenContext head.prepared actual

def Errors (head : Head context scope assignment) (faults : FunctionCalls.FaultRep) : Prop :=
  faults (.invalidUnaryOperand .bitNot) head.invalid

theorem of_lower_with_token {values : ValuesContext} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {expression : ExpressionLowerer} {fuel : Nat} {next code : Expr} {output : Ty}
    {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (bare : assignment.target.projections = [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment .equal none
      output next reasonAt invalid invalidOperand missing = .ok code) :
    ∃ head : Head context scope assignment, code = head.emit next output ∧ head.invalid = invalidOperand := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  exact ⟨⟨prepared, index, invalidOperand, bare, layout, slot, rootEq ▸ writable binder binding,
    view ▸ profile⟩, lowering, rfl⟩

theorem of_lower {values : ValuesContext} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {expression : ExpressionLowerer} {fuel : Nat} {next code : Expr} {output : Ty}
    {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (bare : assignment.target.projections = [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment .equal none
      output next reasonAt invalid invalidOperand missing = .ok code) :
    ∃ head : Head context scope assignment, code = head.emit next output := by
  obtain ⟨head, emitted, _⟩ := of_lower_with_token writable bare profile accepted
  exact ⟨head, emitted⟩
end Head
end Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
