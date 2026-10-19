import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCertificates
import Solcore.SourceSemantics.CoreLowering.ProtectedStagedProjectedBitNotTail

/-! A projected unary head retains only the actual key children. The compiler's
Unit slot has no corresponding Source expression. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open SourceCoreCompatibleDataPlaces
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

structure Head (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (certificate : GenericExpressionMeaning.Certificate) (scope : Scope)
    (administrative : Core.Context) (definitions : DataEnvironment) (assignment : AssignmentResolution) where
  prepared : Prepared
  index : Nat
  codes : List SourceCoreBasic.LoweredExpr
  leaf : TypeSystem.Ty
  sourceTypes : List TypeSystem.Ty
  site : SourceCoreElaboration.ErrorSite
  invalid : Word
  layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source certificate scope site
    assignment.target prepared codes sourceTypes leaf administrative .unit
  ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType)
  writable : WritableLocal context assignment.target.root prepared.route.rootSourceType
  profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer

namespace Head
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {definitions : DataEnvironment} {assignment : AssignmentResolution}

theorem projected (head : Head values source context certificate scope administrative definitions assignment) :
    assignment.target.projections ≠ [] := by
  intro empty
  have path := head.layout.path
  rw [empty] at path
  have noSteps {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
      {root leaf : TypeSystem.Ty} {position : Nat} {steps : List PreparedStep}
      {keys : List (ExpressionId × Ty)}
      (path : CompatibleMixedRoute.PreparedPath checked source site root [] position steps keys leaf) : steps = [] := by
    cases path
    rfl
  exact head.layout.nonempty (noSteps path)

def emit (head : Head values source context certificate scope administrative definitions assignment)
    (next : Expr) (output : Ty) : Expr :=
  execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) (LanguageResult.success .unit)
    next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid

def writtenContext (head : Head values source context certificate scope administrative definitions assignment)
    (actual : Core.Context) : Core.Context :=
  ProtectedStagedProjectedBitNotCommit.writtenContext head.prepared (SourceCoreCalls.packArguments head.codes).type actual

structure Errors (head : Head values source context certificate scope administrative definitions assignment)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop where
  missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token
  uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection

/-- Genuine lowering and Source typing determine every key and leaf view. -/
theorem of_lower {site : SourceCoreElaboration.ErrorSite} {expression : ExpressionLowerer}
    {fuel : Nat} {reasonAt : ExpressionId → Word} {next code : Expr} {output resultType : Ty}
    {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (nonempty : assignment.target.projections ≠ [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (extract : ∀ id lowered, expression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id lowered)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment .equal none output
      next reasonAt invalid invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code resultType definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment,
      code = head.emit next output ∧ head.invalid = invalidOperand := by
  obtain ⟨binder, leaf, prepared, codes, sourceTypes, index, _, binding, rootEq, view, slot, layout, ordinary, _, emitted⟩ :=
    CompatiblePlaceBitNotCertificates.of_lower unique signatures sourceTyped nonempty extract accepted typed
  exact ⟨⟨prepared, index, codes, leaf, sourceTypes, site, invalidOperand, layout, ordinary, slot,
    rootEq ▸ writable binder binding, view ▸ profile⟩, emitted, rfl⟩

end Head
end Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements
