import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMatchPrefixAdmission
import Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchBodyContracts

/-! Selected match children retain their actual Source grades and reached
caller states. Restoring lexical bindings preserves captured heap cells and
both semantic and staging failures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedConditionalHeads (BranchPreserves BranchReflects)
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchSelectionPrefix DataMatchBranchPrefix
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  (parent : SourceSemantics.Context) (control : ControlContext) (resolution : MatchResolution)
  (bodyCertificate : BodyCertificate) (expected : TypeSystem.Ty) (type : Ty) (budget : Nat)

def ArmPreservesBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend invocation.source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType invocation.source control armContext statements staticFinal facts →
    BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition armContext finalScope statements expected type body budget

def ArmReflectsBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend invocation.source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType invocation.source control armContext statements staticFinal facts →
    BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition armContext finalScope statements expected type body budget

def DefaultPreservesBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType invocation.source control parent statements staticFinal facts →
    BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition parent finalScope statements expected type body budget

def DefaultReflectsBelow (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType invocation.source control parent statements staticFinal facts →
    BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition parent finalScope statements expected type body budget

theorem restore_rep {catalog projects definitions}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping world mode raw type faults outcome value}
    (represented : Represents model mapping world mode raw type faults outcome value)
    (environment : Dynamic.Environment) :
    Represents model mapping world mode raw type faults (outcome.restore environment) value := by
  cases represented with
  | returned payload => exact .returned payload
  | breaking _ => exact .breaking environment
  | continuing _ => exact .continuing environment
  | fault matched => exact .fault matched
  | fallthrough _ allowed => exact .fallthrough environment allowed

private theorem value_backward {owner context target binders heap value raw}
    (extended : BindersExtend owner context binders target)
    (typed : Dynamic.ValueHasType target heap value raw) :
    Dynamic.ValueHasType context heap value raw := by
  induction extended with
  | nil => exact typed
  | cons head tail ih => exact (Dynamic.ValueHasType.iff_of_binderExtends head).mpr (ih typed)

/-- Restore only the lexical view of a selected arm. All facts concern the
same returned heap, store, mapping and authenticated function rows. -/
theorem restore_arm {source : TypedSource}
    {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ProtectedStateTransition.ReturnTo callerProtocol scope canonical selectedScope selectedCanonical)
    {context armContext : SourceSemantics.Context} {binders : List TypedBinder}
    (extended : BindersExtend source.owner context binders armContext)
    {mapping world heap store expected outcome}
    (state : callerProtocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩)
    (environment : Dynamic.Environment)
    (post : Post bridge armContext expected outcome state) :
    Post bridge context expected (outcome.restore environment) (returnTo.restore state) := by
  have rows := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (bridge.pool state) (bridge.pool (returnTo.restore state)) post.rows (.refl _ _)
  cases outcome with
  | returned value =>
    obtain ⟨typed, admitted⟩ := CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value post
    exact ⟨rows, by intro result same; cases same; exact ⟨value_backward extended typed,
      Dynamic.BindersExtend.control_heap_backward extended admitted.heap⟩⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨rows, by intro result same; cases same⟩
    | stage origin call reason => exact rows
  | fallthrough _ | breaking _ | continuing _ => exact CallableIndexedOwnedMatchPrefixAdmission.restore_arm bridge returnTo extended state post

/-- Default and empty selections restore the native frame at the original
Source context and retain the actual selected body's postcondition. -/
theorem restore_parent
    {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ProtectedStateTransition.ReturnTo callerProtocol scope canonical selectedScope selectedCanonical)
    {context : SourceSemantics.Context} {mapping world heap store expected outcome}
    (state : callerProtocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩)
    (environment : Dynamic.Environment)
    (post : Post bridge context expected outcome state) :
    Post bridge context expected (outcome.restore environment) (returnTo.restore state) := by
  have rows := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (bridge.pool state) (bridge.pool (returnTo.restore state)) post.rows (.refl _ _)
  cases outcome with
  | returned value =>
    obtain ⟨typed, admitted⟩ := CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value post
    exact ⟨rows, by intro result same; cases same; exact ⟨typed, admitted.heap⟩⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨rows, by intro result same; cases same⟩
    | stage origin call reason => exact rows
  | fallthrough _ | breaking _ | continuing _ => exact CallableIndexedOwnedMatchPrefixAdmission.restore_parent bridge returnTo state post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchHeads
