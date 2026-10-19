import Solcore.SourceSemantics.CoreLowering.CellAwareScopeForPostBounds
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForPost
import Solcore.SourceSemantics.CoreLowering.CellAwareForState
import Solcore.SourceSemantics.CoreLowering.CellAwareLoopProgress
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileEdges

/-! Actual condition and body children execute under the installed self cell.
The reached mixed heap, exact descriptor effect and caller admission survive
both Source preservation and native reflection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForPostEdges
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CellAwareLoopState (Progress)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions)
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)

theorem preserves_at {continuing : Bool} {budget size : Nat} {items : List ForItemForm} {expected : TypeSystem.Ty}
    (correct : CellAwareScopeForPostBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope items expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode body (code.rename ξ) selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (postTyped : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context items final)
    (ready : Admission bridge context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.ForItemsOutcome}
    (trace : Staging.Recursive.Size.ForItems program stages size invocation context environment before items finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (TypedImperativeFor.postValues type location continuing ++ actual) store
        (ForLoop.postCode (code.rename ξ)) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected (restoredOutcome environment outcome) reached.retained := by
  have postAgrees : EnvironmentsAgree ((fun index => index + 6).comp ξ) canonical
      (TypedImperativeFor.postValues type location continuing ++ actual) :=
    TypedImperativeFor.postValues_agree agrees type location continuing
  obtain ⟨postContext, actualPostTyped⟩ := TypedImperativeFor.postValues_typed continuing state.selfTyped state.actualTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    correct size within state.environments state.heaps state.locals postAgrees actualPostTyped
      runtime covers sameLedger postTyped state.retained ready state.authority state.physical state.owner state.ownerAt state.ready trace
  have progress : Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [TypedImperativeFor.post_rename] using evaluated,
    represented, progress, reached, retained, post⟩

theorem reflects_at {continuing : Bool} {budget size : Nat} {items : List ForItemForm} {expected : TypeSystem.Ty}
    (correct : CellAwareScopeForPostBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope items expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode body (code.rename ξ) selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (postTyped : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context items final)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (TypedImperativeFor.postValues type location continuing ++ actual) store
      (ForLoop.postCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.ForItems program stages sourceSize invocation context environment before items finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected (restoredOutcome environment outcome) reached.retained := by
  have postAgrees : EnvironmentsAgree ((fun index => index + 6).comp ξ) canonical
      (TypedImperativeFor.postValues type location continuing ++ actual) :=
    TypedImperativeFor.postValues_agree agrees type location continuing
  obtain ⟨postContext, actualPostTyped⟩ := TypedImperativeFor.postValues_typed continuing state.selfTyped state.actualTyped
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    correct size within state.environments state.heaps state.locals postAgrees actualPostTyped
      runtime covers sameLedger postTyped state.retained ready state.authority state.physical state.owner state.ownerAt state.ready
      (by simpa only [TypedImperativeFor.post_rename] using evaluated)
  have progress : Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareForPostEdges
