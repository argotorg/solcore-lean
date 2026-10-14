import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForPostContracts
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForPost
import Solcore.SourceSemantics.CoreLowering.ProtectedStateFor

/-! Staged condition and body children run under the actual installed loop
self cell. Hidden native arguments change only renamings; the reached Source
heap, staged fault tag, and full admitted caller post are retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForPostEdges
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedForPostContracts
open TypedLexicalWhile (Progress)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body postCode : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
local notation "values" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem preserves_at {continuing : Bool} {budget size : Nat} {items : List ForItemForm} {expected : TypeSystem.Ty}
    (correct : Preserves (administrative := administrative) (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope items expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (guarded : guard contextLocation native)
    (ready : Admission bridge context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.ForItemsOutcome}
    (trace : Staging.Recursive.Size.ForItems program stages size invocation context environment before items finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (TypedImperativeFor.postValues type location continuing ++ actual) store
        (ForLoop.postCode (code.rename ξ)) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected (restoredOutcome environment outcome) reached.retained := by
  have postAgrees : EnvironmentsAgree ((fun index => index + 6).comp ξ) canonical
      (TypedImperativeFor.postValues type location continuing ++ actual) :=
    TypedImperativeFor.postValues_agree agrees type location continuing
  obtain ⟨postContext, postTyped⟩ := TypedImperativeFor.postValues_typed continuing state.live.selfTyped state.live.actualTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    correct within state.live.environments state.live.heaps state.live.locals postAgrees postTyped
      reference read state.live.contextUnmapped state.retained guarded ready trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [TypedImperativeFor.post_rename] using evaluated,
    represented, progress, reached, retained, post⟩

theorem reflects_at {continuing : Bool} {budget size : Nat} {items : List ForItemForm} {expected : TypeSystem.Ty}
    (correct : Reflects (administrative := administrative) (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope items expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (guarded : guard contextLocation native)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (TypedImperativeFor.postValues type location continuing ++ actual) store
      (ForLoop.postCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.ForItems program stages sourceSize invocation context environment before items finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected (restoredOutcome environment outcome) reached.retained := by
  have postAgrees : EnvironmentsAgree ((fun index => index + 6).comp ξ) canonical
      (TypedImperativeFor.postValues type location continuing ++ actual) :=
    TypedImperativeFor.postValues_agree agrees type location continuing
  obtain ⟨postContext, postTyped⟩ := TypedImperativeFor.postValues_typed continuing state.live.selfTyped state.live.actualTyped
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    correct within state.live.environments state.live.heaps state.live.locals postAgrees postTyped
      reference read state.live.contextUnmapped state.retained guarded ready
      (by simpa only [TypedImperativeFor.post_rename] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForPostEdges
