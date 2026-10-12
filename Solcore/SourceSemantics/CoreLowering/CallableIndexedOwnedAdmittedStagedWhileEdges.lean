import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalHeads
import Solcore.SourceSemantics.CoreLowering.ProtectedStateWhile

/-! Staged condition and body children run under the actual installed loop
self cell. Hidden native arguments change only renamings; the reached Source
heap, staged fault tag, and full admitted caller post are retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileEdges
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedConditionalHeads (FlowPreserves FlowReflects)
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
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
local notation "values" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

theorem condition_preserves_at {size : Nat}
    (meaning : PreservesAt bridge context model stages invocation certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : invocation.source.lookupExpression? condition = some node)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.While.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    (ready : Admission bridge context state.retained)
    {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        PostAdmission bridge context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    meaning tree found typed state.live.environments state.live.heaps state.live.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)) state.retained ready trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.While.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, progress, reached, retained, post⟩

theorem condition_reflects_at {size : Nat}
    (reflection : ReflectsAt bridge context model stages invocation certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : invocation.source.lookupExpression? condition = some node)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.While.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before condition outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        PostAdmission bridge context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    reflection tree found typed state.live.environments state.live.heaps state.live.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)) state.retained ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.While.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, post⟩

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem body_preserves_at {budget size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : FlowPreserves (administrative := administrative) (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope false statements expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.While.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (guarded : guard contextLocation native)
    (ready : Admission bridge context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (trace : Staging.Recursive.Size.StatementsIn program stages false size invocation context environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected outcome reached.retained := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    correct within state.live.environments state.live.heaps state.live.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)))
      reference read state.live.contextUnmapped state.retained guarded ready trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.While.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
      Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, progress, reached, retained, post⟩

theorem body_reflects_at {budget size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : FlowReflects (administrative := administrative) (receiving := registry) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions guard context scope false statements expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.While.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (guarded : guard contextLocation native)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages false sourceSize invocation context environment before statements finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected outcome reached.retained := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    correct within state.live.environments state.live.heaps state.live.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)))
      reference read state.live.contextUnmapped state.retained guarded ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
        Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.While.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileEdges
