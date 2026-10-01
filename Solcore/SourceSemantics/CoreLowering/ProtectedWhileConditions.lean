import Solcore.SourceSemantics.CoreLowering.ProtectedWhileState

/-! Guarded condition edges use the real Unit/self-cell environment. The
two inserted native slots are typed from the actual loop activation. They do
not shift or recreate the canonical installed named-call observations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext Progress)
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {certificate : GenericExpressionMeaning.Certificate} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
  {scope : Scope} {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

include transport in
/-- Generic child meaning is an internal composition interface. The concrete
named consumer supplies it from the accepted recursive expression Tree. -/
theorem condition_preserves
    (meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, preserved, metadata⟩ :=
    meaning tree found state.1.environments state.1.heaps state.1.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.1.selfTyped) state.1.actualTyped)) state.2 trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, progress, state.advance transport progress⟩

include transport in
/-- Actual completed condition code recovers the independent source outcome
and transports the original guard through the observed prefix effects. -/
theorem condition_reflects
    (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, preserved, metadata⟩ :=
    reflection tree found state.1.environments state.1.heaps state.1.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.1.selfTyped) state.1.actualTyped)) state.2
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  exact ⟨outcome, after, finalMap, finalWorld, trace, related, progress, state.advance transport progress⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile
