import Solcore.SourceSemantics.CoreLowering.TypedImperativeForState

/-! Condition certificates run under the real Unit/self-cell prefix. The
installed closure, administrative reads and common heap are the existing loop
state; arbitrary captured values stay typed in the actual ambient definitions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (LoopState Progress)
variable {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode body postCode : Expr} {selfReason : Word}

variable {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
variable (functions) (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {certificate : GenericExpressionMeaning.Certificate}
  (meaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults)
  (reflection : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults)

include meaning in
theorem condition_preserves {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (_unique : NodeOccurrencesUnique source)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata⟩ :=
    meaning tree found
      state.environments state.heaps state.locals actualAgrees (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)) trace
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, heaps, maps, worlds, frame, metadata⟩

include reflection in
theorem condition_reflects {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩ :=
    reflection tree found
      state.environments state.heaps state.locals actualAgrees (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped))
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
