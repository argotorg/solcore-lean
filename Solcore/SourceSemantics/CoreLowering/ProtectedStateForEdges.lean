import Solcore.SourceSemantics.CoreLowering.ProtectedStateFor
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalGate
import Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition

/-! The existing measured condition and body edges relay their actual child
post-witness. Hidden native slots only affect the actual environment and
renaming. The original source grade and native completion are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open TypedImperativeFor (Progress)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : Scope} {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

variable {certificate : GenericExpressionMeaning.Certificate} {body : Expr}

/-- Generic child meaning is an internal composition interface. The concrete
named consumer supplies it from the accepted recursive expression Tree. -/
theorem condition_preserves_at {size : Nat}
    (meaning : ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, preserved, metadata, transition⟩ :=
    meaning tree found state.live.environments state.live.heaps state.live.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)) state.retained trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  obtain ⟨reached, retained⟩ := state.reach progress transition
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, progress, reached, retained⟩

/-- Actual completed condition code recovers the independent source outcome
and transports the original guard through the observed prefix effects. -/
theorem condition_reflects_at {size : Nat}
    (reflection : ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, preserved, metadata, transition⟩ :=
    reflection tree found state.live.environments state.live.heaps state.live.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)) state.retained
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  obtain ⟨reached, retained⟩ := state.reach progress transition
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained⟩


variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

/-- The body contract is an internal composition interface. Recursive statement
induction supplies it for the current child, including control transfers. -/
theorem body_preserves_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, lexical, transition⟩ :=
    correct valid state.live.environments state.live.heaps state.live.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)))
      reference read state.live.contextUnmapped state.retained guarded trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  obtain ⟨reached, retained⟩ := state.reach progress transition
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
      Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, progress, reached, retained, lexical⟩


/-- A completed body reconstructs its independent source trace and reached
lexical context while retaining the original outer installed entry. -/
theorem body_reflects_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, lexical, transition⟩ :=
    correct valid state.live.environments state.live.heaps state.live.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)))
      reference read state.live.contextUnmapped state.retained guarded
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
        Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  obtain ⟨reached, retained⟩ := state.reach progress transition
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, lexical⟩


end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful
