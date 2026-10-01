import Solcore.SourceSemantics.CoreLowering.ProtectedWhileConditions
import Solcore.SourceSemantics.CoreLowering.ProtectedLexicalAssignmentReflection

/-! Concrete lexical body edges under the actual Bool/Unit/self prefix.
Source-local bindings remain in the returned lexical result and live heap;
the outer loop's canonical installed entry survives the protected effects. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope} {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

include transport in
/-- The body contract is an internal composition interface. The public named
consumer supplies it from its concrete recursive lexical/assignment Tree. -/
theorem body_preserves {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) false statements expected type code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : Executes false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  obtain ⟨native, read⟩ := state.1.contextRead
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, lexical⟩ :=
    correct valid state.1.environments state.1.heaps state.1.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.1.selfTyped) state.1.actualTyped)))
      reference read state.1.contextUnmapped state.2 trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
      Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    FlowRep.of_lexical represented, progress, state.advance transport progress, lexical⟩

include transport in
/-- A completed body reconstructs its independent source trace and reached
lexical context while retaining the original outer installed entry. -/
theorem body_reflects {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ProtectedLexicalAssignments.ControlAt.Reflects functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) false statements expected type code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ finalContext outcome after finalMap finalWorld,
      Executes false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  obtain ⟨native, read⟩ := state.1.contextRead
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, lexical⟩ :=
    correct valid state.1.environments state.1.heaps state.1.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.1.selfTyped) state.1.actualTyped)))
      reference read state.1.contextUnmapped state.2
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
        Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  exact ⟨finalContext, outcome, after, finalMap, finalWorld, trace,
    FlowRep.of_lexical represented, progress, state.advance transport progress, lexical⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile
