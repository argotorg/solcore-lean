import Solcore.SourceSemantics.CoreLowering.ProtectedWhileReflection

/-! The real self-cell installation and recursive invocation surround the
finite iteration proofs. Both completed outcomes retain the original protected
entry, captured code and frame observations through the actual progress. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep Restored restored restore_rep initial_state)
variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context} {type : Ty} {conditionCode code : Expr} {selfReason : Word} {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)

def HeadPreserves {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_installed : entry scope mapping world before store canonical)
    (_trace : Dynamic.StatementExecutesOutcome program context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical

def HeadReflects {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_installed : entry scope mapping world before store canonical)
    (_evaluated : Evaluates actual store (code.rename ξ) value finalStore),
    ∃ outcome after finalMap finalWorld,
      Dynamic.StatementExecutesOutcome program context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical

/- The generated prelude installs its self closure before the first condition;
source heap and scope stay unchanged during this administrative step. -/
include transport meaning in
theorem while_preserves {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code) :
    HeadPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨state, installedProgress⟩ := initial_state functions environments heaps locals agrees actualTyped read unmapped typed
  have protectedState : State entry values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation store.length type (conditionCode.rename ξ) (code.rename ξ) selfReason
      mapping (TypedLexicalWhile.installedWorld world type) before
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason actual) :=
    ⟨state, transport.extend installed installedProgress.2.1 installedProgress.2.2.1
      installedProgress.2.2.2.1 installedProgress.2.2.2.2⟩
  cases trace with
  | control sourceTrace =>
    obtain ⟨rfl, _, innerOutcome, rfl, sourceLoop⟩ := ScalarStatementViews.whileLoop unique (lookupStatement?_sound found) form sourceTrace
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress⟩ :=
      iterations_success sourceLoop transport meaning conditionTree conditionFound valid unique agrees reference correct protectedState
    exact ⟨rfl, restored environment innerOutcome, value, finalStore, finalMap, finalWorld,
      by simpa only [LoopRenaming.whileLoop] using nativeTrace.whileLoop_evaluates,
      restore_rep represented environment, (installedProgress.trans progress).1,
      (installedProgress.trans progress).2.1, (installedProgress.trans progress).2.2.1,
      (installedProgress.trans progress).2.2.2.1, (installedProgress.trans progress).2.2.2.2,
      (protectedState.advance transport progress).2⟩
  | fault failed =>
    have sourceLoop := ScalarStatementViews.whileLoop_fault unique (lookupStatement?_sound found) form failed
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress⟩ :=
      iterations_fault sourceLoop transport meaning conditionTree conditionFound valid unique agrees reference correct protectedState
    exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld,
      by simpa only [LoopRenaming.whileLoop] using nativeTrace.whileLoop_evaluates,
      represented, (installedProgress.trans progress).1,
      (installedProgress.trans progress).2.1, (installedProgress.trans progress).2.2.1,
      (installedProgress.trans progress).2.2.2.1, (installedProgress.trans progress).2.2.2.2,
      (protectedState.advance transport progress).2⟩

include transport reflection in
theorem while_reflects {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : ProtectedLexicalAssignments.ControlAt.Reflects functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    HeadReflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨state, installedProgress⟩ := initial_state functions environments heaps locals agrees actualTyped read unmapped typed
  have protectedState : State entry values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation store.length type (conditionCode.rename ξ) (code.rename ξ) selfReason
      mapping (TypedLexicalWhile.installedWorld world type) before
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason actual) :=
    ⟨state, transport.extend installed installedProgress.2.1 installedProgress.2.2.1
      installedProgress.2.2.2.1 installedProgress.2.2.2.2⟩
  rw [LoopRenaming.whileLoop] at evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨entrySize, _, nativeEntry⟩ := sized.iterate_entry
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, progress⟩ :=
    iterations_reflect functions program evidence transport reflection conditionTree conditionFound valid agrees reference correct
      bodyCannotFault entrySize protectedState nativeEntry
  refine ⟨Dynamic.restoreControl environment outcome, after, finalMap, finalWorld, ?_, restored environment outcome,
    restore_rep represented environment, (installedProgress.trans progress).1,
    (installedProgress.trans progress).2.1, (installedProgress.trans progress).2.2.1,
    (installedProgress.trans progress).2.2.2.1, (installedProgress.trans progress).2.2.2.2,
    (protectedState.advance transport progress).2⟩
  cases trace with
  | control sourceLoop => exact .control (.whileLoop (lookupStatement?_sound found) form sourceLoop)
  | fault sourceLoop => exact .fault (.whileIteration (lookupStatement?_sound found) form sourceLoop)
end Solcore.SourceSemantics.CoreLowering.ProtectedWhile
