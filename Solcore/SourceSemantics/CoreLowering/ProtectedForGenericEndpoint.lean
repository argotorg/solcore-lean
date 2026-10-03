import Solcore.SourceSemantics.CoreLowering.ProtectedForGenericIteration

/-! The actual for installation and invocation surround the shared finite
proof. Post callbacks are induction results on the real captured environment;
the protected entry remains canonical through all hidden slots and effects. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep installedStore installedWorld)
open TypedImperativeFor (SourceLoop initial_state)
open ProtectedWhile.Body (Preserves Reflects)
open RecursiveNamedForContracts (Below)
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  {certificate : GenericExpressionMeaning.Certificate}
  (meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)

def LoopPreservesFor (validity : SourceSemantics.Context → Prop) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome}
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
    (_trace : SourceLoop program context evidence source environment before condition post statements outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical

def LoopPreserves {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  LoopPreservesFor (entry := entry) (source := source) (context := context)
    (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals)
    (administrative := administrative) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (scope := scope) condition post statements expected type code

def LoopReflectsFor (validity : SourceSemantics.Context → Prop) {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
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
      SourceLoop program context evidence source environment before condition post statements outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical

def LoopReflects {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  LoopReflectsFor (entry := entry) (source := source) (context := context)
    (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals)
    (administrative := administrative) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (scope := scope) condition post statements expected type code

variable {scope : Scope} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}

include transport in
theorem loop_preserves_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaningB : Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postPreserves : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode))
    (postFaults : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => RecursiveNamedForContracts.PostFaultsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode)) :
    ∀ size, size ≤ budget → RecursiveNamedForContracts.LoopPreservesAtFor (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro size bounded valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨state, installedProgress⟩ := initial_state functions environments heaps locals agrees actualTyped read unmapped typed
  have protectedState : State entry values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation store.length type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason
      mapping (installedWorld world type) before
      (installedStore store type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason actual) :=
    ⟨state, transport.extend installed installedProgress.2.1 installedProgress.2.2.1
      installedProgress.2.2.2.1 installedProgress.2.2.2.2⟩
  have postCorrect : Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry)
      (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := store.length) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode) :=
    postPreserves agrees reference valid
  have postFailed : Below budget (fun size => RecursiveNamedForContracts.PostFaultsAt size functions program evidence (entry := entry)
      (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := store.length) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode) :=
    postFaults agrees reference valid
  cases trace with
  | control sourceTrace =>
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress⟩ :=
      iterations_success_bounded_for validity sourceTrace budget bounded meaningB transport conditionTree conditionFound valid unique agrees reference correct postCorrect protectedState
    exact ⟨value, finalStore, finalMap, finalWorld,
      by
        rw [LoopRenaming.iterate]
        apply LocalLoop.iterate_evaluates
        exact LocalLoop.invoke_success _ _ (.var rfl) state.selfRead nativeTrace,
      represented, (installedProgress.trans progress).1,
      (installedProgress.trans progress).2.1, (installedProgress.trans progress).2.2.1,
      (installedProgress.trans progress).2.2.2.1, (installedProgress.trans progress).2.2.2.2,
      (protectedState.advance transport progress).2⟩
  | fault failed =>
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress⟩ :=
      iterations_fault_bounded_for validity failed budget bounded meaningB transport conditionTree conditionFound valid unique agrees reference correct postCorrect postFailed protectedState
    exact ⟨value, finalStore, finalMap, finalWorld,
      by
        rw [LoopRenaming.iterate]
        apply LocalLoop.iterate_evaluates
        exact LocalLoop.invoke_success _ _ (.var rfl) state.selfRead nativeTrace,
      represented, (installedProgress.trans progress).1,
      (installedProgress.trans progress).2.1, (installedProgress.trans progress).2.2.1,
      (installedProgress.trans progress).2.2.2.1, (installedProgress.trans progress).2.2.2.2,
      (protectedState.advance transport progress).2⟩

include transport in
theorem loop_preserves_bounded (budget : Nat)
    (meaningB : Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)) {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => ProtectedWhile.Body.PreservesAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postPreserves : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      CompatibleExpressionLiterals.ContextValid solved context evidence →
      Below budget (fun size => RecursiveNamedForContracts.PostPreservesAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode))
    (postFaults : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      CompatibleExpressionLiterals.ContextValid solved context evidence →
      Below budget (fun size => RecursiveNamedForContracts.PostFaultsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode)) :
    ∀ size, size ≤ budget → RecursiveNamedForContracts.LoopPreservesAt (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  apply loop_preserves_bounded_for (functions := functions)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
  all_goals assumption

include transport in
theorem loop_reflects_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (reflectionB : Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry))
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False)
    (postReflects : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => RecursiveNamedForContracts.PostReflectsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode)) :
    ∀ size, size ≤ budget → RecursiveNamedForContracts.LoopReflectsAtFor (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (validity := validity) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro size bounded valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨state, installedProgress⟩ := initial_state functions environments heaps locals agrees actualTyped read unmapped typed
  have protectedState : State entry values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation store.length type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason
      mapping (installedWorld world type) before
      (installedStore store type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason actual) :=
    ⟨state, transport.extend installed installedProgress.2.1 installedProgress.2.2.1
      installedProgress.2.2.2.1 installedProgress.2.2.2.2⟩
  have postCorrect : Below budget (fun size => RecursiveNamedForContracts.PostReflectsAt size functions program evidence (entry := entry)
      (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := store.length) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode) :=
    postReflects agrees reference valid
  rw [LoopRenaming.iterate] at evaluated
  obtain ⟨entrySize, entrySmaller, nativeEntry⟩ := evaluated.iterate_entry
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress⟩ :=
    iterations_reflect_bounded_for functions program evidence reflectionB transport validity conditionTree conditionFound valid agrees reference correct
      postCorrect bodyCannotFault entrySize (Nat.le_trans (Nat.le_of_lt entrySmaller) bounded) protectedState nativeEntry
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
    (installedProgress.trans progress).1, (installedProgress.trans progress).2.1,
    (installedProgress.trans progress).2.2.1, (installedProgress.trans progress).2.2.2.1,
    (installedProgress.trans progress).2.2.2.2, (protectedState.advance transport progress).2⟩
include transport in
theorem loop_reflects_bounded (budget : Nat)
    (reflectionB : Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry))
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Below budget (fun size => ProtectedWhile.Body.ReflectsAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False)
    (postReflects : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      CompatibleExpressionLiterals.ContextValid solved context evidence →
      Below budget (fun size => RecursiveNamedForContracts.PostReflectsAt size functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode)) :
    ∀ size, size ≤ budget → RecursiveNamedForContracts.LoopReflectsAt (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  apply loop_reflects_bounded_for (functions := functions)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
  all_goals assumption

include transport meaning in
theorem loop_preserves {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (postPreserves : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      CompatibleExpressionLiterals.ContextValid solved context evidence →
      PostPreserves functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode)
    (postFaults : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      CompatibleExpressionLiterals.ContextValid solved context evidence →
      PostFaults functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode) :
    LoopPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨size, sized⟩ := RecursiveNamedForContracts.ForOutcome.has_size trace
  exact loop_preserves_bounded functions program evidence transport size
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning child)
    conditionFound conditionTree typed unique
    (fun child _ => ProtectedWhile.Body.preserves_at_of_unbounded functions program evidence correct child)
    (fun agrees reference valid child _ => postpreserves_at_of_unbounded functions program evidence post postCode
      (postPreserves agrees reference valid) child)
    (fun agrees reference valid child _ => postfaults_at_of_unbounded functions program evidence post postCode
      (postFaults agrees reference valid) child)
    size (Nat.le_refl _) valid environments heaps locals agrees actualTyped reference read unmapped installed sized

include transport reflection in
theorem loop_reflects
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Reflects functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False)
    (postReflects : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      CompatibleExpressionLiterals.ContextValid solved context evidence →
      PostReflects functions program evidence (entry := entry) (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode) :
    LoopReflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    loop_reflects_bounded functions program evidence transport size
      (fun child _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded reflection child)
      conditionFound conditionTree typed
      (fun child _ => ProtectedWhile.Body.reflects_at_of_unbounded functions program evidence correct child)
      bodyCannotFault
      (fun agrees reference valid child _ => postreflects_at_of_unbounded functions program evidence faults post postCode
        (postReflects agrees reference valid) child)
      size (Nat.le_refl _) valid environments heaps locals agrees actualTyped reference read unmapped installed sized
  exact ⟨outcome, after, finalMap, finalWorld, trace.sound, rest⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body
