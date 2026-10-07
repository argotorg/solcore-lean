import Solcore.SourceSemantics.CoreLowering.ProtectedStateWhileEdges
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalControl
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLoopContracts

/-! One guarded five-way body interface for finite loops. The actual environment
and frame prefix are separate from the canonical protected entry. The old
lexical relation embeds without changing native values, captures or stores. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalControl (LexicalResult)
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

def Preserves (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
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
    (_trace : Executes mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after

def Reflects (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
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
    ∃ finalContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after

abbrev PreservesAt := @RecursiveNamedLoopContracts.PreservesAt
abbrev ReflectsAt := @RecursiveNamedLoopContracts.ReflectsAt

/-- Restrict an established body theorem to its actual source size. -/
theorem preserves_at_of_unbounded {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : Preserves functions program evidence (administrative := administrative) (entry := entry)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) mode statements expected type code)
    (size : Nat) : PreservesAt functions program evidence (administrative := administrative) (entry := entry)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) size mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact correct valid environments heaps locals agrees actualTyped reference read unmapped installed trace.sound

/-- Reflection keeps the supplied original native size. -/
theorem reflects_at_of_unbounded {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : Reflects functions program evidence (administrative := administrative) (entry := entry)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) mode statements expected type code)
    (size : Nat) : ReflectsAt functions program evidence (administrative := administrative) (entry := entry)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) size mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, lexical⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size trace
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, sized, represented, heaps, maps, worlds, frame, metadata, lexical⟩

/-- Embed the guarded lexical body while keeping its exact evaluation,
heap effects and reached source context. -/
theorem of_lexical_preserves {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) mode statements expected type code) :
    Preserves functions program evidence (administrative := administrative) (entry := entry)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope)
      mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata, lexical⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, preserved, metadata, lexical⟩

/-- Embed the guarded lexical body while keeping its exact evaluation,
heap effects and reached source context. -/
theorem of_lexical_reflects {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ProtectedLexicalAssignments.ControlAt.Reflects functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) mode statements expected type code) :
    Reflects functions program evidence (administrative := administrative) (entry := entry)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frameLayout) (globals := globals) (scope := scope)
      mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, metadata, lexical⟩ :=
    correct valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ⟨finalContext, outcome, after, finalMap, finalWorld, trace, FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, preserved, metadata, lexical⟩

variable {certificate : GenericExpressionMeaning.Certificate} {body : Expr}

include transport in
/-- Generic child meaning is an internal composition interface. The concrete
named consumer supplies it from the accepted recursive expression Tree. -/
theorem condition_preserves_at {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, progress, reached, _retained⟩ :=
    Stateful.condition_preserves_at (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      functions program evidence
      (RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        (expressions := fun _ => certificate) functions program evidence transport meaning)
      tree found agrees ⟨state.1, ⟨state.2⟩⟩ trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, related, progress, reached.live, reached.retained.down⟩

include transport in
/-- Actual completed condition code recovers the independent source outcome
and transports the original guard through the observed prefix effects. -/
theorem condition_reflects_at {size : Nat}
    (reflection : RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, _retained⟩ :=
    Stateful.condition_reflects_at (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      functions program evidence
      (RecursiveNamedLexicalContracts.Stateful.legacy_expression_reflects
        (expressions := fun _ => certificate) functions program evidence transport reflection)
      tree found agrees ⟨state.1, ⟨state.2⟩⟩ evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached.live, reached.retained.down⟩

include transport in
/-- The body contract is an internal composition interface. Recursive statement
induction supplies it for the current child, including control transfers. -/
theorem body_preserves_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : RecursiveNamedLoopContracts.PreservesAtFor (validity := validity) functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size false program context evidence source environment before statements finalContext outcome after) :
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
  have lifted := ProtectedStateTransition.Lexical.legacy_preserves functions program evidence transport correct
  have guarded := ProtectedStateTransition.Lexical.Gated.preserves_of_unguarded
    (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence lifted
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, reached, _retained, lexical⟩ :=
    Stateful.body_preserves_at_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) functions program evidence validity guarded valid agrees reference
      ⟨state.1, ⟨state.2⟩⟩ read True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, ⟨reached.live, reached.retained.down⟩, lexical⟩

include transport in
theorem body_preserves_at {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : PreservesAt functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  exact body_preserves_at_for (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    functions program evidence transport correct valid agrees reference state trace
include transport in
/-- A completed body reconstructs its independent source trace and reached
lexical context while retaining the original outer installed entry. -/
theorem body_reflects_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : RecursiveNamedLoopContracts.ReflectsAtFor (validity := validity) functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  obtain ⟨native, read⟩ := state.1.contextRead
  have lifted := ProtectedStateTransition.Lexical.legacy_reflects functions program evidence transport correct
  have guarded := ProtectedStateTransition.Lexical.Gated.reflects_of_unguarded
    (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence lifted
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, progress, reached, _retained, lexical⟩ :=
    Stateful.body_reflects_at_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) functions program evidence validity guarded valid agrees reference
      ⟨state.1, ⟨state.2⟩⟩ read True.intro evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, progress, ⟨reached.live, reached.retained.down⟩, lexical⟩

include transport in
theorem body_reflects_at {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ReflectsAt functions program evidence
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  exact body_reflects_at_for (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    functions program evidence transport correct valid agrees reference state evaluated
include transport in
theorem body_preserves {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : Preserves functions program evidence
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
  obtain ⟨size, sized⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size trace
  exact body_preserves_at functions program evidence transport
    (preserves_at_of_unbounded functions program evidence correct size) valid agrees reference state sized

include transport in
theorem body_reflects {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : Reflects functions program evidence
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
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    body_reflects_at functions program evidence transport
      (reflects_at_of_unbounded functions program evidence correct size) valid agrees reference state sized
  exact ⟨finalContext, outcome, after, finalMap, finalWorld, trace.sound, rest⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body
