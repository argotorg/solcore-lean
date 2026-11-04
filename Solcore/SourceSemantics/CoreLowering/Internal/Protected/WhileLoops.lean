import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileReflection

/-!
# Protected contracts: while loops

Body contracts, generic iteration, endpoints and reflection of `while` loops.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedWhileBodyContracts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedWhileGenericIteration
/-! Finite source while derivations run under the actual installed self-cell.
Each evaluated condition and lexical body retains the protected entry through
its observed heap, world and administrative progress. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile
open Core Frontend SourceInference
inductive SourceLoop (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition : ExpressionId) (statements : List StatementId) :
    Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {outcome after} (trace : Dynamic.WhileExecutes program context evidence source environment before condition statements context outcome after) :
      SourceLoop program context evidence source environment before condition statements outcome after
  | fault {reason after} (trace : Dynamic.WhileFaults program context evidence source environment before condition statements reason after) :
      SourceLoop program context evidence source environment before condition statements (.fault reason) after

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile

namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLoopContracts (Below)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)

theorem iterations_success_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.WhileExecutes program size context evidence source environment before condition statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {native : CallableIndexedHistory.NativeFrame} {faults : FunctionCalls.FaultRep},
      Below budget (fun size => ExpressionPreservesAt protocol readiness (context := context) (source := source) (faults := faults)
        program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness guard facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      exprFacts context condition node → facts context false statements expected →
      ∀ state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native → readiness.Ready context state.retained →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ PostReady readiness context outcome reached.retained := by
  induction size using Nat.strongRecOn generalizing context finalContext evidence source environment before after condition statements outcome with
  | ind size ih =>
    intro budget bounded certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node native faults
      meaning conditionTree found valid unique agrees reference correct conditionFacts bodyFacts state fixedRead guarded ready
    cases trace with
      | done conditionEvaluation =>
        obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
        cases represented with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          exact ⟨_, nextStore, nextMap, nextWorld, .done evaluated, .fallthrough environment, progress, conditionState, conditionRetained, conditionPost.1⟩
      | nextFallthrough conditionEvaluation bodyEvaluation next =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) (readiness := readiness) (facts := facts) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
          cases bodyRelated with
          | fallthrough _ =>
            have progress := conditionProgress.trans bodyProgress
            let nextState := bodyState
            obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress, finalState, finalRetained, finalPost⟩ :=
              ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget
                (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded)
                meaning conditionTree found valid unique agrees reference correct conditionFacts bodyFacts nextState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded bodyPost
            exact ⟨result, finalStore, finalMap, finalWorld,
              .nextFallthrough conditionEval bodyEval nextState.live.selfRead nativeTrace, related, progress.trans finalProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained, finalPost⟩
      | nextContinue conditionEvaluation bodyEvaluation next =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) (readiness := readiness) (facts := facts) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
          cases bodyRelated with
          | continuing _ =>
            have progress := conditionProgress.trans bodyProgress
            let nextState := bodyState
            obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress, finalState, finalRetained, finalPost⟩ :=
              ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget
                (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded)
                meaning conditionTree found valid unique agrees reference correct conditionFacts bodyFacts nextState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded bodyPost
            exact ⟨result, finalStore, finalMap, finalWorld,
              .nextContinue conditionEval bodyEval nextState.live.selfRead nativeTrace, related, progress.trans finalProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained, finalPost⟩
      | breaks conditionEvaluation bodyEvaluation =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) (readiness := readiness) (facts := facts) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
          cases bodyRelated with
          | breaking _ =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, .breaks conditionEval bodyEval, .fallthrough environment, conditionProgress.trans bodyProgress, bodyState, protocol.trans conditionRetained bodyRetained, bodyPost⟩
      | returns conditionEvaluation bodyEvaluation =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) (readiness := readiness) (facts := facts) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
          cases bodyRelated with
          | returned payload =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, .returns conditionEval bodyEval, .returned payload, conditionProgress.trans bodyProgress, bodyState, protocol.trans conditionRetained bodyRetained, bodyPost⟩

theorem iterations_fault_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.WhileFaults program size context evidence source environment before condition statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {native : CallableIndexedHistory.NativeFrame} {faults : FunctionCalls.FaultRep},
      Below budget (fun size => ExpressionPreservesAt protocol readiness (context := context) (source := source) (faults := faults)
        program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness guard facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      exprFacts context condition node → facts context false statements expected →
      ∀ state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native → readiness.Ready context state.retained →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ PostReady readiness context (.fault reason) reached.retained := by
  induction size using Nat.strongRecOn generalizing context evidence source environment before after condition statements reason with
  | ind size ih =>
    intro budget bounded certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code selfReason mapping world store node native faults
      meaning conditionTree found valid unique agrees reference correct conditionFacts bodyFacts state fixedRead guarded ready
    cases trace with
      | condition conditionFault =>
        obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.fault conditionFault)
        cases represented with
        | fault matched => exact ⟨_, nextStore, nextMap, nextWorld, .conditionFault evaluated, .fault matched, progress, conditionState, conditionRetained, conditionPost⟩
      | conditionType conditionEvaluation notBoolean runtimeType =>
        obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
        cases represented with
        | value payload =>
          obtain ⟨boolean, rfl, _⟩ := bool_fields payload
          exact False.elim (notBoolean trivial)
      | body conditionEvaluation bodyFault =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) (readiness := readiness) (facts := facts) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.fault bodyFault)
          cases bodyRelated with
          | fault matched => exact ⟨_, bodyStore, bodyMap, bodyWorld, .bodyFault conditionEval bodyEval, .fault matched, conditionProgress.trans bodyProgress, bodyState, protocol.trans conditionRetained bodyRetained, bodyPost⟩
      | nextFallthrough conditionEvaluation bodyEvaluation next =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) (readiness := readiness) (facts := facts) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
          cases bodyRelated with
          | fallthrough _ =>
            have progress := conditionProgress.trans bodyProgress
            let nextState := bodyState
            obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress, finalState, finalRetained, finalPost⟩ :=
              ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget
                (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded)
                meaning conditionTree found valid unique agrees reference correct conditionFacts bodyFacts nextState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded bodyPost
            exact ⟨result, finalStore, finalMap, finalWorld,
              .nextFallthrough conditionEval bodyEval nextState.live.selfRead nativeTrace, related, progress.trans finalProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained, finalPost⟩
      | nextContinue conditionEvaluation bodyEvaluation next =>
        obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence
            (meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) conditionTree found conditionFacts agrees state ready (.value conditionEvaluation)
        cases conditionRelated with
        | value payload =>
          obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
            body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity) (readiness := readiness) (facts := facts) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded)) valid bodyFacts agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 (.control bodyEvaluation)
          cases bodyRelated with
          | continuing _ =>
            have progress := conditionProgress.trans bodyProgress
            let nextState := bodyState
            obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress, finalState, finalRetained, finalPost⟩ :=
              ih _ (SourceExecutionSize.child_lt_stepSize (by simp)) next budget
                (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded)
                meaning conditionTree found valid unique agrees reference correct conditionFacts bodyFacts nextState
                (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded bodyPost
            exact ⟨result, finalStore, finalMap, finalWorld,
              .nextContinue conditionEval bodyEval nextState.live.selfRead nativeTrace, related, progress.trans finalProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained, finalPost⟩

variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {native : CallableIndexedHistory.NativeFrame}
  {budget : Nat}
  (reflection : Below budget (fun size => ExpressionReflectsAt protocol readiness (context := context) (source := source) (faults := faults)
    program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size))


include reflection in
theorem iterations_reflect_bounded_for (validity : SourceSemantics.Context → Prop) {condition : ExpressionId} {node : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (conditionFacts : exprFacts context condition node)
    (bodyFacts : facts context false statements expected)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness guard facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      ∀ state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native → readiness.Ready context state.retained →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedLoopContracts.WhileOutcome program sourceSize context evidence source environment before condition statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ PostReady readiness context outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before store finalStore value state fixedRead guarded ready evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, conditionSmaller, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionSourceSize, conditionOutcome, conditionHeap, conditionMap, conditionWorld, conditionTrace, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
      condition_reflects_at (protocol := protocol) (readiness := readiness) (exprFacts := exprFacts) functions program evidence (reflection _ (Nat.lt_of_lt_of_le conditionSmaller bounded)) conditionTree found conditionFacts agrees state ready conditionEval
    cases conditionRelated with
    | fault matched =>
      cases conditionTrace with
      | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure conditionEval.sound)
        exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .fault (.condition failed), .fault matched, conditionProgress, conditionState, conditionRetained, conditionPost⟩
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      subst sameSource
      subst sameCore
      cases conditionTrace with
      | value conditionTrace =>
        cases boolean with
        | false =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false conditionEval.sound)
          exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .control (.done conditionTrace), .fallthrough environment, conditionProgress, conditionState, conditionRetained, conditionPost.1⟩
        | true =>
          obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch conditionEval.sound
          obtain ⟨bodySize, bodyStore, bodyValue, bodySmaller, bodyEval⟩ := branch.bind_computation
          obtain ⟨bodySourceSize, bodyContext, bodyOutcome, bodyHeap, bodyMap, bodyWorld, bodyTrace, bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost, _lexical⟩ :=
            body_reflects_at_for (protocol := protocol) (guard := guard) (validity := validity) (readiness := readiness) (facts := facts) functions program evidence
              (correct _ (Nat.lt_of_lt_of_le bodySmaller (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded)))
              valid bodyFacts agrees reference conditionState
              (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead conditionProgress.2.2.2.1).2 guarded conditionPost.1 bodyEval
          have progress := conditionProgress.trans bodyProgress
          cases bodyRelated with
          | fault matched =>
            cases bodyTrace with
            | control impossible => exact False.elim (bodyCannotFault impossible.sound)
            | fault failed =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_failure conditionEval.sound bodyEval.sound)
              exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .fault (.body conditionTrace failed), .fault matched, progress, bodyState, protocol.trans conditionRetained bodyRetained, bodyPost⟩
          | returned payload =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_returned conditionEval.sound bodyEval.sound)
              exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .control (.returns conditionTrace bodyTrace), .returned payload, progress, bodyState, protocol.trans conditionRetained bodyRetained, bodyPost⟩
          | breaking bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_breaking conditionEval.sound bodyEval.sound)
              exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .control (.breaks conditionTrace bodyTrace), .fallthrough environment, progress, bodyState, protocol.trans conditionRetained bodyRetained, bodyPost⟩
          | fallthrough bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              let nextState := bodyState
              obtain ⟨nextSize, smaller, nextEval⟩ := branch.loop_next_fallthrough bodyEval.sound nextState.live.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress, finalState, finalRetained, finalPost⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) nextState
                  (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded bodyPost nextEval
              cases nextTrace with
              | control nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .control (.nextFallthrough conditionTrace bodyTrace nextTrace), related, progress.trans nextProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained, finalPost⟩
              | fault nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .fault (.nextFallthrough conditionTrace bodyTrace nextTrace), related, progress.trans nextProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained, finalPost⟩
          | continuing bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              let nextState := bodyState
              obtain ⟨nextSize, smaller, nextEval⟩ := branch.loop_next_continuing bodyEval.sound nextState.live.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress, finalState, finalRetained, finalPost⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) nextState
                  (TypedLexicalWhile.retain state.live.contextUnmapped fixedRead progress.2.2.2.1).2 guarded bodyPost nextEval
              cases nextTrace with
              | control nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .control (.nextContinue conditionTrace bodyTrace nextTrace), related, progress.trans nextProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained, finalPost⟩
              | fault nextTrace => exact ⟨_, _, after, finalMap, finalWorld, .fault (.nextContinue conditionTrace bodyTrace nextTrace), related, progress.trans nextProgress, finalState, protocol.trans (protocol.trans conditionRetained bodyRetained) finalRetained, finalPost⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful.WithReady

namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLoopContracts (Below)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem iterations_success_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.WhileExecutes program size context evidence source environment before condition statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {native : CallableIndexedHistory.NativeFrame} {faults : FunctionCalls.FaultRep},
      Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults size) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      ∀ state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  intro budget bounded certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node native faults
    meaning conditionTree found valid unique agrees reference correct state fixedRead guarded
  obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, related, progress, reached, retained, _post⟩ :=
    WithReady.iterations_success_bounded_for (protocol := protocol) (guard := guard) (validity := validity)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) (facts := fun _ _ _ _ => True) trace budget bounded
      (fun child strict => WithReady.expression_preserves_trivial protocol (meaning child strict))
      conditionTree found valid unique agrees reference
      (fun child strict => WithReady.body_preserves_trivial protocol guard functions program evidence validity (correct child strict))
      True.intro True.intro state fixedRead guarded True.intro
  exact ⟨value, finalStore, finalMap, finalWorld, nativeTrace, related, progress, reached, retained⟩

theorem iterations_fault_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.WhileFaults program size context evidence source environment before condition statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {native : CallableIndexedHistory.NativeFrame} {faults : FunctionCalls.FaultRep},
      Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults size) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      ∀ state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  intro budget bounded certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node native faults
    meaning conditionTree found valid unique agrees reference correct state fixedRead guarded
  obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, related, progress, reached, retained, _post⟩ :=
    WithReady.iterations_fault_bounded_for (protocol := protocol) (guard := guard) (validity := validity)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) (facts := fun _ _ _ _ => True) trace budget bounded
      (fun child strict => WithReady.expression_preserves_trivial protocol (meaning child strict))
      conditionTree found valid unique agrees reference
      (fun child strict => WithReady.body_preserves_trivial protocol guard functions program evidence validity (correct child strict))
      True.intro True.intro state fixedRead guarded True.intro
  exact ⟨value, finalStore, finalMap, finalWorld, nativeTrace, related, progress, reached, retained⟩

variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {native : CallableIndexedHistory.NativeFrame}
  {budget : Nat}
  (reflection : Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults size))


include reflection in
theorem iterations_reflect_bounded_for (validity : SourceSemantics.Context → Prop) {condition : ExpressionId} {node : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      ∀ state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store,
      store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
      guard contextLocation native →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedLoopContracts.WhileOutcome program sourceSize context evidence source environment before condition statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  intro size bounded mapping world before store finalStore value state fixedRead guarded evaluation
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, _post⟩ :=
    WithReady.iterations_reflect_bounded_for (protocol := protocol) (guard := guard) (validity := validity)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) (facts := fun _ _ _ _ => True) functions program evidence
      (fun child strict => WithReady.expression_reflects_trivial protocol (reflection child strict))
      conditionTree found True.intro True.intro valid agrees reference
      (fun child strict => WithReady.body_reflects_trivial protocol guard functions program evidence validity (correct child strict))
      bodyCannotFault size bounded state fixedRead guarded True.intro evaluation
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful

namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLoopContracts (Below)

theorem iterations_success_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.WhileExecutes program size context evidence source environment before condition statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor (validity := validity) functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  obtain ⟨native, fixedRead⟩ := state.1.contextRead
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, _reached, _retained⟩ :=
    Stateful.iterations_success_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) (validity := validity) trace budget bounded
      (fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        (expressions := fun _ => certificate) functions program evidence transport (meaning child childBound))
      conditionTree found valid unique agrees reference
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.preserves_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_preserves functions program evidence transport (correct child childBound)))
      ⟨state.1, ⟨state.2⟩⟩ fixedRead True.intro
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩

theorem iterations_success_bounded
    {program : Program} {size : Nat} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : SourceExecutionSize.WhileExecutes program size context evidence source environment before condition statements finalContext outcome after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => PreservesAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  exact iterations_success_bounded_for
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    trace budget bounded transport meaning conditionTree found valid unique agrees reference correct state

theorem iterations_fault_bounded_for (validity : SourceSemantics.Context → Prop)
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.WhileFaults program size context evidence source environment before condition statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      validity context → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor (validity := validity) functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  obtain ⟨native, fixedRead⟩ := state.1.contextRead
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, _reached, _retained⟩ :=
    Stateful.iterations_fault_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) (validity := validity) trace budget bounded
      (fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        (expressions := fun _ => certificate) functions program evidence transport (meaning child childBound))
      conditionTree found valid unique agrees reference
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.preserves_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_preserves functions program evidence transport (correct child childBound)))
      ⟨state.1, ⟨state.2⟩⟩ fixedRead True.intro
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩

theorem iterations_fault_bounded
    {program : Program} {size : Nat} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.WhileFaults program size context evidence source environment before condition statements reason after) :
    ∀ (budget : Nat), size ≤ budget →
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry) →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Below budget (fun size => PreservesAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) size false statements expected type code) →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro budget bounded entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  exact iterations_fault_bounded_for
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    trace budget bounded transport meaning conditionTree found valid unique agrees reference correct state

section BoundedReflection
variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)
  {budget : Nat}
  (reflection : Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry))

include transport reflection in
theorem iterations_reflect_bounded_for (validity : SourceSemantics.Context → Prop) {condition : ExpressionId} {node : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAtFor (validity := validity) functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedLoopContracts.WhileOutcome program sourceSize context evidence source environment before condition statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro size bounded mapping world before store finalStore value state evaluation
  obtain ⟨native, fixedRead⟩ := state.1.contextRead
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress, _reached, _retained⟩ :=
    Stateful.iterations_reflect_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) functions program evidence
      (fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_reflects
        (expressions := fun _ => certificate) functions program evidence transport (reflection child childBound))
      validity conditionTree found valid agrees reference
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.reflects_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_reflects functions program evidence transport (correct child childBound)))
      bodyCannotFault size bounded ⟨state.1, ⟨state.2⟩⟩ fixedRead True.intro evaluation
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress⟩

include transport reflection in
theorem iterations_reflect_bounded {condition : ExpressionId} {node : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Below budget (fun size => ReflectsAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat), size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedLoopContracts.WhileOutcome program sourceSize context evidence source environment before condition statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  exact iterations_reflect_bounded_for
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    functions program evidence transport reflection conditionTree found valid agrees reference correct bodyCannotFault

end BoundedReflection

theorem iterations_success
    {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.WhileExecutes program context evidence source environment before condition statements finalContext outcome after) :
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  obtain ⟨size, sized⟩ := SourceExecutionSize.WhileExecutes.has_size trace
  exact iterations_success_bounded sized size (Nat.le_refl _)
    transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size)
    conditionTree found valid unique agrees reference
    (fun child _ => preserves_at_of_unbounded functions program evidence correct child) state


theorem iterations_fault
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.WhileFaults program context evidence source environment before condition statements reason after) :
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  obtain ⟨size, sized⟩ := SourceExecutionSize.WhileFaults.has_size trace
  exact iterations_fault_bounded sized size (Nat.le_refl _)
    transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size)
    conditionTree found valid unique agrees reference
    (fun child _ => preserves_at_of_unbounded functions program evidence correct child) state


variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)
  (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)

include transport reflection in
theorem iterations_reflect {condition : ExpressionId} {node : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Reflects functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat) {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason) value finalStore →
      ∃ outcome after finalMap finalWorld,
        SourceLoop program context evidence source environment before condition statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro size mapping world before store finalStore value state evaluation
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress⟩ :=
    iterations_reflect_bounded functions program evidence transport
      (RecursiveNamedBoundedContracts.reflects_below_of_unbounded reflection size)
      conditionTree found valid agrees reference
      (fun child _ => reflects_at_of_unbounded functions program evidence correct child)
      bodyCannotFault size (Nat.le_refl _) state evaluation
  refine ⟨outcome, after, finalMap, finalWorld, ?_, represented, progress⟩
  cases trace with
  | control trace => exact .control trace.sound
  | fault trace => exact .fault trace.sound

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedWhileGenericEndpoint
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


def HeadPreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
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
    (_trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical

def HeadPreservesAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  HeadPreservesAtFor functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
    (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope)
    size id expected type code


def HeadReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
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
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical

def HeadReflectsAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  HeadReflectsAtFor functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
    (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope)
    size id expected type code


end Solcore.SourceSemantics.CoreLowering.ProtectedWhile

namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep Restored)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context} {type : Ty} {conditionCode code : Expr} {selfReason : Word} {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}

def HeadPreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
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
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_guarded : guard contextLocation native)
    (_trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def HeadReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
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
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_guarded : guard contextLocation native)
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Stateful

namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedLoopContracts (Below)
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep Restored restored restore_rep)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context} {type : Ty} {conditionCode code : Expr} {selfReason : Word} {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (transport : AdministrativeTransport protocol)

include transport in
/-- The real renamed self-cell prelude preserves the original record vector. -/
theorem initial_state {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
    {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
    {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation store.length type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping
      (TypedLexicalWhile.installedWorld world type) before
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason actual),
      Progress values registry functions before before mapping mapping world (TypedLexicalWhile.installedWorld world type) store
        (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason actual) ∧
      protocol.Relates initial reached.retained ∧ protocol.records reached.retained = protocol.records initial := by
  have actualCode := typed.rename (TypedLexicalWhile.environment_respects environments.runtime_hasTypes actualTyped agrees)
  rw [LoopRenaming.whileLoop] at actualCode
  let reached := ProtectedStateTransition.While.install transport environments heaps locals actualTyped actualCode read unmapped initial
  have facts := TypedLexicalWhile.install selfReason heaps actualTyped actualCode
  exact ⟨reached, ⟨facts.1, .refl mapping, facts.2.1, facts.2.2.2.2.2, .refl before⟩,
    ProtectedStateTransition.While.install_related transport environments heaps locals actualTyped actualCode read unmapped initial,
    ProtectedStateTransition.While.install_records transport environments heaps locals actualTyped actualCode read unmapped initial⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful

namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedLoopContracts (Below)
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep Restored restored restore_rep)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context} {type : Ty} {conditionCode code : Expr} {selfReason : Word} {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (transport : AdministrativeTransport protocol)

open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (activation : ActivationTransfers protocol readiness)

private theorem post_restore {index : Index} (readiness : Readiness protocol)
    (environment : Dynamic.Environment) (outcome : Dynamic.ControlOutcome) {reached : protocol.State index}
    (post : PostReady readiness context outcome reached) :
    PostReady readiness context (Dynamic.restoreControl environment outcome) reached := by
  cases outcome <;> exact post

include transport activation in
theorem while_preserves_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaningB : Below budget (fun size => ExpressionPreservesAt protocol readiness (context := context) (source := source) (faults := faults)
      program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size)) {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionFacts : exprFacts context condition conditionNode)
    (bodyFacts : facts context false statements expected)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness guard facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code)) :
    ∀ size, size ≤ budget → RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadPreservesAtWith protocol readiness guard (fun _ _ _ => True) (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro size bounded valid _headFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed guarded ready trace
  obtain ⟨protectedState, installedProgress, installedRelated, _installedRecords⟩ :=
    ProtectedWhile.Body.Stateful.initial_state (protocol := protocol) functions transport environments heaps locals agrees actualTyped read unmapped typed installed
  have activated := activation.ready installed protectedState.retained installedProgress.2.2.2.1
    installedRelated _installedRecords ready
  have installedRead := (TypedLexicalWhile.retain unmapped read installedProgress.2.2.2.1).2
  cases trace with
  | control sourceTrace =>
    obtain ⟨rfl, child, _, innerOutcome, rfl, sourceLoop, smaller⟩ := RecursiveNamedLoopContracts.statement_while_control unique (lookupStatement?_sound found) form sourceTrace
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress, reached, related, post⟩ :=
      iterations_success_bounded_for (protocol := protocol) (guard := guard) (validity := validity) (readiness := readiness) (exprFacts := exprFacts) (facts := facts) sourceLoop budget (Nat.le_trans (Nat.le_of_lt smaller) bounded) meaningB conditionTree conditionFound valid unique agrees reference correct conditionFacts bodyFacts protectedState installedRead guarded activated
    exact ⟨rfl, restored environment innerOutcome, value, finalStore, finalMap, finalWorld,
      by simpa only [LoopRenaming.whileLoop] using nativeTrace.whileLoop_evaluates,
      restore_rep represented environment, (installedProgress.trans progress).1,
      (installedProgress.trans progress).2.1, (installedProgress.trans progress).2.2.1,
      (installedProgress.trans progress).2.2.2.1, (installedProgress.trans progress).2.2.2.2,
      ⟨reached.retained, protocol.trans installedRelated related, post_restore protocol readiness environment innerOutcome post⟩⟩
  | fault failed =>
    obtain ⟨child, sourceLoop, smaller⟩ := RecursiveNamedLoopContracts.statement_while_fault unique (lookupStatement?_sound found) form failed
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress, reached, related, post⟩ :=
      iterations_fault_bounded_for (protocol := protocol) (guard := guard) (validity := validity) (readiness := readiness) (exprFacts := exprFacts) (facts := facts) sourceLoop budget (Nat.le_trans (Nat.le_of_lt smaller) bounded) meaningB conditionTree conditionFound valid unique agrees reference correct conditionFacts bodyFacts protectedState installedRead guarded activated
    exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld,
      by simpa only [LoopRenaming.whileLoop] using nativeTrace.whileLoop_evaluates,
      represented, (installedProgress.trans progress).1,
      (installedProgress.trans progress).2.1, (installedProgress.trans progress).2.2.1,
      (installedProgress.trans progress).2.2.2.1, (installedProgress.trans progress).2.2.2.2,
      ⟨reached.retained, protocol.trans installedRelated related, post⟩⟩

include transport activation in
theorem while_reflects_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (reflectionB : Below budget (fun size => ExpressionReflectsAt protocol readiness (context := context) (source := source) (faults := faults)
      program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size)) {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionFacts : exprFacts context condition conditionNode)
    (bodyFacts : facts context false statements expected)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness guard facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ size, size ≤ budget → RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadReflectsAtWith protocol readiness guard (fun _ _ _ => True) (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro size bounded valid _headFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed guarded ready evaluated
  obtain ⟨protectedState, installedProgress, installedRelated, _installedRecords⟩ :=
    ProtectedWhile.Body.Stateful.initial_state (protocol := protocol) functions transport environments heaps locals agrees actualTyped read unmapped typed installed
  have activated := activation.ready installed protectedState.retained installedProgress.2.2.2.1
    installedRelated _installedRecords ready
  have installedRead := (TypedLexicalWhile.retain unmapped read installedProgress.2.2.2.1).2
  rw [LoopRenaming.whileLoop] at evaluated
  obtain ⟨entrySize, entrySmaller, nativeEntry⟩ := evaluated.iterate_entry
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress, reached, related, post⟩ :=
    iterations_reflect_bounded_for (protocol := protocol) (guard := guard) (validity := validity) (readiness := readiness) (exprFacts := exprFacts) (facts := facts) functions program evidence reflectionB conditionTree conditionFound conditionFacts bodyFacts valid agrees reference correct
      bodyCannotFault entrySize (Nat.le_trans (Nat.le_of_lt entrySmaller) bounded) protectedState installedRead guarded activated nativeEntry
  have statementTrace : RecursiveNamedLoopContracts.StatementOutcome program (SourceExecutionSize.stepSize [sourceSize])
      context evidence source environment before id context (Dynamic.restoreControl environment outcome) after := by
    cases trace with
    | control sourceLoop => exact .control (.whileLoop (lookupStatement?_sound found) form sourceLoop)
    | fault sourceLoop => exact .fault (.whileIteration (lookupStatement?_sound found) form sourceLoop)
  exact ⟨SourceExecutionSize.stepSize [sourceSize], Dynamic.restoreControl environment outcome, after, finalMap, finalWorld,
    statementTrace, restored environment outcome, restore_rep represented environment, (installedProgress.trans progress).1,
    (installedProgress.trans progress).2.1, (installedProgress.trans progress).2.2.1,
    (installedProgress.trans progress).2.2.2.1, (installedProgress.trans progress).2.2.2.2,
    ⟨reached.retained, protocol.trans installedRelated related, post_restore protocol readiness environment outcome post⟩⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful.WithReady

namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedLoopContracts (Below)
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep Restored restored restore_rep)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context} {type : Ty} {conditionCode code : Expr} {selfReason : Word} {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (transport : AdministrativeTransport protocol)

include transport in
theorem while_preserves_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaningB : Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults size)) {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code)) :
    ∀ size, size ≤ budget → ProtectedWhile.Stateful.HeadPreservesAtFor protocol guard (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro size bounded valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed guarded trace
  obtain ⟨sameContext, restored, value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    WithReady.while_preserves_bounded_for (protocol := protocol) (guard := guard) (validity := validity)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) (facts := fun _ _ _ _ => True)
      (activation := WithReady.ActivationTransfers.trivial protocol)
      functions program evidence transport budget
      (fun child strict => WithReady.expression_preserves_trivial protocol (meaningB child strict))
      found form conditionFound True.intro True.intro conditionTree typed unique
      (fun child strict => WithReady.body_preserves_trivial protocol guard functions program evidence validity (correct child strict))
      size bounded valid True.intro environments heaps locals agrees actualTyped reference read unmapped installed guarded True.intro trace
  exact ⟨sameContext, restored, value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, post.forget⟩

include transport in
theorem while_reflects_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (reflectionB : Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults size)) {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Below budget (fun size => ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ size, size ≤ budget → ProtectedWhile.Stateful.HeadReflectsAtFor protocol guard (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro size bounded valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed guarded evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented,
    finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    WithReady.while_reflects_bounded_for (protocol := protocol) (guard := guard) (validity := validity)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) (facts := fun _ _ _ _ => True)
      (activation := WithReady.ActivationTransfers.trivial protocol)
      functions program evidence transport budget
      (fun child strict => WithReady.expression_reflects_trivial protocol (reflectionB child strict))
      found form conditionFound True.intro True.intro conditionTree typed
      (fun child strict => WithReady.body_reflects_trivial protocol guard functions program evidence validity (correct child strict))
      bodyCannotFault size bounded valid True.intro environments heaps locals agrees actualTyped reference read unmapped installed guarded True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented,
    finalHeaps, maps, worlds, frame, metadata, post.forget⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful

namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedLoopContracts (Below)
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

include transport in
theorem while_preserves_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaningB : Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)) {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedLoopContracts.PreservesAtFor (validity := validity) functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code)) :
    ∀ size, size ≤ budget → HeadPreservesAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro size bounded valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨sameContext, restored, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, _related⟩ :=
    Stateful.while_preserves_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) functions program evidence (ProtectedStateTransition.Lexical.legacyTransport transport)
      validity budget
      (fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        (expressions := fun _ => certificate) functions program evidence transport (meaningB child childBound))
      found form conditionFound conditionTree typed unique
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.preserves_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_preserves functions program evidence transport (correct child childBound)))
      size bounded valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ True.intro trace
  exact ⟨sameContext, restored, value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, reached.down⟩

include transport in
theorem while_preserves_bounded (budget : Nat)
    (meaningB : Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)) {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => PreservesAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code)) :
    ∀ size, size ≤ budget → HeadPreservesAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  exact while_preserves_bounded_for
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    functions program evidence transport budget meaningB found form conditionFound conditionTree typed unique correct


include transport in
theorem while_reflects_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (reflectionB : Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)) {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAtFor (validity := validity) functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ size, size ≤ budget → HeadReflectsAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro size bounded valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, _related⟩ :=
    Stateful.while_reflects_bounded_for (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry)
      (guard := fun _ _ => True) functions program evidence (ProtectedStateTransition.Lexical.legacyTransport transport)
      validity budget
      (fun child childBound => RecursiveNamedLexicalContracts.Stateful.legacy_expression_reflects
        (expressions := fun _ => certificate) functions program evidence transport (reflectionB child childBound))
      found form conditionFound conditionTree typed
      (fun child childBound => ProtectedStateTransition.Lexical.Gated.reflects_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_reflects functions program evidence transport (correct child childBound)))
      bodyCannotFault size bounded valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented,
    finalHeaps, maps, worlds, frame, metadata, reached.down⟩

include transport in
theorem while_reflects_bounded (budget : Nat)
    (reflectionB : Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)) {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Below budget (fun size => ReflectsAt functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ size, size ≤ budget → HeadReflectsAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  exact while_reflects_bounded_for
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    functions program evidence transport budget reflectionB found form conditionFound conditionTree typed correct bodyCannotFault


include transport meaning in
theorem while_preserves {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code) :
    HeadPreserves (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  obtain ⟨size, sized⟩ := RecursiveNamedLoopContracts.StatementOutcome.has_size trace
  exact while_preserves_bounded functions program evidence transport size
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning child)
    found form conditionFound conditionTree typed unique
    (fun child _ => preserves_at_of_unbounded functions program evidence correct child)
    size (Nat.le_refl _) valid environments heaps locals agrees actualTyped reference read unmapped installed sized

include transport reflection in
theorem while_reflects {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (correct : Reflects functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    HeadReflects (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    while_reflects_bounded functions program evidence transport size
      (fun child _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded reflection child)
      found form conditionFound conditionTree typed
      (fun child _ => reflects_at_of_unbounded functions program evidence correct child)
      bodyCannotFault size (Nat.le_refl _) valid environments heaps locals agrees actualTyped reference read unmapped installed sized
  exact ⟨outcome, after, finalMap, finalWorld, trace.sound, rest⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedWhileIteration
/-! Finite source while derivations run under the actual installed self-cell.
Each evaluated condition and lexical body retains the protected entry through
its observed heap, world and administrative progress. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open CompatibleExpressionPrimitives (bool_fields)

theorem iterations_success
    {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.WhileExecutes program context evidence source environment before condition statements finalContext outcome after) :
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore  := by
  intro entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  exact Body.iterations_success trace transport meaning conditionTree found valid unique agrees reference
    (Body.of_lexical_preserves functions program evidence correct) state

theorem iterations_fault
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.WhileFaults program context evidence source environment before condition statements reason after) :
    ∀ {entry : ProtectedExpressionMeaning.Entry} {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep},
      ProtectedExpressionMeaning.Transport entry →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source certificate faults entry →
      certificate scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore  := by
  intro entry certificate values scope solved ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
    contextLocation location expected type conditionCode code selfReason mapping world store node faults
    transport meaning conditionTree found valid unique agrees reference correct state
  exact Body.iterations_fault trace transport meaning conditionTree found valid unique agrees reference
    (Body.of_lexical_preserves functions program evidence correct) state

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedWhileReflection
/-! Completed native iterations reconstruct source iterations by strict
induction on the actual Core derivation. Condition and body traces are obtained
from their concrete-tree induction hypotheses, including their heap effects. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open CompatibleExpressionPrimitives (bool_fields)

variable {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)
  (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)

include transport reflection in
theorem iterations_reflect {condition : ExpressionId} {node : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : ProtectedLexicalAssignments.ControlAt.Reflects functions program evidence (entry := entry) (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat) {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      State entry values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason) value finalStore →
      ∃ outcome after finalMap finalWorld,
        SourceLoop program context evidence source environment before condition statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore  := by
  exact Body.iterations_reflect functions program evidence transport reflection conditionTree found valid agrees reference
    (Body.of_lexical_reflects functions program evidence correct) bodyCannotFault

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedWhileEndpoint
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
      (scope := scope) id expected type (LocalLoop.whileLoop type conditionCode code selfReason)  := by
  exact Body.while_preserves functions program evidence transport meaning found form conditionFound conditionTree typed unique
    (Body.of_lexical_preserves functions program evidence correct)

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
      (scope := scope) id expected type (LocalLoop.whileLoop type conditionCode code selfReason)  := by
  exact Body.while_reflects functions program evidence transport reflection found form conditionFound conditionTree typed
    (Body.of_lexical_reflects functions program evidence correct) bodyCannotFault

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile
end
