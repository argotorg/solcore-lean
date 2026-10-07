import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeLexicalBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds

/-! The static lexical Tree closes this ordinary-let fragment itself. Its
expression certificate is empty, so no expression or body semantic callback is
assumed. The actual owned producer supplies allocation, captured state and the
registered post-pool; binder restoration retains that reached pool. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedLexicalBody
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open ProtectedStateTransition

/-- A static tree with this certificate has no executable expression leaf. -/
def noExpressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  fun _ _ _ _ => False

def noExpressionSyntax : ExpressionId → Prop := fun _ => False

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- Transport only the native definition index of the concrete owned producer. -/
private def ownedProducer {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment}
    (model : GenericHeap.PayloadModel catalog projects definitions)
    (sameDefinitions : compiled.indexed.layouts.definitions = definitions) :
    OrdinaryAllocation.Producer (protocol headers keys) compiled.indexed.layouts
      compiled.indexed.ancestry.layout.frame model := by
  subst definitions
  exact CallableIndexedOwnedAllocationProducer.producer headers keys model

private theorem acquire {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (sameDefinitions : compiled.indexed.layouts.definitions = definitions)
    (location : Location) (native : NativeFrame)
    (seed : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (ownedProducer (headers := headers) (keys := keys) model sameDefinitions) location native := by
  subst definitions
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner model seed

private theorem no_expression_preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {faults : FunctionCalls.FaultRep} (size : Nat) :
    ProtectedStateTransition.PreservesAt (protocol headers keys) model program context evidence source
      (noExpressions context) faults size := by
  intro scope id lowered impossible
  cases impossible

private theorem no_expression_reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {faults : FunctionCalls.FaultRep} (size : Nat) :
    ProtectedStateTransition.ReflectsAt (protocol headers keys) model program context evidence source
      (noExpressions context) faults size := by
  intro scope id lowered impossible
  cases impossible

section Tree
variable {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
  (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
  {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
  (tree : GenericLexicalStatements.Tree compiled.indexed.layouts owner active compiled.indexed.ancestry.layout.frame
    globals onError values source noExpressions context scope mode statements expected type code)

include definitions registered tree in
/-- All semantic children are derived from the static empty certificate. -/
theorem closed_tree_preserves_at (size : Nat) (unique : NodeOccurrencesUnique source) :
    RecursiveNamedLexicalContracts.Stateful.PreservesAtFor (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program evidence
      (fun _ => True) size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro _valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped initial seed trace
  exact RecursiveNamedLexicalTreeBounds.Stateful.preserves_at_for functions definitions registered program evidence
    (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ownedProducer (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (acquire (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (fun _ => True) (fun _ _ => trivial) size size (Nat.le_refl _) (fun child _ _ _ =>
      no_expression_preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions) child)
    tree trivial unique environments heaps locals agrees typed reference read unmapped initial seed trace

include definitions registered tree in
/-- The original native child grade remains the reflection bound. -/
theorem closed_tree_reflects_at (size : Nat) :
    RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program evidence
      (fun _ => True) size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro _valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial seed evaluated
  exact RecursiveNamedLexicalTreeBounds.Stateful.reflects_at_for functions definitions registered program evidence
    (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ownedProducer (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (acquire (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (fun _ => True) (fun _ _ => trivial) size size (Nat.le_refl _) (fun child _ _ _ =>
      no_expression_reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions) child)
    tree trivial environments heaps locals agrees typed reference read unmapped initial seed evaluated
end Tree

/-- The reached witness keeps every ordered row and authentic snapshot read. -/
theorem reached_pool_observations {initialIndex reachedIndex : Index}
    {initial : State headers keys initialIndex} {final : State headers keys reachedIndex}
    (related : Relates initial final) :
    (∀ row, RecordPrefix (records initial row) (records final row)) ∧
    (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame reachedIndex.mapping reachedIndex.store record) ∧
    (∀ row record, record ∈ records initial row → record ∈ records final row) := by
  exact ⟨related, fun row record member => record_snapshot final row member,
    fun row record member => Relates.mem related row member⟩

section Body
open RecursiveNamedCallBounds (BodyTrace)
variable {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {faults : FunctionCalls.FaultRep}
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
  (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
  (unitResult : function.resultType = .unit)
  (admission : GenericLexicalStatements.Syntax function.source noExpressionSyntax context true function.body function.resultType)
  {flow code : Expr} {fellThrough escaped : Word}
  (tree : GenericLexicalStatements.Tree compiled.indexed.layouts owner active compiled.indexed.ancestry.layout.frame
    globals onError values function.source noExpressions context scope true function.body function.resultType .unit flow)
  (emitted : code = CompatibleStatements.finish .unit flow fellThrough escaped)
  (unique : NodeOccurrencesUnique function.source) (escapedFault : faults .controlEscapedFunction escaped)

include definitions registered unitResult admission tree emitted unique escapedFault in
/-- Source body execution closes through the real lexical Tree and native
finish. Every state callback is derived here from static receipts. -/
theorem closed_body_preserves (size : Nat)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType .unit faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds
          compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        Transition (protocol headers keys) initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have projection : values.checked.catalog.project function.resultType = .ok .unit := by
    rw [unitResult]
    rfl
  have closed := closed_tree_preserves_at (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    functions function.evidence definitions registered tree size unique
  have flowMeaning := RecursiveNamedImperativeLexicalBounds.Stateful.preserves_at_for
    (functions := functions) (program := program) (evidence := function.evidence)
    (protocol := protocol headers keys) (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (administrative := administrative) (fun _ => True) closed
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, heapMetadata, lexical, post⟩ :=
    RecursiveNamedFunctionFinishBounds.preserves_at_emitted_with_state_when
      (functions := functions) (program := program)
      (tree := GenericImperativeMatch.Tree.body admission tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) emitted (fun _ => True)
      size flowMeaning trivial environments heaps locals agrees typed reference read unmapped initial seed trace
  obtain ⟨final, related⟩ := post
  obtain ⟨prefixes, snapshots, _oldMembers⟩ := reached_pool_observations related
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, heapMetadata, lexical,
    final, related, prefixes, snapshots, ⟨final, related⟩⟩

include definitions registered unitResult admission tree emitted unique escapedFault in
/-- Reflection consumes the original native completion and constructs an
independent Source body grade, preserving its actual reached pool. -/
theorem closed_body_reflects (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType .unit faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds
          compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        Transition (protocol headers keys) initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have projection : values.checked.catalog.project function.resultType = .ok .unit := by
    rw [unitResult]
    rfl
  have flowMeaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      ProtectedStateTransition.Lexical.Gated.ReflectsAtFor (protocol headers keys)
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program function.evidence (fun _ => True)
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType .unit flow) := by
    intro child _strictChild
    exact RecursiveNamedImperativeLexicalBounds.Stateful.reflects_at_for
      (functions := functions) (program := program) (evidence := function.evidence)
      (protocol := protocol headers keys) (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (administrative := administrative) (fun _ => True)
      (closed_tree_reflects_at (headers := headers) (keys := keys) functions function.evidence definitions registered tree child)
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, preservation, heapMetadata, lexical, post⟩ :=
    RecursiveNamedFunctionFinishBounds.reflects_at_emitted_with_state_when
      (functions := functions) (program := program)
      (tree := GenericImperativeMatch.Tree.body admission tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) emitted (fun _ => True)
      budget size within flowMeaning trivial environments heaps locals agrees typed reference read unmapped initial seed evaluated
  obtain ⟨final, related⟩ := post
  obtain ⟨prefixes, snapshots, _oldMembers⟩ := reached_pool_observations related
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, preservation, heapMetadata, lexical,
    final, related, prefixes, snapshots, ⟨final, related⟩⟩
end Body

end Tests.SourceCoreClosedOwnedLexicalBody
