import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeControl
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedProjected
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodPrincipal
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedOperators
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StatePlaceAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.WhileLoops
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeFor

/-!
# Closed owned tests

Closed owned bodies: expressions, coercions, indirect calls, named families and loops.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedLexicalBody
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedAnonymousInvocation
/-! A genuine static anonymous origin with an empty Unit body closes through
the shared actual body family. Its stored payload application retains real
marked parameters, full captures and the actual restored caller pool. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedAnonymousInvocation
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open CallableIndexedOwnedLambdaInvocationBounds ProtectedStateTransition
open Tests.SourceCoreClosedOwnedLexicalBody (noExpressions noExpressionSyntax reached_pool_observations)

section EmptyOrigin
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (original : CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults)
  (emptyBody : original.function.body = []) (unitResult : original.function.resultType = .unit)

include emptyBody in
/-- Invert the original static empty statement tree, without another fold. -/
private theorem original_flow : original.body.flow = LocalLoop.fallthrough original.output := by
  have tree := original.body.tree
  rw [emptyBody] at tree
  generalize sameFlow : original.body.flow = flow at tree ⊢
  cases tree with
  | body _ lexical => cases lexical with | nil _ => rfl

/-- Re-extract the same emitted empty body under an empty leaf certificate.
All source contexts, layouts, output types and code receipts stay original. -/
private def emptyKernel : CallableRuntimeBodyKernel.BodyFor original.layouts original.owner original.active
    original.frameLayout original.globals original.onError values original.function noExpressionSyntax noExpressions
    original.validity original.diagnosticPolicy ambient original.administrative original.context original.scope
    original.output original.code original.fellThrough original.escaped registry faults where
  flow := LocalLoop.fallthrough original.output
  tree := .body (emptyBody ▸ .nil (Or.inr unitResult)) (emptyBody ▸ .nil (Or.inr unitResult))
  sites := .body (syntaxTree := emptyBody ▸ .nil (Or.inr unitResult)) (body := emptyBody ▸ .nil (Or.inr unitResult))
  initialValid := original.body.initialValid
  projection := original.body.projection
  unique := original.body.unique
  emitted := by rw [← original_flow original emptyBody]; exact original.body.emitted

def emptyOrigin : CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults :=
  { original with expressionSyntax := noExpressionSyntax, certificates := noExpressions, body := emptyKernel original emptyBody unitResult }
end EmptyOrigin

section Bodies
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : BodyOrigin (program := program) code inputs registry faults)
  (emptyBody : function.body = []) (unitResult : function.resultType = .unit)

/-- The original full ClosureFrame and every capture/code alignment are retained. -/
def emptyBodyOrigin : BodyOrigin (program := program) code inputs registry faults where
  origin := emptyOrigin body.origin (by simpa only [body.function_eq] using emptyBody)
    (by simpa only [body.function_eq] using unitResult)
  frame := body.frame
  function_eq := body.function_eq
  context_eq := body.context_eq
  administrative_eq := body.administrative_eq
  scope_eq := body.scope_eq
  frame_eq := body.frame_eq
  globals_eq := body.globals_eq
  output_eq := body.output_eq
  code_eq := body.code_eq

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (layouts : body.origin.layouts = compiled.indexed.layouts)

private def producer : MarkedAllocation.Producer (protocol headers keys) body.origin.layouts body.origin.frameLayout
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  layouts.symm ▸ (body.frame_eq.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))

private theorem ready_cast {first second : SourceCoreAllocationLayouts.Prepared}
    {firstFrame secondFrame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second) (sameFrame : firstFrame = secondFrame)
    (marked : MarkedAllocation.Producer (protocol headers keys) second secondFrame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    {location : Location} {native : NativeFrame} (ready : OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    OrdinaryAllocation.ReadyAt ((same.symm ▸ (sameFrame.symm ▸ marked)).toOrdinary) location native := by
  cases same
  cases sameFrame
  exact ready

private theorem acquire (location : Location) (native : NativeFrame)
    (seed : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (producer (headers := headers) (keys := keys) code inputs body functions layouts).toOrdinary location native := by
  exact ready_cast functions layouts body.frame_eq
    (CallableIndexedOwnedMarkedAllocation.producer headers keys (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) seed)

include extension faithful observations layouts in
/-- The single authentic anonymous origin closes its own body family. No
smaller body or expression execution meaning is assumed. -/
theorem empty_preserves (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (emptyBodyOrigin code inputs body emptyBody unitResult).origin size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.preserves_at
    (fun (_ : Unit) => (emptyBodyOrigin code inputs body emptyBody unitResult).origin)
    functions extension program faithful observations (protocol headers keys)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => producer code inputs body functions layouts)
    (fun _ => acquire code inputs body functions layouts)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (by intro _ context _ budget child _ _ scope id lowered impossible; cases impossible) size ()

include extension faithful observations functionTypes layouts in
/-- Native reflection uses the same shared closer and keeps its independent
source grade and exact reached state. -/
theorem empty_reflects (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (emptyBodyOrigin code inputs body emptyBody unitResult).origin size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.reflects_at
    (fun (_ : Unit) => (emptyBodyOrigin code inputs body emptyBody unitResult).origin)
    functions extension program faithful observations functionTypes (protocol headers keys)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => producer code inputs body functions layouts)
    (fun _ => acquire code inputs body functions layouts)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (by intro _ context _ budget child _ _ scope id lowered impossible; cases impossible) size ()
end Bodies

section Application
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope callerScope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual callerCanonical : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : CallableIndexedOwnedFunctionValues.StaticSupport headers registry faults code)
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
  (emptyBody : function.body = []) (unitResult : function.resultType = .unit)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments payloads)
  {before : Dynamic.Heap} {store : Store}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {metadata : Option MetadataState}
  (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost metadata)

set_option quotPrecheck false in
local notation "inputs" => support.2.2.receipt.body.toContext
set_option quotPrecheck false in
local notation "originalBody" => BodyOrigin.nested code inputs support.2.2.receipt escaped
set_option quotPrecheck false in
local notation "closedBody" => emptyBodyOrigin code inputs originalBody emptyBody unitResult

/-- Observations use every ordered row of the genuine returned pool. -/
def poolObservations {firstIndex lastIndex : Index}
    (first : State headers keys firstIndex) (last : State headers keys lastIndex) : Prop :=
  (∀ row, RecordPrefix (records first row) (records last row)) ∧
  (∀ row record, record ∈ records last row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
    compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame lastIndex.mapping lastIndex.store record) ∧
  (∀ row record, record ∈ records first row → record ∈ records last row)

include captured code history support escaped emptyBody unitResult extension faithful observations represented heaps reference carried in
/-- Actual source lambda formation supplies capture validity at this heap.
The stored carrier then runs the genuine parameter/body/restore application. -/
theorem formed_application_source_post
    {formationContext callContext : SourceSemantics.Context} {formationSource : TypedSource}
    {formationEvidence callerEvidence : Dynamic.EvidenceEnvironment} {formationEnvironment : Dynamic.Environment}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    (formationLocals : Dynamic.EnvironmentAgrees before formationContext.locals formationEnvironment)
    (formation : Dynamic.ExpressionFormEvaluates program formationContext formationEvidence formationSource formationEnvironment before
      (.lambda function.parameters function.resultType function.body) requirements coercions (.closure function) before)
    (size : Nat) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome program size callContext callerEvidence function.evidence before
      (.closure function) arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues payloads] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩,
        Relates caller reached ∧ poolObservations caller reached := by
  have captures := (CallableIndexedOwnedCaptureValidity.captures_of_formation formationLocals formation).2
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, preserved, metadata, reached, related⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.application_preserves_bounded_with captured code history inputs functions represented
      owner caller heaps captures reference carried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
      closedBody size (fun child _ => empty_preserves code inputs originalBody emptyBody unitResult functions
        extension faithful observations (by rfl) child) trace (Nat.le_refl _)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, preserved, metadata,
    reached, related, reached_pool_observations related⟩

include captured code history support escaped emptyBody unitResult extension faithful observations functionTypes represented heaps reference carried in
/-- Source closure typing authenticates raw capture declarations separately
from its stored native carrier. Reflection returns the original source call
at its own grade and retains the actual restored pool. -/
theorem typed_application_native_post
    {typingContext callContext : SourceSemantics.Context} {parameter result : TypeSystem.Ty}
    {callerEvidence : Dynamic.EvidenceEnvironment}
    (sourceTyped : Dynamic.ValueHasType typingContext before (.closure function) (.function parameter result))
    (size : Nat) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
      DataPatternValues.packValues payloads] store CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome program sourceSize callContext callerEvidence function.evidence before
        (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩,
        Relates caller reached ∧ poolObservations caller reached := by
  have captures := CallableIndexedOwnedCaptureValidity.captures_of_source_typed sourceTyped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, preserved, metadata, reached, related⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.application_reflects_bounded_with captured code history inputs functions represented
      owner caller heaps captures reference carried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
      closedBody size (fun child _ => empty_reflects code inputs originalBody emptyBody unitResult functions
        extension faithful observations functionTypes (by rfl) child) completed (Nat.le_refl _)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, preserved, metadata,
    reached, related, reached_pool_observations related⟩
end Application

end Tests.SourceCoreClosedOwnedAnonymousInvocation
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedBodyKernel
/-! A real lexical static receipt embeds into the general body Tree and its
CatalogSites. Empty expression certificates close the actual body kernel and
family without an assumed expression or body meaning. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedBodyKernel
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open ProtectedStateTransition
open Tests.SourceCoreClosedOwnedLexicalBody (noExpressions noExpressionSyntax reached_pool_observations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

private def ownedProducer {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment}
    (model : GenericHeap.PayloadModel catalog projects definitions)
    (sameDefinitions : compiled.indexed.layouts.definitions = definitions) :
    MarkedAllocation.Producer (protocol headers keys) compiled.indexed.layouts
      compiled.indexed.ancestry.layout.frame model := by
  subst definitions
  exact CallableIndexedOwnedMarkedAllocation.producer headers keys model

private theorem acquire {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (sameDefinitions : compiled.indexed.layouts.definitions = definitions)
    (location : Location) (native : NativeFrame)
    (seed : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (ownedProducer (headers := headers) (keys := keys) model sameDefinitions).toOrdinary location native := by
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

section Body
open RecursiveNamedCallBounds (BodyTrace)
variable {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
  (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
  {solved : List SolvedRequirement}
  (valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence)
  (unitResult : function.resultType = .unit)
  (admission : GenericLexicalStatements.Syntax function.source noExpressionSyntax context true function.body function.resultType)
  {flow code : Expr} {fellThrough escaped : Word}
  (tree : GenericLexicalStatements.Tree compiled.indexed.layouts owner active compiled.indexed.ancestry.layout.frame
    globals onError values function.source noExpressions context scope true function.body function.resultType .unit flow)
  (emitted : code = CompatibleStatements.finish .unit flow fellThrough escaped)
  (unique : NodeOccurrencesUnique function.source) (escapedFault : faults .controlEscapedFunction escaped)

private def kernel : CallableRuntimeBodyKernel.BodyFor compiled.indexed.layouts owner active
    compiled.indexed.ancestry.layout.frame globals onError values function noExpressionSyntax noExpressions
    (fun context => CompatibleRuntimeContextValidity.Valid solved context function.evidence)
    .reachable ambient administrative context scope .unit code fellThrough escaped registry faults where
  flow := flow
  tree := GenericImperativeMatch.Tree.body admission tree
  sites := .body (syntaxTree := admission) (body := tree)
  initialValid := valid
  projection := by rw [unitResult]; rfl
  unique := unique
  emitted := emitted

include definitions registered extension faithful observations valid unitResult admission tree emitted unique escapedFault in
/-- Source body execution closes through the real lexical Tree and native
finish. Every state callback is derived here from static receipts. -/
theorem closed_kernel_preserves (size : Nat)
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
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, heapMetadata, lexical, post⟩ :=
    CallableRuntimeBodyKernel.Stateful.BodyFor.preserves_sized
      (body := kernel valid unitResult admission tree emitted unique)
      (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
      (program := program) (faithful := faithful) (observations := observations) (escapedFault := escapedFault)
      (extend := fun valid extended => valid.extend extended) (runtimeOf := fun valid => valid)
      (protocol := protocol headers keys) (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (producer := ownedProducer (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
      (acquire := acquire (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
      (stateTransport := administrativeTransport headers keys) (stateBindings := CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      size size (Nat.le_refl _) (fun _ _ child _ => no_expression_preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions) child)
      environments heaps locals agrees typed reference read unmapped initial seed trace
  obtain ⟨final, related⟩ := post
  obtain ⟨prefixes, snapshots, _oldMembers⟩ := reached_pool_observations related
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, heapMetadata, lexical,
    final, related, prefixes, snapshots, ⟨final, related⟩⟩

include definitions registered extension faithful observations functionTypes valid unitResult admission tree emitted unique escapedFault in
/-- Reflection consumes the original native completion and constructs an
independent Source body grade, preserving its actual reached pool. -/
theorem closed_kernel_reflects (budget size : Nat) (within : size ≤ budget)
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
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, preservation, heapMetadata, lexical, post⟩ :=
    CallableRuntimeBodyKernel.Stateful.BodyFor.reflects_sized
      (body := kernel valid unitResult admission tree emitted unique)
      (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
      (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes) (escapedFault := escapedFault)
      (extend := fun valid extended => valid.extend extended) (runtimeOf := fun valid => valid)
      (protocol := protocol headers keys) (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (producer := ownedProducer (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
      (acquire := acquire (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
      (stateTransport := administrativeTransport headers keys) (stateBindings := CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      budget size within (fun _ _ child _ => no_expression_reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions) child)
      environments heaps locals agrees typed reference read unmapped initial seed evaluated
  obtain ⟨final, related⟩ := post
  obtain ⟨prefixes, snapshots, _oldMembers⟩ := reached_pool_observations related
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, preservation, heapMetadata, lexical,
    final, related, prefixes, snapshots, ⟨final, related⟩⟩
private def origin : CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults where
  layouts := compiled.indexed.layouts
  owner := owner
  active := active
  frameLayout := compiled.indexed.ancestry.layout.frame
  globals := globals
  onError := onError
  function := function
  expressionSyntax := noExpressionSyntax
  certificates := noExpressions
  validity := fun context => CompatibleRuntimeContextValidity.Valid solved context function.evidence
  diagnosticPolicy := .reachable
  administrative := administrative
  context := context
  scope := scope
  output := .unit
  code := code
  fellThrough := fellThrough
  escaped := escaped
  solved := solved
  body := kernel valid unitResult admission tree emitted unique
  definitions := definitions
  registered := registered
  escapedFault := escapedFault
  extend := fun valid extended => valid.extend extended
  runtimeOf := fun valid => valid

include definitions registered extension faithful observations valid unitResult admission tree emitted unique escapedFault in
/-- A nonempty actual origin family closes with the static empty expression
certificate. No smaller callee or body semantic law is supplied. -/
theorem closed_family_preserves (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (origin (registry := registry) (administrative := administrative) definitions registered valid unitResult admission tree emitted unique escapedFault) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.preserves_at
    (fun (_ : Unit) => origin (registry := registry) (administrative := administrative) definitions registered valid unitResult admission tree emitted unique escapedFault)
    functions extension program faithful observations (protocol headers keys)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => ownedProducer (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (fun _ => acquire (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (fun _ _ _ _ child _ _ => no_expression_preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions) child)
    size ()

include definitions registered extension faithful observations functionTypes valid unitResult admission tree emitted unique escapedFault in
/-- Actual native family reflection closes separately and returns an
independent source grade from the original measured completion. -/
theorem closed_family_reflects (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (origin (registry := registry) (administrative := administrative) definitions registered valid unitResult admission tree emitted unique escapedFault) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.reflects_at
    (fun (_ : Unit) => origin (registry := registry) (administrative := administrative) definitions registered valid unitResult admission tree emitted unique escapedFault)
    functions extension program faithful observations functionTypes (protocol headers keys)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => ownedProducer (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (fun _ => acquire (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (fun _ _ _ _ child _ _ => no_expression_reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions) child)
    size ()

end Body

end Tests.SourceCoreClosedOwnedBodyKernel
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedExpressionHead
/-! Full prepared Header receipts close nil Unit bodies through the actual
named mutual family. The selected argument/callee head then retains its real
returned pool, without an assumed expression or body meaning. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedExpressionHead
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds ProtectedStateTransition
open Tests.SourceCoreClosedOwnedLexicalBody (noExpressions noExpressionSyntax reached_pool_observations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- The complete factory attribution is retained as the static test premise. -/
def PreparedReceipts : Prop :=
  ∀ header, header ∈ headers → ∃ row, ∃ prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row,
    ∃ instantiation, RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header

variable (receipts : PreparedReceipts (headers := headers))
  (body_nil : ∀ header, header ∈ headers → header.function.body = [])
  (unit_result : ∀ header, header ∈ headers → header.function.resultType = .unit)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)

include receipts in
theorem layouts {header} (member : header ∈ headers) : header.layouts = compiled.indexed.layouts := by
  obtain ⟨row, prepared, instantiation, aligned⟩ := receipts header member
  exact aligned.layouts

include receipts in
private theorem accepted {header} (member : header ∈ headers) :
    SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body := by
  obtain ⟨row, prepared, instantiation, aligned⟩ := receipts header member
  exact aligned.accepted

include receipts in
private theorem projection {header} (member : header ∈ headers) :
    compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output := by
  obtain ⟨row, prepared, instantiation, aligned⟩ := receipts header member
  exact aligned.projection

private def nilProfile {header} (member : header ∈ headers) (administrative : Core.Context) :
    MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
      noExpressions .reachable header noExpressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults := by
  let lexical : GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) header.function.source noExpressions header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true header.function.body
      header.function.resultType header.output (LocalLoop.fallthrough header.output) := by
    rw [body_nil header member]
    exact .nil (Or.inr (unit_result header member))
  let admission : GenericLexicalStatements.Syntax header.function.source noExpressionSyntax header.context true
      header.function.body header.function.resultType := by
    rw [body_nil header member]
    exact .nil (Or.inr (unit_result header member))
  let tree := GenericImperativeMatch.Tree.body
    (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) admission lexical
  have generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok (LocalLoop.fallthrough header.output) := by
    rw [body_nil header member]
    cases header.fuel <;> rfl
  exact MatchProfileWith.of_extracted header.valid (accepted receipts member) (projection receipts member) generated tree
    (.body (syntaxTree := admission) (body := lexical))

private def producer {header} (member : header ∈ headers) : MarkedAllocation.Producer (protocol headers keys)
    header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  (layouts receipts member).symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (same : first = second) (marked : MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame} (ready : OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    OrdinaryAllocation.ReadyAt ((same.symm ▸ marked).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire {header} (member : header ∈ headers) (location : Location) (native : NativeFrame)
    (seed : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (producer (functions := functions) (registry := registry) (keys := keys) receipts member).toOrdinary location native := by
  intro index reached read
  exact (ready_layout (headers := headers) (keys := keys) (layouts receipts member)
    (CallableIndexedOwnedMarkedAllocation.producer headers keys (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) seed)) reached read

def conditions (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) :
    BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header :=
  CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
    (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header

include extension faithful observations receipts body_nil unit_result escaped in
/-- The actual named family closes the bodies; only impossible expression
certificate leaves are discharged. No body law is a test premise. -/
theorem bodies_preserve (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (conditions functions owner header) size := by
  exact CallableRuntimeNamedBodyFamily.preserves_at (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) true functions extension faithful observations escaped
    (protocol headers keys) (conditions functions owner)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun header member => producer (functions := functions) (registry := registry) (keys := keys) receipts member)
    (fun header member => acquire functions receipts member)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (fun _ => noExpressions)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry aligned
      exact nilProfile (registry := registry) (faults := faults) receipts body_nil unit_result member administrative)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry aligned
      exact aligned)
    (by intro header member context valid budget child within below scope id lowered impossible; cases impossible) size

include extension faithful observations functionTypes receipts body_nil unit_result escaped in
theorem bodies_reflect (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (conditions functions owner header) size := by
  exact CallableRuntimeNamedBodyFamily.reflects_at (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) true functions extension faithful observations functionTypes escaped
    (protocol headers keys) (conditions functions owner)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun header member => producer (functions := functions) (registry := registry) (keys := keys) receipts member)
    (fun header member => acquire functions receipts member)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (fun _ => noExpressions)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry aligned
      exact nilProfile (registry := registry) (faults := faults) receipts body_nil unit_result member administrative)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry aligned
      exact aligned)
    (by intro header member context valid budget child within below scope id lowered impossible; cases impossible) size


open CallableIndexedOwnedExpressionHeads
variable {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {compilation : SourceCoreFunctions.Context}

include extension faithful observations receipts body_nil unit_result escaped in
/-- Real ordinary/direct metadata chooses the callee; its nil Unit body is
closed by the named family above, with no semantic child assumption. -/
theorem closed_head_preserves (size : Nat)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup) :
    PreservesAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner compilation.administrativePrefix
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence (noExpressions context)) size := by
  exact CallableIndexedOwnedExpressionHeads.preserves_at_with functions owner (fun header member => layouts receipts member)
    (conditions functions owner)
    (fun header _member => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
    size size (Nat.le_refl _) idsUnique unique owners
    (by intro child smaller scope id lowered impossible; cases impossible)
    (by
      intro header member child smaller
      exact bodies_preserve functions extension faithful observations owner receipts body_nil unit_result escaped child header member)

include extension faithful observations functionTypes receipts body_nil unit_result escaped in
/-- Native reflection derives its source grade independently and uses the
same real metadata, actual body family and reached caller pool. -/
theorem closed_head_reflects (size : Nat) :
    ReflectsAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner compilation.administrativePrefix
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence (noExpressions context)) size := by
  exact CallableIndexedOwnedExpressionHeads.reflects_at_with functions owner (fun header member => layouts receipts member)
    (conditions functions owner)
    (fun header _member => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
    size size (Nat.le_refl _)
    (by intro child smaller scope id lowered impossible; cases impossible)
    (by
      intro header member child smaller
      exact bodies_reflect functions extension faithful observations functionTypes owner receipts body_nil unit_result escaped child header member)


/-- Every observation is made on the actual returned pool, including all
ordered rows and readable snapshot records. -/
def PoolObservations {initialIndex reachedIndex : Index}
    (initial : State headers keys initialIndex) (reached : State headers keys reachedIndex) : Prop :=
  (∀ row, RecordPrefix (records initial row) (records reached row)) ∧
  (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
    compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame reachedIndex.mapping reachedIndex.store record) ∧
  (∀ row record, record ∈ records initial row → record ∈ records reached row)

section Drivers
variable {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
  {lowered : SourceCoreBasic.LoweredExpr}
  (head : RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers compilation source context evidence (noExpressions context) scope id lowered)
  (found : source.lookupExpression? id = some node)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
    administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (globals : Globals (headers := headers) owner compilation.administrativePrefix scope canonical)

include extension faithful observations receipts body_nil unit_result escaped head found environments heaps locals agrees typed initial globals in
/-- A genuine source call trace drives the actual argument, parameter and body
receipts. The caller is restored in that returned pool. -/
theorem closed_head_source_post (size : Nat)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size context evidence source
      environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PoolObservations initial reached := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
    closed_head_preserves functions extension faithful observations owner receipts body_nil unit_result escaped size idsUnique unique owners
      head found environments heaps locals agrees typed initial globals trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, reached_pool_observations related⟩

include extension faithful observations functionTypes receipts body_nil unit_result escaped head found environments heaps locals agrees typed initial globals in
/-- The original measured native completion reconstructs full source evidence
at its independent grade, retaining the exact returned caller pool. -/
theorem closed_head_native_post (size : Nat) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PoolObservations initial reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
    closed_head_reflects functions extension faithful observations functionTypes owner receipts body_nil unit_result escaped size
      head found environments heaps locals agrees typed initial globals completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, reached_pool_observations related⟩
end Drivers

end Tests.SourceCoreClosedOwnedExpressionHead
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedExpressionTree
/-! A complete owned expression Tree uses literal receipts and the proved nil
Unit named body family. Real Boolean arguments drive marked parameter cells,
and surrounding tuple children retain the exact returned pools. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedExpressionTree
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open CallableIndexedOwnedExpressionHeads
open Tests.SourceCoreClosedOwnedExpressionHead

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (receipts : PreparedReceipts (headers := headers))
  (body_nil : ∀ header, header ∈ headers → header.function.body = [])
  (unit_result : ∀ header, header ∈ headers → header.function.resultType = .unit)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {compilation : SourceCoreFunctions.Context} {solved : List SolvedRequirement} {fuel : Nat}
  {reasonAt : ExpressionId → Word}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

abbrev Calls := RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
  (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
  (some evidence) headers compilation source context

abbrev Expressions := CompatibleExpressionCalls.Tree (Calls (headers := headers) (source := source) (context := context) (compilation := compilation) evidence)
  fuel (.initial compiled.compatible.checked) source context solved reasonAt

include extension faithful observations functionTypes receipts body_nil unit_result escaped valid unique owners uninitialized missing in
/-- All literal and callee callbacks are proved from static receipts. The
original Tree fold closes every expression child at its actual post-state. -/
theorem closed_tree_preserves (size : Nat) (idsUnique : RequirementIdsUnique context) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (Program.ofChecked compiled.sourceProgram) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := Calls (headers := headers) (source := source) (context := context) (compilation := compilation) evidence)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code)) faults size := by
  exact CallableIndexedOwnedExpressionTreeBounds.preserves_at_with_literals
    (solved := solved) (fuel := fuel) (compilation := compilation) functions extension faithful observations functionTypes
    evidence unique owners uninitialized missing owner (fun header member => layouts receipts member)
    (conditions functions owner)
    (fun header member => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
    idsUnique (CompatibleExpressionLiterals.preserves functions (Program.ofChecked compiled.sourceProgram) context evidence valid unique faults)
    size size (Nat.le_refl _) (by
      intro header member child smaller
      exact bodies_preserve functions extension faithful observations owner receipts body_nil unit_result escaped child header member)

include extension faithful observations functionTypes receipts body_nil unit_result escaped valid uninitialized missing in
/-- Native children select their own grades; the reconstructed source grade
and actual reached pool come from the same closed Tree. -/
theorem closed_tree_reflects (size : Nat) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner compilation.administrativePrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (Program.ofChecked compiled.sourceProgram) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := Calls (headers := headers) (source := source) (context := context) (compilation := compilation) evidence)
        (fuel := fuel) (values := .initial compiled.compatible.checked) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt)
        (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code)) faults size := by
  exact CallableIndexedOwnedExpressionTreeBounds.reflects_at_with_literals
    (solved := solved) (fuel := fuel) (compilation := compilation) functions extension faithful observations functionTypes
    evidence uninitialized missing owner (fun header member => layouts receipts member)
    (conditions functions owner)
    (fun header member => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
    (CompatibleExpressionLiterals.reflects functions (Program.ofChecked compiled.sourceProgram) context evidence valid source faults)
    size size (Nat.le_refl _) (by
      intro header member child smaller
      exact bodies_reflect functions extension faithful observations functionTypes owner receipts body_nil unit_result escaped child header member)


/-- The exact code emitted for the ordinary Boolean literal receipt. -/
def booleanCode (boolean : Bool) : SourceCoreBasic.LoweredExpr :=
  ⟨.bool, LanguageResult.success (.bool boolean)⟩

/-- The original fragment constructors embed a real literal certificate into
the whole static Tree without a semantic callback. -/
theorem literal_tree {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (literal : CompatibleExpressionLiterals.Certificate solved source id code) :
    Expressions (headers := headers) (source := source) (context := context) (compilation := compilation)
      (solved := solved) (fuel := fuel) (reasonAt := reasonAt) evidence scope id code := by
  exact .fragment (.fragment (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal literal))))))))

/-- This receipt chooses one genuine named header and one Boolean parameter.
The source nodes, retained metadata and complete compiler emission are inputs. -/
structure BooleanCall
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (scope : SourceCoreLocalCell.Scope) (id callee argument : ExpressionId) (boolean : Bool) (expression : Expr) where
  member : header ∈ headers
  node : ExpressionNode
  calleeNode : ExpressionNode
  argumentNode : ExpressionNode
  name : String
  booleanName : String
  metadata : CompatibleExpressionPrimitives.Metadata compiled.compatible.checked source id node header.output
  sourceType : node.type = header.function.resultType
  form : node.form = .call callee [argument] (.declaration header.instantiation)
  calleeFound : source.lookupExpression? callee = some calleeNode
  calleeForm : calleeNode.form = .reference name (.declaration header.instantiation)
  calleeRequirements : calleeNode.requirements = []
  calleeCoercions : calleeNode.coercions = []
  argumentFound : source.lookupExpression? argument = some argumentNode
  argumentForm : argumentNode.form = .reference booleanName (.builtinBoolean boolean)
  argumentType : argumentNode.type = .bool
  argumentRequirements : argumentNode.requirements = []
  argumentCoercions : argumentNode.coercions = []
  valid : SourceSemantics.DeclarationInstantiation.Valid context header.instantiation
  predicates : header.instantiation.predicates = []
  calleeEvidence : header.function.evidence = []
  parameterTypes : header.bindings.map (fun binding => binding.1.scheme.body) = [.bool]
  nativeTypes : header.bindings.map Prod.snd = [.bool]
  emission : NamedCalls.Arguments.Emission compilation source scope id callee [argument]
    header.instantiation header.named.signature [booleanCode boolean] ⟨header.output, expression⟩
  selectedSlot : emission.index = header.slot

/-- The actual source parameter vector is nonempty, so the real named prefix
runs its marked allocation before reaching the closed nil Unit body. -/
theorem boolean_call_tree
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {scope : SourceCoreLocalCell.Scope} {id callee argument : ExpressionId} {boolean : Bool} {expression : Expr}
    (receipt : BooleanCall (headers := headers) (source := source) (context := context) (compilation := compilation)
      header scope id callee argument boolean expression) :
    Expressions (headers := headers) (source := source) (context := context) (compilation := compilation)
      (solved := solved) (fuel := fuel) (reasonAt := reasonAt) evidence scope id ⟨header.output, expression⟩ := by
  have literal : CompatibleExpressionLiterals.Certificate solved source argument (booleanCode boolean) :=
    ⟨receipt.argumentNode, receipt.argumentFound, .bool boolean receipt.argumentForm receipt.argumentType
      receipt.argumentRequirements receipt.argumentCoercions⟩
  have child := literal_tree (scope := scope) (headers := headers) (context := context) (compilation := compilation)
    (fuel := fuel) (reasonAt := reasonAt) evidence literal
  have arity : header.function.parameters.length = [argument].length := by
    rw [header.parameters, List.length_map]
    have count := congrArg List.length receipt.parameterTypes
    simpa only [List.length_map, List.length_singleton] using count
  refine .node (entries := [(argument, booleanCode boolean)]) (.call (.ordinary (.named receipt.member receipt.metadata receipt.sourceType receipt.form
    receipt.calleeFound receipt.calleeForm receipt.calleeRequirements receipt.calleeCoercions receipt.valid
    receipt.predicates receipt.calleeEvidence arity receipt.emission receipt.selectedSlot ?_ ?_))) ?_
  · rw [receipt.parameterTypes]
    have sequence : DataExpressionSequence.Tree source
        (CompatibleExpressionCalls.Entries scope [(argument, booleanCode boolean)]) scope
        [argument] [receipt.argumentNode.type] [booleanCode boolean] :=
      .single receipt.argumentFound ⟨rfl, by simp⟩
    simpa only [receipt.argumentType] using sequence
  · simpa only [List.map_cons, List.map_nil, booleanCode] using receipt.nativeTypes.symm
  · intro selected code member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
    exact child

/-- A real tuple head can enclose the Boolean call and another literal. Both
ordered child Trees are retained by the original factory. -/
theorem tuple_of_trees {scope : SourceCoreLocalCell.Scope} {id left right : ExpressionId}
    {node leftNode rightNode : ExpressionNode} {first second : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionPrimitives.Metadata compiled.compatible.checked source id node (.product first.type second.type))
    (form : node.form = .tuple [left, right])
    (leftFound : source.lookupExpression? left = some leftNode) (rightFound : source.lookupExpression? right = some rightNode)
    (sourceType : node.type = .product leftNode.type rightNode.type)
    (leftTree : Expressions (headers := headers) (source := source) (context := context) (compilation := compilation)
      (solved := solved) (fuel := fuel) (reasonAt := reasonAt) evidence scope left first)
    (rightTree : Expressions (headers := headers) (source := source) (context := context) (compilation := compilation)
      (solved := solved) (fuel := fuel) (reasonAt := reasonAt) evidence scope right second) :
    Expressions (headers := headers) (source := source) (context := context) (compilation := compilation)
      (solved := solved) (fuel := fuel) (reasonAt := reasonAt) evidence scope id
      ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩ := by
  refine .node (entries := [(left, first), (right, second)]) (.primitive (.pair metadata form leftFound rightFound sourceType ⟨rfl, by simp⟩ ⟨rfl, by simp⟩)) ?_
  intro child code member
  rcases List.mem_cons.mp member with equal | rest
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    exact leftTree
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp rest)
    exact rightTree


section ComposedCall
variable {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {scope : SourceCoreLocalCell.Scope} {callId callee argument tupleId right : ExpressionId}
  {boolean rightBoolean : Bool} {expression : Expr} {tupleNode rightNode : ExpressionNode}
  (call : BooleanCall (headers := headers) (source := source) (context := context) (compilation := compilation)
    header scope callId callee argument boolean expression)
  (tupleMetadata : CompatibleExpressionPrimitives.Metadata compiled.compatible.checked source tupleId tupleNode (.product header.output .bool))
  (tupleForm : tupleNode.form = .tuple [callId, right])
  (rightFound : source.lookupExpression? right = some rightNode)
  (tupleType : tupleNode.type = .product call.node.type rightNode.type)
  (rightLiteral : CompatibleExpressionLiterals.Certificate solved source right (booleanCode rightBoolean))

include call tupleMetadata tupleForm rightFound tupleType rightLiteral in
/-- The composed expression has a real call with one Boolean parameter,
followed by a Boolean literal in the original ordered tuple Tree. -/
theorem boolean_call_tuple_tree :
    Expressions (headers := headers) (source := source) (context := context) (compilation := compilation)
      (solved := solved) (fuel := fuel) (reasonAt := reasonAt) evidence scope tupleId
      ⟨.product header.output .bool, LocalSequence.pair header.output .bool expression (booleanCode rightBoolean).expression⟩ := by
  exact tuple_of_trees evidence tupleMetadata tupleForm call.metadata.found rightFound tupleType
    (boolean_call_tree evidence call) (literal_tree evidence rightLiteral)

variable {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
    administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (globals : Globals (headers := headers) owner compilation.administrativePrefix scope canonical)

include fuel extension faithful observations functionTypes receipts body_nil unit_result escaped valid unique owners uninitialized missing
  call tupleMetadata tupleForm rightFound tupleType rightLiteral environments heaps locals agrees typed initial globals in
/-- A source execution of the composed Tree obtains the actual parameter,
callee and restored caller states. All semantic callbacks are closed above. -/
theorem boolean_call_tuple_source_post (size : Nat) (idsUnique : RequirementIdsUnique context)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size context evidence source
      environment before tupleId outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store
        ((LocalSequence.pair header.output .bool expression (booleanCode rightBoolean).expression).rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld tupleNode.type (.product header.output .bool) faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PoolObservations initial reached := by
  have tree := boolean_call_tuple_tree (fuel := fuel) (reasonAt := reasonAt) evidence call tupleMetadata tupleForm rightFound tupleType rightLiteral
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
    closed_tree_preserves functions extension faithful observations functionTypes owner receipts body_nil unit_result escaped
      evidence valid unique owners uninitialized missing size idsUnique
      ⟨tree, tree.literalSites⟩ tupleMetadata.found environments heaps locals agrees typed ⟨initial, globals⟩ trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    reached.val, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩

include fuel extension faithful observations functionTypes receipts body_nil unit_result escaped valid uninitialized missing
  call tupleMetadata tupleForm rightFound tupleType rightLiteral environments heaps locals agrees typed initial globals in
/-- Native completion reconstructs the complete source tuple and call evidence
at an independent source grade. The observations use the actual returned pool. -/
theorem boolean_call_tuple_native_post (size : Nat) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalSequence.pair header.output .bool expression (booleanCode rightBoolean).expression).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before tupleId outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld tupleNode.type (.product header.output .bool) faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PoolObservations initial reached := by
  have tree := boolean_call_tuple_tree (fuel := fuel) (reasonAt := reasonAt) evidence call tupleMetadata tupleForm rightFound tupleType rightLiteral
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
    closed_tree_reflects functions extension faithful observations functionTypes owner receipts body_nil unit_result escaped
      evidence valid uninitialized missing size
      ⟨tree, tree.literalSites⟩ tupleMetadata.found environments heaps locals agrees typed ⟨initial, globals⟩ completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached.val, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩
end ComposedCall

end Tests.SourceCoreClosedOwnedExpressionTree
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedIndirectExpression
/-! Complete indirect expressions close their literal/read children and their
actual anonymous body internally. The same concrete returned pool supplies all
record observations. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedIndirectExpression
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open CallableIndexedOwnedLambdaInvocationBounds ProtectedStateTransition
open Tests.SourceCoreClosedOwnedAnonymousInvocation

universe u v
/-- Static certificate replacement changes no field of the concrete entry. -/
private def entry_for_empty {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {Records : Type v} (protocol : Protocol.{u, v} Records) (gate : Location → NativeFrame → Prop)
    (original : CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults)
    (emptyBody : original.function.body = []) (unitResult : original.function.resultType = .unit)
    (functions : FunctionModel values.checked.catalog ambient)
    (entry : CallableRuntimeBodyOrigins.Stateful.Entry protocol gate original functions) :
    CallableRuntimeBodyOrigins.Stateful.Entry protocol gate (emptyOrigin original emptyBody unitResult) functions where
  mapping := entry.mapping
  world := entry.world
  environment := entry.environment
  canonical := entry.canonical
  actual := entry.actual
  heap := entry.heap
  store := entry.store
  embedding := entry.embedding
  actualContext := entry.actualContext
  frameLocation := entry.frameLocation
  native := entry.native
  environments := entry.environments
  heaps := entry.heaps
  locals := entry.locals
  lookups := entry.lookups
  actualTyped := entry.actualTyped
  reference := entry.reference
  read := entry.read
  unmapped := entry.unmapped
  initial := entry.initial
  gate := entry.gate

section OriginalBody
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : BodyOrigin (program := program) code inputs registry faults)
  (emptyBody : function.body = []) (unitResult : function.resultType = .unit)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (layouts : body.origin.layouts = compiled.indexed.layouts)

include emptyBody unitResult extension faithful observations layouts in
/-- The original selected body receipt is closed by the actual empty-body
family; its full source, captured entry, code and reached state are identical. -/
theorem original_body_preserves (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program body.origin size := by
  intro entry outcome after trace
  let reindexed := entry_for_empty (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    body.origin (by simpa only [body.function_eq] using emptyBody)
    (by simpa only [body.function_eq] using unitResult) functions entry
  exact empty_preserves code inputs body emptyBody unitResult functions extension faithful observations layouts size
    reindexed trace

include emptyBody unitResult extension faithful observations functionTypes layouts in
/-- Native completion reconstructs the independent source grade at the same
original entry through the internally proved empty anonymous body family. -/
theorem original_body_reflects (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program body.origin size := by
  intro entry value finalStore completed
  let reindexed := entry_for_empty (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    body.origin (by simpa only [body.function_eq] using emptyBody)
    (by simpa only [body.function_eq] using unitResult) functions entry
  exact empty_reflects code inputs body emptyBody unitResult functions extension faithful observations functionTypes layouts size
    reindexed completed
end OriginalBody

section StaticChildren
variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- Embed an original product leaf through the existing builtin grammar. -/
private theorem product_child
    (child : CompatibleExpressionProducts.Tree.WithLiterals
      (fuel := fuel) (values := values) (source := source) (context := context)
      (solved := solved) (reasonAt := reasonAt)
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code) scope id lowered) :
    CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt scope id lowered := by
  obtain ⟨tree, sites⟩ := child
  exact ⟨.fragment (.fragment (.fragment (.fragment (.fragment (.primitive (.product tree)))))),
    .fragment _ (.fragment _ (.fragment _ (.fragment _ (.fragment _ (.primitive _ (.product _ sites))))))⟩

/-- The authentic original local-read receipt supplies the callee leaf. -/
private theorem read_child
    (read : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id lowered) :
    CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt scope id lowered :=
  product_child ⟨.read read, .read read⟩

/-- The genuine Boolean source node supplies the argument leaf, including
its full original empty metadata and runtime literal receipt. -/
private theorem bool_child {node : ExpressionNode} {name : String} (boolean : Bool)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinBoolean boolean)) (type : node.type = .bool)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt scope id
      ⟨.bool, LanguageResult.success (.bool boolean)⟩ := by
  have original : CompatibleExpressionLiterals.Certificate solved source id
      ⟨.bool, LanguageResult.success (.bool boolean)⟩ :=
    ⟨node, found, .bool boolean form type requirements coercions⟩
  have runtime : CompatibleExpressionLiteralRuntime.Certificate solved source id
      ⟨.bool, LanguageResult.success (.bool boolean)⟩ :=
    ⟨node, found, .bool boolean form type requirements coercions, by intro literal resolution impossible; simp [form] at impossible⟩
  exact product_child ⟨.literal original, .literal original runtime⟩
/-- A real ordinary Source heap read constructs the callee execution; no
callee evaluation or execution meaning is assumed by this factory. -/
theorem actual_callee_read
    (readCode : CompatibleExpressionReads.Certificate fuel values source scope id (reasonAt id) lowered.expression)
    {program : SourceSemantics.Program} {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.Closure}
    (lookup : Dynamic.Environment.LooksUp environment readCode.binder location)
    (read : Dynamic.Heap.Reads before location cell) (ordinary : cell.generalized = none)
    (stored : cell.value = some (.closure function)) :
    ∃ size, SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before id
      (.closure function) before := by
  refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [], SourceExecutionSize.stepSize []],
    .intro (raw := .closure function) (middle := before) (lookupExpression?_sound readCode.metadata.found) ?_ ?_⟩
  · rw [readCode.form, readCode.metadata.requirements, readCode.metadata.coercions]
    exact .local rfl lookup read ordinary stored
  · rw [readCode.metadata.coercions]
    exact .nil
end StaticChildren

section Children
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (sameLedger : context.solvedRequirements = solved) (runtime : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique source)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations functionTypes sameLedger runtime unique uninitialized missing in
/-- Real read/literal certificates supply the finite child family. This
administrative lift applies only to the original builtin/data/read grammar. -/
private theorem children_preserve (size : Nat) :
    ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionBuiltinRuntime.Certificate fuel (.initial compiled.compatible.checked) source context solved reasonAt)
      faults size := by
  apply ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _ (administrativeTransport headers keys)
  exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
    (ProtectedExpressionMeaning.preserves_of_typed (ProtectedStateTransition.entry (protocol headers keys))
      (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations functionTypes program evidence
        sameLedger runtime unique uninitialized missing)) size

include extension faithful observations functionTypes sameLedger runtime uninitialized missing in
/-- Original native read/literal completion reconstructs its own Source grade.
All child callbacks are proved here from static builtin certificates. -/
private theorem children_reflect (size : Nat) :
    ProtectedStateTransition.ReflectsAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionBuiltinRuntime.Certificate fuel (.initial compiled.compatible.checked) source context solved reasonAt)
      faults size := by
  apply ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _ (administrativeTransport headers keys)
  exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
    (ProtectedExpressionMeaning.reflects_of_typed (ProtectedStateTransition.entry (protocol headers keys))
      (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes program evidence
        sameLedger runtime uninitialized missing)) size
end Children

section SourceChildren
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {name : String}

/-- Construct the actual ordered Boolean argument from its original node. -/
private theorem boolean_arguments (boolean : Bool)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinBoolean boolean))
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    SourceExecutionSize.ExpressionsEvaluate program
      (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [], SourceExecutionSize.stepSize []], SourceExecutionSize.stepSize []])
      context evidence source environment before [id] [.bool boolean] before := by
  refine .cons (.intro (raw := .bool boolean) (middle := before) (lookupExpression?_sound found) ?_ ?_) .nil
  · rw [form, requirements, coercions]
    exact .builtinBoolean rfl
  · rw [coercions]; exact .nil

/-- This real Source cell is appended after the call's copies of the captured
cells. -/
def parameterHeap (before : Dynamic.Heap) (binder : TypedBinder) (boolean : Bool) : Dynamic.Heap :=
  ⟨before.cells ++ [⟨binder.scheme.body, some (.bool boolean), none⟩]⟩

/-- The call's copies of the captured cells, a nonempty parameter allocation and
an actual nil Unit body construct the original closure application. No body
trace or body meaning is a premise. -/
private theorem boolean_nil_call {function : Dynamic.Closure} (binder : TypedBinder) (boolean : Bool)
    (parameters : function.parameters = [binder]) (emptyBody : function.body = [])
    (unitResult : function.resultType = .unit) (frame : Dynamic.ClosureFrame program function)
    {callContext : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types callContext)
    {copies : Dynamic.Environment} {copiedHeap : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copiedHeap) :
    RecursiveNamedCallBounds.CallOutcome program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize []])
      context evidence function.evidence before (.closure function) [.bool boolean] (.value .unit)
      (parameterHeap copiedHeap binder boolean) := by
  have allocated : Dynamic.BindersAllocate copies copiedHeap function.parameters [.bool boolean]
      ((binder.id, ⟨copiedHeap.cells.length⟩) :: copies) (parameterHeap copiedHeap binder boolean) := by
    rw [parameters]
    exact .cons .append (.nil _ _)
  have executed : SourceExecutionSize.FunctionStatementsExecute program (SourceExecutionSize.stepSize [])
      callContext function.evidence function.source ((binder.id, ⟨copiedHeap.cells.length⟩) :: copies)
      (parameterHeap copiedHeap binder boolean) function.body callContext
      (.fallthrough ((binder.id, ⟨copiedHeap.cells.length⟩) :: copies)) (parameterHeap copiedHeap binder boolean) := by
    rw [emptyBody]; exact .nil
  exact .value (.closureUnit rfl frame unitResult extended copy allocated executed ⟨_, rfl⟩)
end SourceChildren

section ClosedParent
open CallableIndexedOwnedIndirectExpressionHeads CallableIndexedOwnedIndirectSourceAdapters
open Tests.SourceCoreClosedOwnedLexicalBody (reached_pool_observations)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee argument : ExpressionId} {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy lowerBody fuel compilation source scope
    id callee [argument] metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context) (unique : NodeOccurrencesUnique source)
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
  (closure : ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    mapping world function sourceType carrier type)
  {binder : TypedBinder} (parameters : closure.code.receipt.loweredParameters = [(binder, .bool)])
  (emptyBody : function.body = []) (unitResult : function.resultType = .unit)
  (escaped : faults .controlEscapedFunction closure.code.compilation.internalReason)
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType)
  (nativeResult : compiler.resultType = closure.code.receipt.resultCore)
  (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
  (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
  {boolean : Bool} {booleanNode : ExpressionNode} {booleanName : String}
  (booleanFound : source.lookupExpression? argument = some booleanNode)
  (booleanForm : booleanNode.form = .reference booleanName (.builtinBoolean boolean))
  (booleanType : booleanNode.type = .bool) (binderType : binder.scheme.body = .bool)
  (booleanRequirements : booleanNode.requirements = []) (booleanCoercions : booleanNode.coercions = [])
  (booleanTyped : ExpressionHasType source context argument .bool)
  (codes : compiler.codes = [⟨.bool, LanguageResult.success (.bool boolean)⟩])
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩) (stable : StableRows initial)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (heapTyped : Dynamic.HeapWellTyped context before)
  {parameter result : TypeSystem.Ty} (sourceTyped : ExpressionHasType source context callee (.function parameter result))
  (readCode : CompatibleExpressionReads.Certificate fuel (.initial compiled.compatible.checked) source scope callee
    (reasonAt callee) compiler.calleeCode.expression)
  (ordinaryCode : compiler.calleeCode.expression = OptionalCell.read readCode.type (.var readCode.index) (reasonAt callee))
  {sourceLocation : Dynamic.Location} {sourceCell : Dynamic.Cell}
  (sourceLookup : Dynamic.Environment.LooksUp environment readCode.binder sourceLocation)
  (sourceRead : Dynamic.Heap.Reads before sourceLocation sourceCell)
  (ordinaryCell : sourceCell.generalized = none) (stored : sourceCell.value = some (.closure function))
  {nativeLocation : Location}
  (nativeLookup : actual[ξ readCode.index]? = some (.cellRef (OptionalCell.cellType readCode.type) nativeLocation))
  (nativeRead : store.read? nativeLocation = some (.inRight .unit carrier))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include ordinaryCode nativeLookup nativeRead in
/-- Exact ordinary native cell receipts construct the callee completion,
including its unchanged whole store. -/
private theorem native_callee : Evaluates actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store := by
  rw [ordinaryCode]
  simpa only [OptionalCell.read, LanguageResult.success, LanguageResult.failure, Expr.rename,
    Renaming.lift] using OptionalCell.read_success (reasonAt callee) (.var nativeLookup) nativeRead

include parameters booleanFound booleanForm booleanType binderType booleanRequirements booleanCoercions codes in
private theorem argument_tree : DataExpressionSequence.Tree source
    (CompatibleExpressionBuiltinRuntime.Certificate fuel (.initial compiled.compatible.checked) source context solved reasonAt)
    scope [argument] (closure.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) compiler.codes := by
  rw [parameters, codes]
  simpa only [List.map_cons, List.map_nil, binderType, booleanType] using
    (DataExpressionSequence.Tree.single booleanFound
      (bool_child (values := .initial compiled.compatible.checked) (context := context) (fuel := fuel)
        (scope := scope) (solved := solved) (reasonAt := reasonAt) boolean
        booleanFound booleanForm booleanType booleanRequirements booleanCoercions))

include parameters codes in
private theorem argument_types : compiler.codes.map (·.type) = closure.code.receipt.loweredParameters.map Prod.snd := by
  simp only [codes, parameters, List.map_cons, List.map_nil]

include booleanTyped parent in
private theorem source_arguments : ExpressionsHaveTypes source context [argument] [.bool] ∧ ([TypeSystem.Ty.bool] : List TypeSystem.Ty).length = metadata.argumentCount := by
  exact ⟨.cons booleanTyped (.nil _), parent.arity⟩

include parameters in
private theorem source_parameters : function.parameters = [binder] := by
  rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) closure.code, parameters]
  rfl

include parent parameters emptyBody unitResult escaped rawResult nativeResult stageAccepted arityAccepted
  booleanFound booleanForm booleanType binderType booleanRequirements booleanCoercions booleanTyped codes
  environments heaps locals agrees typed stable wellFormed runtime covers heapTyped sourceTyped
  ordinaryCode sourceLookup sourceRead ordinaryCell stored nativeLookup nativeRead
  extension faithful observations functionTypes sameLedger runtimeLedger unique uninitialized missing in
/-- This full accepted indirect parent is constructed from real read/literal
children, the call's copies of the captured cells and a genuine nonempty
Source allocation. Its body and child meaning families are closed internally;
the returned pool is the actual restored post. -/
theorem parent_source_post :
    ∃ copies copiedHeap sourceSize value finalStore finalMap finalWorld,
      Dynamic.EnvironmentCopies function.source function.captured before copies copiedHeap ∧
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id
        (.value .unit) (parameterHeap copiedHeap binder boolean) ∧
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults (.value .unit) value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
        finalMap finalWorld (parameterHeap copiedHeap binder boolean) finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend before (parameterHeap copiedHeap binder boolean) ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, parameterHeap copiedHeap binder boolean, finalStore,
        canonical⟩,
        Relates initial reached ∧ poolObservations initial reached := by
  obtain ⟨calleeSize, calleeTrace⟩ := actual_callee_read (context := context) readCode sourceLookup sourceRead ordinaryCell stored
  have calleeEvaluation := native_callee compiler readCode ordinaryCode nativeLookup nativeRead
  have captures := (CallableIndexedOwnedCaptureExecutionValidity.captures_of_expression
    wellFormed runtime covers locals heapTyped sourceTyped calleeTrace.sound).1
  have args := boolean_arguments (program := program) (context := context) (evidence := evidence)
    (environment := environment) (before := before) boolean booleanFound booleanForm booleanRequirements booleanCoercions
  obtain ⟨copies, copiedHeap, copy⟩ := CellAwareGeneralizedSourceInversion.copies_exist function.source
    (show Dynamic.EnvironmentAgrees before function.context.locals function.captured from captures)
  have called := boolean_nil_call (program := program) (context := context) (evidence := evidence)
    (before := before) binder boolean (source_parameters closure parameters) emptyBody unitResult
    (closure.bodyOrigin escaped).frame closure.inputs.extended copy
  let argumentsSize := SourceExecutionSize.stepSize
    [SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [], SourceExecutionSize.stepSize []], SourceExecutionSize.stepSize []]
  let callSize := SourceExecutionSize.stepSize [SourceExecutionSize.stepSize []]
  let budget := max argumentsSize callSize
  have sourceArgs := source_arguments compiler parent booleanTyped
  obtain ⟨sourceSize, value, finalStore, finalMap, finalWorld, original, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedIndirectSourceAdapters.preserves_bounded profile compiler prepared parent closure
      (argument_tree compiler closure parameters booleanFound booleanForm booleanType binderType booleanRequirements booleanCoercions codes)
      (argument_types compiler closure parameters codes) escaped rawResult nativeResult
      environments heaps locals captures agrees typed initial stable wellFormed runtime covers heapTyped sourceArgs.1 sourceArgs.2
      budget
      (fun child _ => children_preserve (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
        extension faithful observations functionTypes sameLedger runtimeLedger unique uninitialized missing child)
      (fun child _ => original_body_preserves closure.code closure.inputs (closure.bodyOrigin escaped)
        emptyBody unitResult (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
        extension faithful observations (by rfl) child)
      initial (Relates.refl initial) (.refl _) (.refl _) (AdministrativePreserved.refl _ _) (Dynamic.HeapMetadataExtend.refl _)
      calleeTrace calleeEvaluation stageAccepted arityAccepted
      (SourceSuffix.of_call args called) (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  exact ⟨copies, copiedHeap, sourceSize, value, finalStore, finalMap, finalWorld, copy, original, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, reached, related, reached_pool_observations related⟩

include parent parameters emptyBody unitResult escaped rawResult nativeResult stageAccepted arityAccepted
  booleanFound booleanForm booleanType binderType booleanRequirements booleanCoercions booleanTyped codes
  environments heaps locals agrees typed stable wellFormed runtime covers heapTyped sourceTyped
  ordinaryCode sourceLookup sourceRead ordinaryCell stored nativeLookup nativeRead
  extension faithful observations functionTypes sameLedger runtimeLedger uninitialized missing in
/-- Original whole native completion reflects through the same accepted
parent and selected body. The Source size is independent, and every row is
observed on the actual restored final pool. -/
theorem parent_native_post {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ poolObservations initial reached := by
  obtain ⟨calleeSize, calleeTrace⟩ := actual_callee_read (context := context) readCode sourceLookup sourceRead ordinaryCell stored
  have calleeEvaluation := native_callee compiler readCode ordinaryCode nativeLookup nativeRead
  have captures := (CallableIndexedOwnedCaptureExecutionValidity.captures_of_expression
    wellFormed runtime covers locals heapTyped sourceTyped calleeTrace.sound).1
  have sourceArgs := source_arguments compiler parent booleanTyped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, original, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedIndirectSourceAdapters.reflects_bounded profile compiler prepared parent closure
      (argument_tree compiler closure parameters booleanFound booleanForm booleanType binderType booleanRequirements booleanCoercions codes)
      (argument_types compiler closure parameters codes) escaped rawResult nativeResult
      environments heaps locals captures agrees typed initial stable wellFormed runtime covers heapTyped sourceArgs.1 sourceArgs.2
      size
      (fun child _ => children_reflect (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
        extension faithful observations functionTypes sameLedger runtimeLedger uninitialized missing child)
      (fun child _ => original_body_reflects closure.code closure.inputs (closure.bodyOrigin escaped)
        emptyBody unitResult (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
        extension faithful observations functionTypes (by rfl) child)
      initial (Relates.refl initial) (.refl _) (.refl _) (AdministrativePreserved.refl _ _) (Dynamic.HeapMetadataExtend.refl _)
      calleeTrace calleeEvaluation stageAccepted arityAccepted completed (Nat.le_refl _)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, original, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, reached_pool_observations related⟩

end ClosedParent

end Tests.SourceCoreClosedOwnedIndirectExpression
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedMethodBootstrap
/-! Genuine selected methods consume the same actual typed bootstrap capture,
raw Source admission and closed builtin profile. Every parameter/body post and
caller restoration retains its actual reached pool. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedMethodBootstrap
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodCaptureReceipts
open Tests.SourceCoreClosedOwnedLexicalBody (reached_pool_observations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
  (dictionary : Dynamic.EvidenceEnvironment)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profileFlag : compiled.compatible.checked.catalog.callableContracts = true)

/-- Complete typed capture from the actual factory, including the whole store.
The Source heap is empty; native administrative closures remain fully typed. -/
structure TypedCapture where
  world : StoreTyping
  typed : RuntimeStoreHasTypes world (RecursiveNamedCatalogPreparedInitialization.store compiled) compiled.indexed.layouts.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) [] world ⟨[]⟩
    (RecursiveNamedCatalogPreparedInitialization.store compiled)
  capture : BootstrapCapture cached dictionary (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) world

/-- The genuine Source selector and actual preparation construct every field;
no native capture, initial heap relation or execution law is assumed. -/
theorem typed_capture_of_selected {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context caller traitName methodName
      requirements (sourceBody (compiled := compiled) (method := method)) dictionary)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults) cached dictionary profileFlag) := by
  obtain ⟨world, typed, heaps, ⟨capture⟩⟩ := of_selected_with_heap cached dictionary
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) accepted selected wellFormed
  exact ⟨⟨world, typed, heaps, capture⟩⟩

section Invocation
variable (bootstrap : TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults) cached dictionary profileFlag)
  (profile : Profile cached.compilation (.initial compiled.compatible.checked) (CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody (compiled := compiled) (method := method)) dictionary bootstrap.capture.administrative registry faults)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
    [] bootstrap.world cached.named.inputs arguments payloads)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (physical : owner.key.frameLocation = 0)
  (initial : State headers keys ⟨[], [], bootstrap.world, ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
    RecursiveNamedCatalogPreparedInitialization.environment compiled⟩)
  {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
  {traitName methodName : String} {requirements : List RequirementId}
  (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) callerContext callerEvidence traitName methodName
    requirements (sourceBody (compiled := compiled) (method := method)) dictionary)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include profile represented physical selected wellFormed in
/-- The real marked parameter producer's own allocation drives original full
Source admission. The reached heap, environments and pool are the same witness. -/
theorem selected_parameter_admission
    (rawTyped : Dynamic.ValuesHaveTypes (sourceBody (compiled := compiled) (method := method)).context ⟨[]⟩ arguments profile.types) :
    ∃ environment heap canonical store mapping world,
      Dynamic.BindersAllocate [] ⟨[]⟩ (methodFunction cached.compilation (sourceBody (compiled := compiled) (method := method)) dictionary).parameters
        arguments environment heap ∧
      Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) profile.context
        (sourceBody (compiled := compiled) (method := method)).source ∧ dictionary.Covers profile.context ∧
      Dynamic.HeapWellTyped profile.context heap ∧ Dynamic.EnvironmentAgrees heap profile.context.locals environment ∧
      (∃ facts finalContext,
        StatementsHaveType (sourceBody (compiled := compiled) (method := method)).source
          { returnType := (sourceBody (compiled := compiled) (method := method)).resultType } profile.context
          cached.compilation.statements finalContext facts ∧
        BodyCompletes (sourceBody (compiled := compiled) (method := method)).resultType facts) ∧
      ∃ reached : State headers keys ⟨cached.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
        mapping, world, heap, store, canonical⟩,
        Relates initial reached ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame mapping store record) := by
  have sameFrame := bootstrap.capture.frame_eq.trans physical.symm
  obtain ⟨_origin, _index, _metadata, _owned, _history, _emitted, entry, _added, _length, _spine, reached, related⟩ :=
    CallableIndexedOwnedMethodInvocationBounds.parameters_with_state cached.compilation
      (CallablePreparedMethodCatalogHookMeaning.of_builtin cached.compilation profile)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) bootstrap.capture.installed
      represented owner initial sameFrame bootstrap.heaps
  have emptyTyped : Dynamic.HeapWellTyped (sourceBody (compiled := compiled) (method := method)).context ⟨[]⟩ := by
    intro cell impossible; simp at impossible
  obtain ⟨runtime, covers, typed, locals, facts, finalContext, bodyTyped, completes⟩ :=
    CallableIndexedOwnedBodySourceAdmission.admission_at_selected_method_parameters profile.extended entry.allocation
      emptyTyped rawTyped wellFormed selected bootstrap.capture.sourceFrame
  exact ⟨entry.environment, entry.heap, entry.canonical, entry.store, entry.mapping, entry.world,
    entry.allocation, runtime, covers, typed, locals, ⟨facts, finalContext, bodyTyped, completes⟩,
    reached, related, fun row record member => record_snapshot reached row member⟩

include profile physical selected wellFormed in
/-- A genuine one-Boolean method signature supplies raw and native arguments
internally. Its actual parameter producer creates the one Source cell, while
all record observations come from that same actual reached pool. -/
theorem boolean_parameter_admission {binder : TypedBinder} (boolean : Bool)
    (bindings : cached.named.inputs = [(binder, .bool)]) (binderType : binder.scheme.body = .bool) :
    ∃ canonical store mapping world,
      Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) profile.context
        (sourceBody (compiled := compiled) (method := method)).source ∧ dictionary.Covers profile.context ∧
      Dynamic.HeapWellTyped profile.context ⟨[⟨.bool, some (.bool boolean), none⟩]⟩ ∧
      ∃ reached : State headers keys ⟨cached.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
        mapping, world, ⟨[⟨.bool, some (.bool boolean), none⟩]⟩, store, canonical⟩,
        Relates initial reached ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame mapping store record) := by
  have arguments : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
      [] bootstrap.world cached.named.inputs [.bool boolean] [.bool boolean] := by
    rw [bindings]
    apply CallableIndexedParameterMeaning.Arguments.cons _ .nil
    change ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      [] bootstrap.world binder.scheme.body (.bool boolean) (.bool boolean) .bool
    rw [binderType]
    exact .bool boolean
  have parameters : (methodFunction cached.compilation (sourceBody (compiled := compiled) (method := method)) dictionary).parameters = [binder] := by
    change (sourceBody (compiled := compiled) (method := method)).source.inputs = [binder]
    simpa only [bindings, List.map_cons, List.map_nil] using profile.parameters
  have rawTypes : profile.types = [.bool] := by
    rw [← Dynamic.MonoBindersExtend.bodyTypes_eq profile.extended, profile.parameters, bindings]
    simp only [List.map_cons, List.map_nil, binderType]
  have rawTyped : Dynamic.ValuesHaveTypes (sourceBody (compiled := compiled) (method := method)).context ⟨[]⟩
      [.bool boolean] profile.types := by
    rw [rawTypes]
    exact .cons (.bool boolean) .nil
  obtain ⟨environment, heap, canonical, store, mapping, world, allocated, runtime, covers, typed, _locals, _body, reached, related, snapshots⟩ :=
    selected_parameter_admission cached dictionary profileFlag bootstrap profile arguments owner physical initial selected wellFormed rawTyped
  have actualHeap : heap = ⟨[⟨.bool, some (.bool boolean), none⟩]⟩ := by
    rw [parameters] at allocated
    cases allocated with
    | cons head tail =>
      cases tail with
      | nil =>
        cases head
        simp only [binderType, List.nil_append]
  subst heap
  exact ⟨canonical, store, mapping, world, runtime, covers, typed, reached, related, snapshots⟩

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
  (escaped : faults .controlEscapedFunction cached.compilation.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location)
    (cached.diagnostics.reasonAt cached.named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((cached.diagnostics.reasonAt cached.named.signature.key id).add tag))

include profile represented physical extension faithful observations functionTypes escaped uninitialized missing in
/-- This Source method invocation uses the genuine bootstrap and internally
closed builtin body family; its actual reached pool supplies restoration. -/
theorem selected_source_post {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) size
      (sourceBody (compiled := compiled) (method := method)) dictionary ⟨[]⟩ arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: bootstrap.capture.installed.captured)
        (RecursiveNamedCatalogPreparedInitialization.store compiled)
        (cached.compilation.output.rename bootstrap.capture.installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
        finalMap finalWorld (sourceBody (compiled := compiled) (method := method)).resultType cached.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore, RecursiveNamedCatalogPreparedInitialization.environment compiled⟩,
        Relates initial reached ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedMethodBuiltinBounds.invocation_preserves cached.compilation profile
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) extension faithful observations functionTypes
      escaped uninitialized missing bootstrap.capture.installed represented owner initial
      (bootstrap.capture.frame_eq.trans physical.symm) bootstrap.heaps trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata,
    reached, related, fun row record member => record_snapshot reached row member⟩

include profile represented physical extension faithful observations functionTypes escaped uninitialized missing in
/-- Original whole hook completion reconstructs its independent Source grade
and retains the exact restored pool with every reached snapshot authenticated. -/
theorem selected_native_post {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: bootstrap.capture.installed.captured)
      (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (cached.compilation.output.rename bootstrap.capture.installed.embedding.lift) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        (sourceBody (compiled := compiled) (method := method)) dictionary ⟨[]⟩ arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
        finalMap finalWorld (sourceBody (compiled := compiled) (method := method)).resultType cached.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore, RecursiveNamedCatalogPreparedInitialization.environment compiled⟩,
        Relates initial reached ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, original, represented, heaps, maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedMethodBuiltinBounds.invocation_reflects cached.compilation profile
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) extension faithful observations functionTypes
      escaped uninitialized missing bootstrap.capture.installed represented owner initial
      (bootstrap.capture.frame_eq.trans physical.symm) bootstrap.heaps completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, original, represented, heaps, maps, worlds, frame, metadata,
    reached, related, fun row record member => record_snapshot reached row member⟩
end Invocation
end Tests.SourceCoreClosedOwnedMethodBootstrap
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedCoercionStep
/-! A genuine selected Coerce method enters its actual saved slot. The original
builtin profile closes its parameters and body internally, retaining the real
returned pool. Native reflection keeps the original strict body child and
constructs a separate Source grade. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedCoercionStep
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodCaptureReceipts
open Tests.SourceCoreClosedOwnedMethodBootstrap (TypedCapture)
open Tests.SourceCoreClosedOwnedLexicalBody (reached_pool_observations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
  (dictionary : Dynamic.EvidenceEnvironment)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profileFlag : compiled.compatible.checked.catalog.callableContracts = true)
  (bootstrap : TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults) cached dictionary profileFlag)
  (profile : Profile cached.compilation (.initial compiled.compatible.checked) (CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody (compiled := compiled) (method := method)) dictionary bootstrap.capture.administrative registry faults)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {step : CoercionStep} {call : CallableCoercionSpine.Call}

/-- Full raw edge, genuine selector/dictionary and actual cached slot association
are independent static receipts. Singleton arity follows the same binder row. -/
structure Selected where
  binder : TypedBinder
  signature : cached.named.signature = call.signature
  index : bootstrap.capture.installed.globalIndex = call.index
  bindings : cached.named.inputs = [(binder, call.signature.parameterType)]
  inputType : binder.scheme.body = step.source
  result : (sourceBody (compiled := compiled) (method := method)).resultType = step.target
  selector : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context evidence "Coerce" "coerce"
    step.requirements (sourceBody (compiled := compiled) (method := method)) dictionary

variable (selected : Selected (step := step) (call := call) (context := context) (evidence := evidence)
  cached dictionary profileFlag bootstrap)

/-- The original complete method row is assembled from these genuine receipts.
It is used only for the existing native completion inversion. -/
def method_row : CallablePreparedOperatorSuffixMeaning.Method compiled.indexed (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults
    (Program.ofChecked compiled.sourceProgram) context evidence := {
  step := step, call := call, named := cached.named, diagnostics := cached.diagnostics, code := cached.code
  compiled := cached.compilation, signature := selected.signature
  sourceBody := sourceBody (compiled := compiled) (method := method), dictionary := dictionary
  selected := selected.selector, administrative := bootstrap.capture.administrative, profile := profile
  input := selected.binder, bindings := selected.bindings, inputType := selected.inputType, result := selected.result }

include selected in
private theorem singleton_arguments {input : Dynamic.Value} {native : Value}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      [] bootstrap.world step.source input native call.signature.parameterType) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
      [] bootstrap.world cached.named.inputs [input] [native] := by
  rw [selected.bindings]
  apply CallableIndexedParameterMeaning.Arguments.cons _ .nil
  change ValueRep _ _ _ _ _ selected.binder.scheme.body _ _ _
  simpa only [selected.inputType] using represented

/-- Source method grades are reconstructed separately from native budgets. -/
def StepOutcome (sourceSize : Nat) (input : Dynamic.Value) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .value output => SourceExecutionSize.CoercionStepExecutes (Program.ofChecked compiled.sourceProgram)
      (SourceExecutionSize.stepSize [sourceSize]) context evidence ⟨[]⟩ step input output after
  | .fault reason => SourceExecutionSize.CoercionStepFaults (Program.ofChecked compiled.sourceProgram)
      (SourceExecutionSize.stepSize [sourceSize]) context evidence ⟨[]⟩ step input reason after

include selected in
private theorem step_of_body {sourceSize : Nat} {input : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
      (sourceBody (compiled := compiled) (method := method)) dictionary ⟨[]⟩ [input] outcome after) :
    StepOutcome (compiled := compiled) (context := context) (evidence := evidence) (step := step) sourceSize input outcome after := by
  cases trace with
  | value trace => exact .method selected.selector trace
  | fault trace => exact .method selected.selector trace

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
  (escaped : faults .controlEscapedFunction cached.compilation.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (cached.diagnostics.reasonAt cached.named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((cached.diagnostics.reasonAt cached.named.signature.key id).add tag))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (physical : owner.key.frameLocation = 0)
  (initial : State headers keys ⟨[], [], bootstrap.world, ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
    RecursiveNamedCatalogPreparedInitialization.environment compiled⟩)

section Emitted
variable {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction} {available : SourceCompilationPlan.EvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
  {inputCode outputCode : SourceCoreBasic.LoweredExpr}
  (emission : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available scope node policy inputCode step outputCode call)
  (sameMethod : emission.method = method)

include profile selected extension faithful observations functionTypes escaped uninitialized missing physical emission sameMethod in
/-- A real Source method outcome enters the same observed global slot. The
closed builtin producer supplies the actual parameter/body/restoration pool. -/
theorem source_invoke {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      [] bootstrap.world step.source input native call.signature.parameterType)
    (trace : NamedCalls.BodyOutcome (Program.ofChecked compiled.sourceProgram)
      (sourceBody (compiled := compiled) (method := method)) dictionary ⟨[]⟩ [input] outcome after) (reason : Word) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      SourceCompilationPlan.checkedCoercionMethod compiled.sourceProgram caller node available step = .ok method ∧
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        (sourceBody (compiled := compiled) (method := method)) dictionary ⟨[]⟩ [input] outcome after ∧
      StepOutcome (compiled := compiled) (context := context) (evidence := evidence) (step := step) sourceSize input outcome after ∧
      CallableCoercionSpine.Invoke (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason call
        (RecursiveNamedCatalogPreparedInitialization.store compiled) (.inRight .word native) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)) finalMap finalWorld
        step.target call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore, RecursiveNamedCatalogPreparedInitialization.environment compiled⟩,
        Relates initial reached ∧ (∀ row, RecordPrefix (records initial row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records initial row → record ∈ records reached row) := by
  obtain ⟨sourceSize, actualTrace⟩ := RecursiveNamedCallBounds.BodyOutcome.has_size trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata, reached, poolRelated⟩ :=
    CallableIndexedOwnedMethodBuiltinBounds.invocation_preserves cached.compilation profile
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) extension faithful observations functionTypes
      escaped uninitialized missing bootstrap.capture.installed
      (singleton_arguments cached dictionary profileFlag bootstrap selected represented) owner initial
      (bootstrap.capture.frame_eq.trans physical.symm) bootstrap.heaps actualTrace
  have reference := bootstrap.capture.installed.globalReference
  rw [selected.index] at reference
  have invoked : CallableCoercionSpine.Invoke (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason call
      (RecursiveNamedCatalogPreparedInitialization.store compiled) (.inRight .word native) value finalStore :=
    .applied reference bootstrap.capture.installed.globalRead evaluated
  have chosen : SourceCompilationPlan.checkedCoercionMethod compiled.sourceProgram caller node available step = .ok method := by
    simpa only [sameMethod] using emission.selectedMethod
  refine ⟨sourceSize, value, finalStore, finalMap, finalWorld, chosen, actualTrace,
    step_of_body cached dictionary profileFlag bootstrap selected actualTrace, invoked, ?_, heaps, maps, worlds, frame, metadata,
    reached, poolRelated, reached_pool_observations poolRelated⟩
  simpa only [selected.result, selected.signature] using related

include profile selected extension faithful observations functionTypes escaped uninitialized missing physical emission sameMethod in
/-- The real InvokeSized child remains strict in the native budget. Shared
reflection supplies an independent Source grade and the same restored pool. -/
theorem native_invoke {input : Dynamic.Value} {native value : Value} {budget : Nat} {reason : Word} {finalStore : Store}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      [] bootstrap.world step.source input native call.signature.parameterType)
    (completed : CallableCoercionSpine.InvokeSized budget (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason call
      (RecursiveNamedCatalogPreparedInitialization.store compiled) (.inRight .word native) value finalStore) :
    ∃ bodySize sourceSize outcome after finalMap finalWorld,
      SourceCompilationPlan.checkedCoercionMethod compiled.sourceProgram caller node available step = .ok method ∧
      bodySize < budget ∧ EvaluationSize bodySize (native :: bootstrap.capture.installed.captured)
        (RecursiveNamedCatalogPreparedInitialization.store compiled)
        (cached.compilation.output.rename bootstrap.capture.installed.embedding.lift) value finalStore ∧
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        (sourceBody (compiled := compiled) (method := method)) dictionary ⟨[]⟩ [input] outcome after ∧
      StepOutcome (compiled := compiled) (context := context) (evidence := evidence) (step := step) sourceSize input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)) finalMap finalWorld
        step.target call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore, RecursiveNamedCatalogPreparedInitialization.environment compiled⟩,
        Relates initial reached ∧ (∀ row, RecordPrefix (records initial row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records initial row → record ∈ records reached row) := by
  let saved : CallablePreparedOperatorSuffixMeaning.Capture
      (method_row cached dictionary profileFlag bootstrap profile selected)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      (RecursiveNamedCatalogPreparedInitialization.environment compiled) [] bootstrap.world ⟨[]⟩
      (RecursiveNamedCatalogPreparedInitialization.store compiled) :=
    ⟨bootstrap.capture.installed, selected.index⟩
  obtain ⟨bodySize, strict, evaluated⟩ := CallablePreparedOperatorSuffixMeaning.Capture.completed_sized
    (method := method_row cached dictionary profileFlag bootstrap profile selected)
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) saved completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, actualTrace, related, heaps, maps, worlds, frame, metadata, reached, poolRelated⟩ :=
    CallableIndexedOwnedMethodBuiltinBounds.invocation_reflects cached.compilation profile
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) extension faithful observations functionTypes
      escaped uninitialized missing bootstrap.capture.installed
      (singleton_arguments cached dictionary profileFlag bootstrap selected represented) owner initial
      (bootstrap.capture.frame_eq.trans physical.symm) bootstrap.heaps evaluated
  have chosen : SourceCompilationPlan.checkedCoercionMethod compiled.sourceProgram caller node available step = .ok method := by
    simpa only [sameMethod] using emission.selectedMethod
  refine ⟨bodySize, sourceSize, outcome, after, finalMap, finalWorld, chosen, strict, evaluated, actualTrace,
    step_of_body cached dictionary profileFlag bootstrap selected actualTrace, ?_, heaps, maps, worlds, frame, metadata,
    reached, poolRelated, reached_pool_observations poolRelated⟩
  simpa only [selected.result, selected.signature] using related
end Emitted
end Tests.SourceCoreClosedOwnedCoercionStep
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedCoercionPath
/-! Actual ordered Coerce methods retain their full compiled rows and saved
captures. Each closed body produces the real next pool; only the capture reads
are transported through its actual effects. The shared path folds keep every
record-producing post, including success and faults. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
namespace Tests.SourceCoreClosedOwnedCoercionPath
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodCaptureReceipts
open Tests.SourceCoreClosedOwnedMethodBootstrap (TypedCapture)
open Tests.SourceCoreClosedOwnedLexicalBody (reached_pool_observations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profileFlag : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction} {available : SourceCompilationPlan.EvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}

/-- Each actual row retains the original compiler Step, checked method/cache,
full independent Source selector/dictionary, typed bootstrap and builtin profile. -/
structure CheckedRow where
  method : ExecutableImplMethods.CheckedMethod
  cached : CallablePreparedMethodSelection.Cached compiled method.specialized
  dictionary : Dynamic.EvidenceEnvironment
  bootstrap : TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults) cached dictionary profileFlag
  profile : Profile cached.compilation (.initial compiled.compatible.checked) (CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody (compiled := compiled) (method := method)) dictionary bootstrap.capture.administrative registry faults
  step : CoercionStep
  call : CallableCoercionSpine.Call
  selected : Tests.SourceCoreClosedOwnedCoercionStep.Selected (step := step) (call := call) (context := context) (evidence := evidence)
    cached dictionary profileFlag bootstrap
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  physical : owner.key.frameLocation = 0
  inputCode : SourceCoreBasic.LoweredExpr
  outputCode : SourceCoreBasic.LoweredExpr
  emission : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available scope node policy inputCode step outputCode call
  sameMethod : emission.method = method

variable (row : CheckedRow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
  (context := context) (evidence := evidence) (project := project) (compilation := compilation)
  (caller := caller) (available := available) (scope := scope) (node := node) (policy := policy) profileFlag)

/-- This is the same complete original method row used for strict child inversion. -/
def CheckedRow.method_row := Tests.SourceCoreClosedOwnedCoercionStep.method_row
  row.cached row.dictionary profileFlag row.bootstrap row.profile row.selected

def CheckedRow.coercion_row : CallableCoercionPathMeaning.Row :=
  ⟨row.step, row.call, sourceBody (compiled := compiled) (method := row.method), row.dictionary⟩

/-- The saved native capture belongs to this actual state, with the exact
physical owner and selected global slot. It stores no body meaning. -/
structure Saved (index : ProtectedStateTransition.Index) where
  installed : Installed row.cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (sourceBody := sourceBody (compiled := compiled) (method := row.method))
    (administrative := row.bootstrap.capture.administrative) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    index.mapping index.world index.heap index.store index.canonical
  sameFrame : installed.frameLocation = row.owner.key.frameLocation
  sameIndex : installed.globalIndex = row.call.index

/-- Captures extend from real effects. Ordered records remain in the actual
returned pool and are never reconstructed by this operation. -/
def Saved.extend {index : ProtectedStateTransition.Index} (saved : Saved profileFlag row index)
    {mapping world heap store}
    (maps : LocationMap.Extends index.mapping mapping) (worlds : WorldExtends index.world world)
    (frame : AdministrativePreserved index.mapping index.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend index.heap heap) :
    Saved profileFlag row (index.extend mapping world heap store) :=
  ⟨saved.installed.extend maps worlds frame metadata, saved.sameFrame, saved.sameIndex⟩

variable (rows : List (CheckedRow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
  (context := context) (evidence := evidence) (project := project) (compilation := compilation)
  (caller := caller) (available := available) (scope := scope) (node := node) (policy := policy) profileFlag))

/-- The same complete Owned pool is accompanied by actual saved reads for
these finite checked rows. The relation observes only the genuine pool records. -/
def pathProtocol : ProtectedStateTransition.Protocol (Records keys) where
  State := fun index => { _pool : State headers keys index // ∀ row, row ∈ rows → Nonempty (Saved profileFlag row index) }
  records := fun state => records state.val
  Relates := fun first last => Relates first.val last.val
  refl := fun state => Relates.refl state.val
  trans := fun first last => first.trans last

/-- One actual post is wrapped with captures extended through exactly its true
effects. The complete pool and record vector are retained verbatim. -/
def wrap_post {index : ProtectedStateTransition.Index}
    (initial : (pathProtocol profileFlag rows).State index) {mapping world heap store}
    (reached : State headers keys (index.extend mapping world heap store))
    (maps : LocationMap.Extends index.mapping mapping) (worlds : WorldExtends index.world world)
    (frame : AdministrativePreserved index.mapping index.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend index.heap heap) :
    (pathProtocol profileFlag rows).State (index.extend mapping world heap store) :=
  ⟨reached, by
    intro other member
    obtain ⟨saved⟩ := initial.property other member
    exact ⟨Saved.extend profileFlag other saved maps worlds frame metadata⟩⟩

theorem wrapped_pool {index : ProtectedStateTransition.Index}
    (initial : (pathProtocol profileFlag rows).State index) {mapping world heap store}
    (reached : State headers keys (index.extend mapping world heap store))
    (maps : LocationMap.Extends index.mapping mapping) (worlds : WorldExtends index.world world)
    (frame : AdministrativePreserved index.mapping index.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend index.heap heap) :
    (wrap_post profileFlag rows initial reached maps worlds frame metadata).val = reached := rfl

variable (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
  (escaped : ∀ row, row ∈ rows → faults .controlEscapedFunction row.cached.compilation.own.table.escapedReason)
  (uninitialized : ∀ row, row ∈ rows → ∀ id location,
    faults (.uninitializedLocation location) (row.cached.diagnostics.reasonAt row.cached.named.signature.key id))
  (missing : ∀ row, row ∈ rows → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((row.cached.diagnostics.reasonAt row.cached.named.signature.key id).add tag))

include extension faithful observations functionTypes escaped uninitialized missing in
/-- Every method callback is derived here from the actual captured slot and
proved closed builtin body family; it is never a semantic hypothesis. -/
private theorem steps_preserve (reason : Word) :
    ProtectedCoercionPathMeaning.StepPreserves (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (row := CheckedRow.coercion_row profileFlag) (registry := registry) (faults := faults)
      (caller := (RecursiveNamedCatalogPreparedInitialization.environment compiled)) (reason := reason) (pathProtocol profileFlag rows) [] (RecursiveNamedCatalogPreparedInitialization.environment compiled) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (SourceSemantics.Program.ofChecked compiled.sourceProgram) rows := by
  intro current mapping world before after store input native outcome member initial heaps represented trace
  obtain ⟨saved⟩ := initial.property current member
  change ValueRep compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) mapping world current.step.source input native current.call.signature.parameterType at represented
  change CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) mapping world before store at heaps
  have arguments : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
      mapping world current.cached.named.inputs [input] [native] := by
    rw [current.selected.bindings]
    apply CallableIndexedParameterMeaning.Arguments.cons _ .nil
    change ValueRep _ _ _ _ _ current.selected.binder.scheme.body _ _ _
    simpa only [current.selected.inputType] using represented
  change NamedCalls.BodyOutcome (SourceSemantics.Program.ofChecked compiled.sourceProgram) (sourceBody (compiled := compiled) (method := current.method)) current.dictionary before [input] outcome after at trace
  obtain ⟨sourceSize, actualTrace⟩ := RecursiveNamedCallBounds.BodyOutcome.has_size trace
  have produced :=
    CallableIndexedOwnedMethodBuiltinBounds.invocation_preserves
      (compiled := compiled) (program := (SourceSemantics.Program.ofChecked compiled.sourceProgram)) (headers := headers) (keys := keys)
      (registry := registry) (faults := faults)
      (named := current.cached.named) (diagnostics := current.cached.diagnostics) (code := current.cached.code)
      (sourceBody := sourceBody (compiled := compiled) (method := current.method))
      (dictionary := current.dictionary) (administrative := current.bootstrap.capture.administrative)
      (mapping := mapping) (world := world) (before := before) (store := store)
      (callerEnvironment := (RecursiveNamedCatalogPreparedInitialization.environment compiled)) (callerScope := []) (callerCanonical := (RecursiveNamedCatalogPreparedInitialization.environment compiled))
      current.cached.compilation current.profile (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      extension faithful observations functionTypes (escaped current member) (uninitialized current member) (missing current member)
      saved.installed arguments current.owner initial.val saved.sameFrame heaps actualTrace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, reached, poolRelated⟩ := produced
  have reference := saved.installed.globalReference
  rw [saved.sameIndex] at reference
  refine ⟨value, finalStore, finalMap, finalWorld, .applied reference saved.installed.globalRead evaluated,
    ?_, finalHeaps, maps, worlds, frame, metadata,
    wrap_post profileFlag rows initial reached maps worlds frame metadata, poolRelated⟩
  simpa only [SourceCoreCompatibleValues.Context.initial, CheckedRow.coercion_row, current.selected.result, current.selected.signature] using related

include extension faithful observations functionTypes escaped uninitialized missing in
/-- The original InvokeSized child remains native-strict, while the closed
reflection independently supplies the Source outcome and actual reached pool. -/
private theorem steps_reflect (budget : Nat) (reason : Word) :
    ProtectedCoercionPathMeaning.StepReflects (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (row := CheckedRow.coercion_row profileFlag) (registry := registry) (faults := faults)
      (pathProtocol profileFlag rows) [] (RecursiveNamedCatalogPreparedInitialization.environment compiled) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (SourceSemantics.Program.ofChecked compiled.sourceProgram) (CallableCoercionSpine.InvokeSized budget (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason) rows := by
  intro current mapping world before store finalStore input native value member initial heaps represented completed
  obtain ⟨saved⟩ := initial.property current member
  change ValueRep compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) mapping world current.step.source input native current.call.signature.parameterType at represented
  change CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) mapping world before store at heaps
  have arguments : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
      mapping world current.cached.named.inputs [input] [native] := by
    rw [current.selected.bindings]
    apply CallableIndexedParameterMeaning.Arguments.cons _ .nil
    change ValueRep _ _ _ _ _ current.selected.binder.scheme.body _ _ _
    simpa only [current.selected.inputType] using represented
  change CallableCoercionSpine.InvokeSized budget (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason current.call store (.inRight .word native) value finalStore at completed
  let captured : CallablePreparedOperatorSuffixMeaning.Capture (current.method_row profileFlag) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (RecursiveNamedCatalogPreparedInitialization.environment compiled) mapping world before store :=
    ⟨saved.installed, saved.sameIndex⟩
  obtain ⟨bodySize, _strict, body⟩ := CallablePreparedOperatorSuffixMeaning.Capture.completed_sized
    (method := current.method_row profileFlag) (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) captured completed
  have produced :=
    CallableIndexedOwnedMethodBuiltinBounds.invocation_reflects
      (compiled := compiled) (program := (SourceSemantics.Program.ofChecked compiled.sourceProgram)) (headers := headers) (keys := keys)
      (registry := registry) (faults := faults)
      (named := current.cached.named) (diagnostics := current.cached.diagnostics) (code := current.cached.code)
      (sourceBody := sourceBody (compiled := compiled) (method := current.method))
      (dictionary := current.dictionary) (administrative := current.bootstrap.capture.administrative)
      (mapping := mapping) (world := world) (before := before) (store := store)
      (callerEnvironment := (RecursiveNamedCatalogPreparedInitialization.environment compiled)) (callerScope := []) (callerCanonical := (RecursiveNamedCatalogPreparedInitialization.environment compiled))
      current.cached.compilation current.profile (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      extension faithful observations functionTypes (escaped current member) (uninitialized current member) (missing current member)
      saved.installed arguments current.owner initial.val saved.sameFrame heaps body
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, actualTrace, related, finalHeaps, maps, worlds, frame, metadata, reached, poolRelated⟩ := produced
  refine ⟨outcome, after, finalMap, finalWorld, actualTrace.sound, ?_, finalHeaps, maps, worlds, frame, metadata,
    wrap_post profileFlag rows initial reached maps worlds frame metadata, poolRelated⟩
  simpa only [SourceCoreCompatibleValues.Context.initial, CheckedRow.coercion_row, current.selected.result, current.selected.signature] using related


section Pair
variable (first second : CheckedRow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
  (context := context) (evidence := evidence) (project := project) (compilation := compilation)
  (caller := caller) (available := available) (scope := scope) (node := node) (policy := policy) profileFlag)

/-- Both true bootstrap receipts have the same entire store, so their actual
worlds agree. The pool and the two ordered capture rows are retained directly. -/
def initial_pair
    (pool : State headers keys ⟨[], [], first.bootstrap.world, ⟨[]⟩, (RecursiveNamedCatalogPreparedInitialization.store compiled), (RecursiveNamedCatalogPreparedInitialization.environment compiled)⟩) :
    (pathProtocol profileFlag [first, second]).State
      ⟨[], [], first.bootstrap.world, ⟨[]⟩, (RecursiveNamedCatalogPreparedInitialization.store compiled), (RecursiveNamedCatalogPreparedInitialization.environment compiled)⟩ :=
  ⟨pool, by
    intro current member
    rcases List.mem_cons.mp member with same | member
    · subst current
      exact ⟨⟨first.bootstrap.capture.installed,
        first.bootstrap.capture.frame_eq.trans first.physical.symm, first.selected.index⟩⟩
    · have same := List.mem_singleton.mp member
      subst current
      have saved : Saved profileFlag second
          ⟨[], [], second.bootstrap.world, ⟨[]⟩, (RecursiveNamedCatalogPreparedInitialization.store compiled), (RecursiveNamedCatalogPreparedInitialization.environment compiled)⟩ :=
        ⟨second.bootstrap.capture.installed,
          second.bootstrap.capture.frame_eq.trans second.physical.symm, second.selected.index⟩
      have same : second.bootstrap.world = first.bootstrap.world :=
        second.bootstrap.typed.world_eq.trans first.bootstrap.typed.world_eq.symm
      exact ⟨same ▸ saved⟩⟩

/-- Raw Source types and native types join separately; their projection alone
is never used to identify the original Source path. -/
theorem pair_chain (sourceJoin : first.step.target = second.step.source)
    (nativeJoin : first.call.signature.resultType = second.call.signature.parameterType) :
    CallableCoercionPathMeaning.ChainFor (CheckedRow.coercion_row profileFlag)
      first.step.source first.call.signature.parameterType [first, second]
      second.step.target second.call.signature.resultType := by
  apply CallableCoercionPathMeaning.ChainFor.cons
  change CallableCoercionPathMeaning.ChainFor _ first.step.target first.call.signature.resultType
    [second] second.step.target second.call.signature.resultType
  rw [sourceJoin, nativeJoin]
  exact .cons (.nil _ _)

/-- The actual compiler steps compose in their recorded order, retaining full
method/dictionary/global receipts and the real emitted suffix. -/
theorem emitted_pair (codeJoin : first.outputCode = second.inputCode) :
    CallableCoercionSpine.Spine compiled.sourceProgram project compilation caller available scope node policy
      first.inputCode [first.step, second.step] second.outputCode [first.call, second.call] := by
  apply CallableCoercionSpine.Spine.cons first.emission
  rw [codeJoin]
  exact .cons second.emission .nil

private theorem ordinary_pair {before after : Dynamic.Heap} {input : Dynamic.Value}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : CallableCoercionPathMeaning.SelectedTraceFor (CheckedRow.coercion_row profileFlag)
      (SourceSemantics.Program.ofChecked compiled.sourceProgram) [first, second] before input outcome after) :
    CallableCoercionExpressionMeaning.Path (SourceSemantics.Program.ofChecked compiled.sourceProgram) context evidence before
      [first.step, second.step] input outcome after := by
  cases trace with
  | fault failed => exact .head (.method first.selected.selector failed)
  | cons invoked tail =>
    cases tail with
    | fault failed => exact .tail (.method first.selected.selector invoked) (.head (.method second.selected.selector failed))
    | cons called tail =>
      cases tail
      exact .cons (.method first.selected.selector invoked) (.cons (.method second.selected.selector called) .nil)

/-- The independent original Source grade is obtained from the same genuine
selected path, reusing existing Source grading rather than a new induction. -/
theorem graded_pair {before after : Dynamic.Heap} {input : Dynamic.Value}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : CallableCoercionPathMeaning.SelectedTraceFor (CheckedRow.coercion_row profileFlag)
      (SourceSemantics.Program.ofChecked compiled.sourceProgram) [first, second] before input outcome after) :
    ∃ sourceSize, CallablePreparedOperatorSourceBounds.PathAt (SourceSemantics.Program.ofChecked compiled.sourceProgram) sourceSize context evidence
      before [first.step, second.step] input outcome after := by
  have source := ordinary_pair profileFlag first second trace
  cases outcome with
  | value value => exact SourceExecutionSize.CoercionPathExecutes.has_size source
  | fault reason => exact SourceExecutionSize.CoercionPathFaults.has_size source

variable (sourceJoin : first.step.target = second.step.source)
  (nativeJoin : first.call.signature.resultType = second.call.signature.parameterType)
  (codeJoin : first.outputCode = second.inputCode)
  (pool : State headers keys ⟨[], [], first.bootstrap.world, ⟨[]⟩, (RecursiveNamedCatalogPreparedInitialization.store compiled), (RecursiveNamedCatalogPreparedInitialization.environment compiled)⟩)
  (pairEscaped : ∀ row, row ∈ [first, second] → faults .controlEscapedFunction row.cached.compilation.own.table.escapedReason)
  (pairUninitialized : ∀ row, row ∈ [first, second] → ∀ id location,
    faults (.uninitializedLocation location) (row.cached.diagnostics.reasonAt row.cached.named.signature.key id))
  (pairMissing : ∀ row, row ∈ [first, second] → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((row.cached.diagnostics.reasonAt row.cached.named.signature.key id).add tag))

include extension faithful observations functionTypes pairEscaped pairUninitialized pairMissing sourceJoin nativeJoin codeJoin pool in
/-- Two closed checked methods use the actual first post as the second input.
Both success and faults return the true final pool and the same ordered source
path; every retained record still has its live snapshot observation. -/
theorem pair_preserves {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      [] first.bootstrap.world first.step.source input native first.call.signature.parameterType)
    (trace : CallableCoercionPathMeaning.SelectedTraceFor (CheckedRow.coercion_row profileFlag)
      (SourceSemantics.Program.ofChecked compiled.sourceProgram) [first, second] ⟨[]⟩ input outcome after) (reason : Word) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      CallableCoercionSpine.Spine compiled.sourceProgram project compilation caller available scope node policy
        first.inputCode [first.step, second.step] second.outputCode [first.call, second.call] ∧
      CallablePreparedOperatorSourceBounds.PathAt (SourceSemantics.Program.ofChecked compiled.sourceProgram) sourceSize context evidence ⟨[]⟩ [first.step, second.step] input outcome after ∧
      CallableCoercionSpine.Runs (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason (RecursiveNamedCatalogPreparedInitialization.store compiled) (.inRight .word native) [first.call, second.call] value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)) finalMap finalWorld
        second.step.target second.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends first.bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore, (RecursiveNamedCatalogPreparedInitialization.environment compiled)⟩,
        Relates pool reached ∧ (∀ row, RecordPrefix (records pool row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records pool row → record ∈ records reached row) := by
  have step : ProtectedCoercionPathMeaning.StepPreserves
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (row := CheckedRow.coercion_row profileFlag) (registry := registry) (faults := faults)
      (caller := (RecursiveNamedCatalogPreparedInitialization.environment compiled)) (reason := reason) (pathProtocol profileFlag [first, second]) [] (RecursiveNamedCatalogPreparedInitialization.environment compiled)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (SourceSemantics.Program.ofChecked compiled.sourceProgram) [first, second] :=
    steps_preserve profileFlag [first, second] extension faithful observations functionTypes
    pairEscaped pairUninitialized pairMissing reason
  obtain ⟨value, finalStore, finalMap, finalWorld, runs, related, heaps, maps, worlds, frame, metadata, reached, poolRelated⟩ :=
    ProtectedCoercionPathMeaning.preserves
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (row := CheckedRow.coercion_row profileFlag) (registry := registry) (faults := faults)
      (caller := (RecursiveNamedCatalogPreparedInitialization.environment compiled)) (reason := reason) (pathProtocol profileFlag [first, second]) [] (RecursiveNamedCatalogPreparedInitialization.environment compiled)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (SourceSemantics.Program.ofChecked compiled.sourceProgram) step
      (pair_chain profileFlag first second sourceJoin nativeJoin)
      (initial_pair profileFlag first second pool) first.bootstrap.heaps represented trace
  obtain ⟨sourceSize, graded⟩ := graded_pair profileFlag first second trace
  exact ⟨sourceSize, value, finalStore, finalMap, finalWorld, emitted_pair profileFlag first second codeJoin,
    graded, runs, related, heaps, maps, worlds, frame, metadata, reached.val, poolRelated, reached_pool_observations poolRelated⟩

include extension faithful observations functionTypes pairEscaped pairUninitialized pairMissing sourceJoin nativeJoin codeJoin pool in
/-- Actual measured native invocations reflect the same two selected Source
methods. Source grading remains independent of the native budget, and final
records come only from the returned state of the shared ordered fold. -/
theorem pair_reflects {input : Dynamic.Value} {native value : Value} {budget : Nat} {reason : Word} {finalStore : Store}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
      [] first.bootstrap.world first.step.source input native first.call.signature.parameterType)
    (runs : CallableCoercionSpine.RunsFor (CallableCoercionSpine.InvokeSized budget (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason)
      (RecursiveNamedCatalogPreparedInitialization.store compiled) (.inRight .word native) [first.call, second.call] value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      CallableCoercionSpine.Spine compiled.sourceProgram project compilation caller available scope node policy
        first.inputCode [first.step, second.step] second.outputCode [first.call, second.call] ∧
      CallableCoercionPathMeaning.SelectedTraceFor (CheckedRow.coercion_row profileFlag)
        (SourceSemantics.Program.ofChecked compiled.sourceProgram) [first, second] ⟨[]⟩ input outcome after ∧
      CallablePreparedOperatorSourceBounds.PathAt (SourceSemantics.Program.ofChecked compiled.sourceProgram) sourceSize context evidence ⟨[]⟩ [first.step, second.step] input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)) finalMap finalWorld
        second.step.target second.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends first.bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore, (RecursiveNamedCatalogPreparedInitialization.environment compiled)⟩,
        Relates pool reached ∧ (∀ row, RecordPrefix (records pool row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records pool row → record ∈ records reached row) := by
  have step : ProtectedCoercionPathMeaning.StepReflects
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (row := CheckedRow.coercion_row profileFlag) (registry := registry) (faults := faults)
      (pathProtocol profileFlag [first, second]) [] (RecursiveNamedCatalogPreparedInitialization.environment compiled)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (SourceSemantics.Program.ofChecked compiled.sourceProgram)
      (CallableCoercionSpine.InvokeSized budget (RecursiveNamedCatalogPreparedInitialization.environment compiled) reason) [first, second] :=
    steps_reflect profileFlag [first, second] extension faithful observations functionTypes
    pairEscaped pairUninitialized pairMissing budget reason
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, reached, poolRelated⟩ :=
    ProtectedCoercionPathMeaning.reflects
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (row := CheckedRow.coercion_row profileFlag) (registry := registry) (faults := faults)
      (caller := (RecursiveNamedCatalogPreparedInitialization.environment compiled)) (reason := reason) (pathProtocol profileFlag [first, second]) [] (RecursiveNamedCatalogPreparedInitialization.environment compiled)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) (SourceSemantics.Program.ofChecked compiled.sourceProgram)
      (fun completed => completed.forget) step (pair_chain profileFlag first second sourceJoin nativeJoin)
      (initial_pair profileFlag first second pool) first.bootstrap.heaps represented (by simpa only [List.map_cons, List.map_nil, CheckedRow.coercion_row] using runs)
  obtain ⟨sourceSize, graded⟩ := graded_pair profileFlag first second trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, emitted_pair profileFlag first second codeJoin,
    trace, graded, related, heaps, maps, worlds, frame, metadata, reached.val, poolRelated, reached_pool_observations poolRelated⟩
end Pair

end Tests.SourceCoreClosedOwnedCoercionPath
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedMethodPrincipalBuiltin
/-! A genuine selected method and typed bootstrap drive a real Boolean argument
through the authentic principal packet body family and caller restoration.
Original builtin bodies close internally; all observations use the actual
returned pool and independent Source/native grades. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedMethodPrincipalBuiltin
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodPrincipal
open Tests.SourceCoreClosedOwnedMethodBootstrap

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : Principal compiled method)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profileFlag : compiled.compatible.checked.catalog.callableContracts = true)

/-- Whole preparation and the full method selector construct the native and
Source bootstrap together; the test requires no external initial heap law. -/
theorem typed_bootstrap {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      principal.cached principal.dictionary profileFlag) :=
  typed_capture_of_selected principal.cached principal.dictionary profileFlag accepted principal.selected wellFormed

variable
  (bootstrap : TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    principal.cached principal.dictionary profileFlag)
  (profile : Profile principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary
    bootstrap.capture.administrative registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (physical : owner.key.frameLocation = 0)
  (locations : ∀ header, header ∈ headers → owner.key.locations header =
    RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
  (initial : State headers keys ⟨[], [], bootstrap.world, ⟨[]⟩,
    RecursiveNamedCatalogPreparedInitialization.store compiled,
    RecursiveNamedCatalogPreparedInitialization.environment compiled⟩)
  {binder : TypedBinder}
  (bindings : principal.named.inputs = [(binder, .bool)])
  (binderType : binder.scheme.body = .bool)
  (boolean : Bool)

include bindings binderType in
private theorem boolean_arguments : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
    [] bootstrap.world principal.named.inputs [.bool boolean] [.bool boolean] := by
  rw [bindings]
  apply CallableIndexedParameterMeaning.Arguments.cons _ .nil
  change ValueRep compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    [] bootstrap.world binder.scheme.body (.bool boolean) (.bool boolean) .bool
  rw [binderType]
  exact .bool boolean

variable
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location)
    (principal.cached.diagnostics.reasonAt principal.named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((principal.cached.diagnostics.reasonAt principal.named.signature.key id).add tag))

include profile physical locations bindings binderType extension faithful observations functionTypes escaped uninitialized missing in
/-- Actual Source method execution consumes a genuine Bool parameter and the
closed principal packet family. It restores the same reached body pool. -/
theorem boolean_source_post {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) size
      principal.sourceBody principal.dictionary ⟨[]⟩ [.bool boolean] outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues [Value.bool boolean] :: bootstrap.capture.installed.captured)
        (RecursiveNamedCatalogPreparedInitialization.store compiled)
        (principal.cached.compilation.output.rename bootstrap.capture.installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore,
        RecursiveNamedCatalogPreparedInitialization.environment compiled⟩,
        Relates initial reached ∧
        (∀ row, RecordPrefix (records initial row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records initial row → record ∈ records reached row) := by
  have arguments := boolean_arguments principal profileFlag bootstrap bindings binderType boolean
  have observed := CallableIndexedOwnedMethodCaptureReceipts.BootstrapCapture.globals_for_owner
    principal.cached principal.dictionary (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    bootstrap.capture owner locations
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedMethodPrincipalBuiltinBounds.invocation_preserves principal owner profile
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) extension faithful observations functionTypes
      escaped uninitialized missing bootstrap.capture.installed arguments initial observed
      (bootstrap.capture.frame_eq.trans physical.symm) bootstrap.heaps trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata,
    reached, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩

include profile physical locations bindings binderType extension faithful observations functionTypes escaped uninitialized missing in
/-- Whole native completion reflects through the actual authentic parameter
packet, closed builtin body and reached-pool restoration. Source grade is independent. -/
theorem boolean_native_post {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues [Value.bool boolean] :: bootstrap.capture.installed.captured)
      (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (principal.cached.compilation.output.rename bootstrap.capture.installed.embedding.lift) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        principal.sourceBody principal.dictionary ⟨[]⟩ [.bool boolean] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
        finalMap finalWorld principal.sourceBody.resultType principal.named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends bootstrap.world finalWorld ∧
      AdministrativePreserved [] (RecursiveNamedCatalogPreparedInitialization.store compiled) finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ after ∧
      ∃ reached : State headers keys ⟨[], finalMap, finalWorld, after, finalStore,
        RecursiveNamedCatalogPreparedInitialization.environment compiled⟩,
        Relates initial reached ∧
        (∀ row, RecordPrefix (records initial row) (records reached row)) ∧
        (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs
          compiled.indexed.ancestry.graph.table compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        (∀ row record, record ∈ records initial row → record ∈ records reached row) := by
  have arguments := boolean_arguments principal profileFlag bootstrap bindings binderType boolean
  have observed := CallableIndexedOwnedMethodCaptureReceipts.BootstrapCapture.globals_for_owner
    principal.cached principal.dictionary (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    bootstrap.capture owner locations
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedMethodPrincipalBuiltinBounds.invocation_reflects principal owner profile
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) extension faithful observations functionTypes
      escaped uninitialized missing bootstrap.capture.installed arguments initial observed
      (bootstrap.capture.frame_eq.trans physical.symm) bootstrap.heaps completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata,
    reached, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩

end Tests.SourceCoreClosedOwnedMethodPrincipalBuiltin
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedNamedFamily
/-! Static nil and named-call body receipts close a complete owned body
family. A real Boolean argument enters the marked parameter prefix, and the
parent statement retains the exact returned pool. No expression or body
execution law is a premise. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedNamedFamily
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds ProtectedStateTransition
open Tests.SourceCoreClosedOwnedExpressionTree (BooleanCall booleanCode)
open Tests.SourceCoreClosedOwnedExpressionHead (PreparedReceipts layouts)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {compilation : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceCoreFunctions.Context}

abbrev expressions (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) :=
  RecursiveNamedCatalog.Expressions (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers (compilation header)
    header.readFuel header.function.source context header.solved header.reasonAt

/-- The original ordinary Head and Tree factories retain the same real
Boolean argument, emitted call code and selected header slot. -/
theorem ordinary_boolean_call_tree
    {parent callee : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {scope : SourceCoreLocalCell.Scope} {id target argument : ExpressionId} {boolean : Bool} {code : Expr}
    (receipt : BooleanCall (headers := headers) (source := parent.function.source) (context := parent.context)
      (compilation := compilation parent) callee scope id target argument boolean code) :
    expressions (headers := headers) (compilation := compilation) parent parent.context scope id ⟨callee.output, code⟩ := by
  have literal : CompatibleExpressionLiterals.Certificate parent.solved parent.function.source argument (booleanCode boolean) :=
    ⟨receipt.argumentNode, receipt.argumentFound, .bool boolean receipt.argumentForm receipt.argumentType
      receipt.argumentRequirements receipt.argumentCoercions⟩
  have child : expressions (headers := headers) (compilation := compilation) parent parent.context scope argument (booleanCode boolean) :=
    .fragment (.fragment (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal literal))))))))
  have arity : callee.function.parameters.length = [argument].length := by
    rw [callee.parameters, List.length_map]
    have count := congrArg List.length receipt.parameterTypes
    simpa only [List.length_map, List.length_singleton] using count
  refine .node (entries := [(argument, booleanCode boolean)]) (.call (.named receipt.member receipt.metadata receipt.sourceType receipt.form
    receipt.calleeFound receipt.calleeForm receipt.calleeRequirements receipt.calleeCoercions receipt.valid
    receipt.predicates receipt.calleeEvidence arity receipt.emission receipt.selectedSlot ?_ ?_)) ?_
  · rw [receipt.parameterTypes]
    have sequence : DataExpressionSequence.Tree parent.function.source
        (CompatibleExpressionCalls.Entries scope [(argument, booleanCode boolean)]) scope [argument]
        [receipt.argumentNode.type] [booleanCode boolean] := .single receipt.argumentFound ⟨rfl, by simp⟩
    simpa only [receipt.argumentType] using sequence
  · simpa only [List.map_cons, List.map_nil, booleanCode] using receipt.nativeTypes.symm
  · intro selected lowered member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp member)
    exact child

/-- The source parent contains an actual callee expression. Every field is a
source, typing or compiler receipt, with no execution callback. -/
structure CallBody (parent : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) where
  statement : StatementId
  statementNode : StatementNode
  expression : ExpressionId
  target : ExpressionId
  argument : ExpressionId
  boolean : Bool
  code : Expr
  callee : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)
  body : parent.function.body = [statement]
  found : parent.function.source.lookupStatement? statement = some statementNode
  form : statementNode.form = .expression expression true
  statementType : statementNode.type = .unit
  call : BooleanCall (headers := headers) (source := parent.function.source) (context := parent.context)
    (compilation := compilation parent) callee
    (parent.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression target argument boolean code
  typed : ExpressionHasType parent.function.source parent.context expression call.node.type
  unitResult : parent.function.resultType = .unit
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy parent.policy parent.fuel parent.function.source
    (parent.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) parent.function.body
    parent.output parent.reasonAt true parent.escaped =
      .ok (LocalSequence.discard (LocalLoop.controlType parent.output) code (LocalLoop.fallthrough parent.output))

/-- The selected source and native parameter vectors genuinely contain one
Boolean, so this call reaches the marked allocation path. -/
theorem call_body_parameter_count
    {parent : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (receipt : CallBody (headers := headers) (compilation := compilation) parent) :
    receipt.callee.function.parameters.length = 1 ∧ receipt.callee.bindings.length = 1 := by
  have sourceCount := congrArg List.length receipt.call.parameterTypes
  have nativeCount := congrArg List.length receipt.call.nativeTypes
  constructor
  · rw [receipt.callee.parameters, List.length_map]
    simpa only [List.length_map, List.length_singleton] using sourceCount
  · simpa only [List.length_map, List.length_singleton] using nativeCount

/-- Only these static body shapes are admitted by this regression family. -/
inductive BodyReceipt (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) where
  | nil (valid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
      (body : header.function.body = []) (unitResult : header.function.resultType = .unit)
  | call (valid : CompatibleExpressionLiterals.ContextValid header.solved header.context header.function.evidence)
      (receipt : CallBody (headers := headers) (compilation := compilation) header)

variable (receipts : PreparedReceipts (headers := headers))
  (bodies : ∀ header, header ∈ headers → BodyReceipt (headers := headers) (compilation := compilation) header)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = owner.key.capturePrefix + 1)

include receipts in
private theorem accepted {header} (member : header ∈ headers) :
    SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body := by
  obtain ⟨row, prepared, instantiation, aligned⟩ := receipts header member
  exact aligned.accepted

include receipts in
private theorem projection {header} (member : header ∈ headers) :
    compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output := by
  obtain ⟨row, prepared, instantiation, aligned⟩ := receipts header member
  exact aligned.projection

private def profile {header} (member : header ∈ headers) (administrative : Core.Context) :
    RecursiveNamedCatalogMutualMeaning.MatchProfileForModeWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true false .reachable headers header (compilation header) header.readFuel (fun _ => True)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults := by
  cases bodies header member with
  | nil valid body unitResult =>
    let admission : GenericLexicalStatements.Syntax header.function.source (fun _ => True) header.context true
        header.function.body header.function.resultType := body ▸ .nil (Or.inr unitResult)
    let lexical : GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
        header.globals header.onError (.initial compiled.compatible.checked) header.function.source
        (expressions (headers := headers) (compilation := compilation) header) header.context
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true header.function.body
        header.function.resultType header.output (LocalLoop.fallthrough header.output) := body ▸ .nil (Or.inr unitResult)
    have generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
        header.output header.reasonAt true header.escaped = .ok (LocalLoop.fallthrough header.output) := by
      rw [body]
      cases header.fuel <;> rfl
    exact MatchProfileWith.of_extracted valid (accepted receipts member) (projection receipts member) generated
      (.body admission lexical) (.body (syntaxTree := admission) (body := lexical))
  | call valid receipt =>
    let admission : GenericLexicalStatements.Syntax header.function.source (fun _ => True) header.context true
        header.function.body header.function.resultType := by
      rw [receipt.body]
      exact .discard receipt.found receipt.form (by decide) receipt.statementType receipt.call.metadata.found
        receipt.typed trivial (.nil (Or.inr receipt.unitResult))
    let lexical : GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
        header.globals header.onError (.initial compiled.compatible.checked) header.function.source
        (expressions (headers := headers) (compilation := compilation) header) header.context
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true header.function.body
        header.function.resultType header.output
        (LocalSequence.discard (LocalLoop.controlType header.output) receipt.code (LocalLoop.fallthrough header.output)) := by
      rw [receipt.body]
      exact .discard receipt.found receipt.form (by decide) receipt.call.metadata.found
        (ordinary_boolean_call_tree receipt.call) (.nil (Or.inr receipt.unitResult))
    exact MatchProfileWith.of_extracted valid (accepted receipts member) (projection receipts member) receipt.generated
      (.body admission lexical) (.body (syntaxTree := admission) (body := lexical))

include extension faithful observations functionTypes receipts bodies owners uninitialized missing escaped prefixMatches in
/-- The closed named family proves every body callback from the static shapes
above, including the parent call and its real nonempty parameter prefix. -/
theorem family_preserves (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys)
      (CallableIndexedOwnedNamedBodyBounds.stableCondition functions owner header) size := by
  exact CallableIndexedOwnedNamedFamilyClosure.preserves_at functions extension faithful observations functionTypes owner
    (fun _ member => layouts receipts member) false owners uninitialized missing escaped prefixMatches
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry
      exact profile (registry := registry) (faults := faults) receipts bodies member administrative) size

include extension faithful observations functionTypes receipts bodies uninitialized missing escaped prefixMatches in
/-- Native completion selects the strict callees independently and returns its
own source grade together with the actual final pool. -/
theorem family_reflects (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys)
      (CallableIndexedOwnedNamedBodyBounds.stableCondition functions owner header) size := by
  exact CallableIndexedOwnedNamedFamilyClosure.reflects_at functions extension faithful observations functionTypes owner
    (fun _ member => layouts receipts member) false uninitialized missing escaped prefixMatches
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry
      exact profile (registry := registry) (faults := faults) receipts bodies member administrative) size

section Parent
variable {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (member : header ∈ headers)
  (parent : CallBody (headers := headers) (compilation := compilation) header)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers owner.key.locations owner.key.capturePrefix
    functions registry header arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost)
  (initial : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (seed : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current)

include extension faithful observations functionTypes receipts bodies owners uninitialized missing escaped prefixMatches member parent entry initial seed in
/-- A source parent-call execution yields genuine native completion and the
live snapshots of the returned pool, with all earlier row records retained. -/
theorem parent_source_post (size : Nat) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size header.function header.context
      entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      header.function.body = [parent.statement] ∧ parent.callee ∈ headers ∧
      ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩,
        Relates initial reached ∧ Tests.SourceCoreClosedOwnedExpressionHead.PoolObservations initial reached := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, reached, related⟩ :=
    family_preserves functions extension faithful observations functionTypes owner receipts bodies owners uninitialized missing escaped prefixMatches
      size header member entry initial seed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata,
    parent.body, parent.call.member, reached, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩

include extension faithful observations functionTypes receipts bodies uninitialized missing escaped prefixMatches member parent entry initial seed in
/-- Original native completion reflects the actual parent call at an
independent source grade and observes the same authentic reached pool. -/
theorem parent_native_post (size : Nat) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize header.function header.context
        entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      header.function.body = [parent.statement] ∧ parent.callee ∈ headers ∧
      ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩,
        Relates initial reached ∧ Tests.SourceCoreClosedOwnedExpressionHead.PoolObservations initial reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, reached, related⟩ :=
    family_reflects functions extension faithful observations functionTypes owner receipts bodies uninitialized missing escaped prefixMatches
      size header member entry initial seed completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata,
    parent.body, parent.call.member, reached, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩
end Parent
end Tests.SourceCoreClosedOwnedNamedFamily
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedNestedNamedFamily
/-! A real named Unit body discards an actual compiler lambda formation site.
Its empty literal body retains honest rank-zero static support. The original
Tree/profile factories and closed nested family prove every execution callback
internally, preserving the actual returned pool and its ordered snapshots. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
namespace Tests.SourceCoreClosedOwnedNestedNamedFamily
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds RecursiveNamedLambdaFormationHeads
open Tests.SourceCoreClosedOwnedExpressionHead (PreparedReceipts layouts PoolObservations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profileFlag : compiled.compatible.checked.catalog.callableContracts = true)

/-- Every parent uses rank one; its actual empty lambda body has rank zero.
This order is static and independent of Source/native execution grades. -/
def ranks (_header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) : Nat := 1

abbrev expressions (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) :=
  CallableIndexedOwnedNestedNamedFamilyClosure.certificates (headers := headers) (registry := registry) (faults := faults)
    ranks header context

/-- This packet contains only actual Source/compiler/static body receipts.
Site has a private constructor: its full original Code comes from real
ordinary contextual lambda compilation. BodyAt stores no execution law. -/
structure FormationBody (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) where
  statement : StatementId
  statementNode : StatementNode
  body : header.function.body = [statement]
  found : header.function.source.lookupStatement? statement = some statementNode
  site : CallableIndexedLambdaGeneration.Site compiled.indexed header.named [] .unit []
    header.context header.function.evidence []
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (nativePrefix (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      (program := Program.ofChecked compiled.sourceProgram) header)
  literalBody : CallableIndexedLambdaNestedRuntimeCertificates.BodyAt
    (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
    headers header registry faults 0 site.code
  expressionFound : header.function.source.lookupExpression? site.code.id = some site.code.sourceNode
  sourceType : site.code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure header.named [] .unit [] header.context header.function.evidence [])
  requirements : site.code.sourceNode.requirements = []
  coercions : site.code.sourceNode.coercions = []
  form : statementNode.form = .expression site.code.id true
  statementType : statementNode.type = .unit
  typed : ExpressionHasType header.function.source header.context site.code.id site.code.sourceNode.type
  unitResult : header.function.resultType = .unit
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped =
      .ok (LocalSequence.discard (LocalLoop.controlType header.output) site.code.lowered.expression
        (LocalLoop.fallthrough header.output))

/-- Lambda.of_site builds the original ranked leaf and empty ordered-child
Tree from the same genuine site and honest smaller static body. -/
theorem formation_tree
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (receipt : FormationBody (headers := headers) (registry := registry) (faults := faults) header) :
    expressions (headers := headers) (registry := registry) (faults := faults) header header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) receipt.site.code.id receipt.site.code.lowered := by
  have smaller : 0 < ranks header := by change 0 < 1; decide
  have support : CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport
      (indexed := compiled.indexed) (values := .initial compiled.compatible.checked)
      headers header registry faults (ranks header) 0 receipt.site.code := by
    simpa only [CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport, dif_pos smaller] using receipt.literalBody
  obtain ⟨head⟩ := CallableIndexedLambdaNestedRuntimeCertificates.Lambda.of_site
    (support := CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport
      (indexed := compiled.indexed) (values := .initial compiled.compatible.checked) headers header registry faults (ranks header))
    receipt.site smaller support receipt.expressionFound receipt.sourceType receipt.requirements receipt.coercions
  refine ⟨.node (entries := []) (.call (.lambda head)) (by intro _ _ member; cases member), ?_⟩
  exact .node (entries := []) (.call (.lambda head)) (by intro _ _ member; cases member) (by intro _ _ member; cases member)

/-- All family members use these concrete static body shapes. -/
inductive BodyReceipt (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) where
  | nil (valid : CompatibleRuntimeContextValidity.Valid header.solved header.context header.function.evidence)
      (body : header.function.body = []) (unitResult : header.function.resultType = .unit)
  | formation (valid : CompatibleRuntimeContextValidity.Valid header.solved header.context header.function.evidence)
      (receipt : FormationBody (headers := headers) (registry := registry) (faults := faults) header)

variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captureZero : owner.key.capturePrefix = 0)
  (receipts : PreparedReceipts (headers := headers))
  (bodies : ∀ header, header ∈ headers → BodyReceipt (headers := headers) (registry := registry) (faults := faults) header)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)

include receipts in
private theorem accepted {header} (member : header ∈ headers) :
    SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body := by
  obtain ⟨row, prepared, instantiation, aligned⟩ := receipts header member
  exact aligned.accepted

include receipts in
private theorem projection {header} (member : header ∈ headers) :
    compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output := by
  obtain ⟨row, prepared, instantiation, aligned⟩ := receipts header member
  exact aligned.projection

private def body_profile {header} (member : header ∈ headers) (administrative : Core.Context) :
    MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
      (expressions (headers := headers) (registry := registry) (faults := faults) header)
      .reachable header (fun _ => True)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults := by
  cases bodies header member with
  | nil valid body unitResult =>
    let admission : GenericLexicalStatements.Syntax header.function.source (fun _ => True) header.context true
        header.function.body header.function.resultType := body ▸ .nil (Or.inr unitResult)
    let lexical : GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
        header.globals header.onError (.initial compiled.compatible.checked) header.function.source
        (expressions (headers := headers) (registry := registry) (faults := faults) header) header.context
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true header.function.body
        header.function.resultType header.output (LocalLoop.fallthrough header.output) := body ▸ .nil (Or.inr unitResult)
    have generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
        header.output header.reasonAt true header.escaped = .ok (LocalLoop.fallthrough header.output) := by
      rw [body]
      cases header.fuel <;> rfl
    exact MatchProfileWith.of_extracted valid (accepted receipts member) (projection receipts member) generated
      (.body admission lexical) (.body (syntaxTree := admission) (body := lexical))
  | formation valid receipt =>
    let admission : GenericLexicalStatements.Syntax header.function.source (fun _ => True) header.context true
        header.function.body header.function.resultType := by
      rw [receipt.body]
      exact .discard receipt.found receipt.form (by decide) receipt.statementType receipt.expressionFound
        receipt.typed trivial (.nil (Or.inr receipt.unitResult))
    let lexical : GenericLexicalStatements.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
        header.globals header.onError (.initial compiled.compatible.checked) header.function.source
        (expressions (headers := headers) (registry := registry) (faults := faults) header) header.context
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) true header.function.body
        header.function.resultType header.output
        (LocalSequence.discard (LocalLoop.controlType header.output) receipt.site.code.lowered.expression
          (LocalLoop.fallthrough header.output)) := by
      rw [receipt.body]
      exact .discard receipt.found receipt.form (by decide) receipt.expressionFound
        (formation_tree receipt) (.nil (Or.inr receipt.unitResult))
    exact MatchProfileWith.of_extracted valid (accepted receipts member) (projection receipts member) receipt.generated
      (.body admission lexical) (.body (syntaxTree := admission) (body := lexical))

include captureZero profileFlag receipts bodies complete globals slots extension faithful observations functionTypes owners
  uninitialized missing escaped in
/-- The original per-header mutual family closes actual lambda formation from
these static profiles; no expression/body meaning family is a premise. -/
theorem family_preserves (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) registry header faults
      (protocol headers keys)
      (CallableIndexedOwnedNamedCanonicalEntries.condition
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) owner header) size := by
  exact CallableIndexedOwnedNestedNamedFamilyClosure.preserves_at owner captureZero profileFlag complete globals slots
    (fun _ member => layouts receipts member) extension faithful observations functionTypes owners uninitialized missing escaped ranks
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry allowed
      exact body_profile (registry := registry) (faults := faults) receipts bodies member administrative) size

include captureZero profileFlag receipts bodies complete globals slots extension faithful observations functionTypes
  uninitialized missing escaped in
/-- Native reflection returns an independently graded Source body and the same
actual reached pool from the closed nested family. -/
theorem family_reflects (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) registry header faults
      (protocol headers keys)
      (CallableIndexedOwnedNamedCanonicalEntries.condition
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) owner header) size := by
  exact CallableIndexedOwnedNestedNamedFamilyClosure.reflects_at owner captureZero profileFlag complete globals slots
    (fun _ member => layouts receipts member) extension faithful observations functionTypes uninitialized missing escaped ranks
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry allowed
      exact body_profile (registry := registry) (faults := faults) receipts bodies member administrative) size

section Parent
variable {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (member : header ∈ headers)
  (parent : FormationBody (headers := headers) (registry := registry) (faults := faults) header)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers owner.key.locations owner.key.capturePrefix
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) registry header arguments before initialStore
    initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost)
  (initial : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (allowed : CallableIndexedOwnedNamedCanonicalEntries.condition
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) owner header entry)

include captureZero profileFlag receipts bodies complete globals slots extension faithful observations functionTypes owners
  uninitialized missing escaped member parent entry initial allowed in
/-- Original Source execution of the named formation body runs the genuine
compiled lambda leaf and observes every ordered record in the actual post. -/
theorem parent_source_post (size : Nat) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size header.function header.context
      entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      header.function.body = [parent.statement] ∧
      ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩,
        Relates initial reached ∧ PoolObservations initial reached := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, reached, related⟩ :=
    family_preserves profileFlag owner captureZero receipts bodies complete globals slots extension faithful observations functionTypes
      owners uninitialized missing escaped size header member entry initial allowed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata,
    parent.body, reached, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩

include captureZero profileFlag receipts bodies complete globals slots extension faithful observations functionTypes
  uninitialized missing escaped member parent entry initial allowed in
/-- Original native completion reflects the real formation-containing Source
body at its independent grade and retains the same actual reached pool. -/
theorem parent_native_post (size : Nat) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize header.function header.context
        entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      header.function.body = [parent.statement] ∧
      ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, finalStore, entry.canonical⟩,
        Relates initial reached ∧ PoolObservations initial reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, reached, related⟩ :=
    family_reflects profileFlag owner captureZero receipts bodies complete globals slots extension faithful observations functionTypes
      uninitialized missing escaped size header member entry initial allowed completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata,
    parent.body, reached, related, Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related⟩
end Parent

end Tests.SourceCoreClosedOwnedNestedNamedFamily
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedWhile
/-! Closed finite while consumers derive their condition and body callbacks
from static literal and lexical Tree receipts. The actual owned allocator and
fixed frame read supply the body state; finite while folds keep its reached
pool through native recursion and restored source control. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedWhile
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open ProtectedStateTransition

/-- Only the compiler's ordinary builtin Boolean form is admitted. -/
def booleans (source : TypedSource) : GenericExpressionMeaning.Certificate :=
  fun _ id lowered => ∃ node name boolean,
    source.lookupExpression? id = some node ∧
    node.form = .reference name (.builtinBoolean boolean) ∧
    CompatibleExpressionLiterals.Literal [] node lowered.type lowered.expression

private theorem boolean_literal_empty {solved : List SolvedRequirement} {node : ExpressionNode}
    {type : Ty} {code : Expr} {name : String} {boolean : Bool}
    (literal : CompatibleExpressionLiterals.Literal solved node type code)
    (form : node.form = .reference name (.builtinBoolean boolean)) :
    CompatibleExpressionLiterals.Literal [] node type code := by
  cases literal with
  | bool value actual type requirements coercions =>
    exact .bool value actual type requirements coercions
  | unit actual _ _ _ | word _ actual _ _ _ _ | resolvedWord actual _ | resolvedInteger actual _ =>
    rw [form] at actual
    cases actual

/-- Actual accepted lowering supplies the static Boolean receipt. -/
theorem boolean_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr} {name : String} {boolean : Bool}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinBoolean boolean))
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered) :
    booleans source scope id lowered := by
  obtain ⟨other, otherFound, literal⟩ := CompatibleExpressionLiterals.of_functions
    found (by rw [form]; exact .bool name boolean)
    (by intro impossible; rw [form] at impossible; cases impossible)
    special readPolicy leafPolicy accepted
  have same := Option.some.inj (otherFound.symm.trans found)
  subst other
  exact ⟨node, name, boolean, found, form, boolean_literal_empty literal form⟩

private theorem boolean_receipts {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) (receipt : booleans source scope id lowered) :
    ∃ node, source.lookupExpression? id = some node ∧
      CompatibleExpressionLiterals.Literal [] node lowered.type lowered.expression ∧
      CompatibleExpressionLiterals.NumericEvidence context evidence node := by
  obtain ⟨node, name, boolean, found, form, literal⟩ := receipt
  refine ⟨node, found, literal, ?_⟩
  intro value resolution numeric
  rw [form] at numeric
  cases numeric

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

section Conditions
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

/-- Literal code has certified administrative effects and preserves records. -/
theorem boolean_preserves_at (size : Nat) (unique : NodeOccurrencesUnique source) :
    ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (booleans source) faults size := by
  have plain : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (booleans source) faults :=
    CompatibleExpressionLiterals.preserves_with_evidence (registry := registry) functions program context evidence
    (certificate := booleans source) boolean_receipts unique faults
  intro scope id lowered receipt node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees _typed initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    plain receipt found environments heaps locals agrees trace.sound
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    AdministrativeTransport.transition (protocol headers keys) (administrativeTransport headers keys) initial maps worlds frame metadata⟩

/-- A literal's original native completion yields an independent source grade. -/
theorem boolean_reflects_at (size : Nat) :
    ProtectedStateTransition.ReflectsAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (booleans source) faults size := by
  have plain : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (booleans source) faults :=
    CompatibleExpressionLiterals.reflects_with_evidence (registry := registry) functions program context evidence source
    (certificate := booleans source) boolean_receipts faults
  intro scope id lowered receipt node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees _typed initial evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    plain receipt found environments heaps locals agrees evaluated.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata,
    AdministrativeTransport.transition (protocol headers keys) (administrativeTransport headers keys) initial maps worlds frame metadata⟩
end Conditions

section While
variable {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
  (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {bodyCode conditionCode : Expr} {reason : Word}
  {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
  (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
  (conditionFound : source.lookupExpression? condition = some conditionNode)
  (conditionReceipt : booleans source scope condition ⟨.bool, conditionCode⟩)
  (codeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
    (LocalLoop.whileLoop type conditionCode bodyCode reason) (LocalLoop.resultType type) ambient.definitions)
  (tree : GenericLexicalStatements.Tree compiled.indexed.layouts owner active compiled.indexed.ancestry.layout.frame
    globals onError values source Tests.SourceCoreClosedOwnedLexicalBody.noExpressions context scope false statements expected type bodyCode)
  (admission : GenericLexicalStatements.Syntax source Tests.SourceCoreClosedOwnedLexicalBody.noExpressionSyntax context false statements expected)
  (unique : NodeOccurrencesUnique source)

include definitions registered found form conditionFound conditionReceipt codeTyped tree unique in
/-- Source head execution consumes literal and closed Tree proofs internally. -/
theorem closed_while_preserves (size : Nat)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
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
    (trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ TypedLexicalWhile.Restored environment outcome ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.whileLoop type conditionCode bodyCode reason).rename ξ) value finalStore ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        Transition (protocol headers keys) initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have bodies : RecursiveNamedLoopContracts.Below size (fun child => ProtectedStateTransition.Lexical.Gated.PreservesAtFor
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program evidence (fun _ => True)
      child (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type bodyCode) := by
    intro child _
    exact RecursiveNamedImperativeLexicalBounds.Stateful.preserves_at_for
      (functions := functions) (program := program) (evidence := evidence)
      (protocol := protocol headers keys) (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (administrative := administrative) (fun _ => True)
      (Tests.SourceCoreClosedOwnedLexicalBody.closed_tree_preserves_at functions evidence definitions registered tree child unique)
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  obtain ⟨sameContext, restored, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, final, related⟩ :=
    ProtectedWhile.Body.Stateful.while_preserves_bounded_for
      (protocol := protocol headers keys) (guard := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      functions program evidence (administrativeTransport headers keys) (fun _ => True) size
      (fun child _ => boolean_preserves_at functions evidence child unique)
      found form conditionFound conditionReceipt codeTyped unique bodies
      size (Nat.le_refl _) trivial environments heaps locals agrees typed reference read unmapped initial seed trace
  obtain ⟨prefixes, snapshots, _oldMembers⟩ := Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related
  exact ⟨sameContext, restored, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, heapMetadata, final, related, prefixes, snapshots, ⟨final, related⟩⟩

include definitions registered found form conditionFound conditionReceipt codeTyped tree admission unique in
/-- Native completion independently reconstructs source control and its pool. -/
theorem closed_while_reflects (budget size : Nat) (within : size ≤ budget)
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
    (evaluated : EvaluationSize size actual store ((LocalLoop.whileLoop type conditionCode bodyCode reason).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      TypedLexicalWhile.Restored environment outcome ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        Transition (protocol headers keys) initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have bodies : RecursiveNamedLoopContracts.Below budget (fun child => ProtectedStateTransition.Lexical.Gated.ReflectsAtFor
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program evidence (fun _ => True)
      child (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type bodyCode) := by
    intro child _
    exact RecursiveNamedImperativeLexicalBounds.Stateful.reflects_at_for
      (functions := functions) (program := program) (evidence := evidence)
      (protocol := protocol headers keys) (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (administrative := administrative) (fun _ => True)
      (Tests.SourceCoreClosedOwnedLexicalBody.closed_tree_reflects_at functions evidence definitions registered tree child)
  have bodyCannotFault : ∀ {actualProgram actualContext actualEvidence actualEnvironment before after finalContext reason},
      Dynamic.StatementsExecute actualProgram actualContext actualEvidence source actualEnvironment before statements finalContext (.fault reason) after → False := by
    intro actualProgram actualContext actualEvidence actualEnvironment before after finalContext reason trace
    exact GenericLexicalStatements.control_not_fault admission unique trace
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps, maps, worlds, frame, heapMetadata, final, related⟩ :=
    ProtectedWhile.Body.Stateful.while_reflects_bounded_for
      (protocol := protocol headers keys) (guard := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      functions program evidence (administrativeTransport headers keys) (fun _ => True) budget
      (fun child _ => boolean_reflects_at functions evidence child)
      found form conditionFound conditionReceipt codeTyped bodies bodyCannotFault
      size within trivial environments heaps locals agrees typed reference read unmapped initial seed evaluated
  obtain ⟨prefixes, snapshots, _oldMembers⟩ := Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps,
    maps, worlds, frame, heapMetadata, final, related, prefixes, snapshots, ⟨final, related⟩⟩
include codeTyped in
/-- The actual false loop installs its captured self closure, skips its body,
and keeps every row's exact record list. -/
theorem false_loop_keeps_records
    (falseCode : conditionCode = LanguageResult.success (.bool false))
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping) :
    let finalStore := TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ)
      (LocalLoop.fallthrough type) reason actual
    let finalWorld := TypedLexicalWhile.installedWorld world type
    ∃ final : State headers keys ⟨scope, mapping, finalWorld, before, finalStore, canonical⟩,
      Evaluates actual store ((LocalLoop.whileLoop type conditionCode bodyCode reason).rename ξ)
        (LocalLoop.fallthroughValue type) finalStore ∧
      Relates initial final ∧ records final = records initial ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping finalWorld before finalStore ∧
      finalStore.read? store.length = some (.inRight .unit
        (LocalLoop.installedClosure type (conditionCode.rename ξ) (bodyCode.rename ξ)
          (LocalLoop.fallthrough type) reason store.length actual)) ∧
      store.length ∉ mapping ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native) ∧
      CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native ∧
      (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        compiled.indexed.ancestry.layout.frame mapping finalStore record) := by
  obtain ⟨activation, progress, related, sameRecords⟩ :=
    ProtectedWhile.Body.Stateful.initial_state (protocol := protocol headers keys)
      functions (administrativeTransport headers keys) environments heaps locals agrees typed read unmapped codeTyped initial
  have conditionEval : Evaluates (Core.LoopExecution.entryEnvironment type store.length actual)
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (LocalLoop.fallthrough type) reason actual)
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) (.inRight .word (.bool false))
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (LocalLoop.fallthrough type) reason actual) := by
    rw [falseCode]
    simp only [Core.LoopExecution.conditionCode, LanguageResult.success, Expr.weakenAt, Expr.rename]
    exact .inRight .bool
  have nativeTrace : Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (bodyCode.rename ξ) reason store.length actual
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (LocalLoop.fallthrough type) reason actual)
      (LocalLoop.fallthroughValue type)
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (LocalLoop.fallthrough type) reason actual) :=
    .done conditionEval
  refine ⟨activation.retained, ?_, related, sameRecords, progress.1, activation.live.selfRead,
    activation.live.selfUnmapped, (TypedLexicalWhile.retain unmapped read progress.2.2.2.1).2,
    ⟨selected, ghost, metadata, physicalOwner, stable⟩, ?_⟩
  · simpa only [LoopRenaming.whileLoop] using nativeTrace.whileLoop_evaluates
  · intro row record member
    exact record_snapshot activation.retained row member

include definitions registered found form conditionFound conditionReceipt codeTyped tree admission unique in
/-- A constructed false-loop completion reaches the shared reflection fold;
neither an evaluation nor a source execution is assumed. -/
theorem false_loop_reflection_exists
    (falseCode : conditionCode = LanguageResult.success (.bool false))
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
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
    (unmapped : contextLocation ∉ mapping) :
    let finalStore := TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ)
      (LocalLoop.fallthrough type) reason actual
    ∃ nativeSize sourceSize outcome after finalMap finalWorld,
      EvaluationSize nativeSize actual store ((LocalLoop.whileLoop type conditionCode bodyCode reason).rename ξ)
        (LocalLoop.fallthroughValue type) finalStore ∧
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      TypedLexicalWhile.Restored environment outcome ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome (LocalLoop.fallthroughValue type) ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) := by
  obtain ⟨_installed, evaluated, _observations⟩ := false_loop_keeps_records
    (headers := headers) (keys := keys) functions codeTyped falseCode initial selected physicalOwner stable
    environments heaps locals agrees typed read unmapped
  obtain ⟨nativeSize, completed⟩ := evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, _heaps, _maps, _worlds, _frame, _metadata,
      final, related, prefixes, snapshots, _transition⟩ :=
    closed_while_reflects (headers := headers) (keys := keys) functions evidence definitions registered
      found form conditionFound conditionReceipt codeTyped tree admission unique nativeSize nativeSize (Nat.le_refl _)
      initial selected physicalOwner stable environments heaps locals agrees typed reference read unmapped completed
  exact ⟨nativeSize, sourceSize, outcome, after, finalMap, finalWorld, completed, trace, restored, represented,
    final, related, prefixes, snapshots⟩

end While
end Tests.SourceCoreClosedOwnedWhile
end

section
-- leanmerge: from Solcore.Test.SourceCoreClosedOwnedFor
/-! Closed for consumers derive literal/closed lexical callbacks, use real nil
post and header receipts, and construct an actual false-condition completion.
No expression, body, or assignment meaning family is assumed. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedFor
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open ProtectedStateTransition
open Tests.SourceCoreClosedOwnedWhile (booleans boolean_preserves_at boolean_reflects_at)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

section NilPost
variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming} {contextLocation location : Location}
  {type : Ty} {conditionCode bodyCode : Expr} {reason : Word}

private theorem nil_post_preserves (size : Nat) :
    ProtectedFor.Body.Stateful.PostPreservesAt (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := compiled.indexed.ancestry.layout.frame)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type) (conditionCode := conditionCode)
      (body := bodyCode) (selfReason := reason) [] (LocalLoop.fallthrough type) := by
  intro mapping world before after store finalContext finalEnvironment state native _read _guarded continued trace
  cases trace
  refine ⟨store, mapping, world, ?_, ⟨state.live.heaps, .refl _, .refl _, .refl _ _, .refl _⟩, state, ?_⟩
  · rw [TypedImperativeFor.post_rename]
    simpa only [LoopRenaming.fallthrough] using
      LocalLoop.fallthrough_evaluates type (TypedImperativeFor.postValues type location continued ++ actual) store
  · exact (protocol headers keys).refl state.retained

private theorem nil_post_faults (size : Nat) :
    ProtectedFor.Body.Stateful.PostFaultsAt (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := compiled.indexed.ancestry.layout.frame)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type) (conditionCode := conditionCode)
      (body := bodyCode) (selfReason := reason) [] (LocalLoop.fallthrough type) := by
  intro mapping world before after store finalContext reason state native _read _guarded continued trace
  cases trace

private theorem nil_post_reflects (size : Nat) :
    ProtectedFor.Body.Stateful.PostReflectsAt (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (administrative := administrative) (actualContext := actualContext) (frameLayout := compiled.indexed.ancestry.layout.frame)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type) (conditionCode := conditionCode)
      (body := bodyCode) (selfReason := reason) faults [] (LocalLoop.fallthrough type) := by
  intro mapping world before store finalStore value state native _read _guarded continued evaluated
  have pure : Evaluates (TypedImperativeFor.postValues type location continued ++ actual) store
      (ForLoop.postCode ((LocalLoop.fallthrough type).rename ξ)) (LocalLoop.fallthroughValue type) store := by
    rw [TypedImperativeFor.post_rename]
    simpa only [LoopRenaming.fallthrough] using
      LocalLoop.fallthrough_evaluates type (TypedImperativeFor.postValues type location continued ++ actual) store
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound pure
  exact Or.inl ⟨SourceExecutionSize.stepSize [], context, environment, before, mapping, world, .nil, rfl,
    ⟨state.live.heaps, .refl _, .refl _, .refl _ _, .refl _⟩, state, (protocol headers keys).refl state.retained⟩
end NilPost

section For
variable {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
  (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {bodyCode conditionCode : Expr} {reason : Word}
  {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
  (found : source.lookupStatement? id = some node) (form : node.form = .forLoop [] condition [] statements)
  (conditionFound : source.lookupExpression? condition = some conditionNode)
  (conditionReceipt : booleans source scope condition ⟨.bool, conditionCode⟩)
  (codeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
    (LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason) (LocalLoop.resultType type) ambient.definitions)
  (tree : GenericLexicalStatements.Tree compiled.indexed.layouts owner active compiled.indexed.ancestry.layout.frame
    globals onError values source Tests.SourceCoreClosedOwnedLexicalBody.noExpressions context scope false statements expected type bodyCode)
  (admission : GenericLexicalStatements.Syntax source Tests.SourceCoreClosedOwnedLexicalBody.noExpressionSyntax context false statements expected)
  (unique : NodeOccurrencesUnique source)


include definitions registered conditionFound conditionReceipt codeTyped tree unique in
/-- The literal and closed lexical Tree supply every smaller preservation
callback; the nil post's real source trace supplies its exact unchanged state. -/
theorem closed_loop_preserves_at (budget size : Nat) (within : size ≤ budget) :
    ProtectedFor.Body.Stateful.LoopPreservesAtFor (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      functions program evidence (fun _ => True) size (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition [] statements expected type
      (LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason) := by
  have bodies : RecursiveNamedLoopContracts.Below budget (fun child => ProtectedStateTransition.Lexical.Gated.PreservesAtFor
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program evidence (fun _ => True)
      child (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type bodyCode) := by
    intro child _
    exact RecursiveNamedImperativeLexicalBounds.Stateful.preserves_at_for
      (functions := functions) (program := program) (evidence := evidence)
      (protocol := protocol headers keys) (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (administrative := administrative) (fun _ => True)
      (Tests.SourceCoreClosedOwnedLexicalBody.closed_tree_preserves_at functions evidence definitions registered tree child unique)
  exact ProtectedFor.Body.Stateful.loop_preserves_bounded_for
    (protocol := protocol headers keys) (guard := CallableIndexedOwnedAllocationProducer.StableOwner keys)
    functions program evidence (administrativeTransport headers keys) (fun _ => True) budget
    (fun child _ => boolean_preserves_at functions evidence child unique)
    conditionFound conditionReceipt codeTyped unique bodies
    (fun _ _ _ child _ => nil_post_preserves functions evidence child)
    (fun _ _ _ child _ => nil_post_faults functions evidence child)
    size within

include definitions registered conditionFound conditionReceipt codeTyped tree admission unique in
/-- Native loop reflection uses independently graded literal and closed Tree
proofs; its nil post is reconstructed from the actual pure completion. -/
theorem closed_loop_reflects_at (budget size : Nat) (within : size ≤ budget) :
    ProtectedFor.Body.Stateful.LoopReflectsAtFor (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      functions program evidence (fun _ => True) size (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition [] statements expected type
      (LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason) := by
  have bodies : RecursiveNamedLoopContracts.Below budget (fun child => ProtectedStateTransition.Lexical.Gated.ReflectsAtFor
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program evidence (fun _ => True)
      child (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type bodyCode) := by
    intro child _
    exact RecursiveNamedImperativeLexicalBounds.Stateful.reflects_at_for
      (functions := functions) (program := program) (evidence := evidence)
      (protocol := protocol headers keys) (condition := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (administrative := administrative) (fun _ => True)
      (Tests.SourceCoreClosedOwnedLexicalBody.closed_tree_reflects_at functions evidence definitions registered tree child)
  have bodyCannotFault : ∀ {actualProgram actualContext actualEvidence actualEnvironment before after finalContext reason},
      Dynamic.StatementsExecute actualProgram actualContext actualEvidence source actualEnvironment before statements finalContext (.fault reason) after → False := by
    intro actualProgram actualContext actualEvidence actualEnvironment before after finalContext reason trace
    exact GenericLexicalStatements.control_not_fault admission unique trace
  exact ProtectedFor.Body.Stateful.loop_reflects_bounded_for
    (protocol := protocol headers keys) (guard := CallableIndexedOwnedAllocationProducer.StableOwner keys)
    functions program evidence (administrativeTransport headers keys) (fun _ => True) budget
    (fun child _ => boolean_reflects_at functions evidence child)
    conditionFound conditionReceipt codeTyped bodies bodyCannotFault
    (fun _ _ _ child _ => nil_post_reflects functions evidence child)
    size within
include definitions registered found form conditionFound conditionReceipt codeTyped tree admission unique in
/-- Native completion independently reconstructs source control and its pool. -/
theorem closed_for_reflects (budget size : Nat) (within : size ≤ budget)
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
    (evaluated : EvaluationSize size actual store ((LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      TypedLexicalWhile.Restored environment outcome ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        Transition (protocol headers keys) initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  let continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop :=
    fun nextContext nextScope nextCode => nextContext = context ∧ nextScope = scope ∧
      nextCode = LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason
  have loopCorrect : ∀ {nextContext nextScope nextCode}, continuation nextContext nextScope nextCode →
      RecursiveNamedHeaderContracts.AtMost budget (fun child => ProtectedFor.Body.Stateful.LoopReflectsAtFor
        (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program evidence
        (fun _ => True) child (source := source) (context := nextContext) (registry := registry) (faults := faults)
        (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := globals) (administrative := administrative)
        (scope := nextScope) condition [] statements expected type nextCode) := by
    intro nextContext nextScope nextCode receipt child bounded
    obtain ⟨rfl, rfl, rfl⟩ := receipt
    exact closed_loop_reflects_at functions evidence definitions registered conditionFound conditionReceipt codeTyped
      tree admission unique budget child bounded
  let tail : ProtectedForHeader.Stateful.TailFor (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ => True) registry functions source [] evidence administrative compiled.indexed.ancestry.layout.frame globals
      contextLocation native continuation context environment before :=
    ⟨⟨scope, LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason,
      mapping, world, canonical, actual, actualContext, ξ, store, ⟨rfl, rfl, rfl⟩, trivial,
      environments, heaps, locals, agrees, typed, reference, read, unmapped⟩, initial, seed⟩
  have headerResult := ProtectedForHeader.Stateful.ResultAtFor.nil (program := program) (type := type) (faults := faults) tail evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps, maps, worlds, frame, heapMetadata, final, related⟩ :=
    RecursiveNamedImperativeFor.Stateful.header_reflects_at_with_result
      (functions := functions) (program := program) (evidence := evidence) (protocol := protocol headers keys)
      (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys) (validity := fun _ => True) (budget := budget)
      size within found form loopCorrect initial headerResult
  obtain ⟨prefixes, snapshots, _oldMembers⟩ := Tests.SourceCoreClosedOwnedLexicalBody.reached_pool_observations related
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, finalHeaps,
    maps, worlds, frame, heapMetadata, final, related, prefixes, snapshots, ⟨final, related⟩⟩

include codeTyped in
/-- The actual false loop installs its captured self closure, skips its body,
and keeps every row's exact record list. -/
theorem false_for_keeps_records
    (falseCode : conditionCode = LanguageResult.success (.bool false))
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping) :
    let finalStore := TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ)
      (LocalLoop.fallthrough type) reason actual
    let finalWorld := TypedLexicalWhile.installedWorld world type
    ∃ final : State headers keys ⟨scope, mapping, finalWorld, before, finalStore, canonical⟩,
      Evaluates actual store ((LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason).rename ξ)
        (LocalLoop.fallthroughValue type) finalStore ∧
      Relates initial final ∧ records final = records initial ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping finalWorld before finalStore ∧
      finalStore.read? store.length = some (.inRight .unit
        (LocalLoop.installedClosure type (conditionCode.rename ξ) (bodyCode.rename ξ)
          (LocalLoop.fallthrough type) reason store.length actual)) ∧
      store.length ∉ mapping ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native) ∧
      CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native ∧
      (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        compiled.indexed.ancestry.layout.frame mapping finalStore record) := by
  obtain ⟨activation, progress, related, sameRecords⟩ :=
    ProtectedStateTransition.For.initial_state (protocol := protocol headers keys)
      (administrativeTransport headers keys) environments heaps locals agrees typed read unmapped codeTyped initial
  simp only [LoopRenaming.fallthrough] at activation progress related sameRecords
  have conditionEval : Evaluates (Core.LoopExecution.entryEnvironment type store.length actual)
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (LocalLoop.fallthrough type) reason actual)
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) (.inRight .word (.bool false))
      (TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (LocalLoop.fallthrough type) reason actual) := by
    rw [falseCode]
    simp only [Core.LoopExecution.conditionCode, LanguageResult.success, Expr.weakenAt, Expr.rename]
    exact .inRight .bool
  have nativeTrace := Core.LoopExecution.condition_false (type := type) (body := bodyCode.rename ξ)
    (post := LocalLoop.fallthrough type) (selfReason := reason) conditionEval
  refine ⟨activation.retained, ?_, related, sameRecords, progress.1, activation.live.selfRead,
    activation.live.selfUnmapped, (TypedLexicalWhile.retain unmapped read progress.2.2.2.1).2,
    ⟨selected, ghost, metadata, physicalOwner, stable⟩, ?_⟩
  · rw [LoopRenaming.iterate]
    apply LocalLoop.iterate_evaluates
    exact LocalLoop.invoke_success _ _ (.var rfl) activation.live.selfRead nativeTrace
  · intro row record member
    exact record_snapshot activation.retained row member

include definitions registered found form conditionFound conditionReceipt codeTyped tree admission unique in
/-- A constructed false-loop completion reaches the shared reflection fold;
neither an evaluation nor a source execution is assumed. -/
theorem false_for_reflection_exists
    (falseCode : conditionCode = LanguageResult.success (.bool false))
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location}
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
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
    (unmapped : contextLocation ∉ mapping) :
    let finalStore := TypedLexicalWhile.installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ)
      (LocalLoop.fallthrough type) reason actual
    ∃ nativeSize sourceSize outcome after finalMap finalWorld,
      EvaluationSize nativeSize actual store ((LocalLoop.iterate type conditionCode bodyCode (LocalLoop.fallthrough type) reason).rename ξ)
        (LocalLoop.fallthroughValue type) finalStore ∧
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      TypedLexicalWhile.Restored environment outcome ∧
      TypedLexicalWhile.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome (LocalLoop.fallthroughValue type) ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) := by
  obtain ⟨_installed, evaluated, _observations⟩ := false_for_keeps_records
    (headers := headers) (keys := keys) functions codeTyped falseCode initial selected physicalOwner stable
    environments heaps locals agrees typed read unmapped
  obtain ⟨nativeSize, completed⟩ := evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restored, represented, _heaps, _maps, _worlds, _frame, _metadata,
      final, related, prefixes, snapshots, _transition⟩ :=
    closed_for_reflects (headers := headers) (keys := keys) functions evidence definitions registered
      found form conditionFound conditionReceipt codeTyped tree admission unique nativeSize nativeSize (Nat.le_refl _)
      initial selected physicalOwner stable environments heaps locals agrees typed reference read unmapped completed
  exact ⟨nativeSize, sourceSize, outcome, after, finalMap, finalWorld, completed, trace, restored, represented,
    final, related, prefixes, snapshots⟩

end For
end Tests.SourceCoreClosedOwnedFor
end
