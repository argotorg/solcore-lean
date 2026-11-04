import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.AcceptedPrefixes
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.Heaps
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.OrdinaryBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MatchPrefixes
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ActualInvocationAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicStatements

/-!
# Cell-aware invocations: physical entry

Physical evidence for one actual named or contextual invocation, its extension, and the prefixes of ordinary, absent and generalized declarations.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
/-! Physical evidence for one actual named or contextual body invocation. Stored generalized entries
retain their original descriptor typing and the exact shared frame reference.
This package is supplied by real parameter entry and declaration allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalLocatedRows GeneralizedLocalBundleContexts CallableIndexedHistory
open GeneralizedLocalAcceptedLocatedRows ActualBodyInvocation

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {index : Index compiled bodyRelation} {context : SourceSemantics.Context}

inductive Entry {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    (index : Index compiled bodyRelation) (context : SourceSemantics.Context)
    (frameLocation : Core.Location) (id : Resolved.LocalId) (location : Dynamic.Location)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) : Prop where
  | ordinary {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads heap location cell)
      (descriptor : cell.generalized = none) :
      Entry (attachment := attachment) compiled index context frameLocation id location mapping world heap store
  | generalized {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
      {lexical : Substitution}
      (located : Located (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        function binding lexical location mapping world heap store)
      (owner : binding.caller = index.owner) (binder : binding.binder.id = id)
      (lexicalContext : ContextExtension lexical index.active)
      (frames : GeneralizedLocalAcceptedLocatedRows.Located.FramesWith attachment located frameLocation)
      (fields : Dynamic.RuntimeContextFields function.definitionContext context)
      (requirements : context.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements) :
      Entry (attachment := attachment) compiled index context frameLocation id location mapping world heap store

theorem Entry.transport {frameLocation id location mapping world heap store nextMap nextWorld after finalStore}
    (entry : Entry (attachment := attachment) compiled index context frameLocation id location mapping world heap store)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      mapping world heap store nextMap nextWorld after finalStore) :
    Entry (attachment := attachment) compiled index context frameLocation id location nextMap nextWorld after finalStore := by
  cases entry with
  | ordinary read descriptor =>
    obtain ⟨cell, updated, _, same⟩ := effect.metadata _ _ read
    exact .ordinary updated (same.trans descriptor)
  | generalized located owner binder lexical frames fields requirements =>
    obtain ⟨next, same⟩ := effect.retains_values located
    exact .generalized next owner binder lexical
      (GeneralizedLocalAcceptedLocatedRows.Located.FramesWith.transport frames effect.maps effect.worlds same) fields requirements

theorem Entry.authority {frameLocation id location mapping world heap store}
    (entry : Entry (attachment := attachment) compiled index context frameLocation id location mapping world heap store) :
    CellAwareScopeAuthority.Entry (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      index.owner index.active id location mapping world heap store := by
  cases entry with
  | ordinary read descriptor => exact .ordinary read descriptor
  | generalized located owner binder lexical _ _ _ => exact .generalized owner binder lexical ⟨located⟩

theorem Entry.weaken_view {before after : BodyRelation} {index : Index compiled before}
    {frameLocation id location mapping world heap store}
    (entry : Entry (attachment := attachment) compiled index context frameLocation id location mapping world heap store)
    (weaken : ∀ source view body, before source view body → after source view body) :
    Entry (attachment := attachment) compiled (index.weaken_view weaken) context frameLocation id location mapping world heap store := by
  cases entry with
  | ordinary read descriptor => exact .ordinary read descriptor
  | generalized located owner binder lexical frames fields requirements =>
    have same := index.weaken_view_fields weaken
    exact .generalized located (owner.trans same.2.2.1.symm) binder
      (same.2.2.2.1.symm ▸ lexical) frames fields requirements

structure Physical {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    (index : Index compiled bodyRelation) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (canonical : Core.Environment)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (environment : Dynamic.Environment) where
  frame : ActualBodyInvocation.Frame index
  declarations : CompatibleExpressionReads.ScopeDeclarations
    index.source scope context
  ownership : LocalIdentityOwnership index.source
  sourceDeclarations : CellAwareScopeDeclarations.Full index.source scope context
  location : Core.Location
  reference : canonical[scope.length + 1 + compiled.indexed.base.globals.length]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type location)
  read : store.read? location =
    some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame frame.native)
  unmapped : location ∉ mapping
  entries : ∀ {id sourceLocation}, Dynamic.Environment.LooksUp environment id sourceLocation →
    Entry (attachment := attachment) compiled index context location id sourceLocation mapping world heap store

def Physical.weaken_view {before after : BodyRelation} {index : Index compiled before}
    {scope canonical mapping world heap store environment}
    (physical : Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment)
    (weaken : ∀ source view body, before source view body → after source view body) :
    Physical (attachment := attachment) compiled (index.weaken_view weaken) context scope canonical mapping world heap store environment := by
  cases index <;>
    exact { physical with frame := physical.frame.weaken_view weaken
                          entries := fun found => (physical.entries found).weaken_view weaken }


abbrev Physical.native {scope canonical mapping world heap store environment}
    (physical : Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment) : NativeFrame :=
  physical.frame.native

abbrev Physical.ghost {scope canonical mapping world heap store environment}
    (physical : Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment) : GhostFrame :=
  physical.frame.ghost


def Physical.transport {scope canonical mapping world heap store environment nextMap nextWorld after finalStore}
    (physical : Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      mapping world heap store nextMap nextWorld after finalStore)
    (preserved : AdministrativePreserved mapping store nextMap finalStore) :
    Physical (attachment := attachment) compiled index context scope canonical nextMap nextWorld after finalStore environment :=
  { frame := physical.frame
    declarations := physical.declarations
    ownership := physical.ownership
    sourceDeclarations := physical.sourceDeclarations
    location := physical.location
    reference := physical.reference
    read := ((preserved physical.location physical.unmapped
      (List.getElem?_eq_some_iff.mp physical.read).1).2).trans physical.read
    unmapped := (preserved physical.location physical.unmapped
      (List.getElem?_eq_some_iff.mp physical.read).1).1
    entries := fun lookup => (physical.entries lookup).transport effect }

@[simp] theorem Physical.transport_location {scope canonical mapping world heap store environment nextMap nextWorld after finalStore}
    (physical : Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      mapping world heap store nextMap nextWorld after finalStore)
    (preserved : AdministrativePreserved mapping store nextMap finalStore) :
    (physical.transport effect preserved).location = physical.location := rfl

@[simp] theorem Physical.transport_native {scope canonical mapping world heap store environment nextMap nextWorld after finalStore}
    (physical : Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      mapping world heap store nextMap nextWorld after finalStore)
    (preserved : AdministrativePreserved mapping store nextMap finalStore) :
    (physical.transport effect preserved).native = physical.native := rfl

theorem Physical.generalized {scope canonical mapping world heap store environment id location cell function}
    (physical : Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment)
    (lookup : Dynamic.Environment.LooksUp environment id location)
    (read : Dynamic.Heap.Reads heap location cell) (descriptor : cell.generalized = some function) :
    ∃ binding lexical, ∃ located : Located (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        function binding lexical location mapping world heap store,
      binding.caller = index.owner ∧ binding.binder.id = id ∧ ContextExtension lexical index.active ∧
      GeneralizedLocalAcceptedLocatedRows.Located.FramesWith attachment located physical.location ∧ Dynamic.RuntimeContextFields function.definitionContext context ∧
      context.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements := by
  cases physical.entries lookup with
  | ordinary previous empty =>
    have same := read.functional previous
    rw [same, empty] at descriptor
    cases descriptor
  | generalized located owner binder lexical frames fields requirements =>
    have same := read.functional located.sourceRead
    have functionEq := Option.some.inj
      (descriptor.symm.trans ((congrArg Dynamic.Cell.generalized same).trans located.descriptor))
    cases functionEq
    exact ⟨_, _, located, owner, binder, lexical, frames, fields, requirements⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysicalExtension
/-! Real monomorphic parameters initialize the actual body physical scope. Each
subsequent lexical declaration extends only the original binder context and
retains the same selected frame and caller key. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalLocatedRows GeneralizedLocalBundleContexts CallableIndexedHistory

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {index : ActualBodyInvocation.Index compiled bodyRelation} {context nextContext : SourceSemantics.Context}

theorem Entry.recontext {frameLocation id location mapping world heap store binder}
    {sourceOwner : Resolved.DeclarationId}
    (entry : Entry (attachment := attachment) compiled index context frameLocation id location mapping world heap store)
    (extended : BinderExtends sourceOwner context binder nextContext)
    (different : binder.id ≠ id) :
    Entry (attachment := attachment) compiled index nextContext frameLocation id location mapping world heap store := by
  cases entry with
  | ordinary read descriptor => exact .ordinary read descriptor
  | generalized located owner binderId lexical frames fields requirements =>
    refine .generalized located owner binderId lexical frames
      (fields.trans (.ofBinderExtends extended)) ?_
    cases extended
    exact .tail (by simpa only [located.attachment.binder, binderId] using different) requirements

private theorem monomorphic_entries {frameLocation mapping world heap store environment scope}
    (agrees : Dynamic.EnvironmentAgrees heap scope environment)
    (typed : Dynamic.HeapWellTyped context heap)
    (monomorphic : ∀ id scheme, (id, scheme) ∈ scope → scheme.quantified = []) :
    ∀ {id location}, Dynamic.Environment.LooksUp environment id location →
      Entry (attachment := attachment) compiled index context frameLocation id location mapping world heap store := by
  induction agrees with
  | nil => intro id location lookup; cases lookup
  | @cons scope environment headId scheme headLocation cell read _ storage tail ih =>
    intro id location lookup
    cases lookup with
    | head =>
      cases storage with
      | ordinary _ empty => exact .ordinary read empty
      | generalized descriptor _ binderScheme =>
        have principal := ((typed cell read.member).generalized_inv descriptor).2.code.polymorphic
        exact False.elim (principal (binderScheme ▸ monomorphic headId scheme (by simp)))
    | tail _ next =>
      exact ih (fun child childScheme member => monomorphic child childScheme (List.mem_cons_of_mem _ member)) next

def Physical.of_monomorphic {scope canonical mapping world heap store environment}
    (frame : ActualBodyInvocation.Frame index)
    (declarations : CompatibleExpressionReads.ScopeDeclarations index.source scope context)
    (ownership : LocalIdentityOwnership index.source)
    (sourceDeclarations : CellAwareScopeDeclarations.Full index.source scope context)
    (location : Core.Location)
    (reference : canonical[scope.length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame frame.native))
    (unmapped : location ∉ mapping)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (typed : Dynamic.HeapWellTyped context heap)
    (monomorphic : ∀ id scheme, (id, scheme) ∈ context.locals → scheme.quantified = []) :
    Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment :=
  ⟨frame, declarations, ownership, sourceDeclarations, location, reference, read, unmapped,
    monomorphic_entries locals typed monomorphic⟩

def Physical.cons {scope canonical mapping world heap store environment binder payload sourceLocation}
    (physical : Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment)
    (extended : BinderExtends index.source.owner context binder nextContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations index.source
      ((binder.id, payload) :: scope) nextContext)
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
    (reference : Core.Value)
    (head : Entry (attachment := attachment) compiled index nextContext physical.location binder.id sourceLocation mapping world heap store) :
    Physical (attachment := attachment) compiled index nextContext ((binder.id, payload) :: scope) (reference :: canonical)
      mapping world heap store ((binder.id, sourceLocation) :: environment) := by
  refine ⟨physical.frame, declarations, physical.ownership,
    CellAwareScopeDeclarations.scope_bind payload member physical.sourceDeclarations extended, physical.location, ?_, physical.read, physical.unmapped, ?_⟩
  · change (reference :: canonical)[scope.length + 1 + 1 + compiled.indexed.base.globals.length]? = _
    rw [show scope.length + 1 + 1 + compiled.indexed.base.globals.length =
      (scope.length + 1 + compiled.indexed.base.globals.length) + 1 by omega]
    exact physical.reference
  · intro id location lookup
    cases lookup with
    | head => exact head
    | tail different previous => exact (physical.entries previous).recontext extended different

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryPrefix
/-! An ordinary initialized declaration allocates from the successful child's
actual post. Every earlier generalized descriptor, frame and lexical authority
survives, and the real continuation receives the newly bound Source cell. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (initializedRequest sequence)
open GeneralizedLocalDescriptorHeap

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index whole bodyRelation}

theorem complete_at_source {allocationSource : TypedSource} {scope : SourceCoreLocalCell.Scope} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {lowered : SourceCoreBasic.LoweredExpr} {administrative actualContext : Core.Context}
    (mono : binder.scheme.quantified = [])
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
    (extended : BinderExtends index.source.owner context binder nextContext)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
      (initializedRequest allocationSource scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest allocationSource scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap}
    {startStore store : Store} {sourceValue : Dynamic.Value} {value : Value} {location : Dynamic.Location}
    (initialized : Evaluates actual startStore (lowered.expression.rename embedding) (.inRight .word value) store)
    (represented : model.Represents mapping world binder.scheme.body sourceValue value lowered.type)
    (valueTyped : Dynamic.ValueHasType context before sourceValue binder.scheme.body)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context scope canonical mapping world before store environment)
    (ready : producer.Ready initial physical.location physical.native)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (output : Ty) (body : Expr) :
    ∃ marker,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit value]
      let nextWorld := world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual startStore
        ((sequence output lowered.expression annotation.expression body).rename embedding)
        (nextRef :: value :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) ∧
      (∀ {size result finalStore}, EvaluationSize size actual startStore
        ((sequence output lowered.expression annotation.expression body).rename embedding) result finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: value :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) result finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, lowered.type) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) embedding).lift
        (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        index.owner index.active nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, lowered.type) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index nextContext ((binder.id, lowered.type) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  obtain ⟨marker, _captures, _markerTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, _nextReference, _nextRead, preserved, reached, related⟩ :=
    CellAwareOrdinaryAllocation.allocate_initialized_at_source (ordinary_cells (ordinary := model) (instances := GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      producer rfl registered mono extended ordinary allocation annotation same represented environments heaps locals agrees actualTyped
      physical.reference physical.read allocated initial ready
  have metadata := Dynamic.HeapMetadataExtend.of_allocation allocated
  have effect := CellAwareScopeAuthority.Effect.append
    (instances := GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment) store
    [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
      SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit value] metadata
    (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
    (show WorldExtends world (world ++ [whole.indexed.ancestry.layout.frame.type,
      allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩)
  have nextAuthority := CellAwareScopeAuthority.At.cons (id := binder.id)
    (.ordinary allocated.reads_new rfl) (authority.transport effect)
  have nextAdmitted := CallableIndexedOwnedAdmittedLexicalAllocation.after_allocation bridge initial reached admitted
    extended (.some valueTyped) allocated preserved
  have head : CellAwareInvocationPhysical.Entry (attachment := attachment) whole index nextContext physical.location binder.id location
      (mapping ++ [store.length + 2])
      (world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]) after
      (store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit value]) :=
    .ordinary allocated.reads_new rfl
  let nextPhysical := (physical.transport effect preserved).cons extended
    (CompatibleMatchArmScopes.scope_bind lowered.type physical.declarations member extended) member
    (.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)) head
  exact ⟨marker, CellAwareOrdinaryContinuation.agreement initialized allocationEval,
    fun completed => CellAwareOrdinaryContinuation.smaller initialized allocationEval completed,
    nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, preserved, effect,
    nextAuthority, reached, related, nextAdmitted, nextPhysical, rfl, rfl⟩

theorem complete {scope : SourceCoreLocalCell.Scope} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {lowered : SourceCoreBasic.LoweredExpr} {administrative actualContext : Core.Context}
    (mono : binder.scheme.quantified = [])
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
    (extended : BinderExtends index.source.owner context binder nextContext)
    (ordinary : index.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
      (initializedRequest index.source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest index.source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap}
    {startStore store : Store} {sourceValue : Dynamic.Value} {value : Value} {location : Dynamic.Location}
    (initialized : Evaluates actual startStore (lowered.expression.rename embedding) (.inRight .word value) store)
    (represented : model.Represents mapping world binder.scheme.body sourceValue value lowered.type)
    (valueTyped : Dynamic.ValueHasType context before sourceValue binder.scheme.body)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context scope canonical mapping world before store environment)
    (ready : producer.Ready initial physical.location physical.native)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after)
    (output : Ty) (body : Expr) :
    ∃ marker,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit value]
      let nextWorld := world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual startStore
        ((sequence output lowered.expression annotation.expression body).rename embedding)
        (nextRef :: value :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) ∧
      (∀ {size result finalStore}, EvaluationSize size actual startStore
        ((sequence output lowered.expression annotation.expression body).rename embedding) result finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: value :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) embedding).lift) result finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, lowered.type) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) embedding).lift
        (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        index.owner index.active nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, lowered.type) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index nextContext ((binder.id, lowered.type) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  apply complete_at_source (allocationSource := index.source) bridge <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOrdinaryPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentPrefix
/-! The actual absent-cell allocation extends the mixed lexical state without
evaluating an initializer. Its continuation preserves all prior generalized
descriptors, source bindings and the original physical frame. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalControl (absentRequest)
open GeneralizedLocalDescriptorHeap

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index whole bodyRelation}

theorem complete_at_source {allocationSource : TypedSource} {scope : SourceCoreLocalCell.Scope} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {payload : Ty} {administrative actualContext : Core.Context}
    (mono : binder.scheme.quantified = [])
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
    (extended : BinderExtends index.source.owner context binder nextContext)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
      (absentRequest allocationSource scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (absentRequest allocationSource scope binder payload))
    (same : annotation.original = allocation.expression)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap}
    {store : Store} {location : Dynamic.Location}
    (projection : projects binder.scheme.body payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context scope canonical mapping world before store environment)
    (ready : producer.Ready initial physical.location physical.native)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after)
    (body : Expr) :
    ∃ marker,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inLeft payload .unit]
      let nextWorld := world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      ContinuationAgreement actual store
        ((Expr.letE annotation.expression body).rename embedding)
        (nextRef :: actual) nextStore
        (body.rename embedding.lift) ∧
      (∀ {size result finalStore}, EvaluationSize size actual store
        ((Expr.letE annotation.expression body).rename embedding) result finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: actual) nextStore
          (body.rename embedding.lift) result finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree embedding.lift
        (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType payload :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        index.owner index.active nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index nextContext ((binder.id, payload) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  obtain ⟨marker, _captures, _markerTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, _nextReference, _nextRead, preserved, reached, related⟩ :=
    CellAwareAbsentAllocation.allocate_absent_at_source (ordinary_cells (ordinary := model) (instances := GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      producer rfl registered mono extended ordinary projection allocation annotation same environments heaps locals agrees actualTyped
      physical.reference physical.read allocated initial ready
  have metadata := Dynamic.HeapMetadataExtend.of_allocation allocated
  have effect := CellAwareScopeAuthority.Effect.append
    (instances := GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment) store
    [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
      SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inLeft payload .unit] metadata
    (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
    (show WorldExtends world (world ++ [whole.indexed.ancestry.layout.frame.type,
      allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩)
  have nextAuthority := CellAwareScopeAuthority.At.cons (id := binder.id)
    (.ordinary allocated.reads_new rfl) (authority.transport effect)
  have nextAdmitted := CallableIndexedOwnedAdmittedLexicalAllocation.after_allocation bridge initial reached admitted
    extended (.none _) allocated preserved
  have head : CellAwareInvocationPhysical.Entry (attachment := attachment) whole index nextContext physical.location binder.id location
      (mapping ++ [store.length + 2])
      (world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType payload]) after
      (store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inLeft payload .unit]) :=
    .ordinary allocated.reads_new rfl
  let nextPhysical := (physical.transport effect preserved).cons extended
    (CompatibleMatchArmScopes.scope_bind payload physical.declarations member extended) member
    (.cellRef (OptionalCell.cellType payload) (store.length + 2)) head
  exact ⟨marker, (by simpa only [Expr.rename] using ContinuationAgreement.letE (body := body.rename embedding.lift) allocationEval),
    (fun completed => by simpa only [Expr.rename] using completed.let_body allocationEval),
    nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, preserved, effect,
    nextAuthority, reached, related, nextAdmitted, nextPhysical, rfl, rfl⟩

theorem complete {scope : SourceCoreLocalCell.Scope} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {payload : Ty} {administrative actualContext : Core.Context}
    (mono : binder.scheme.quantified = [])
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
    (extended : BinderExtends index.source.owner context binder nextContext)
    (ordinary : index.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
      (absentRequest index.source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (absentRequest index.source scope binder payload))
    (same : annotation.original = allocation.expression)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap}
    {store : Store} {location : Dynamic.Location}
    (projection : projects binder.scheme.body payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context scope canonical mapping world before store environment)
    (ready : producer.Ready initial physical.location physical.native)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after)
    (body : Expr) :
    ∃ marker,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame physical.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inLeft payload .unit]
      let nextWorld := world ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      ContinuationAgreement actual store
        ((Expr.letE annotation.expression body).rename embedding)
        (nextRef :: actual) nextStore
        (body.rename embedding.lift) ∧
      (∀ {size result finalStore}, EvaluationSize size actual store
        ((Expr.letE annotation.expression body).rename embedding) result finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: actual) nextStore
          (body.rename embedding.lift) result finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree embedding.lift
        (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType payload :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        index.owner index.active nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index nextContext ((binder.id, payload) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  apply complete_at_source (allocationSource := index.source) bridge <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAbsentPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedPrefix
/-! An actual initialized statement constructs its ordered bundle from the
compiler receipt, then retains its same frame and lexical scope through the
marked allocation and continuation in either invocation kind. The declaration
first copies its scope; the principal captures the copies and the continuation
keeps the original cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (initializedRequest)
open CellAwareGeneralizedSnapshotCode (snapshotInner snapshotSequence)
open SourceSemantics.CaptureBinders (copiedBinder?)
open GeneralizedLocalDescriptorHeap GeneralizedLocalLocatedRows
open ActualBodyInvocation

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView}

include bridge in
/-- The caller witness reaches every administrative extension through the
owned pool and its returned wrapper. -/
theorem transitions : ProtectedStateTransition.AdministrativeTransitions protocol := by
  intro _ initial _ _ _ _ maps worlds frame metadata
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedFunctionState.protocol headers keys)
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys) (bridge.pool initial)
    maps worlds frame metadata
  obtain ⟨returned, _, callerRelated⟩ := bridge.restore initial reached maps worlds frame metadata related
  exact ⟨returned, callerRelated⟩

set_option maxHeartbeats 2000000 in
theorem complete_at_source {allocationSource : TypedSource} {scope : SourceCoreLocalCell.Scope} {sourceContext nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {initializer : ExpressionId} {childFuel : Nat} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {administrative actualContext : Core.Context}
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    (entry : index.ResidualEntry) (unique : NodeOccurrencesUnique index.source)
    {statementId : StatementId}
    (site : index.Site (.statement statementId)) {statement : StatementNode} {stored : Ty}
    (readStatement : index.policy.readStatement index.compilerSource statementId = .ok (statement, stored))
    (form : statement.form = .letDecl binder (some initializer))
    {payload : Ty}
    (projected : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
    (generated : index.policy.lowerExpression childFuel index.compilerSource scope initializer reasonAt = .ok lowered)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
      (index.initializerInputs childFuel scope initializer reasonAt))
    (declaration : (SourceCoreDataPlaces.declaredBinders index.source).filter
      (fun actual => decide (actual.id = binder.id)) = [binder])
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends index.source.owner sourceContext binder nextContext)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
      (initializedRequest allocationSource scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest allocationSource scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    {captured : Expr}
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))))
      allocationSource scope (fun index => index) (snapshotInner lowered.type lowered.expression annotation.expression) =
        .ok captured)
    (copiedIds : ∀ id, (copiedBinder? allocationSource id).isSome = (copiedBinder? index.source id).isSome)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)))
    (bindings : ProtectedStateTransition.Bindings protocol)
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap} {store : Store}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before sourceContext.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge sourceContext initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
      index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := GeneralizedLocalCapturedScopes.Attachment) whole index sourceContext scope canonical mapping world before store environment)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {copies : Dynamic.Environment} {snapshotHeap : Dynamic.Heap}
    {function : Dynamic.GeneralizedClosure} {location : Dynamic.Location}
    (snapshot : Dynamic.EnvironmentCopies index.source environment before copies snapshotHeap)
    (captures : Dynamic.GeneralizedClosureCaptures sourceContext index.source copies binder initializer function)
    (functionTyped : Dynamic.GeneralizedClosureWellTyped sourceContext snapshotHeap function)
    (allocated : Dynamic.Heap.AllocatesGeneralized snapshotHeap function location after)
    (output : Ty) (body : Expr) :
    ∃ values marker, ∃ (copiedStore : Store) (copiedMap : LocationMap) (copiedWorld : StoreTyping),
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := copiedStore ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame
        physical.native, SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := copiedWorld ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := copiedMap ++ [copiedStore.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)
      ContinuationAgreement actual store ((snapshotSequence output captured body).rename embedding)
        (nextRef :: actual) nextStore (body.rename embedding.lift) ∧
      (∀ {size value finalStore}, EvaluationSize size actual store
          ((snapshotSequence output captured body).rename embedding) value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: actual) nextStore
          (body.rename embedding.lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, lowered.type) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree embedding.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType lowered.type :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
        index.owner index.active nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, lowered.type) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareInvocationPhysical.Physical (attachment := GeneralizedLocalCapturedScopes.Attachment) whole index nextContext ((binder.id, lowered.type) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  obtain ⟨binding, located, metadata, initializerEq, originalSource, _payload, ⟨receipt⟩⟩ :=
    index.initialized_accepted_receipt artifact checked site.reached readStatement form
      polymorphic projected generated
  obtain ⟨_representation, _program, _catalog, _native, _plan, inputOwner, globals,
      administrativePrefix, inputInitializer, inputScope, _reason⟩ :=
    index.initializerInputs_fields childFuel scope initializer reasonAt
  have found : index.compilerSource.lookupStatement? statementId = some statement :=
    (index.reached_view.statement (.inr site.reached)).symm.trans
      (index.statement_read_reached site.reached readStatement)
  obtain ⟨_node, parameters, resultType, statements, _found, _form, _rawType, _type, _requirements, _coercions, rfl⟩ :=
    captures.canonical
  let function := Dynamic.GeneralizedClosure.ofDirectLambda sourceContext index.source copies binder
    initializer parameters resultType statements
  obtain ⟨retainedOrigin, nativeEq, _ghostEq, _metadataEq, attached, ⟨attachment⟩⟩ :=
    entry.descriptor_at_statement physical.frame site found form located metadata initializerEq originalSource
      captures unique
  generalize inputsEq : index.initializerInputs childFuel scope initializer reasonAt = originalInputs at receipt issuer inputOwner globals administrativePrefix inputInitializer inputScope
  let inputs : GeneralizedLocalInstanceCompilation.Inputs :=
    { originalInputs with
      scope := scope
      initializer := initializer
      current := { originalInputs.current with
        owner := index.owner
        globals := whole.indexed.base.globals
        administrativePrefix := 1 } }
  have sameInputs : inputs = originalInputs := by
    dsimp only [inputs]
    rw [← inputScope, ← inputInitializer, ← inputOwner, ← globals, ← administrativePrefix]
  rw [← sameInputs] at receipt issuer
  let origin : GeneralizedLocalDescriptorOrigin.Origin whole.indexed function binding index.active :=
    { retainedOrigin with
      native := physical.native
      carried := by simpa only [nativeEq] using retainedOrigin.carried }
  let current : CallableIndexedLambdaValues.Captures whole.indexed mapping world inputs.scope environment actual :=
    ⟨administrative, canonical, actualContext, embedding, environments,
      agrees, TypedLexicalWhile.environment_respects environments.runtime_hasTypes actualTyped agrees,
      actualTyped⟩
  obtain ⟨bindingOwner, bindingId⟩ := SourceCoreLocalPolymorphism.Catalog.binding_identity located
  have originalExtended : BinderExtends function.source.owner function.definitionContext function.binder nextContext := extended
  have originalOrdinary : allocationSource.inputs.any (fun input => decide (input.id = function.binder.id)) = false := ordinary
  let originalAllocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts inputs.current.owner index.active
      (initializedRequest allocationSource inputs.scope function.binder lowered.type) := allocation
  let originalAnnotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt inputs.current.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest allocationSource inputs.scope function.binder lowered.type) := annotation
  have sameOriginal : originalAnnotation.original = originalAllocation.expression := by
    simpa only [originalAnnotation, originalAllocation] using same
  have originalCopied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt inputs.current.owner index.active
          (fun error => .sourceAllocation (reprStr error)))))
      allocationSource inputs.scope (fun index => index)
      (snapshotInner lowered.type lowered.expression originalAnnotation.expression) = .ok captured := copied
  have originalCopiedIds :
      ∀ id, (copiedBinder? allocationSource id).isSome = (copiedBinder? function.source id).isSome := copiedIds
  have originalDeclarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext := physical.declarations
  have originalLocals : Dynamic.EnvironmentAgrees before function.definitionContext.locals environment := locals
  have originalSnapshot : Dynamic.EnvironmentCopies function.source environment before function.captured snapshotHeap :=
    snapshot
  have originalTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ current.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions := nativeTyped
  have originalReference : current.canonical[inputs.scope.length + 1 + whole.indexed.base.globals.length]? =
      some (.cellRef whole.indexed.ancestry.layout.frame.type physical.location) := physical.reference
  have referenceIndex : SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope =
      inputs.scope.length + 1 + whole.indexed.base.globals.length := rfl
  let originalInitial : protocol.State ⟨inputs.scope, mapping, world, before, store, current.canonical⟩ := initial
  have originalReady : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location origin.native := ready
  obtain ⟨values, marker, copiedStore, copiedMap, copiedWorld, agreement, smaller, nextEnvironments, nextHeaps,
      nextLocals, nextAgrees, nextTyped, _nextReference, _nextRead, preserved, maps, worlds, ⟨suffix, storeEq⟩,
      locatedRows, transition⟩ :=
    GeneralizedLocalAcceptedSnapshotPrefix.complete_with_at_source receipt GeneralizedLocalCapturedScopes.Attachment
      attached bindingOwner.symm initializerEq.symm origin attachment originalExtended originalOrdinary
      originalAllocation originalAnnotation sameOriginal originalCopied originalCopiedIds producer
      (transitions bridge) bindings registered current originalDeclarations physical.ownership issuer originalTyped
      heaps originalLocals originalReference referenceIndex physical.read originalSnapshot allocated originalInitial
      originalReady output body
  obtain ⟨locatedRows, frames⟩ := locatedRows
  have heapMetadata := snapshot.metadata_extends.trans (Dynamic.HeapMetadataExtend.of_generalized_allocation allocated)
  have effect : CellAwareScopeAuthority.Effect
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
      mapping world before store (copiedMap ++ [copiedStore.length + 2])
      (copiedWorld ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]) after
      (copiedStore ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker,
        .inRight .unit (SourceCoreLocalPolymorphism.ProductBundle.value values)]) := by
    rw [storeEq]
    exact CellAwareScopeAuthority.Effect.append
      (instances := GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
      store suffix heapMetadata maps worlds
  have lexical : GeneralizedLocalBundleContexts.ContextExtension index.active index.active :=
    ⟨fun _ member => member, fun _ _ => rfl⟩
  have nextAuthority := CellAwareScopeAuthority.At.cons
    (.generalized bindingOwner bindingId lexical ⟨locatedRows⟩) (authority.transport effect)
  obtain ⟨reached, related⟩ := transition
  have nextAdmitted : Admission bridge nextContext reached :=
    ⟨(Dynamic.HeapWellTyped.iff_of_binderExtends originalExtended).mp
        ((admitted.heap.copy snapshot).allocateGeneralized functionTyped allocated),
      CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
        (bridge.pool initial) (bridge.pool reached) admitted.rows preserved⟩
  have fields : Dynamic.RuntimeContextFields function.definitionContext nextContext :=
    Dynamic.RuntimeContextFields.ofBinderExtends extended
  have requirements : nextContext.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements := extended.local_scheme_requirements_self
  have head : CellAwareInvocationPhysical.Entry (attachment := GeneralizedLocalCapturedScopes.Attachment)
      whole index nextContext physical.location binder.id location (copiedMap ++ [copiedStore.length + 2]) _ after _ :=
    .generalized locatedRows bindingOwner bindingId lexical frames fields requirements
  let nextPhysical := (physical.transport effect preserved).cons extended
    (CellAwareNativeBodyCollectors.scope_generalized lowered.type physical.declarations declaration polymorphic extended)
    ((List.mem_filter.mp (declaration ▸ List.mem_singleton_self binder)).1)
    (.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)) head
  exact ⟨values, marker, copiedStore, copiedMap, copiedWorld, agreement, smaller, nextEnvironments, nextHeaps,
    nextLocals, nextAgrees, nextTyped, preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical,
    rfl, rfl⟩

theorem complete {scope : SourceCoreLocalCell.Scope} {sourceContext nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {initializer : ExpressionId} {childFuel : Nat} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {administrative actualContext : Core.Context}
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    (entry : index.ResidualEntry) (unique : NodeOccurrencesUnique index.source)
    {statementId : StatementId}
    (site : index.Site (.statement statementId)) {statement : StatementNode} {stored : Ty}
    (readStatement : index.policy.readStatement index.compilerSource statementId = .ok (statement, stored))
    (form : statement.form = .letDecl binder (some initializer))
    {payload : Ty}
    (projected : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
    (generated : index.policy.lowerExpression childFuel index.compilerSource scope initializer reasonAt = .ok lowered)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
      (index.initializerInputs childFuel scope initializer reasonAt))
    (declaration : (SourceCoreDataPlaces.declaredBinders index.source).filter
      (fun actual => decide (actual.id = binder.id)) = [binder])
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends index.source.owner sourceContext binder nextContext)
    (ordinary : index.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts index.owner index.active
      (initializedRequest index.source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest index.source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    {captured : Expr}
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))))
      index.source scope (fun index => index) (snapshotInner lowered.type lowered.expression annotation.expression) =
        .ok captured)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
      whole.indexed.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)))
    (bindings : ProtectedStateTransition.Bindings protocol)
    (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {embedding : Renaming} {before after : Dynamic.Heap} {store : Store}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before sourceContext.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge sourceContext initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
      index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := GeneralizedLocalCapturedScopes.Attachment) whole index sourceContext scope canonical mapping world before store environment)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {copies : Dynamic.Environment} {snapshotHeap : Dynamic.Heap}
    {function : Dynamic.GeneralizedClosure} {location : Dynamic.Location}
    (snapshot : Dynamic.EnvironmentCopies index.source environment before copies snapshotHeap)
    (captures : Dynamic.GeneralizedClosureCaptures sourceContext index.source copies binder initializer function)
    (functionTyped : Dynamic.GeneralizedClosureWellTyped sourceContext snapshotHeap function)
    (allocated : Dynamic.Heap.AllocatesGeneralized snapshotHeap function location after)
    (output : Ty) (body : Expr) :
    ∃ values marker, ∃ (copiedStore : Store) (copiedMap : LocationMap) (copiedWorld : StoreTyping),
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := copiedStore ++ [SourceCoreCallableIndexedFrames.encode whole.indexed.ancestry.layout.frame
        physical.native, SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := copiedWorld ++ [whole.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := copiedMap ++ [copiedStore.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)
      ContinuationAgreement actual store ((snapshotSequence output captured body).rename embedding)
        (nextRef :: actual) nextStore (body.rename embedding.lift) ∧
      (∀ {size value finalStore}, EvaluationSize size actual store
          ((snapshotSequence output captured body).rename embedding) value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: actual) nextStore
          (body.rename embedding.lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, lowered.type) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) whole.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree embedding.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType lowered.type :: actualContext) whole.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
        mapping world before store nextMap nextWorld after nextStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed GeneralizedLocalCapturedScopes.Attachment)
        index.owner index.active nextMap nextWorld after nextStore ((binder.id, location) :: environment) ∧
      ∃ reached : protocol.State ⟨(binder.id, lowered.type) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
        protocol.Relates initial reached ∧ Admission bridge nextContext reached ∧
      ∃ nextPhysical : CellAwareInvocationPhysical.Physical (attachment := GeneralizedLocalCapturedScopes.Attachment) whole index nextContext ((binder.id, lowered.type) :: scope)
          (nextRef :: canonical) nextMap nextWorld after nextStore ((binder.id, location) :: environment),
        nextPhysical.location = physical.location ∧ nextPhysical.native = physical.native := by
  exact complete_at_source bridge artifact checked entry unique site readStatement form projected generated issuer
    declaration polymorphic extended ordinary nativeTyped allocation annotation same copied (fun _ => rfl) producer
    bindings registered environments heaps locals agrees actualTyped initial admitted authority physical ready snapshot
    captures functionTyped allocated output body

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedPrefix
end
