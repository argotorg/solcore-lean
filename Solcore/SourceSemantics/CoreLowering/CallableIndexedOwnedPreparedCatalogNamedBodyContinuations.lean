import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedProfiles

/-! At an actual complete named parameter entry, the finite compiler factory
supplies its literal coupled extraction. The strict F child is indexed by that
positive packet, so its structural eliminator and authentic token issuance
remain available. Typed finish consumes the same actual nested state and
returns the original reached pool. No static input contains a body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedBodyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds (BodyState Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

/-- The exact coupled collector packet is the only static profile in this interface. -/
abbrev Profile (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (administrative : Core.Context) :=
  CallableIndexedOwnedPreparedCatalogNamedProfiles.Profile
    (certificates := certificates) (expressionSyntax := expressionSyntax) header administrative

def body_protocol (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) :=
  CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.body_protocol (headers := headers) owner header

def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) :=
  CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.bridge (headers := headers) owner header

def Validity (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) : Prop :=
  CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.Validity true header context

section Flows
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {administrative : Core.Context}
  (profile : Profile (certificates := certificates) (expressionSyntax := expressionSyntax) header administrative)

def FlowPreserves (size : Nat) : Prop :=
  CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.FlowPreserves
    (headers := headers) (registry := registry) (faults := faults) functions owner true profile.nested size

def FlowReflects (size : Nat) : Prop :=
  CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.FlowReflects
    (headers := headers) (registry := registry) (faults := faults) functions owner true profile.nested size
end Flows

section Entries
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (captureZero : owner.key.capturePrefix = 0)
  (globals : header.globals = compiled.indexed.base.globals.length)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value}
  (beforeTyped : Dynamic.HeapWellTyped header.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

/-- Profiles are requested at an authentic complete parameter entry. -/
def ProfilesFor :=
  ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost},
    BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore
      mapping world administrative actualContext actual ξ frameLocation current ghost →
    Profile (certificates := certificates)
      (expressionSyntax := expressionSyntax) header administrative

private theorem body_facts {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType)
    (source : SourceReceipt (Program.ofChecked compiled.sourceProgram) header.function header.context environment heap) :
    ProtectedStateImperativeTypedSourceSites.Facts header.function.source (expressionSyntax header)
      header.context true header.function.body header.function.resultType := by
  obtain ⟨final, facts, typed, _⟩ := source.bodyTyped
  exact ⟨syntaxTree, { returnType := header.function.resultType }, final, facts, typed⟩

include stable in
private theorem parameter_rows {origin : Word} {index : Int} {metadata : MetadataState}
    {frameLocation : Location} {final : ProtectedStateTransition.Index}
    (physical : frameLocation = owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named origin) (some metadata))
    (reached : State headers keys final)
    (parameters : AdministrativePreserved mapping
      (store.set frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index)))
      final.mapping final.store) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows reached := by
  have actualFrame := Eq.mp (congrArg (fun location => AdministrativePreserved mapping
    (store.set location (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (.state index)))
    final.mapping final.store) physical) parameters
  exact CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (install caller owner.position (.stable history)) reached
    (CallableIndexedOwnedAdmittedBodyEntries.stable_rows_install caller stable owner.position history) actualFrame

variable (profiles : ProfilesFor (registry := registry) (certificates := certificates)
    (expressionSyntax := expressionSyntax) functions owner (header := header))
  (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
    header.context (.statements true header.function.body) header.function.resultType)

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree in
/-- The real parameter allocation supplies Source admission. Its original
canonical globals wrap the same reached pool before the strict flow child. -/
theorem source_continuation (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowPreserves (registry := registry) (faults := faults) (headers := headers) functions owner profile child)) :
    CallableIndexedOwnedInvocationBounds.SourceContinuation
      (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header) budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation
    physical selected history emitted entry _agreement reached _related _allowed child strict outcome after trace
  let selectedProfile := profiles entry
  let profile := selectedProfile.nested
  have source := SourceReceipt.of_named wellFormed header.frame header.extended entry.allocation beforeTyped argumentsTyped
  let initial : (body_protocol (headers := headers) owner header).State
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ :=
    CallableIndexedOwnedNamedCanonicalEntries.wrap functions owner header entry reached captureZero globals
      (CallableIndexedOwnedNamedCanonicalEntries.authorized functions owner header
        physical selected history emitted entry)
  have admitted : Admission (bridge (headers := headers) owner header) header.context initial :=
    ⟨source.heapTyped, parameter_rows owner caller stable physical history reached entry.frame⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation (.state index) :=
    ⟨owner.position, .named origin, some metadata, physical.symm, history⟩
  have reference : entry.canonical[
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) := by
    simpa only [List.length_map, List.length_reverse] using entry.reference
  have unmapped := Eq.mp (congrArg (fun location => location ∉ entry.mapping) entry.catalog_frame)
    entry.catalog.authority.unmapped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, _exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.preserves_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := Program.ofChecked compiled.sourceProgram) (tree := profile.tree)
      (projection := profile.projection) (unique := header.unique)
      (body_protocol (headers := headers) owner header) (readiness (bridge (headers := headers) owner header))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts header.function.source (expressionSyntax header))
      profile.emitted (Validity header) child (below child strict administrative selectedProfile)
      ⟨profile.initialValid, source.runtime⟩ (body_facts syntaxTree source)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped
      reference entry.state.read unmapped initial gate admitted source wellFormed trace
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, returned.val, related⟩

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree in
/-- The independent measured native body consumes strict flow grades only.
The returned Source grade and exact actual parameter pool remain unchanged. -/
theorem native_continuation (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowReflects (registry := registry) (faults := faults) (headers := headers) functions owner profile child)) :
    CallableIndexedOwnedInvocationBounds.NativeContinuation
      (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header) budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical selected history emitted _prefix _prefixWithin _restored entry reached _related _allowed
    child strict bodyValue bodyStore completed
  let selectedProfile := profiles entry
  let profile := selectedProfile.nested
  have source := SourceReceipt.of_named wellFormed header.frame header.extended entry.allocation beforeTyped argumentsTyped
  let initial : (body_protocol (headers := headers) owner header).State
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ :=
    CallableIndexedOwnedNamedCanonicalEntries.wrap functions owner header entry reached captureZero globals
      (CallableIndexedOwnedNamedCanonicalEntries.authorized functions owner header
        physical selected history emitted entry)
  have admitted : Admission (bridge (headers := headers) owner header) header.context initial :=
    ⟨source.heapTyped, parameter_rows owner caller stable physical history reached entry.frame⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation (.state index) :=
    ⟨owner.position, .named origin, some metadata, physical.symm, history⟩
  have reference : entry.canonical[
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) := by
    simpa only [List.length_map, List.length_reverse] using entry.reference
  have unmapped := Eq.mp (congrArg (fun location => location ∉ entry.mapping) entry.catalog_frame)
    entry.catalog.authority.unmapped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, _exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.reflects_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := Program.ofChecked compiled.sourceProgram) (tree := profile.tree)
      (projection := profile.projection) (unique := header.unique)
      (body_protocol (headers := headers) owner header) (readiness (bridge (headers := headers) owner header))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts header.function.source (expressionSyntax header))
      profile.emitted (Validity header) budget child (Nat.le_of_lt strict)
      (fun grade smaller => below grade smaller administrative selectedProfile)
      ⟨profile.initialValid, source.runtime⟩ (body_facts syntaxTree source)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped
      reference entry.state.read unmapped initial gate admitted source wellFormed completed
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, returned.val, related⟩

end Entries
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedBodyContinuations
