import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedFunctionFinishBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCallerProtocol
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCanonicalEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning

/-! A named body starts at its complete actual parameter entry. The real
hook authenticates its full named Source seed, and the parameter catalog
provides the original frame reference, parameter bundle and global slots.
Those observations travel beside the same actual pool in the nested protocol.
Strict flow children feed the original typed finish and low invocation once.
No static field supplies a completed execution or body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds (BodyState Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled program →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}

/-- Actual static compilation evidence for this Header. Registry-specific
reached diagnostics are supplied to the flow producer separately. -/
structure Profile (runtime : Bool) (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (administrative : Core.Context) where private mk ::
  initialValid : RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved header.context header.function.evidence
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
    header.output header.reasonAt true header.escaped = .ok flow
  emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped
  tree : GenericImperativeMatch.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame header.globals
    header.onError (.initial compiled.compatible.checked) header.function.source (expressionSyntax header)
    (certificates header)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) header.context
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (.statements true header.function.body) header.function.resultType header.output flow

/-- Accepted body and flow equations derive the actual finish equation. The
retained Tree is static compiler evidence and supplies no execution law. -/
def Profile.of_extracted {runtime : Bool}
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} {administrative : Core.Context} {flow : Expr}
    (initialValid : RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved header.context header.function.evidence)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeMatch.Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame header.globals
      header.onError (.initial compiled.compatible.checked) header.function.source (expressionSyntax header)
      (certificates header)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow) :
    Profile (certificates := certificates) (expressionSyntax := expressionSyntax) runtime header administrative := by
  have emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped := by
    unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
    rw [generated] at accepted
    exact Except.ok.inj accepted.symm
  exact ⟨initialValid, accepted, projection, flow, generated, emitted, tree⟩

def body_protocol (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) :=
  CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header

def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) :=
  CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner header)

/-- Visited contexts retain the real ledger and independent Source validity. -/
def Validity (runtime : Bool) (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (context : SourceSemantics.Context) : Prop :=
  RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence ∧
    Dynamic.SourceRuntimeValid program context header.function.source

section Flows
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (runtime : Bool)
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {administrative : Core.Context}
  (profile : Profile (certificates := certificates)
    (expressionSyntax := expressionSyntax) runtime header administrative)

/-- This is a flow obligation at the exact retained profile, before finish. -/
def FlowPreserves (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (body_protocol (headers := headers) owner header) (readiness (bridge (headers := headers) owner header))
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts header.function.source (expressionSyntax header))
    functions program header.function.evidence (Validity runtime header)
    (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := header.globals)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    true header.function.body header.function.resultType header.output profile.flow

def FlowReflects (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (body_protocol (headers := headers) owner header) (readiness (bridge (headers := headers) owner header))
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts header.function.source (expressionSyntax header))
    functions program header.function.evidence (Validity runtime header)
    (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := header.globals)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    true header.function.body header.function.resultType header.output profile.flow

end Flows

section Entries
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (runtime : Bool)
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  (captureZero : owner.key.capturePrefix = 0)
  (globals : header.globals = compiled.indexed.base.globals.length)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value}
  (beforeTyped : Dynamic.HeapWellTyped header.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (wellFormed : ProgramWellFormed program)

/-- Profiles are requested at an authentic complete parameter entry. -/
def ProfilesFor :=
  ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost},
    BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore
      mapping world administrative actualContext actual ξ frameLocation current ghost →
    Profile (certificates := certificates)
      (expressionSyntax := expressionSyntax) runtime header administrative

private theorem body_facts {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType)
    (source : SourceReceipt program header.function header.context environment heap) :
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
    (expressionSyntax := expressionSyntax) functions owner runtime (header := header))
  (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
    header.context (.statements true header.function.body) header.function.resultType)

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree in
/-- The real parameter allocation supplies Source admission. Its original
canonical globals wrap the same reached pool before the strict flow child. -/
theorem source_continuation (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) runtime header administrative),
      FlowPreserves (registry := registry) (faults := faults) (headers := headers) functions owner runtime profile child)) :
    CallableIndexedOwnedInvocationBounds.SourceContinuation
      (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header) budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation
    physical selected history emitted entry _agreement reached _related _allowed child strict outcome after trace
  let profile := profiles entry
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
      (functions := functions) (program := program) (tree := profile.tree)
      (projection := profile.projection) (unique := header.unique)
      (body_protocol (headers := headers) owner header) (readiness (bridge (headers := headers) owner header))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts header.function.source (expressionSyntax header))
      profile.emitted (Validity runtime header) child (below child strict administrative profile)
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
        (expressionSyntax := expressionSyntax) runtime header administrative),
      FlowReflects (registry := registry) (faults := faults) (headers := headers) functions owner runtime profile child)) :
    CallableIndexedOwnedInvocationBounds.NativeContinuation
      (functions := functions) (registry := registry) (faults := faults)
      (header := header) (arguments := arguments) owner caller
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header) budget := by
  intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical selected history emitted _prefix _prefixWithin _restored entry reached _related _allowed
    child strict bodyValue bodyStore completed
  let profile := profiles entry
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
      (functions := functions) (program := program) (tree := profile.tree)
      (projection := profile.projection) (unique := header.unique)
      (body_protocol (headers := headers) owner header) (readiness (bridge (headers := headers) owner header))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (ProtectedStateImperativeTypedSourceSites.Facts header.function.source (expressionSyntax header))
      profile.emitted (Validity runtime header) budget child (Nat.le_of_lt strict)
      (fun grade smaller => below grade smaller administrative profile)
      ⟨profile.initialValid, source.runtime⟩ (body_facts syntaxTree source)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped
      reference entry.state.read unmapped initial gate admitted source wellFormed completed
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, returned.val, related⟩

end Entries
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations
