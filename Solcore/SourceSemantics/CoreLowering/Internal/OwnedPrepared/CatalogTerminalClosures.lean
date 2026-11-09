import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ProfileExtraction
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies

/-!
# Prepared callables: catalog and terminal closures

Catalog profiles and named flow steps, and factories of terminal closures.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedProfiles
/-! A named profile retains the literal prepared row and the coupled native
collector output at its actual parameter entry. The authentic diagnostic
issuance is aligned pointwise with that same collected plan. These are static
compiler fields; no expression, flow or body execution law is stored here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedProfiles
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicSpecializationMeaning RecursiveNamedPreparedHeaderPolicies
open CallableIndexedOwnedContextualLambdaSourceDiagnostics (IssuedSource)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

/-- The positive compiler packet keeps its actual Prepared/HeaderAt and
collection. Token equalities concern the genuine receiving issuance. -/
structure Profile (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (administrative : Core.Context) where
  row : SourceSpecialization.SpecializedFunction
  prepared : Prepared compiled row
  instantiation : DeclarationInstantiation
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header
  first : Nat
  operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source
  assignmentsPrepared : SourceCoreAssignmentFaultSites.prepare header.function.source first = .ok prepared.compilation.own.assignments
  extraction : CallableIndexedOwnedPreparedDirectNamedProfileExtraction.Receipt
    (certificates := certificates) (expressionSyntax := expressionSyntax) (administrative := administrative)
    prepared operandsTyped assignmentsPrepared
  issued : IssuedSource compiled header.owner header.function.source
  assignments : issued.assignments = prepared.compilation.own.assignments
  operand : issued.invalidOperand = Prepared.invalidOperand prepared
  unary : issued.invalidUnary = Prepared.invalidUnary prepared
  projection : issued.invalidProjection = Prepared.invalidProjection prepared
  missing : issued.missingDefault = Prepared.missingDefault prepared

namespace Profile
variable {administrative : Core.Context}
  (profile : Profile (certificates := certificates) (expressionSyntax := expressionSyntax) header administrative)

/-- Forward projection keeps the exact generated flow and compiler Tree. -/
def nested : CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.Profile
    (certificates := certificates) (expressionSyntax := expressionSyntax) true header administrative :=
  CallableIndexedOwnedPreparedNestedNamedProfileView.of_direct
    (CallableIndexedOwnedPreparedDirectNamedProfileExtraction.Receipt.profile
      profile.prepared profile.aligned profile.operandsTyped profile.assignmentsPrepared profile.extraction)

/-- Replacing the assignment field by its proved-equal literal compiler table
makes the factory index definitionally exact. All issuer provenance is kept. -/
def receiving : IssuedSource compiled header.owner header.function.source :=
  { profile.issued with
    assignments := profile.prepared.compilation.own.assignments
    assignmentsPrepared := profile.assignments ▸ profile.issued.assignmentsPrepared }

/-- The same genuine extraction factory is used at the aligned table. -/
def factory : AssignmentDiagnosticOrigins.Factory true .reachable header.function.source profile.receiving.invalidOperand :=
  CallableIndexedOwnedPreparedDirectNamedProfileExtraction.assignment_factory
    profile.prepared profile.operandsTyped profile.assignmentsPrepared

/-- Pointwise diagnostic alignment keeps the same collected eliminator. -/
theorem prepared_eliminator : GenericImperativeMatch.Structural.Eliminates
    (layouts := header.layouts) (owner := header.owner) (active := header.active)
    (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
    (values := .initial compiled.compatible.checked) (source := header.function.source)
    (expressionSyntax := expressionSyntax header) (certificates := certificates header)
    (definitions := compiled.indexed.layouts.definitions)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (fun head => GenericForHeader.Structural.PreparedAssignment profile.factory profile.receiving.invalidProjection profile.receiving.missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary true header.function.source profile.receiving.invalidUnary head)
    (fun tree => GenericImperativeMatch.Structural.PreparedHeader (factory := profile.factory)
      (invalidProjection := profile.receiving.invalidProjection) (missingDefault := profile.receiving.missingDefault)
      (invalidUnary := profile.receiving.invalidUnary) tree)
    (fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context)
    header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (.statements true header.function.body) header.function.resultType header.output profile.nested.flow := by
  have projection : profile.receiving.invalidProjection = Prepared.invalidProjection profile.prepared :=
    profile.projection
  have missing : profile.receiving.missingDefault = Prepared.missingDefault profile.prepared :=
    profile.missing
  have unary : profile.receiving.invalidUnary = Prepared.invalidUnary profile.prepared := rfl
  rw [projection, missing, unary]
  exact profile.extraction.collected.eliminate
    (header.valid.ledger.trans (by simpa only [Prepared.ambientMatch, Prepared.baseMatch] using profile.aligned.solved))

end Profile
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedProfiles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedBodyContinuations
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds
/-! A global value keeps its actual selected Header, SourceFrame, dictionary
and complete native capture. Strict nested flow at that Header finishes the real body;
the original parameter prefix and caller restoration use the same reached pool.
Source admission is derived from genuine packed Source typing and the retained
instantiation. No whole-body execution law or live closure-slot read is supplied.
The parent argument/callee fold and public gate decisions remain separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open RecursiveNamedCatalogInvocationBounds (Below)
open CallableIndexedOwnedPreparedCatalogNamedBodyContinuations (Profile ProfilesFor FlowPreserves FlowReflects)

section Invocation
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (captureZero : owner.key.capturePrefix = 0)
  (globals : header.globals = compiled.indexed.base.globals.length)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (beforeTyped : Dynamic.HeapWellTyped header.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (profiles : ProfilesFor (registry := registry) (certificates := certificates)
    (expressionSyntax := expressionSyntax) functions owner (header := header))
  (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
    header.context (.statements true header.function.body) header.function.resultType)
  (sameLayouts : header.layouts = compiled.indexed.layouts)
  (member : header ∈ headers)
  (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)

/-- All fields describe the original restored caller and ordered records. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld header.function.resultType header.output faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ProtectedStateTransition.Transition (protocol headers keys) caller
      ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree sameLayouts member represented heaps in
/-- Actual source invocation consumes its strict body flow through the original
parameter continuation. No whole-body law or diagnostic receipt is an input. -/
theorem invocation_preserves_bounded (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowPreserves (registry := registry) (faults := faults) (headers := headers) functions owner profile child))
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) size header.sourceBody header.function.evidence before arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
        (header.code.rename capture.embedding.lift) value finalStore ∧
      ResultAt (functions := functions) (caller := caller) (header := header)
        (registry := registry) (faults := faults) outcome after value finalStore := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, returned⟩ :=
    CallableIndexedOwnedNamedValueInvocationBounds.invocation_preserves_bounded_at
      (functions := functions) (registry := registry) (faults := faults) owner sameLayouts
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
      (CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      budget caller member capture represented heaps
      (CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.source_continuation
        (functions := functions) (owner := owner) (caller := caller)
        (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
        (captureZero := captureZero) (globals := globals) (wellFormed := wellFormed) (profiles := profiles) (syntaxTree := syntaxTree) budget below)
      trace within
  exact ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame, metadata, returned⟩

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree sameLayouts member represented heaps in
/-- The measured native prefix remains original. Its strict body flow returns
an independent Source grade and the same restored caller pool. -/
theorem invocation_reflects_bounded (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowReflects (registry := registry) (faults := faults) (headers := headers) functions owner profile child))
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize header.sourceBody header.function.evidence before arguments outcome after ∧
      ResultAt (functions := functions) (caller := caller) (header := header)
        (registry := registry) (faults := faults) outcome after value finalStore := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, returned⟩ :=
    CallableIndexedOwnedNamedValueInvocationBounds.invocation_reflects_bounded_at
      (functions := functions) (registry := registry) (faults := faults) owner sameLayouts
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
      (CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      budget caller member capture represented heaps
      (CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.native_continuation
        (functions := functions) (owner := owner) (caller := caller)
        (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
        (captureZero := captureZero) (globals := globals) (wellFormed := wellFormed) (profiles := profiles) (syntaxTree := syntaxTree) budget below)
      completed within
  exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame, metadata, returned⟩


include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree sameLayouts member represented heaps in
/-- The actual global dictionary is preserved when selecting its strict body.
Missing declaration and arity alternatives are ruled out only by the retained
SourceFrame, actual owner uniqueness and physical represented argument count. -/
theorem global_preserves_bounded {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {source : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowPreserves (registry := registry) (faults := faults) (headers := headers) functions owner profile child))
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size context callerEvidence source.evidence
      before (.global source) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
        (header.code.rename capture.embedding.lift) value finalStore ∧
      ResultAt (functions := functions) (caller := caller) (header := header)
        (registry := registry) (faults := faults) outcome after value finalStore := by
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have namedCall : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size context callerEvidence
      header.function.evidence before (.global ⟨source.instantiation, header.function.evidence⟩)
      arguments outcome after := by
    have dictionary := sourceAt.dictionary
    cases source with
    | mk instantiation evidence =>
      change header.function.evidence = evidence at dictionary
      simpa only [← dictionary] using called
  obtain ⟨child, trace, smaller⟩ := RecursiveNamedCallBounds.source_call_body owners sourceAt.frame arity namedCall
  exact invocation_preserves_bounded functions owner captureZero globals caller beforeTyped argumentsTyped stable wellFormed
    profiles syntaxTree sameLayouts member capture represented heaps budget below trace
    (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree sameLayouts member represented heaps in
/-- Native invocation returns an independent Source grade for the same retained
global and dictionary, after restoring the real caller from the reached pool. -/
theorem global_reflects_bounded {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {source : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowReflects (registry := registry) (faults := faults) (headers := headers) functions owner profile child))
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context callerEvidence source.evidence before
        (.global source) arguments outcome after ∧
      ResultAt (functions := functions) (caller := caller) (header := header)
        (registry := registry) (faults := faults) outcome after value finalStore := by
  obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
    invocation_reflects_bounded functions owner captureZero globals caller beforeTyped argumentsTyped stable wellFormed
      profiles syntaxTree sameLayouts member capture represented heaps budget below completed within
  have called := RecursiveNamedCallBounds.call_of_body (context := context)
    (caller := callerEvidence) sourceAt.frame trace
  refine ⟨SourceExecutionSize.stepSize [sourceSize], outcome, after, ?_, result⟩
  have dictionary := sourceAt.dictionary
  cases source with
  | mk instantiation evidence =>
    change header.function.evidence = evidence at dictionary
    simpa only [dictionary] using called


/-- This is the exact complete carrier in the authentic General named row. -/
def carrier (identity descriptor : Word) : Value :=
  .pair (.pair (.inRight .unit (.word identity))
    (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor)

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree sameLayouts member represented heaps in
/-- The actual named carrier applies its retained body once, after the strict
Source body child has returned through the original caller restoration. -/
theorem application_preserves_at {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {source : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (identity descriptor : Word) (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowPreserves (registry := registry) (faults := faults) (headers := headers) functions owner profile child))
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size context callerEvidence source.evidence
      before (.global source) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [carrier (header := header) (owner := owner) capture identity descriptor, DataPatternValues.packValues payloads] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (functions := functions) (caller := caller) (header := header)
        (registry := registry) (faults := faults) outcome after value finalStore := by
  obtain ⟨value, finalStore, invoked, result⟩ :=
    global_preserves_bounded functions owner captureZero globals caller beforeTyped argumentsTyped stable wellFormed
      profiles syntaxTree sameLayouts member capture represented heaps sourceAt owners budget below called within
  exact ⟨value, finalStore, .apply (.second (.first (.var rfl))) (.var rfl) invoked, result⟩

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree sameLayouts member represented heaps in
/-- The real measured apply rule yields a strict native body grade; the
Source grade and the same global dictionary are returned independently. -/
theorem application_reflects_at {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {source : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (identity descriptor : Word) (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowReflects (registry := registry) (faults := faults) (headers := headers) functions owner profile child))
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [carrier (header := header) (owner := owner) capture identity descriptor, DataPatternValues.packValues payloads] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context callerEvidence source.evidence before
        (.global source) arguments outcome after ∧
      ResultAt (functions := functions) (caller := caller) (header := header)
        (registry := registry) (faults := faults) outcome after value finalStore := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact global_reflects_bounded functions owner captureZero globals caller beforeTyped argumentsTyped stable wellFormed
    profiles syntaxTree sameLayouts member capture represented heaps sourceAt budget below applied
    (Nat.le_trans (Nat.le_of_lt smaller) within)

end Invocation

section SourceAdmission
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}

/-- Real Source attribution gives the input row at the exact retained body,
including its residual-variable scope and genuine ordered dictionary. -/
theorem source_certificate (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ facts, Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram) source.instantiation header.sourceBody
      header.types header.context facts := by
  obtain ⟨types, lexical, facts, certified⟩ := sourceAt.frame.instantiated.certificate wellFormed
  have extended := header.extended
  rw [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] at extended
  have contextEq := Dynamic.MonoBindersExtend.functional certified.typing.inputs_extend extended
  have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq certified.typing.inputs_extend).symm.trans
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended)
  exact ⟨facts, typesEq ▸ contextEq ▸ certified⟩

/-- The actual Source callable and packed argument typings authenticate the
callee heap and raw input types. Physical arity is independent of packed typing. -/
theorem arguments_at_global (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {context : SourceSemantics.Context} {bodySource : TypedSource} {before : Dynamic.Heap}
    {arguments : List Dynamic.Value} {packed : Dynamic.Value} {parameter result : TypeSystem.Ty}
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context bodySource)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (callableTyped : Dynamic.ValueHasType context before (.global source) (.function parameter result))
    (packing : Dynamic.ValuesPack arguments packed)
    (packedTyped : Dynamic.ValueHasType context before packed parameter)
    (arity : header.function.parameters.length = arguments.length) :
    Dynamic.HeapWellTyped header.function.context before ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  rcases callableTyped.global_inv with ordinary | staged
  · rcases ordinary with ⟨typeEq, _valid, _evidence⟩
    obtain ⟨facts, certified⟩ := source_certificate sourceAt wellFormed
    have parameterEq := (TypeSystem.Ty.function.inj (typeEq.trans certified.callable_type)).1
    rw [parameterEq] at packedTyped
    have signatures := certified.signatures_eq.trans runtime.signatures.symm
    have bodyHeap := heapTyped.transportClosed signatures runtime.closed certified.type_parameters_empty
      runtime.variables_closed certified.residual_type_variables_open
    have bodyPacked := packedTyped.transportClosed signatures runtime.closed certified.type_parameters_empty
      runtime.variables_closed certified.residual_type_variables_open
    have length : arguments.length = header.types.length := arity.symm.trans
      ((congrArg List.length sourceAt.frame.parameters).trans certified.typing.inputs_extend.length_eq)
    have bodyArguments := packing.unpackTypes bodyPacked length
    exact ⟨sourceAt.frame.context.symm ▸ bodyHeap, sourceAt.frame.context.symm ▸ bodyArguments⟩
  · rcases staged with ⟨inner, impossible, innerTyped⟩
    cases impossible

end SourceAdmission
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactories
/-! The accepted same-Code body and its actual static Tree construct the used
terminal child receipt. Only the real terminal Source form, reader policy and
selected staged scope remain static inputs. No execution law is stored here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedLambdaStaticBodySupport
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal Receipt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

private theorem lowered_eq {left right : SourceCoreBasic.LoweredExpr}
    (sameType : left.type = right.type) (sameExpression : left.expression = right.expression) :
    left = right := by
  cases left
  cases right
  cases sameType
  cases sameExpression
  rfl

private theorem finish_injective {type : Ty} {left right : Expr} {fellThrough escaped : Word}
    (same : CompatibleStatements.finish type left fellThrough escaped =
      CompatibleStatements.finish type right fellThrough escaped) : left = right := by
  unfold CompatibleStatements.finish LocalControl.finish LocalLoop.toControl LanguageResult.bind at same
  exact (Expr.caseE.inj (Expr.caseE.inj same).1).1

private theorem return_value_injective {type : Ty} {left right : Expr}
    (same : LocalLoop.returnValue type left = LocalLoop.returnValue type right) : left = right := by
  unfold LocalLoop.returnValue LanguageResult.bind at same
  exact (Expr.caseE.inj same).1

section StaticTrees
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}

private theorem lexical_terminal_child
    (terminal : Terminal source expression statements)
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      certificates context scope true statements expected type flow) :
    ∃ lowered : SourceCoreBasic.LoweredExpr, lowered.type = type ∧
      flow = LocalLoop.returnValue type lowered.expression ∧
      certificates context scope expression lowered := by
  cases terminal with
  | returning rest found form =>
    cases tree <;> try simp_all
    all_goals exact ⟨_, rfl, rfl, by assumption⟩
  | tail found form =>
    cases tree <;> try simp_all
    all_goals exact ⟨_, rfl, rfl, by assumption⟩

private theorem imperative_terminal_child
    (terminal : Terminal source expression statements)
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
      expressionSyntax certificates definitions administrative context scope
      (.statements true statements) expected type flow) :
    ∃ lowered : SourceCoreBasic.LoweredExpr, lowered.type = type ∧
      flow = LocalLoop.returnValue type lowered.expression ∧
      certificates context scope expression lowered := by
  cases tree
  case body syntaxTree body => exact lexical_terminal_child terminal body
  all_goals cases terminal <;> simp_all
end StaticTrees

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}

/-- Accepted lowering and the actual compiler Tree supply both the receipt and
its used child certificate at this Code's real body parameter context. -/
theorem of_actual_body_exact
    (body : BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) registry semanticFaults)
    (expression : ExpressionId)
    (terminal : Terminal code.view expression function.body)
    (readPolicy : body.policy.readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages,
      packet.certificate = certificates body.readFuel code.view body.toContext.context ∧
      packet.child = child ∧ packet.expression = expression ∧
      certificates body.readFuel code.view body.toContext.context
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        expression packet.receipt.child := by
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    readPolicy terminal body.accepted
  obtain ⟨lowered, sameType, flow, certified⟩ := imperative_terminal_child terminal body.actualTree
  have sameFlow : body.flow = LocalLoop.returnValue code.receipt.resultCore receipt.child.expression :=
    finish_injective (body.emitted.symm.trans receipt.emitted)
  have sameExpression : lowered.expression = receipt.child.expression :=
    return_value_injective (flow.symm.trans sameFlow)
  have sameLowered : lowered = receipt.child :=
    lowered_eq (sameType.trans receipt.sameType.symm) sameExpression
  have used : certificates body.readFuel code.view body.toContext.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression receipt.child := sameLowered ▸ certified
  exact ⟨{
    policy := body.policy
    fuel := code.fuel
    expression := expression
    reasonAt := code.reasonAt
    fellThrough := code.compilation.internalReason
    escaped := code.compilation.internalReason
    receipt := receipt
    certificate := certificates body.readFuel code.view body.toContext.context
    certifies := fun lowered generated =>
      (Except.ok.inj (receipt.generated.symm.trans generated)) ▸ used
    child := child
    selected := selected }, rfl, rfl, rfl, used⟩

/-- The original receipt-only interface is preserved. -/
theorem of_actual_body
    (body : BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) registry semanticFaults)
    (expression : ExpressionId)
    (terminal : Terminal code.view expression function.body)
    (readPolicy : body.policy.readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages) := by
  obtain ⟨packet, sameCertificate, sameChild, sameExpression, certified⟩ :=
    of_actual_body_exact body expression terminal readPolicy child selected
  exact ⟨packet⟩

variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Supported terminal syntax is read at the actual ordinary or principal
compiler view retained by the contextual association. -/
def TerminalShapeFor
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId) : Prop :=
  match association with
  | .ordinary _ _ code _ _ _ _ _ _ _ _ => Terminal code.view expression function.body
  | .principal _ _ code _ _ _ _ _ _ _ _ => Terminal code.view expression function.body

/-- The compiler's actual statement reader is retained independently of the
chosen expression grammar and its certificates. -/
def ReadPolicyFor
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) : Prop :=
  match association with
  | .ordinary _ _ _ _ support _ _ _ _ _ _ => support.body.policy.readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked
  | .principal _ _ _ _ support _ _ _ _ _ _ => support.body.policy.readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked

/-- The generated packet uses precisely the actual BodyWith child certificate
at its compiler view and reached parameter context. -/
def HasBodyCertificate
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) : Prop :=
  match association, packet with
  | .ordinary _ _ code _ support _ _ _ _ _ _, packet =>
      packet.certificate = support.certificates support.body.readFuel code.view support.body.toContext.context
  | .principal _ _ code _ support _ _ _ _ _ _, packet =>
      packet.certificate = support.certificates support.body.readFuel code.view support.body.toContext.context

private abbrev body_scope {closure : Dynamic.Closure}
    {localScope : SourceCoreLocalCell.Scope} {admin : Core.Context}
    (code : Code compiled.indexed closure localScope admin) : SourceCoreLocalCell.Scope :=
  code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope

/-- The packet retains the actual selected expression and its original static
child certificate, in addition to the literal BodyWith certificate family. -/
def HasBodyChild
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) : Prop :=
  HasBodyCertificate association packet ∧
    match association, packet with
    | .ordinary _ _ code _ support _ _ _ _ _ _, packet =>
        packet.expression = expression ∧
        support.certificates support.body.readFuel code.view support.body.toContext.context
          (body_scope code)
          expression packet.receipt.child
    | .principal _ _ code _ support _ _ _ _ _ _, packet =>
        packet.expression = expression ∧
        support.certificates support.body.readFuel code.view support.body.toContext.context
          (body_scope code)
          expression packet.receipt.child

/-- The exact certificate conclusion exposes the static child used by numeric
induction, without quantifying over arbitrary terminal packets. -/
theorem terminal_for_exact
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (expression : ExpressionId) (terminal : TerminalShapeFor association expression)
    (readPolicy : ReadPolicyFor association)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages,
      HasBodyChild association expression packet := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    obtain ⟨packet, sameCertificate, sameChild, sameExpression, certified⟩ :=
      of_actual_body_exact support.body expression terminal readPolicy child selected
    exact ⟨packet, sameCertificate, sameExpression, certified⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    obtain ⟨packet, sameCertificate, sameChild, sameExpression, certified⟩ :=
      of_actual_body_exact support.body expression terminal readPolicy child selected
    exact ⟨packet, sameCertificate, sameExpression, certified⟩

/-- Each concrete contextual association constructs TerminalFor internally
from its accepted BodyWith, without a prebuilt terminal packet. -/
theorem terminal_for
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (expression : ExpressionId) (terminal : TerminalShapeFor association expression)
    (readPolicy : ReadPolicyFor association)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    exact of_actual_body support.body expression terminal readPolicy child selected
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact of_actual_body support.body expression terminal readPolicy child selected

/-- The genuine prepared stage registry selects the same actual closure
from its descriptor and original Source receipt; no arbitrary registry totality
is inferred. This specializes the terminal factory to that selected scope. -/
theorem at_prepared_registry
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (expression : ExpressionId) (terminal : TerminalShapeFor association expression)
    (readPolicy : ReadPolicyFor association) :
    Nonempty (CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table)) := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    obtain ⟨sidecar, issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    exact of_actual_body support.body expression terminal readPolicy _ selected
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    obtain ⟨sidecar, issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    exact of_actual_body support.body expression terminal readPolicy _ selected

/-- The real prepared registry supplies a packet whose certificate is the
same actual BodyWith child. The selected scope is constructed internally. -/
theorem at_prepared_registry_exact
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (expression : ExpressionId) (terminal : TerminalShapeFor association expression)
    (readPolicy : ReadPolicyFor association) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table), HasBodyChild association expression packet := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    obtain ⟨sidecar, issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    obtain ⟨packet, sameCertificate, sameChild, sameExpression, certified⟩ :=
      of_actual_body_exact support.body expression terminal readPolicy _ selected
    exact ⟨packet, sameCertificate, sameExpression, certified⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    obtain ⟨sidecar, issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    obtain ⟨packet, sameCertificate, sameChild, sameExpression, certified⟩ :=
      of_actual_body_exact support.body expression terminal readPolicy _ selected
    exact ⟨packet, sameCertificate, sameExpression, certified⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactories
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds
/-! The accepted same-Code compiler factory exposes its exact used body child.
A singleton certificate keeps that scope, expression and lowered child through
the original terminal application producers. The numeric child hypotheses and
every actual Source-selected scope remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedTerminalClosureFactories
universe u

private abbrev preparedStages (compiled : SourceCoreUnifiedCompilation.Compiled) :=
  RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
    compiled.indexed.ancestry.graph.inputs.callable.table

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- A static certificate for one physical compiler child. -/
def Point (scope : SourceCoreLocalCell.Scope) (expression : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current id code => current = scope ∧ id = expression ∧ code = lowered

private abbrev bodyScope {closure : Dynamic.Closure}
    {localScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed closure localScope administrative) : SourceCoreLocalCell.Scope :=
  code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope

/-- The accepted lowering action determines the packet's exact child. All
compiler fields and the selected staged scope stay at that same packet. -/
def narrow {closure : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed closure localScope administrative}
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages :=
  { packet with
    certificate := Point (bodyScope code) packet.expression packet.receipt.child
    certifies := by
      intro lowered generated
      have same : packet.receipt.child = lowered :=
        Except.ok.inj (packet.receipt.generated.symm.trans generated)
      exact ⟨rfl, rfl, same.symm⟩ }

/-- Both contextual association forms retain their real Code and receipt. -/
def narrowFor
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (packet : TerminalFor association stages) :
    TerminalFor association stages :=
  match association, packet with
  | .ordinary _ _ _ _ _ _ _ _ _ _ _, packet => narrow packet
  | .principal _ _ _ _ _ _ _ _ _ _ _, packet => narrow packet

/-- Reflection is requested only at a used child certified by the actual
BodyWith family, with an independent strict native budget. -/
def ReflectsUsedChildBelow
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat) : Prop :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
    ∀ (lowered : SourceCoreBasic.LoweredExpr),
    support.certificates support.body.readFuel code.view support.body.toContext.context
      (bodyScope code) expression lowered →
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (Point (bodyScope code) expression lowered) faults budget
  | .principal _ _ code _ support _ _ _ _ _ _ =>
    ∀ (lowered : SourceCoreBasic.LoweredExpr),
    support.certificates support.body.readFuel code.view support.body.toContext.context
      (bodyScope code) expression lowered →
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (Point (bodyScope code) expression lowered) faults budget

/-- Preservation uses the same exact static child and the Source trace budget.
It still covers every scope genuinely selected by that Source application. -/
def PreservesUsedChildBelow
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat) : Prop :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
    ∀ (lowered : SourceCoreBasic.LoweredExpr),
    support.certificates support.body.readFuel code.view support.body.toContext.context
      (bodyScope code) expression lowered →
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (Point (bodyScope code) expression lowered) faults budget
  | .principal _ _ code _ support _ _ _ _ _ _ =>
    ∀ (lowered : SourceCoreBasic.LoweredExpr),
    support.certificates support.body.readFuel code.view support.body.toContext.context
      (bodyScope code) expression lowered →
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (Point (bodyScope code) expression lowered) faults budget

private theorem reflects_at_packet
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId) (packet : TerminalFor association stages)
    (actualChild : HasBodyChild association expression packet)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat)
    (children : ReflectsUsedChildBelow (registry := registry) (faults := faults) (stages := stages)
      association expression functions budget) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.ReflectsBelowFor
      (registry := registry) (faults := faults) association (narrowFor association packet) functions budget := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    change _ ∧ packet.expression = expression ∧
      support.certificates support.body.readFuel code.view support.body.toContext.context
        (bodyScope code) expression packet.receipt.child at actualChild
    obtain ⟨_sameFamily, sameExpression, certified⟩ := actualChild
    dsimp [ReflectsUsedChildBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.ReflectsBelowFor, narrowFor, narrow]
    have samePoint := congrArg (fun id => Point (bodyScope code) id packet.receipt.child) sameExpression
    exact samePoint.symm ▸ (children packet.receipt.child certified packet.child packet.selected)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    change _ ∧ packet.expression = expression ∧
      support.certificates support.body.readFuel code.view support.body.toContext.context
        (bodyScope code) expression packet.receipt.child at actualChild
    obtain ⟨_sameFamily, sameExpression, certified⟩ := actualChild
    dsimp [ReflectsUsedChildBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.ReflectsBelowFor, narrowFor, narrow]
    have samePoint := congrArg (fun id => Point (bodyScope code) id packet.receipt.child) sameExpression
    exact samePoint.symm ▸ (children packet.receipt.child certified packet.child packet.selected)

private theorem preserves_at_packet
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId) (packet : TerminalFor association stages)
    (actualChild : HasBodyChild association expression packet)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat)
    (children : PreservesUsedChildBelow (registry := registry) (faults := faults) (stages := stages)
      association expression functions budget) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.PreservesBelowFor
      (registry := registry) (faults := faults) association (narrowFor association packet) functions budget := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    change _ ∧ packet.expression = expression ∧
      support.certificates support.body.readFuel code.view support.body.toContext.context
        (bodyScope code) expression packet.receipt.child at actualChild
    obtain ⟨_sameFamily, sameExpression, certified⟩ := actualChild
    dsimp [PreservesUsedChildBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.PreservesBelowFor, narrowFor, narrow]
    have samePoint := congrArg (fun id => Point (bodyScope code) id packet.receipt.child) sameExpression
    exact samePoint.symm ▸ (children packet.receipt.child certified)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    change _ ∧ packet.expression = expression ∧
      support.certificates support.body.readFuel code.view support.body.toContext.context
        (bodyScope code) expression packet.receipt.child at actualChild
    obtain ⟨_sameFamily, sameExpression, certified⟩ := actualChild
    dsimp [PreservesUsedChildBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.PreservesBelowFor, narrowFor, narrow]
    have samePoint := congrArg (fun id => Point (bodyScope code) id packet.receipt.child) sameExpression
    exact samePoint.symm ▸ (children packet.receipt.child certified)

section ContextualApplication
variable (association : Association headers keys bodyRegistry semanticFaults mapping world function native
    bindings parameterCore resultCore)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {before : Dynamic.Heap} {store : Store} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  {sources : List Dynamic.Value} {values : List Value}
  (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before sources)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings sources values)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    mapping world before store)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)

include raw represented heaps stable runtime in
/-- The actual used child certificate supplies the singleton numeric hypothesis
before the original application reflection port runs once. -/
theorem application_reflects
    (expression : ExpressionId) (shape : TerminalShapeFor association expression)
    (reader : ReadPolicyFor association) (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (budget : Nat) (children : ReflectsUsedChildBelow (registry := registry) (faults := faults)
      (stages := preparedStages compiled) association expression functions budget)
    {invocation : Staging.Recursive.Scope} {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) (preparedStages compiled) sourceSize
        invocation context before (.closure function) sources outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
            (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
          context function.resultType outcome returned := by
  obtain ⟨packet, actualChild⟩ := at_prepared_registry_exact association expression shape reader
  exact CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.application_reflects
    association (narrowFor association packet) functions caller raw represented heaps stable runtime valid budget
    (reflects_at_packet association expression packet actualChild functions budget children) completed within

include raw represented heaps stable runtime in
/-- The original Source-selected application consumes its exact static child
through the singleton hypothesis and restores the full reached caller state. -/
theorem application_preserves
    (expression : ExpressionId) (shape : TerminalShapeFor association expression)
    (reader : ReadPolicyFor association) (budget : Nat)
    (children : PreservesUsedChildBelow (registry := registry) (faults := faults)
      (stages := preparedStages compiled) association expression functions budget)
    {invocation : Staging.Recursive.Scope} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) (preparedStages compiled) size
      invocation context before (.closure function) sources outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [native, DataPatternValues.packValues values] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
            (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
          context function.resultType outcome returned := by
  obtain ⟨packet, actualChild⟩ := at_prepared_registry_exact association expression shape reader
  exact CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.application_preserves
    association (narrowFor association packet) functions caller raw represented heaps stable runtime budget
    (preserves_at_packet association expression packet actualChild functions budget children) trace within
end ContextualApplication

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureCanonicalChildFactories
/-! The original Source compiler Tree retains the exact terminal child beside
its actual compiler-view certificate. Statement metadata transports only the
terminal form. Accepted finish equality identifies the same lowered child;
no equality of whole Sources, expression types or coercions is inferred. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureCanonicalChildFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedLambdaStaticBodySupport
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedTerminalClosureFactories

private theorem lowered_eq {left right : SourceCoreBasic.LoweredExpr}
    (sameType : left.type = right.type) (sameExpression : left.expression = right.expression) :
    left = right := by
  cases left
  cases right
  cases sameType
  cases sameExpression
  rfl

private theorem finish_injective {type : Ty} {left right : Expr} {leftFellThrough leftEscaped rightFellThrough rightEscaped : Word}
    (same : CompatibleStatements.finish type left leftFellThrough leftEscaped =
      CompatibleStatements.finish type right rightFellThrough rightEscaped) : left = right := by
  unfold CompatibleStatements.finish LocalControl.finish LocalLoop.toControl LanguageResult.bind at same
  exact (Expr.caseE.inj (Expr.caseE.inj same).1).1

private theorem return_value_injective {type : Ty} {left right : Expr}
    (same : LocalLoop.returnValue type left = LocalLoop.returnValue type right) : left = right := by
  unfold LocalLoop.returnValue LanguageResult.bind at same
  exact (Expr.caseE.inj same).1

section StaticTrees
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}

private theorem lexical_terminal_child
    (terminal : Terminal source expression statements)
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      certificates context scope true statements expected type flow) :
    ∃ lowered : SourceCoreBasic.LoweredExpr, lowered.type = type ∧
      flow = LocalLoop.returnValue type lowered.expression ∧
      certificates context scope expression lowered := by
  cases terminal with
  | returning rest found form =>
    cases tree <;> try simp_all
    all_goals exact ⟨_, rfl, rfl, by assumption⟩
  | tail found form =>
    cases tree <;> try simp_all
    all_goals exact ⟨_, rfl, rfl, by assumption⟩

private theorem imperative_terminal_child
    (terminal : Terminal source expression statements)
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
      expressionSyntax certificates definitions administrative context scope
      (.statements true statements) expected type flow) :
    ∃ lowered : SourceCoreBasic.LoweredExpr, lowered.type = type ∧
      flow = LocalLoop.returnValue type lowered.expression ∧
      certificates context scope expression lowered := by
  cases tree
  case body syntaxTree body => exact lexical_terminal_child terminal body
  all_goals cases terminal <;> simp_all
end StaticTrees

private theorem terminal_on_source {original view : TypedSource}
    {expression : ExpressionId} {statements : List StatementId}
    (metadata : LambdaMetadataViews.MetadataView original view)
    (terminal : Terminal view expression statements) : Terminal original expression statements := by
  cases terminal with
  | returning rest found form => exact .returning rest (metadata.statement found) form
  | tail found form => exact .tail (metadata.statement found) form

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}

private abbrev bodyScope {closure : Dynamic.Closure}
    {localScope : SourceCoreLocalCell.Scope} {admin : Core.Context}
    (code : Code compiled.indexed closure localScope admin) : SourceCoreLocalCell.Scope :=
  code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope

/-- The retained original Source Tree certifies the same lowered child as
this actual terminal packet. The body flow is the real common static witness. -/
theorem canonical_child
    (body : BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) registry semanticFaults)
    (expression : ExpressionId) (terminal : Terminal code.view expression function.body)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages) :
    certificates body.readFuel function.source body.toContext.context
      (bodyScope code) expression packet.receipt.child := by
  have originalTerminal : Terminal function.source expression function.body :=
    terminal_on_source code.viewOfSource terminal
  obtain ⟨lowered, sameType, flow, certified⟩ := imperative_terminal_child originalTerminal body.tree
  have sameFlow : body.flow = LocalLoop.returnValue code.receipt.resultCore packet.receipt.child.expression :=
    finish_injective (body.emitted.symm.trans packet.receipt.emitted)
  have sameExpression : lowered.expression = packet.receipt.child.expression :=
    return_value_injective (flow.symm.trans sameFlow)
  have sameLowered : lowered = packet.receipt.child :=
    lowered_eq (sameType.trans packet.receipt.sameType.symm) sameExpression
  exact sameLowered ▸ certified

variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- The canonical Source child is indexed by the same physical expression and
lowered compiler child; the complete original certificate family stays static. -/
def HasCanonicalBodyChild
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) : Prop :=
  match association, packet with
  | .ordinary _ _ code _ support _ _ _ _ _ _, packet =>
      packet.expression = expression ∧
      support.certificates support.body.readFuel function.source support.body.toContext.context
        (bodyScope code) expression packet.receipt.child
  | .principal _ _ code _ support _ _ _ _ _ _, packet =>
      packet.expression = expression ∧
      support.certificates support.body.readFuel function.source support.body.toContext.context
        (bodyScope code) expression packet.receipt.child

/-- This uses the actual child already exposed by the same-Code factory and
adds the original Source Tree's exact certificate without a transport premise. -/
theorem canonical_for
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (terminal : TerminalShapeFor association expression)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages)
    (actualChild : HasBodyChild association expression packet) :
    HasCanonicalBodyChild association expression packet := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    change _ ∧ packet.expression = expression ∧ _ at actualChild
    exact ⟨actualChild.2.1, canonical_child support.body expression terminal packet⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    change _ ∧ packet.expression = expression ∧ _ at actualChild
    exact ⟨actualChild.2.1, canonical_child support.body expression terminal packet⟩

/-- The accepted factory retains both the actual-view and canonical-Source
child certificates for the same requested expression and selected scope. -/
theorem terminal_for_both
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (terminal : TerminalShapeFor association expression) (reader : ReadPolicyFor association)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages,
      HasBodyChild association expression packet ∧ HasCanonicalBodyChild association expression packet := by
  obtain ⟨packet, actualChild⟩ := terminal_for_exact association expression terminal reader child selected
  exact ⟨packet, actualChild, canonical_for association expression terminal packet actualChild⟩

/-- Real descriptor/Source authority still selects the staged child internally.
The extra canonical child certificate requires no registry totality assumption. -/
theorem at_prepared_registry_both
    (association : Association headers keys registry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId)
    (terminal : TerminalShapeFor association expression) (reader : ReadPolicyFor association) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table),
      HasBodyChild association expression packet ∧ HasCanonicalBodyChild association expression packet := by
  obtain ⟨packet, actualChild⟩ := at_prepared_registry_exact association expression terminal reader
  exact ⟨packet, actualChild, canonical_for association expression terminal packet actualChild⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureCanonicalChildFactories
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedFlowStep
/-! Named F selects the exact Prepared/HeaderAt and coupled collector retained
by the actual entry profile. Its original structural head/loop producer runs
once from graded E induction hypotheses. Authentic receiving table rebuilding
and reached interpretation are explicit static obligations for that same
issuance; no finished expression or body law is stored in the profile. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedFlowStep
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedCatalogNamedProfiles (Profile)
open CallableIndexedOwnedPreparedCatalogNamedBodyContinuations (Validity FlowPreserves FlowReflects bridge body_protocol)
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {administrative : Core.Context}
  (profile : Profile (certificates := certificates) (expressionSyntax := expressionSyntax) header administrative)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : profile.receiving.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep profile.receiving.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep profile.receiving.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity header context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := certificates header)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      (factory := profile.factory) (faults := faults) (registry := registry) profile.receiving
      (bridge (headers := headers) owner header) functions table)

include wellFormed in
private theorem source_runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    header.context header.function.source := by
  obtain ⟨_facts, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields certified.typing.inputs_extend
  simpa only [header.frame.source] using certified.sourceRuntimeValid.transport fields

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- Preservation uses E at sizes at most n at the exact visited contexts. -/
theorem preserves_flow [FunctionCalls.FaultTokens faults] (budget : Nat)
    (meaning : ∀ context, Validity header context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) owner header)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context header.function.evidence header.function.source (certificates header context) faults size)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves (headers := headers) (registry := registry) (faults := faults) functions owner profile) := by
  have eliminated := profile.prepared_eliminator
  rw [profile.aligned.layouts, profile.aligned.globals] at eliminated
  have result := CallableIndexedOwnedContextualLambdaPreparedFlowBounds.preserves_flow
    (active := header.active) (onError := header.onError) (solved := header.solved)
    (expressionSyntax := expressionSyntax header) (certificates := certificates header)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (registry := registry) (faults := faults) (factory := profile.factory)
    profile.receiving (bridge (headers := headers) owner header) functions rfl
    (CallableIndexedAmbient.frame_registered compiled.indexed) extension header.function.evidence faithful observations
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (Origin.producer (headers := headers) (registry := registry) (.ordinary header) owner functions)
    (Origin.acquire (headers := headers) (registry := registry) (.ordinary header) owner functions)
    (Origin.transport (headers := headers) (.ordinary header) owner)
    (Origin.bindings (headers := headers) (.ordinary header) owner)
    header.unique wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (source_runtime wellFormed) meaning eliminated
  have sameValidity :
      CallableIndexedOwnedContextualLambdaPreparedFlowBounds.Validity (compiled := compiled)
        (source := header.function.source) (solved := header.solved) header.function.evidence =
      CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.Validity true header := rfl
  rw [sameValidity] at result
  dsimp only [ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt, RecursiveNamedHeaderContracts.AtMost, FlowPreserves,
    CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.FlowPreserves,
    bridge, body_protocol, CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.body_protocol] at result ⊢
  simpa only [SourceCoreCompatibleValues.Context.initial, profile.aligned.globals] using result

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- Reflection consumes strict native E grades and retains its independent
Source grade through the same original prepared producer. -/
theorem reflects_flow [FunctionCalls.FaultTokens faults] (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (meaning : ∀ context, Validity header context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge (headers := headers) owner header)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context header.function.evidence header.function.source (certificates header context) faults size)) :
    Below budget
      (FlowReflects (headers := headers) (registry := registry) (faults := faults) functions owner profile) := by
  have eliminated := profile.prepared_eliminator
  rw [profile.aligned.layouts, profile.aligned.globals] at eliminated
  have result := CallableIndexedOwnedContextualLambdaPreparedFlowBounds.reflects_flow
    (active := header.active) (onError := header.onError) (solved := header.solved)
    (expressionSyntax := expressionSyntax header) (certificates := certificates header)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (registry := registry) (faults := faults) (factory := profile.factory)
    profile.receiving (bridge (headers := headers) owner header) functions rfl
    (CallableIndexedAmbient.frame_registered compiled.indexed) extension header.function.evidence faithful observations
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (Origin.producer (headers := headers) (registry := registry) (.ordinary header) owner functions)
    (Origin.acquire (headers := headers) (registry := registry) (.ordinary header) owner functions)
    (Origin.transport (headers := headers) (.ordinary header) owner)
    (Origin.bindings (headers := headers) (.ordinary header) owner)
    header.unique wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (source_runtime wellFormed) functionTypes meaning eliminated
  have sameValidity :
      CallableIndexedOwnedContextualLambdaPreparedFlowBounds.Validity (compiled := compiled)
        (source := header.function.source) (solved := header.solved) header.function.evidence =
      CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.Validity true header := rfl
  rw [sameValidity] at result
  dsimp only [ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt, RecursiveNamedBoundedContracts.Below, Below, FlowReflects,
    CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.FlowReflects,
    bridge, body_protocol, CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.body_protocol] at result ⊢
  simpa only [SourceCoreCompatibleValues.Context.initial, profile.aligned.globals] using result

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedFlowStep
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds
/-! Named expression leaves use the literal selected compiler profile at the
actual complete parameter entry. Its Prepared/HeaderAt, coupled extraction and
authentic diagnostic issuance stay available to strict body induction. Ordered
arguments establish Source admission before the original typed finish and
caller restoration. Zero capture prefix, genuine Header globals, static
profile/syntax construction and the shared strict flow family remain explicit
inputs. Ordinary and evidence-bearing named alternatives retain their original
caller dictionary and exact selected Header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedCatalogNamedProfiles (Profile)
open CallableIndexedOwnedPreparedCatalogNamedBodyContinuations (ProfilesFor FlowPreserves FlowReflects)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captureZero : owner.key.capturePrefix = 0)
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

/-- This is the strict body induction input at the same static Header profile. -/
def SourceFlows (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) (budget : Nat) : Prop :=
  Below budget (fun child => ∀ administrative
    (profile : Profile (certificates := certificates)
      (expressionSyntax := expressionSyntax) header administrative),
    FlowPreserves (registry := registry) (faults := faults) (headers := headers) functions owner profile child)

/-- Native body size stays separate from the Source grade returned by finish. -/
def NativeFlows (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) (budget : Nat) : Prop :=
  Below budget (fun child => ∀ administrative
    (profile : Profile (certificates := certificates)
      (expressionSyntax := expressionSyntax) header administrative),
    FlowReflects (registry := registry) (faults := faults) (headers := headers) functions owner profile child)

section InvocationAdapters
variable {owner functions}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (globals : header.globals = compiled.indexed.base.globals.length)
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {callerPrefix : Nat} {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner callerPrefix index.scope index.canonical) callerProtocol)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical : Environment} {environment : Dynamic.Environment}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge) context initial)
  {originalTypes : List TypeSystem.Ty} {rawResult : TypeSystem.Ty} {predicates : List ProgramPredicate}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (argumentTypes : ExpressionsHaveTypes source context ids originalTypes)
  (application : SourceSemantics.DeclarationApplicationValid context header.instantiation originalTypes rawResult predicates)
  (profiles : ProfilesFor (headers := headers) (owner := owner) (functions := functions)
    (registry := registry) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (header := header))
  (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
    header.context (.statements true header.function.body) header.function.resultType)

include captureZero globals admitted wellFormed sourceRuntime covers locals argumentTypes application profiles syntaxTree in
/-- Real Source argument execution and the authentic hook construct admission
for the exact reached parameter pool before a strict Source body is consumed. -/
theorem source_invocations (budget : Nat)
    (below : SourceFlows (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) header budget) :
    CallableIndexedOwnedExpressionHeads.SourceInvocationsFor (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  intro origin index metadata administrative actualContext actual ξ frameLocation
    physical selected history emitted entry agreement reached related allowed child strict outcome after trace
  exact CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.source_continuation
    (functions := functions) (owner := owner) (caller := bridge.pool argumentState)
    (beforeTyped := sourceAdmission.1) (argumentsTyped := sourceAdmission.2) (stable := stable)
    (captureZero := captureZero) (globals := globals)
    (wellFormed := wellFormed) (profiles := profiles) (syntaxTree := syntaxTree) budget below physical selected history emitted entry agreement reached related allowed child strict trace

include captureZero globals admitted wellFormed sourceRuntime covers locals argumentTypes application profiles syntaxTree in
/-- Native arguments first recover their actual independently sized Source
trace; the same Source admission and parameter pool drive the strict body. -/
theorem native_invocations (budget : Nat)
    (below : NativeFlows (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) header budget) :
    CallableIndexedOwnedExpressionHeads.NativeInvocationsFor (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  intro origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical selected history emitted _prefix within restored entry reached related allowed child strict bodyValue bodyFinalStore completed
  exact CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.native_continuation
    (functions := functions) (owner := owner) (caller := bridge.pool argumentState)
    (beforeTyped := sourceAdmission.1) (argumentsTyped := sourceAdmission.2) (stable := stable)
    (captureZero := captureZero) (globals := globals)
    (wellFormed := wellFormed) (profiles := profiles) (syntaxTree := syntaxTree) budget below physical selected history emitted _prefix within restored entry reached related allowed child strict completed

end InvocationAdapters


section Heads
variable {owner functions}
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {compilation : SourceCoreFunctions.Context}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (unique : NodeOccurrencesUnique source)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (globals : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (syntaxTree : ∀ header, header ∈ headers →
    GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType)
  (profiles : ∀ header, header ∈ headers → ProfilesFor (headers := headers) (owner := owner) (functions := functions)
    (registry := registry) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (header := header))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)

include captureZero globals wellFormed sourceRuntime covers unique idsUnique sameLayouts syntaxTree profiles owners in
/-- Named ordinary/direct heads use the authentic Source argument row at their
actual input, then consume only a typed strict body at the real parameter post. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers → SourceFlows (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedExpressionHeads.preserves_at_with_sequence functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      bridge budget size within idsUnique unique owners head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.preserves
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact source_invocations (owner := owner) (functions := functions)
          (captureZero := captureZero) (globals := globals header member)
          bridge initial admitted wellFormed sourceRuntime covers locals argumentTypes application
          (profiles header member) (syntaxTree header member) budget (bodies header member)) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame⟩

include captureZero globals wellFormed sourceRuntime covers unique sameLayouts syntaxTree profiles in
/-- Native heads retain the original native grade. The genuine reflected Source
argument and parent grades establish admission at their actual reached states. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers → NativeFlows (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := certificates)
      (expressionSyntax := expressionSyntax) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedExpressionHeads.reflects_at_with_sequence functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      bridge budget size within head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.reflects
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact native_invocations (owner := owner) (functions := functions)
          (captureZero := captureZero) (globals := globals header member)
          bridge initial admitted wellFormed sourceRuntime covers locals argumentTypes application
          (profiles header member) (syntaxTree header member) budget (bodies header member)) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame⟩


/-- A selected dictionary must be the actual Source caller dictionary. -/
def CallerEvidence (selected : Option Dynamic.EvidenceEnvironment)
    (actual : Dynamic.EvidenceEnvironment) : Prop :=
  match selected with
  | none => True
  | some dictionary => dictionary = actual

include captureZero globals wellFormed sourceRuntime covers unique idsUnique sameLayouts syntaxTree profiles owners in
/-- The raw compiler's two named alternatives preserve their actual Header.
The optional dictionary is retained literally; no method Header is synthesized. -/
theorem preserves_calls (callerEvidence : Option Dynamic.EvidenceEnvironment)
    (sameEvidence : CallerEvidence callerEvidence evidence)
    (budget size : Nat) (within : size ≤ budget)
    (children : Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers → SourceFlows (headers := headers) (keys := keys)
      (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        callerEvidence headers compilation source context certificate) faults size := by
  cases callerEvidence with
  | some dictionary =>
      cases sameEvidence
      exact preserves_at (functions := functions) (owner := owner)
        (captureZero := captureZero) (globals := globals) evidence bridge wellFormed sourceRuntime covers unique idsUnique
        sameLayouts syntaxTree profiles owners budget size within children bodies
  | none =>
      intro scope id lowered head
      exact preserves_at (functions := functions) (owner := owner)
        (captureZero := captureZero) (globals := globals) evidence bridge wellFormed sourceRuntime covers unique idsUnique
        sameLayouts syntaxTree profiles owners budget size within children bodies
        (RecursiveNamedCallEvidenceHeads.Head.ordinary head)

include captureZero globals wellFormed sourceRuntime covers unique sameLayouts syntaxTree profiles in
/-- Native named completion retains the independent Source grade and actual
restored pool in either authentic optional-evidence alternative. -/
theorem reflects_calls (callerEvidence : Option Dynamic.EvidenceEnvironment)
    (sameEvidence : CallerEvidence callerEvidence evidence)
    (budget size : Nat) (within : size ≤ budget)
    (children : Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ header, header ∈ headers → NativeFlows (headers := headers) (keys := keys)
      (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        callerEvidence headers compilation source context certificate) faults size := by
  cases callerEvidence with
  | some dictionary =>
      cases sameEvidence
      exact reflects_at (functions := functions) (owner := owner)
        (captureZero := captureZero) (globals := globals) evidence bridge wellFormed sourceRuntime covers unique
        sameLayouts syntaxTree profiles budget size within children bodies
  | none =>
      intro scope id lowered head
      exact reflects_at (functions := functions) (owner := owner)
        (captureZero := captureZero) (globals := globals) evidence bridge wellFormed sourceRuntime covers unique
        sameLayouts syntaxTree profiles budget size within children bodies
        (RecursiveNamedCallEvidenceHeads.Head.ordinary head)

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactoryBounds
/-! Actual body certificates feed strict staged children and the original
closure application producers. The accepted compiler Tree supplies TerminalFor
internally. Smaller child meaning stays at the real BodyWith certificate and
actual selected Source scope; no arbitrary terminal or whole body law is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactoryBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedTerminalClosureFactories
universe u

private abbrev preparedStages (compiled : SourceCoreUnifiedCompilation.Compiled) :=
  RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
    compiled.indexed.ancestry.graph.inputs.callable.table

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- The reflection hypothesis ranges over actual selected scopes and the
literal static certificate stored by this association's BodyWith. -/
def ReflectsActualBodyBelow
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat) : Prop :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (support.certificates support.body.readFuel code.view support.body.toContext.context) faults budget
  | .principal _ _ code _ support _ _ _ _ _ _ =>
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (support.certificates support.body.readFuel code.view support.body.toContext.context) faults budget

/-- Preservation covers the Source-selected scope at the same real certificate
and independent Source trace budget. -/
def PreservesActualBodyBelow
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat) : Prop :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (support.certificates support.body.readFuel code.view support.body.toContext.context) faults budget
  | .principal _ _ code _ support _ _ _ _ _ _ =>
    ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      support.body.toContext.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child (support.certificates support.body.readFuel code.view support.body.toContext.context) faults budget

private theorem reflects_at_packet
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId) (packet : TerminalFor association stages)
    (actualChild : HasBodyChild association expression packet)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat)
    (children : ReflectsActualBodyBelow (registry := registry) (faults := faults) (stages := stages) association functions budget) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.ReflectsBelowFor
      (registry := registry) (faults := faults) association packet functions budget := by
  have same : HasBodyCertificate association packet := actualChild.1
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    dsimp [HasBodyCertificate] at same
    dsimp [ReflectsActualBodyBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.ReflectsBelowFor]
    rw [same]
    exact children packet.child packet.selected
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    dsimp [HasBodyCertificate] at same
    dsimp [ReflectsActualBodyBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.ReflectsBelowFor]
    rw [same]
    exact children packet.child packet.selected

private theorem preserves_at_packet
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (expression : ExpressionId) (packet : TerminalFor association stages)
    (actualChild : HasBodyChild association expression packet)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (budget : Nat)
    (children : PreservesActualBodyBelow (registry := registry) (faults := faults) (stages := stages) association functions budget) :
    CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.PreservesBelowFor
      (registry := registry) (faults := faults) association packet functions budget := by
  have same : HasBodyCertificate association packet := actualChild.1
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    dsimp [HasBodyCertificate] at same
    dsimp [PreservesActualBodyBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.PreservesBelowFor]
    rw [same]
    exact children
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    dsimp [HasBodyCertificate] at same
    dsimp [PreservesActualBodyBelow] at children
    dsimp [CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.PreservesBelowFor]
    rw [same]
    exact children

section ContextualApplication
variable (association : Association headers keys bodyRegistry semanticFaults mapping world function native
    bindings parameterCore resultCore)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {before : Dynamic.Heap} {store : Store} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  {sources : List Dynamic.Value} {values : List Value}
  (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before sources)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings sources values)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    mapping world before store)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)

include raw represented heaps stable runtime in
/-- The accepted body factory constructs its packet before the original
application reflection port runs once at the literal native completion. -/
theorem application_reflects
    (expression : ExpressionId) (shape : TerminalShapeFor association expression)
    (reader : ReadPolicyFor association) (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (budget : Nat) (children : ReflectsActualBodyBelow (registry := registry) (faults := faults)
      (stages := preparedStages compiled) association functions budget)
    {invocation : Staging.Recursive.Scope} {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) (preparedStages compiled) sourceSize
        invocation context before (.closure function) sources outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
            (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
          context function.resultType outcome returned := by
  obtain ⟨packet, actualChild⟩ := at_prepared_registry_exact association expression shape reader
  exact CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.application_reflects
    association packet functions caller raw represented heaps stable runtime valid budget
    (reflects_at_packet association expression packet actualChild functions budget children) completed within

include raw represented heaps stable runtime in
/-- The same static packet supports the actual Source-selected application;
no completed body meaning or prebuilt TerminalFor is an input. -/
theorem application_preserves
    (expression : ExpressionId) (shape : TerminalShapeFor association expression)
    (reader : ReadPolicyFor association) (budget : Nat)
    (children : PreservesActualBodyBelow (registry := registry) (faults := faults)
      (stages := preparedStages compiled) association functions budget)
    {invocation : Staging.Recursive.Scope} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) (preparedStages compiled) size
      invocation context before (.closure function) sources outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [native, DataPatternValues.packValues values] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
            (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
          context function.resultType outcome returned := by
  obtain ⟨packet, actualChild⟩ := at_prepared_registry_exact association expression shape reader
  exact CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation.application_preserves
    association packet functions caller raw represented heaps stable runtime budget
    (preserves_at_packet association expression packet actualChild functions budget children) trace within
end ContextualApplication

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureFactoryBounds
end
