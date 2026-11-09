import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ProfileExtraction
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements

/-!
# Prepared callables: formation receipts

Formation receipts and bounds of direct, principal, qualified and function model formation, with raw compiler heads.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectNamedProfileExtraction
/-! Actual cached named compilation and a real ordinary parameter entry supply
one enclosing native typing. The finite native-aware compiler induction derives
the same flow Tree, prepared diagnostic plan and structural eliminator. The
forward Profile view retains that Tree and omits universal CatalogSites.
Independent Source syntax, local expression certificates and exact assignment
issuance remain static inputs; this module supplies no execution law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectNamedProfileExtraction
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedPublicSpecializationMeaning
open RecursiveNamedPreparedHeaderPolicies

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {administrative : Core.Context}
  {first : Nat}
  (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source)
  (issued : SourceCoreAssignmentFaultSites.prepare header.function.source first = .ok prepared.compilation.own.assignments)

/-- Only authentic Source syntax and local static certificates remain here.
Every raw child typing is manufactured by the enclosing-code collector. -/
structure Children where
  expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = compiled.compatible.checked.signatures →
    ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
    expressionSyntax header id → header.function.source.lookupExpression? id = some node →
    ExpressionHasType header.function.source sourceContext id node.type →
    header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
    ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      lowered.expression nativeType compiled.indexed.layouts.definitions → certificates header sourceContext scope id lowered
  syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
    (.statements true header.function.body) header.function.resultType

/-- This factory binds its operand token to the actual prepared assignment row.
The returned Plan retains actual reached missing/uninitialized interpretation
obligations for its own diagnostic fields. -/
def assignment_factory : AssignmentDiagnosticOrigins.Factory true .reachable header.function.source
    (Prepared.invalidOperand prepared) :=
  AssignmentDiagnosticOrigins.Factory.prepared operandsTyped issued

/-- Source ownership derives freshness for the same Header body, independently
of native types and compiler Tree extraction. -/
theorem hidden_fresh (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    GenericImperativeMatch.MatchHiddenFresh header.function.source := by
  obtain ⟨facts, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  apply CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh
  rw [header.frame.source]
  exact certified.local_identity_ownership

/-- One actual coupled compiler receipt. The original prepared Plan and its
structural eliminator are retained alongside the finite flow Tree. -/
structure Receipt where
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body header.output header.reasonAt true header.escaped = .ok flow
  collected : GenericImperativeMatch.CatalogCoupledExtractionFor .reachable header.layouts header.owner header.active
    compiled.indexed.ancestry.layout.frame header.globals header.onError (.initial compiled.compatible.checked)
    header.function.source (assignment_factory prepared operandsTyped issued)
    (Prepared.invalidUnary prepared) (Prepared.invalidProjection prepared) (Prepared.missingDefault prepared)
    (expressionSyntax header) (certificates header) compiled.indexed.layouts.definitions
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (Prepared.ambientMatch prepared).solvedRequirements header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (.statements true header.function.body) header.function.resultType header.output flow

variable {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
    administrative actualContext actual ξ frameLocation current ghost)

include aligned recipeAccepted nativeMember functions owner complete entry in
/-- Actual cache and support proofs transport the exact body to its real entry;
one finite collector then derives every visited child native witness. -/
theorem extract_at
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (children : Children (certificates := certificates) (expressionSyntax := expressionSyntax)
      (header := header) (administrative := administrative)) :
    Nonempty (Receipt (certificates := certificates) (expressionSyntax := expressionSyntax)
      (administrative := administrative) prepared operandsTyped issued) := by
  have nativeTyped := RecursiveNamedCatalogNativeContexts.canonical_cached complete aligned.globals
    (CallableIndexedOwnedNamedPublicProfileExtraction.cached_typed prepared aligned nativeMember)
    (CallableIndexedOwnedNamedPublicProfileExtraction.cached_supported recipeAccepted prepared aligned) entry
  have accepted := aligned.accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, emitted⟩ := CompatibleEncoding.bind_ok accepted
  have finished : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped :=
    Except.ok.inj emitted.symm
  rw [finished] at nativeTyped
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow nativeTyped
  have assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy (.initial compiled.compatible.checked)
      (Prepared.invalidProjection prepared) (Prepared.invalidOperand prepared) (Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact Prepared.assignments prepared
  have unaries : CompatibleBitNotStatements.Policy header.policy (.initial compiled.compatible.checked)
      (Prepared.invalidProjection prepared) (Prepared.invalidUnary prepared) (Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact Prepared.unary prepared
  obtain ⟨collected⟩ :=
    CallableIndexedOwnedPreparedNativeImperativeCollectors.extraction_of_typed_position_with_catalog_coupled true .reachable
      (assignment_factory prepared operandsTyped issued)
      (Prepared.header_match prepared aligned) rfl rfl (Prepared.match_allocator prepared aligned)
      (GenericImperativeMatch.MatchChildStatic.of_hidden
        (matchCompilation := Prepared.ambientMatch prepared) (definitions := compiled.indexed.layouts.definitions)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        (certificates := certificates header) (hidden_fresh wellFormed))
      (Prepared.header_read prepared aligned) (Prepared.header_binder prepared aligned)
      (Prepared.header_allocator prepared aligned) children.expressions assignments unaries header.unique
      children.syntaxTree (RecursiveNamedSourceContextFacts.header_typeVariables header)
      (RecursiveNamedSourceContextFacts.header_residual header) (Prepared.header_signatures (header := header))
      (RecursiveNamedHeaderScopeDeclarations.header_scope
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (program := Program.ofChecked compiled.sourceProgram)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header)
      aligned.projection generated flowTyped
  exact ⟨⟨flow, generated, collected⟩⟩

/-- A forward view uses the exact collected Tree. Its prepared structure stays
in Receipt for the eventual reached-diagnostic flow fold. -/
def Receipt.profile
    (receipt : Receipt (certificates := certificates) (expressionSyntax := expressionSyntax)
      (administrative := administrative) prepared operandsTyped issued) :
    CallableIndexedOwnedDirectTypedNamedBodyContinuations.Profile
      (certificates := certificates) (expressionSyntax := expressionSyntax) true header administrative :=
  CallableIndexedOwnedDirectTypedNamedBodyContinuations.Profile.of_extracted
    header.valid aligned.accepted aligned.projection receipt.generated
    receipt.collected.original.original.original.original.tree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectNamedProfileExtraction
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNestedNamedProfileView
/-! The original actual Header collector retains the same accepted body,
flow action and static compiler Tree. This forward view copies those fields
into the nested caller interface through its honest static constructor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNestedNamedProfileView
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled program →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {runtime : Bool} {administrative : Core.Context}

/-- Static fields are copied forward from the original real compiler profile.
Neither direction of body semantics is supplied by this conversion. -/
def of_direct
    (profile : CallableIndexedOwnedDirectTypedNamedBodyContinuations.Profile
      (certificates := certificates) (expressionSyntax := expressionSyntax) runtime header administrative) :
    CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.Profile
      (certificates := certificates) (expressionSyntax := expressionSyntax) runtime header administrative :=
  CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.Profile.of_extracted
    profile.initialValid profile.accepted profile.projection profile.generated profile.tree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNestedNamedProfileView
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectStageScopeReceipts
/-! The real direct closure member selects an independent recursive staging
scope. Its original sidecar comes from the actual descriptor's authenticated
lambda factory. Source, context, evidence, both substitutions and caller
staging markers are retained. This static selection contains no body execution
or guard acceptance law and does not extend the recursive trace's coverage. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectStageScopeReceipts
open Core Frontend SourceInference
open CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins

private theorem metadata_owner {caller : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.validateSpecializationMetadataWith true caller = .ok ()) :
    caller.function.typedBody.owner = caller.key.declaration := by
  by_cases ownership : SourceCompilationPlan.specializationOwnershipCoherent caller = true
  · change decide (caller.key.declaration = caller.declaration ∧
      caller.function.declaration = caller.declaration ∧
      caller.function.typedBody.owner = caller.declaration) = true at ownership
    have coherent := of_decide_eq_true ownership
    exact coherent.2.2.trans coherent.1.symm
  · unfold SourceCompilationPlan.validateSpecializationMetadataWith at accepted
    simp [ownership, throw, bind, Except.bind] at accepted

/-- Successful original preparation authenticates the sidecar's owner. -/
theorem sidecar_owner {plan : SourceCoreStageContracts.Plan}
    {key : SourceCoreStageContracts.Key} {sidecar : SourceCoreStageContracts.Sidecar}
    (accepted : SourceCoreStageContracts.prepareSidecar plan key = .ok sidecar) :
    sidecar.source.owner = sidecar.caller.key.declaration := by
  unfold SourceCoreStageContracts.prepareSidecar at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan key with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    cases valid : SourceCompilationPlan.validateSpecializationMetadataWith true caller with
    | error error => simp [valid, Functor.discard, Functor.mapConst, Except.map] at accepted
    | ok value =>
      cases value
      simp only [valid] at accepted
      dsimp [Functor.discard, Functor.mapConst, Except.map] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
          exact metadata_owner valid
        · cases accepted

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Actual Code and canonical Source attribution recover their own sidecar
and recursive closure selection. No chosen sidecar is an input. -/
theorem code_scope {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (source : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan code.compilation.owner = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar code.active function) := by
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  obtain ⟨site⟩ := RecursiveStageProjection.lambda_site_of_descriptor stages.accepted code.descriptor
  obtain ⟨sidecar, selected, _canonical⟩ := LambdaSourceAlignment.LambdaSource.canonical site.original
  have same := (CallContractCertificates.sidecar_of_accepted selected).2
  have alignedSite : AuthenticatedCallableLedger.LambdaSite compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sidecar.caller.key code.id code.active
      code.descriptor.id := by simpa only [same] using site
  have alignedSource : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      sidecar.caller.key code.active function.source := by simpa only [same] using source
  have owner : function.source.owner = sidecar.caller.key.declaration := by
    rw [source.source selected]
    exact sidecar_owner selected
  refine ⟨sidecar, selected, RecursiveStageRegistry.Selected.lambda
    (by simpa only [same] using selected) alignedSite alignedSource owner ?_⟩
  exact LambdaMetadataViews.lambda_origin alignedSource alignedSite.original code.viewOfSource unique code.found
    (code.form.trans code.sourceForm)

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {qualification : Facet compiled}

/-- Both ordinary and selected Principal leaves use their original compiler
Source receipt. Equal native function types cannot select an invocation scope. -/
theorem Association.scope_at {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {carrier : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (association : Association qualification headers keys bodyRegistry faults
      mapping world function carrier bindings parameter result) :
    ∃ selected : Staging.Recursive.Scope,
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function selected := by
  cases association with
  | ordinary _ _ code _ support _ _ _ _ _ _ _ =>
    obtain ⟨sidecar, _issued, selected⟩ := code_scope code support.source_receipt support.body.unique
    exact ⟨_, selected⟩
  | principal _ _ code _ support _ _ _ _ _ _ _ =>
    obtain ⟨sidecar, _issued, selected⟩ := code_scope code support.source_receipt support.body.unique
    exact ⟨_, selected⟩

theorem StaticMember.scope_at {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {carrier : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : StaticMember qualification headers keys bodyRegistry faults
      mapping world function carrier bindings parameter result) :
    ∃ selected : Staging.Recursive.Scope,
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function selected := by
  obtain ⟨association⟩ := member
  exact Association.scope_at association

/-- The selected scope retains the actual original marker and declaration
substitution together with the full local substitution and closure dictionary. -/
theorem StaticMember.original_scope {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {carrier : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : StaticMember qualification headers keys bodyRegistry faults
      mapping world function carrier bindings parameter result) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar, ∃ active : TypeSystem.Substitution,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan sidecar.caller.key = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar active function) ∧
      (RecursiveStageRegistry.scope sidecar active function).origin.declaration = sidecar.caller.key.declaration ∧
      (RecursiveStageRegistry.scope sidecar active function).origin.declarationSubstitution =
        sidecar.caller.parameterSubstitution ∧
      (RecursiveStageRegistry.scope sidecar active function).origin.localSubstitution = active ∧
      (RecursiveStageRegistry.scope sidecar active function).guards.stages.callerReturnComptime =
        sidecar.caller.function.returnComptime ∧
      (RecursiveStageRegistry.scope sidecar active function).source = function.source ∧
      (RecursiveStageRegistry.scope sidecar active function).context = function.context ∧
      (RecursiveStageRegistry.scope sidecar active function).evidence = function.evidence := by
  obtain ⟨selected, receipt⟩ := StaticMember.scope_at member
  obtain ⟨sidecar, active, issued, same, owner⟩ := RecursiveStageRegistry.Selected.original receipt
  subst selected
  exact ⟨sidecar, active, issued, receipt, owner, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectStageScopeReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveFunctionOrigins
/-! Positive function origins retain their actual bootstrap owner and immutable
key. Named leaves retain the actual current capture, full Source dictionary and
installed code. Closure leaves retain the existing direct compiler association
and the same bootstrap owner. The bootstrap basis is independent of this model,
so storing its provenance does not define a recursive function model. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveFunctionOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedCapture NamedSourceAt NamedInstalledCode)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedNamedBootstrapReceipts (Bootstrap NamedOwner)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {qualification : Facet compiled}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}

abbrev Owner := NamedOwner (headers := headers) keys
  (CallableIndexedLambdaValues.model compiled.indexed profile) bodyRegistry

/-- Coverage is finite static ownership of the fixed key domain. Its producer
below uses the actual singleton bootstrap; it contains no execution claim. -/
def OwnerCover (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) : Prop :=
  ∀ owner : OwnedKey keys, ∃ origin : Owner (headers := headers) (keys := keys)
    (bodyRegistry := bodyRegistry) (profile := profile), origin.owner = owner

/-- Read the physical owner from the actual constructor without erasure. -/
def association_owner {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (association : CallableIndexedOwnedPreparedNativeDirectCellOrigins.Association qualification
      headers keys bodyRegistry faults mapping world function native bindings parameter result) : OwnedKey keys := by
  cases association with
  | ordinary owner _ _ _ _ _ _ _ _ _ _ _ => exact owner
  | principal owner _ _ _ _ _ _ _ _ _ _ _ => exact owner

structure ClosureAssociation (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) where
  association : CallableIndexedOwnedPreparedNativeDirectCellOrigins.Association qualification
    headers keys bodyRegistry faults mapping world function native bindings parameter result
  origin : Owner (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (profile := profile)
  sameOwner : origin.owner = association_owner association

abbrev ClosureMember (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Prop :=
  Nonempty (ClosureAssociation qualification headers keys bodyRegistry faults profile mapping world
    function native bindings parameter result)

section Closures
variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

def ClosureAssociation.extend
    (packet : ClosureAssociation qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ClosureAssociation qualification headers keys bodyRegistry faults profile futureMapping futureWorld
      function native bindings parameter result := by
  refine ⟨packet.association.extend maps worlds, packet.origin, ?_⟩
  have same : association_owner (packet.association.extend maps worlds) = association_owner packet.association := by
    cases packet.association <;> rfl
  exact packet.sameOwner.trans same.symm

/-- The physical prefix is inherited from the actual complete bootstrap key.
It is independent of the lexical lambda capture scope. -/
theorem ClosureAssociation.capture_zero
    (packet : ClosureAssociation qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result) :
    (association_owner packet.association).key.capturePrefix = 0 := by
  rw [← packet.sameOwner]
  exact packet.origin.capture_zero

theorem ClosureAssociation.globals
    (packet : ClosureAssociation qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)} (member : header ∈ headers) :
    header.globals = compiled.indexed.base.globals.length := packet.origin.globals member

theorem ClosureAssociation.global_locations
    (packet : ClosureAssociation qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    (association_owner packet.association).key.locations header =
      RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot := by
  rw [← packet.sameOwner]
  exact packet.origin.global_locations header

theorem ClosureMember.direct
    (member : ClosureMember qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result) :
    CallableIndexedOwnedPreparedNativeDirectCellOrigins.StaticMember qualification headers keys
      bodyRegistry faults mapping world function native bindings parameter result := by
  obtain ⟨packet⟩ := member
  exact ⟨packet.association⟩

theorem ClosureMember.extend
    (member : ClosureMember qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ClosureMember qualification headers keys bodyRegistry faults profile futureMapping futureWorld
      function native bindings parameter result := by
  obtain ⟨packet⟩ := member
  exact ⟨packet.extend maps worlds⟩

theorem closure_of_direct
    (owners : OwnerCover headers keys bodyRegistry profile)
    (member : CallableIndexedOwnedPreparedNativeDirectCellOrigins.StaticMember qualification headers
      keys bodyRegistry faults mapping world function native bindings parameter result) :
    ClosureMember qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result := by
  obtain ⟨association⟩ := member
  obtain ⟨origin, same⟩ := owners (association_owner association)
  exact ⟨⟨association, origin, same⟩⟩
end Closures

/-- The actual formed named carrier is retained; no arbitrary capture is
identified with a static chooser or upgraded to bootstrap ownership. -/
inductive NamedAssociation
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.GlobalFunction → Value → Ty → Type where
  | named {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction} {identity : Word}
      (origin : Owner (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (profile := profile))
      (member : header ∈ headers) (sourceAt : NamedSourceAt header rawD source)
      (capture : NamedCapture headers origin.owner.key header mapping world) (installed : NamedInstalledCode capture)
      (number : Word.ofNat? (header.slot + 1) = some identity)
      (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
        (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
      (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table (.named header.named.signature.key))
      (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)
        header.named.signature.functionType compiled.indexed.layouts.definitions) :
      NamedAssociation headers keys bodyRegistry profile mapping world header.named.specialized.function.type source
        (.pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured))
          (.word descriptor.id)) (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)

section Named
variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {sourceType : TypeSystem.Ty} {source : Dynamic.GlobalFunction} {native : Value} {type : Ty}

def NamedAssociation.extend
    (packet : NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    NamedAssociation headers keys bodyRegistry profile futureMapping futureWorld sourceType source native type := by
  cases packet with
  | named origin member sourceAt capture installed number projection descriptor typed =>
    exact .named origin member sourceAt (capture.extend maps worlds) installed number projection descriptor (typed.weaken worlds)

def NamedAssociation.origin
    (packet : NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type) :
    Owner (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (profile := profile) := by
  cases packet with
  | named origin _ _ _ _ _ _ _ _ => exact origin

theorem NamedAssociation.capture_zero
    (packet : NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type) :
    packet.origin.owner.key.capturePrefix = 0 := packet.origin.capture_zero

theorem NamedAssociation.globals
    (packet : NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)} (member : header ∈ headers) :
    header.globals = compiled.indexed.base.globals.length := packet.origin.globals member

theorem NamedAssociation.global_locations
    (packet : NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    packet.origin.owner.key.locations header =
      RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot :=
  packet.origin.global_locations header

theorem NamedAssociation.general
    (packet : NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults mapping world
      sourceType (.global source) native type := by
  cases packet with
  | named origin member sourceAt capture installed number projection descriptor typed =>
    exact .prior (.prior (.named origin.owner member sourceAt capture installed number projection descriptor typed))
end Named

inductive FunctionOrigins (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | closure {function : Dynamic.Closure} {native : Value}
      {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
      (member : ClosureMember qualification headers keys bodyRegistry faults profile mapping world function native bindings parameter result) :
      FunctionOrigins qualification headers keys bodyRegistry faults profile mapping world
        (FunctionValues.sourceType function) (.closure function) native (CallableContract.functionType parameter result)
  | global {sourceType : TypeSystem.Ty} {source : Dynamic.GlobalFunction} {native : Value} {type : Ty}
      (member : Nonempty (NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type)) :
      FunctionOrigins qualification headers keys bodyRegistry faults profile mapping world sourceType (.global source) native type
  | builtin {function : Dynamic.BuiltinFunction} {sourceType : TypeSystem.Ty} {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world sourceType (.builtin function) native type) :
      FunctionOrigins qualification headers keys bodyRegistry faults profile mapping world sourceType (.builtin function) native type

theorem FunctionOrigins.direct {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (origin : FunctionOrigins qualification headers keys bodyRegistry faults profile mapping world sourceType source native type) :
    CallableIndexedOwnedPreparedNativeDirectCellOrigins.FunctionOrigins qualification headers keys bodyRegistry faults
      mapping world sourceType source native type := by
  cases origin with
  | closure member => exact .closure member.direct
  | global member => obtain ⟨packet⟩ := member; exact .global packet.general
  | builtin related => exact .builtin related

/-- Runtime growth preserves the exact key, Source dictionary, installed code
and carrier. Only actual capture environment typing grows. -/
def functions (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => FunctionOrigins qualification headers keys bodyRegistry faults profile mapping world
  projection := fun origin => (CallableIndexedOwnedPreparedNativeDirectCellOrigins.functions qualification headers keys bodyRegistry faults profile).projection (registry := bodyRegistry) origin.direct
  runtime_hasType := fun origin => (CallableIndexedOwnedPreparedNativeDirectCellOrigins.functions qualification headers keys bodyRegistry faults profile).runtime_hasType (registry := bodyRegistry) origin.direct
  source_function := fun origin => (CallableIndexedOwnedPreparedNativeDirectCellOrigins.functions qualification headers keys bodyRegistry faults profile).source_function (registry := bodyRegistry) origin.direct
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type origin registries maps worlds
    cases origin with
    | closure member => exact .closure (member.extend maps worlds)
    | global member => obtain ⟨packet⟩ := member; exact .global ⟨packet.extend maps worlds⟩
    | builtin related => exact .builtin ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend related registries maps worlds)

theorem includes_direct (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (functions qualification headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedPreparedNativeDirectCellOrigins.functions qualification headers keys bodyRegistry faults profile) :=
  fun origin => origin.direct

abbrev PayloadOrigins (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  ValueRep compiled.compatible.checked registry (functions qualification headers keys bodyRegistry faults profile)

abbrev CellOrigins (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (functions qualification headers keys bodyRegistry faults profile)

section Outputs
variable {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
  {source : Dynamic.Value} {native : Value} {type : Ty}

theorem payload_static_member
    (owners : OwnerCover headers keys bodyRegistry profile)
    {function : Dynamic.Closure} {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : CallableIndexedOwnedPreparedNativeDirectCellOrigins.StaticMember qualification headers keys
      bodyRegistry faults mapping world function native bindings parameter result) :
    PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world
      (FunctionValues.sourceType function) (.closure function) native (CallableContract.functionType parameter result) :=
  .function (.closure (closure_of_direct owners member))

theorem global_member
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world sourceType source native type) :
    ∀ function, source = .global function →
      ∃ actualType, SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType actualType ∧
        Nonempty (NamedAssociation headers keys bodyRegistry profile mapping world actualType function native type) := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    cases related with
    | global member => intro function same; cases same; exact ⟨_, rfl, member⟩
    | closure member => intro function impossible; cases impossible
    | builtin related => intro function impossible; cases impossible
  | compatible same _ ih =>
    intro function equal
    obtain ⟨actualType, previous, packet⟩ := ih function equal
    exact ⟨actualType, same.trans previous, packet⟩
  | unit | bool | word | integer | product | proxy | constructed | mappingValue => intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

theorem closure_member
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world sourceType source native type) :
    ∀ function, source = .closure function →
      ∃ bindings parameter result,
        ClosureMember qualification headers keys bodyRegistry faults profile mapping world function native bindings parameter result ∧
        type = CallableContract.functionType parameter result := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    cases related with
    | closure member => intro function same; cases same; exact ⟨_, _, _, member, rfl⟩
    | global member => intro function impossible; cases impossible
    | builtin related => intro function impossible; cases impossible
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue => intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

end Outputs

/-- The source heap is literally empty at bootstrap. Retargeting preserves the
actual store, entry, frame, world and keys; only its vacuous cell model changes. -/
def bootstrap_retarget
    {initial : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {initialRegistry : SourceCoreRawMetadata.Registry} {world : StoreTyping}
    (packet : Bootstrap (headers := headers) initial initialRegistry world)
    (future : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (futureRegistry : SourceCoreRawMetadata.Registry) : Bootstrap (headers := headers) future futureRegistry world where
  recipe := packet.recipe
  accepted := packet.accepted
  ledger := packet.ledger
  sizes := packet.sizes
  locals := packet.locals
  heaps := ⟨packet.heaps.length_eq, packet.heaps.injective, packet.heaps.runtime_hasTypes, by
    intro source target impossible
    simp at impossible⟩
  entry := packet.entry

/-- Complete bootstrap keys are definitionally unchanged by the empty-heap
retarget. This forwards a genuine owner to a new runtime model. -/
def owner_retarget
    {initial : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {initialRegistry : SourceCoreRawMetadata.Registry}
    (packet : NamedOwner (headers := headers) keys initial initialRegistry)
    (future : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (futureRegistry : SourceCoreRawMetadata.Registry) : NamedOwner (headers := headers) keys future futureRegistry :=
  ⟨packet.world, bootstrap_retarget packet.bootstrap future futureRegistry, packet.embedding⟩

theorem owner_retarget_owner
    {initial : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {initialRegistry : SourceCoreRawMetadata.Registry}
    (packet : NamedOwner (headers := headers) keys initial initialRegistry)
    (future : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (futureRegistry : SourceCoreRawMetadata.Registry) :
    (owner_retarget packet future futureRegistry).owner = packet.owner := rfl

/-- The singleton bootstrap manufactures complete owner coverage directly.
No equality is inferred from an arbitrary reached pool or closure value. -/
theorem bootstrap_owner_cover {world : StoreTyping}
    (packet : Bootstrap (headers := headers)
      (CallableIndexedLambdaValues.model compiled.indexed profile) bodyRegistry world) :
    OwnerCover headers packet.keys bodyRegistry profile := by
  intro owner
  let embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding packet.keys packet.keys :=
    ⟨fun key => key, fun _ => rfl⟩
  let origin := NamedOwner.of_bootstrap packet embedding
  refine ⟨origin, ?_⟩
  have same : owner = packet.owner := by
    have position_eq : owner.position = packet.owner.position := by
      apply Fin.ext
      have bound := owner.position.isLt
      simp only [Bootstrap.keys, List.length_singleton] at bound
      have zero : packet.owner.position.val = 0 := rfl
      omega
    cases owner with
    | mk position => exact congrArg OwnedKey.mk position_eq
  exact (show origin.owner = packet.owner from rfl).trans same.symm

theorem observations (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
      (functions qualification headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type origin
  exact CallableIndexedLambdaValues.observations compiled.indexed profile (registry := registry)
    origin.direct.lambda_represents

theorem runtime_views (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (functions qualification headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type origin
  exact CallableIndexedLambdaValues.runtime_views compiled.indexed profile (registry := registry)
    origin.direct.lambda_represents

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveFunctionOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalCompilerChildren
/-! The raw accepted-child factory is indexed by the actual Named compilation,
so a selected Principal can use its cached compilation and dictionary directly.
A same-site static shell constructs both expression fields of the original
JointBody extraction internally. Source context, scope, id, lowered value and
minimum compiler fuel remain exact. This is a compiler child collector, not a
body meaning theorem. The method expression Tree/head interpretation and the
joint graded family still require their genuine static and semantic producers.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalCompilerChildren
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory (StaticInputs)
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericImperativeMatch

section Accepted
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- The actual compiler action is retained before any expression Tree is
constructed. The separate readFuel indexes the receiving static body grammar. -/
inductive AcceptedAt (expressionSyntax : TypedSource → ExpressionId → Prop) (readFuel : Nat)
    (source : TypedSource) (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate where
  | intro {scope id node lowered compilerFuel residualMode}
      (found : source.lookupExpression? id = some node)
      (typed : ExpressionHasType source sourceContext id node.type)
      (allowed : expressionSyntax source id)
      (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
      (closed : sourceContext.typeVariables = [])
      (residual : sourceContext.residualTypeVariables = residualMode)
      (signatures : sourceContext.signatures = compiled.compatible.checked.signatures)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
        compilerFuel (context compiled.indexed named) source scope id rootReasonAt = .ok lowered) :
      AcceptedAt expressionSyntax readFuel source sourceContext scope id lowered

def certificates (expressionSyntax : TypedSource → ExpressionId → Prop) :
    Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  AcceptedAt root expressionSyntax

end Accepted

section Principal
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) principal.named principal.cached.diagnostics principal.cached.code
    principal.cached.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (site : Site compiled.indexed principal.named parameters result statements sourceContext principal.dictionary [] scope administrative)

/-- The real selected method Site fixes the physical prefix. No ordinary
Header or equality between independent body and receiving registries is used. -/
structure SiteShell where
  issued : IssuedSource compiled site.code.compilation.owner (source principal.named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  entry : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) site.code
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
    (closure principal.named parameters result statements sourceContext principal.dictionary [])
  readFuel : Nat
  canonical : site.code.view = source principal.named
  compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained principal.named site.code
  issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained principal.named site.code
  unique : NodeOccurrencesUnique (source principal.named)
  sameLedger : sourceContext.solvedRequirements = site.code.compilation.solvedRequirements
  syntaxTree : Syntax (source principal.named) (expressionSyntax (source principal.named))
    entry.context (.statements true statements) result
  projection : compiled.compatible.checked.catalog.project result = .ok site.code.receipt.resultCore
  residualMode : Bool
  static : StaticInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
    (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
    (globals := compiled.indexed.base.globals.length) (onError := site.code.allocationError)
    (values := .initial compiled.compatible.checked) (source := site.code.view)
    (expressionSyntax := expressionSyntax site.code.view) (reasonAt := site.code.reasonAt)
    (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
    (invalidOperand := issued.invalidOperand) (invalidUnary := issued.invalidUnary)
    (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
    residualMode (bodyPolicy principal.cached.compilation site.code) entry.context
    (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
  nativeTyped : HasType (SourceCoreLocalCell.coreContext
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative)
    site.code.receipt.body (LanguageResult.resultType site.code.receipt.resultCore) compiled.indexed.layouts.definitions

/-- This is the exact callback used by the method's original body recipe. -/
theorem body_expression : (bodyPolicy principal.cached.compilation site.code).lowerExpression =
    FunctionCode.children site.code.policy site.code.lowerBody site.code.fuel site.code.compilation := rfl

/-- The original minimum fuel stays inside the authentic accepted compiler
receipt. Source typing and lexical context are its actual supplied indices. -/
theorem accepted_child
    (policyEq : site.code.policy = root.selected.policy)
    (bodyEq : site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : site.code.reasonAt = rootReasonAt)
    {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {residualMode : Bool}
    (closed : currentContext.typeVariables = []) (residual : currentContext.residualTypeVariables = residualMode)
    (signatures : currentContext.signatures = compiled.compatible.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations site.code.view childScope currentContext)
    (allowed : expressionSyntax site.code.view id) (found : site.code.view.lookupExpression? id = some node)
    (typed : ExpressionHasType site.code.view currentContext id node.type)
    (accepted : (bodyPolicy principal.cached.compilation site.code).lowerExpression fuel
      site.code.view childScope id site.code.reasonAt = .ok lowered)
    (readFuel : Nat) :
    AcceptedAt root expressionSyntax readFuel site.code.view currentContext childScope id lowered := by
  rw [body_expression, FunctionCode.children, policyEq, bodyEq, reasonEq, site.compilation] at accepted
  exact .intro found typed allowed declarations closed residual signatures accepted

/-- Both expression certificate fields of the existing collector are built
from actual callback acceptance. Every remaining field comes from the same
Site shell. No completed expression or body law is an input. -/
def SiteShell.extraction (shell : SiteShell principal expressionSyntax site)
    (policyEq : site.code.policy = root.selected.policy)
    (bodyEq : site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : site.code.reasonAt = rootReasonAt) :
    ExtractionInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
      (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
      (globals := compiled.indexed.base.globals.length) (onError := site.code.allocationError)
      (values := .initial compiled.compatible.checked) (source := site.code.view)
      (expressionSyntax := expressionSyntax site.code.view) (certificates := certificates root expressionSyntax shell.readFuel site.code.view)
      (reasonAt := site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
      (invalidOperand := shell.issued.invalidOperand) (invalidUnary := shell.issued.invalidUnary)
      (invalidProjection := shell.issued.invalidProjection) (missingDefault := shell.issued.missingDefault)
      shell.residualMode (bodyPolicy principal.cached.compilation site.code) shell.entry.context
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) where
  matchCompilation := shell.static.matchCompilation
  matchPolicy := shell.static.matchPolicy
  matchValues := shell.static.matchValues
  matchDefinitions := shell.static.matchDefinitions
  matchAllocator := shell.static.matchAllocator
  matchChildStatic := MatchChildStatic.of_hidden shell.static.hidden
  readPolicy := shell.static.readPolicy
  binderPolicy := shell.static.binderPolicy
  allocationPolicy := shell.static.allocationPolicy
  expressions := by
    intro currentContext closed residual signatures childScope fuel id node lowered declarations allowed found typed accepted
    exact accepted_child principal root expressionSyntax site policyEq bodyEq reasonEq closed residual signatures
      declarations allowed found typed accepted shell.readFuel
  assignments := shell.static.assignments
  unaries := shell.static.unaries
  assignmentExpressions := by
    intro currentContext childScope fuel id lowered closed residual signatures declarations allowed node found typed accepted
    exact ⟨accepted_child principal root expressionSyntax site policyEq bodyEq reasonEq closed residual signatures
      declarations allowed found typed accepted shell.readFuel,
      shell.static.assignmentNative currentContext childScope fuel id lowered closed residual signatures declarations allowed
        node found typed accepted⟩
  closed := shell.static.closed
  residual := shell.static.residual
  sourceSignatures := shell.static.sourceSignatures
  declarations := shell.static.declarations
  ledger := shell.static.ledger

/-- The real method dictionary remains in the Source closure and retained
Support. A positive constructor requires the actual selected Site, its recipe,
original typed body and the real owning issuance. -/
inductive Collected : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code → Prop where
  | recaptured
      (shell : SiteShell principal expressionSyntax site)
      (body : JointBody principal.cached.compilation site.code (Program.ofChecked compiled.sourceProgram)
        expressionSyntax (certificates root expressionSyntax) shell.diagnosticPolicy
        shell.issued.invalidOperand shell.issued.invalidUnary shell.issued.invalidProjection shell.issued.missingDefault)
      (policyEq : site.code.policy = root.selected.policy)
      (bodyEq : site.code.lowerBody = root.selected.lowerBody)
      (reasonEq : site.code.reasonAt = rootReasonAt)
      (entryEq : body.toContext = shell.entry)
      (readFuelEq : body.readFuel = shell.readFuel)
      (binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy principal.named site.code)
      (environment : Dynamic.Environment) :
      Collected (RecursiveNamedLambdaFormationHeads.recaptureCode
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code environment)
        ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site principal site expressionSyntax
          (certificates root expressionSyntax) shell.issued shell.diagnosticPolicy body).recapture environment)

/-- The original joint producer runs once, at the actual method Site and its
body recipe. No preconstructed final joint body is asked of the shell. -/
theorem SiteShell.collected (shell : SiteShell principal expressionSyntax site)
    (policyEq : site.code.policy = root.selected.policy)
    (bodyEq : site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : site.code.reasonAt = rootReasonAt)
    (environment : Dynamic.Environment) :
    ∃ body : JointBody principal.cached.compilation site.code (Program.ofChecked compiled.sourceProgram)
        expressionSyntax (certificates root expressionSyntax) shell.diagnosticPolicy
        shell.issued.invalidOperand shell.issued.invalidUnary shell.issued.invalidProjection shell.issued.missingDefault,
      body.toContext = shell.entry ∧ body.readFuel = shell.readFuel ∧
      Collected principal root expressionSyntax site
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code environment)
        ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site principal site expressionSyntax
          (certificates root expressionSyntax) shell.issued shell.diagnosticPolicy body).recapture environment) := by
  have recipe : BodyRecipe principal.cached.compilation site.code := bodyEq.trans root.selected.recipe
  have binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy principal.named site.code :=
    (congrArg SourceCoreFunctions.Policy.lowerBinder policyEq).trans root.selected.binder
  have edited : LocalView (source principal.named) site.code.view [] := by
    rw [shell.canonical]
    exact LocalView.refl _
  obtain ⟨body, entryEq, readFuelEq⟩ := at_site principal.cached.compilation site recipe
    (Program.ofChecked compiled.sourceProgram) shell.entry shell.frame expressionSyntax (certificates root expressionSyntax)
    shell.readFuel shell.diagnosticPolicy shell.issued.invalidOperand shell.issued.invalidUnary
    shell.issued.invalidProjection shell.issued.missingDefault
    edited (by intro id member; cases member)
    shell.unique shell.sameLedger
    (by intro id reached allowed; simpa only [shell.canonical] using allowed)
    (by intro currentContext childScope id lowered reached given; simpa only [shell.canonical] using given)
    shell.syntaxTree (shell.canonical.symm ▸ shell.syntaxTree) shell.projection
    (SiteShell.extraction principal root expressionSyntax site shell policyEq bodyEq reasonEq) shell.nativeTyped
  exact ⟨body, entryEq, readFuelEq,
    .recaptured shell body policyEq bodyEq reasonEq entryEq readFuelEq binderPolicy environment⟩

variable {function : Dynamic.Closure} {currentScope : SourceCoreLocalCell.Scope}
  {currentAdministrative : Core.Context} {code : Code compiled.indexed function currentScope currentAdministrative}
  {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}

/-- The real selected dictionary and same accepted child family remain
available after recapture; there is no certificate equality premise. -/
theorem Collected.factories
    (collected : Collected principal root expressionSyntax site code support) :
    support.method = method ∧ HEq support.principal principal ∧
      support.expressionSyntax = expressionSyntax ∧ support.certificates = certificates root expressionSyntax := by
  cases collected with
  | recaptured shell body policyEq bodyEq reasonEq entryEq readFuelEq binderPolicy environment =>
    exact ⟨rfl, HEq.rfl, rfl, rfl⟩

theorem Collected.prepared
    (collected : Collected principal root expressionSyntax site code support) :
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support := by
  cases collected with
  | recaptured shell body policyEq bodyEq reasonEq entryEq readFuelEq binderPolicy environment =>
    exact .recaptured principal site expressionSyntax (certificates root expressionSyntax)
      shell.issued shell.diagnosticPolicy body binderPolicy shell.compilerPolicy shell.issuedRecipe
      (CallableIndexedOwnedContextualLambdaProvenance.BodyView.of_eq shell.canonical) environment

end Principal

section ActualRoot
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

/-- The full authentic method record selects the root policy from the real
contextual pass once. No top-level function instantiation or Header is invented. -/
theorem root_of_accepted
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext principal.named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals principal.cached.compilation.parents principal.cached.compilation.own.assignments
      principal.cached.diagnostics (context compiled.indexed principal.named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered) :
    Nonempty (RootPolicyReceipt (compiled := compiled) principal.named principal.cached.diagnostics principal.cached.code
      principal.cached.compilation fuel view scope id reasonAt lowered) :=
  RootPolicyReceipt.of_accepted principal.cached.compilation principal.record accepted

end ActualRoot
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalCompilerChildren
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCompiledQualification
/-! A concrete compiler qualification selects actual ordinary compiler factories
from the finite Header inventory, or actual selected method factories from their
Principal authority. Each constructor retains the chosen root policy and same
recaptured body. It does not quantify arbitrary Support certificates. This one
facet plugs into the generic qualified function/payload/heap model. The ordinary
collector has an existing actual Tree producer; the method accepted-child packet
still needs its genuine finite method Tree/head producer before family closure.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCompiledQualification
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet QualifiedAssociation)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Only the actual named inventory can authorize the ordinary branch. The
selected compiler receipt is retained through the Collected constructor. -/
inductive Ordinary
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) :
    {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code → Prop where
  | actual {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
      (member : caller ∈ headers)
      {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
      {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
        rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      {code : Code compiled.indexed function scope administrative}
      {support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code}
      (collected : CallableIndexedOwnedPreparedCompilerChildCollector.Collected root expressionSyntax code support) :
      Ordinary headers code support

/-- The Principal carries the selected implementation, full dictionary and
cached compiler row. There is no ordinary Header in this constructor. -/
inductive Principal : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code → Prop where
  | actual {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
      {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
      (root : RootPolicyReceipt (compiled := compiled) principal.named principal.cached.diagnostics principal.cached.code
        principal.cached.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      (site : Site compiled.indexed principal.named parameters result statements sourceContext principal.dictionary [] scope administrative)
      {function : Dynamic.Closure} {currentScope : SourceCoreLocalCell.Scope} {currentAdministrative : Core.Context}
      {code : Code compiled.indexed function currentScope currentAdministrative}
      {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}
      (collected : CallableIndexedOwnedPreparedPrincipalCompilerChildren.Collected
        principal root expressionSyntax site code support) :
      Principal code support

/-- Both facets are actual positive compiler constructors. Payload/heap
operations need only this one FunctionModel instantiation. -/
def facet (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) : Facet compiled where
  ordinary := fun code support => Ordinary headers code support
  principal := fun code support => Principal code support

section Positive
variable
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)

/-- Formation can register the exact compiled ordinary packet immediately.
No inverse on an arbitrary existing positive payload or heap is involved. -/
def ordinary_association
    (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
    (callerGlobals : support.caller.globals = compiled.indexed.base.globals.length)
    (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
    (collected : Ordinary headers code support)
    (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
      .reachable bodyRegistry faults)
    (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
    (origin : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.SourceOrigin support history)
    (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial compiled.compatible.checked) support.caller)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
    (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
    (typed : RuntimeValueHasType world (value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
    QualifiedAssociation (facet headers) headers keys bodyRegistry faults mapping world function
      (value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual) code.receipt.loweredParameters
      code.receipt.parameterCore code.receipt.resultCore :=
  ⟨.ordinary (.ordinary owner captured code history support actualSites sites origin prepared
    prefixContext globals referenceIndex typed callerGlobals callerReceipt), collected⟩

/-- The corresponding actual Principal packet keeps its real dictionary and
leading method bundle, at the same body and carrier. -/
def principal_association
    (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
    (collected : Principal code support)
    (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
      .reachable bodyRegistry faults)
    (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
    (origin : CallableIndexedOwnedPreparedPrincipalLambdaSupport.SourceOrigin support history)
    (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
    (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
    (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
    (typed : RuntimeValueHasType world (value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
    QualifiedAssociation (facet headers) headers keys bodyRegistry faults mapping world function
      (value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual) code.receipt.loweredParameters
      code.receipt.parameterCore code.receipt.resultCore :=
  ⟨.principal (.principal owner captured code history support actualSites sites origin prepared
    globals leading referenceIndex typed), collected⟩

end Positive
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCompiledQualification
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalFormationReceipts
/-! One original principal formation produces the genuine Source/native trace.
The formation copies the captured cells, so the retained prepared principal
support constructs its prospective positive receipt for the formed closure over
the copies. The same trace adds Source admission and the existing positive post
at the reached packet transported to the formed state. No old StaticMember
is inverted and no body callback is supplied. The current payload model still
stores the forward plain leaf; migration to prepared leaves remains separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedPrincipalLambdaSupport (Support PreparedAt Receipt)
open CallableIndexedOwnedContextualCellOrigins (CellOrigins PostWithOrigins)
open CallableIndexedOwnedSourceAdmission

section Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The prepared principal seed of a code is the seed of the same code over
other captures. -/
theorem prepared_recapture {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code} (prepared : PreparedAt code support) (environment : Dynamic.Environment) :
    PreparedAt (code.recapture environment) (support.recapture environment) := by
  cases prepared with
  | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView _ =>
    exact .recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView environment

/-- A prepared principal code is the lambda of a selected method Site, which
copies its captures. -/
theorem prepared_snapshots {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code} (prepared : PreparedAt code support) :
    code.policy.snapshotLambda code.id = true := by
  cases prepared with
  | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView environment =>
    exact site.snapshots

end Prepared

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : PreparedAt code support)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "plain" => support.plain actualSites sites
local notation "history" => CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
  captured code plain owner initial packet
local notation "carrier " formed:max => value code (Formed.embedding formed)
  (CallableIndexedLambdaValues.History.native history) (Formed.closureActual formed)

include actualSites sites packet prepared profile in
/-- The authentic method factory runs once and copies the captured cells.
Preparation is retained from its own support, recaptured at the copies, and
runtime typing comes from that actual formed value. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (carrier formed)) formed.finalStore ∧
      Nonempty (Receipt headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (carrier formed)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (carrier formed) ∧
          finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation
      captured code plain owner initial packet profile heaps (prepared_snapshots prepared) ordinary coercions
  have typed : RuntimeValueHasType formed.finalWorld (carrier formed)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions :=
    (CallableIndexedOwnedMethodLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
      (registry := bodyRegistry) represented
  have leading : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code plain owner initial packet
  exact ⟨formed, sourceTrace, nativeTrace,
    ⟨.principal (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) actualSites sites ⟨rfl⟩ (prepared_recapture prepared formed.captured)
      (packet.observed.of_slots formed.slots) leading
      (CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code plain) typed⟩,
    determined⟩

variable
  (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include actualSites sites cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile in
/-- The prepared receipt and current positive post accompany the same actual
Source/native formation over the copies, at the reached packet transported to
the formed state. The factory is invoked once; only the new value erases
forward into the current plain positive model. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
        captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (carrier formed)) formed.finalStore ∧
      Nonempty (Receipt headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (carrier formed)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore) ∧
      (∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner
          support.principal.named).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩,
        (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates
          ⟨initial, packet⟩ reached ∧
        PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
          function.context profile code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure))
          (.inRight .word (carrier formed)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (carrier formed) ∧
          finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code support actualSites sites prepared owner initial packet profile cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure))
      (.inRight .word (carrier formed)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    obtain ⟨receipt⟩ := member
    exact CallableIndexedOwnedContextualCellOrigins.payload_static_member (registry := registry) profile ⟨receipt.forget⟩
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
    (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member,
    ⟨reached, related,
      CallableIndexedOwnedContextualCellOrigins.post_at_same_state
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        profile reached post formed.heaps represented⟩,
    determined⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalFormationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedQualifiedExpressionOutputs
/-! The qualified model has one genuine closure inversion and one reached
expression output. Both retain the original compiler qualification. Allocation,
write and nested payload operations are the existing generic operations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedQualifiedExpressionOutputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification
open CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (qualification : Facet compiled)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}
  {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}

/-- The qualified leaf is installed at formation before generic payload
construction; no current or General leaf is upgraded. -/
theorem payload_static_member {function : Dynamic.Closure}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result) :=
  .function (.closure member)

/-- A closure child keeps its actual qualification through compatible wrappers
and every genuine positive payload constructor. This is a Source-shape inverse. -/
theorem closure_member
    (origin : PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world
      sourceType source native type) :
    ∀ function, source = .closure function →
      ∃ bindings parameter result,
        StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
        type = CallableContract.functionType parameter result := by
  induction origin using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
      cases related with
      | closure member =>
          intro function same
          cases same
          exact ⟨_, _, _, member, rfl⟩
      | global related => intro function impossible; cases impossible
      | builtin related => intro function impossible; cases impossible
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
      intro function impossible
      cases impossible
  | nil | cons | empty | entry | absent | present => trivial

/-- This is the original reached packet with qualified cells and the actual
qualified result. Its fields contain no body or family execution callback. -/
structure Post
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun _ => True) callerProtocol)
    (context : SourceSemantics.Context)
    (qualification : Facet compiled)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (sourceType : TypeSystem.Ty) (type : Ty)
    (outcome : Dynamic.ExpressionOutcome) (value : Value)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  admission : PostAdmission bridge context sourceType outcome reached
  cells : CellOrigins qualification headers keys bodyRegistry registry faults profile
    index.mapping index.world index.heap index.store
  result : FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functions qualification headers keys bodyRegistry faults profile))
    index.mapping index.world sourceType type faults outcome value

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedQualifiedExpressionOutputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedQualifiedFormationReceipts
/-! Actual ordinary and selected-method formation directly construct the stronger
compiler-qualified prepared closure leaf. Each factory runs once at its
authentic input packet.
Incoming qualified cells remain at that unchanged heap and store; the actual
Source trace establishes admission there. The receiving registry is explicit
and independent of body preparation. No legacy ResultAt projection, old-leaf
upgrade or semantic body callback is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedQualifiedFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualQualification (Facet StaticMember CellOrigins functions)
open CallableIndexedOwnedPreparedQualifiedExpressionOutputs (Post)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (qualification : Facet compiled)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

namespace Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (callerGlobals : support.caller.globals = compiled.indexed.base.globals.length)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  (qualified : ∀ environment, qualification.ordinary (code.recapture environment) (support.recapture environment))
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

local notation "plain" => CallableIndexedOwnedPreparedOrdinaryBodyProjection.plain support actualSites sites
local notation "history" => CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
  captured code plain owner initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

include callerGlobals callerReceipt actualSites sites packet prepared profile qualified prefixContext observed in
/-- The ordinary factory's actual trace and runtime typing justify the one new
leaf. Preparation comes directly from the retained support at that same Code. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual))
        formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedGeneralLambdaValues.ordinary_lambda_of_formation initial owner captured code history plain
      (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.source_origin captured code plain owner initial packet)
      prefixContext observed (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reference_index captured code plain)
      rfl profile heaps (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.prepared_snapshots prepared) ordinary coercions
  have typed : RuntimeValueHasType formed.finalWorld (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions :=
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
      (registry := bodyRegistry) represented
  exact ⟨formed, sourceTrace, nativeTrace,
    ⟨⟨.ordinary (.ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) actualSites sites ⟨rfl⟩
      (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.prepared_recapture prepared formed.captured)
      prefixContext (observed.of_slots formed.slots)
      (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reference_index captured code plain) typed callerGlobals callerReceipt), qualified formed.captured⟩⟩,
    determined⟩

variable
  (cells : CellOrigins qualification headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include callerGlobals callerReceipt actualSites sites cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile qualified prefixContext observed in
/-- Strong cells and the newly prepared value accompany the original formation
at its unchanged actual packet. Only the real trace establishes Source admission. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile)) captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual))
        formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, canonical⟩,
        (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
        Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
          function.context qualification profile code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code owner qualification profile support callerGlobals callerReceipt qualified actualSites sites prepared initial packet prefixContext observed
    cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedPreparedQualifiedExpressionOutputs.payload_static_member (registry := registry) qualification profile member
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller) (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner support.caller)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, ⟨post, formed.heaps, represented⟩⟩,
    determined⟩

end Ordinary

namespace Principal
variable
  (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (qualified : ∀ environment, qualification.principal (code.recapture environment) (support.recapture environment))
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

local notation "plain" => support.plain actualSites sites
local notation "history" => CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
  captured code plain owner initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

include actualSites sites packet prepared profile qualified in
/-- The original method producer runs once with actual selected dictionary
authority. The same real Support enters the qualified prepared leaf directly. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual))
        formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation
      captured code plain owner initial packet profile heaps
      (CallableIndexedOwnedPreparedPrincipalFormationReceipts.prepared_snapshots prepared) ordinary coercions
  have typed : RuntimeValueHasType formed.finalWorld (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions :=
    (CallableIndexedOwnedMethodLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
      (registry := bodyRegistry) represented
  have leading : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code plain owner initial packet
  exact ⟨formed, sourceTrace, nativeTrace,
    ⟨⟨.principal (.principal (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) actualSites sites ⟨rfl⟩
      (CallableIndexedOwnedPreparedPrincipalFormationReceipts.prepared_recapture prepared formed.captured)
      (packet.observed.of_slots formed.slots) leading
      (CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code plain) typed),
      qualified formed.captured⟩⟩,
    determined⟩

variable
  (cells : CellOrigins qualification headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include actualSites sites cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile qualified in
/-- The actual formed carrier and unchanged principal packet receive strong
prepared cells/result without projecting to a one-registry legacy contract. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile)) captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual))
        formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩,
        (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
        Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
          function.context qualification profile code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code owner qualification profile support qualified actualSites sites prepared initial packet
    cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedPreparedQualifiedExpressionOutputs.payload_static_member (registry := registry) qualification profile member
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named) (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, ⟨post, formed.heaps, represented⟩⟩,
    determined⟩

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedQualifiedFormationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectFormationReceipts
/-! Authentic ordinary and selected Principal packets supply the actual frame
read for one original Code formation. The formation copies the captured cells;
the new leaf keeps that same prepared body, recaptured at the copies, and the
static qualification of the recaptured Code without manufacturing universal
diagnostic laws. The real trace supplies admission at the original pool
transported to the formed heap and store. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (StaticMember CellOrigins Post functions)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (qualification : Facet compiled)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

namespace Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (qualified : ∀ environment, qualification.ordinary (code.recapture environment) (support.recapture environment))
  (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

/-- This exact owned row and original Header seed construct lexical history. -/
def history_at : History code where
  native := (initial.rows owner.position).authority.current
  ghost := (initial.rows owner.position).authority.ghost
  metadata := CallableIndexedNamedGeneration.state support.caller.named
  carried := packet.carried
  source := support.source.symm
  owner := by rw [support.compilation]; rfl
  active := support.active.symm

include support in
theorem reference_index : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  rw [CallableIndexedLambdaValues.Code.referenceIndex, support.compilation]
  rfl

local notation "history" => history_at captured code owner support initial packet
local notation "carrier " formed:max => value code (Formed.embedding formed)
  (CallableIndexedLambdaValues.History.native history) (Formed.closureActual formed)

include packet prepared qualified profile prefixContext observed in
/-- One elementary actual formation copies the captured cells and supplies
Source/native traces and runtime typing; the direct positive constructor
retains the prepared packet, recaptured at the copies, for the formed closure. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (carrier formed)) formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (carrier formed) code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (carrier formed) ∧ finalStore = formed.finalStore) := by
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [reference_index captured code support]
    exact observed.reference
  have read : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
        (CallableIndexedLambdaValues.History.native history)) := by
    have actualRead := (initial.rows owner.position).authority.frame.read
    rw [(initial.rows owner.position).frame_eq] at actualRead
    exact actualRead
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured code history
    (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.prepared_snapshots prepared)
    (reference_index captured code support) heaps reference read
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := bodyRegistry) (formed.represents heaps.runtime_hasTypes)
  exact ⟨formed, formed.source _ ordinary coercions, formed.evaluated,
    ⟨.ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨rfl⟩
      (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.prepared_recapture prepared formed.captured)
      (qualified formed.captured) prefixContext (observed.of_slots formed.slots)
      (reference_index captured code support) typed⟩,
    fun _ _ completed => Core.evaluation_deterministic completed formed.evaluated⟩

variable
  (cells : CellOrigins qualification headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile qualified prefixContext observed in
/-- The caller packet, transported to the formed state, keeps incoming direct
cells over the copies and the newly formed direct result. Admission comes from
the actual Source trace. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
        captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (carrier formed)) formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (carrier formed) code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, canonical⟩,
        (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
        Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
          function.context qualification profile code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure)) (.inRight .word (carrier formed)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (carrier formed) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code owner qualification profile support qualified prepared initial packet prefixContext observed
    cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (carrier formed)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedPreparedNativeDirectCellOrigins.payload_static_member (registry := registry) profile member
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner support.caller)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := after_expression
    (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, post, formed.heaps, represented⟩, determined⟩

end Ordinary

namespace Principal

section Prepared
open CallableIndexedOwnedPreparedPrincipalLambdaSupport (Support PreparedAt)

/-- The prepared principal seed of a code is the seed of the same code over
other captures. -/
theorem prepared_recapture {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code} (prepared : PreparedAt code support) (environment : Dynamic.Environment) :
    PreparedAt (code.recapture environment) (support.recapture environment) := by
  cases prepared with
  | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView _ =>
    exact .recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView environment

/-- A prepared principal code is the lambda of a selected method Site, which
copies its captures. -/
theorem prepared_snapshots {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code} (prepared : PreparedAt code support) :
    code.policy.snapshotLambda code.id = true := by
  cases prepared with
  | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView environment =>
    exact site.snapshots

end Prepared

variable
  (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (qualified : ∀ environment, qualification.principal (code.recapture environment) (support.recapture environment))
  (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

/-- Selected method authority supplies its original dictionary-bearing seed. -/
def history_at : History code where
  native := (initial.rows owner.position).authority.current
  ghost := (initial.rows owner.position).authority.ghost
  metadata := CallableIndexedNamedGeneration.state support.principal.named
  carried := packet.carried
  source := support.source.symm
  owner := by rw [support.compilation]; rfl
  active := support.active.symm

include packet in
theorem leading : captured.administrative[0]? = some support.principal.named.signature.parameterType := by
  have bundle := packet.bundle
  rw [captured.represented.runtime_hasTypes.type_tags] at bundle
  simpa [SourceCoreLocalCell.coreContext, List.getElem?_append] using bundle

include support in
theorem reference_index : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  rw [CallableIndexedLambdaValues.Code.referenceIndex, support.compilation]
  rfl

local notation "history" => history_at captured code owner support initial packet
local notation "carrier " formed:max => value code (Formed.embedding formed)
  (CallableIndexedLambdaValues.History.native history) (Formed.closureActual formed)

include packet prepared qualified profile in
/-- The real Principal frame read and the same Code's elementary formation,
which copies the captured cells, construct one direct selected-method member
for the formed closure without an ordinary Header. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (carrier formed)) formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (carrier formed) code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (carrier formed) ∧ finalStore = formed.finalStore) := by
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [reference_index captured code support]
    exact packet.observed.reference
  have read : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
        (CallableIndexedLambdaValues.History.native history)) := by
    have actualRead := (initial.rows owner.position).authority.frame.read
    rw [(initial.rows owner.position).frame_eq] at actualRead
    exact actualRead
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured code history (prepared_snapshots prepared)
    (reference_index captured code support) heaps reference read
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := bodyRegistry) (formed.represents heaps.runtime_hasTypes)
  have leadingFormed : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    leading captured code owner support initial packet
  exact ⟨formed, formed.source _ ordinary coercions, formed.evaluated,
    ⟨.principal (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨rfl⟩ (prepared_recapture prepared formed.captured)
      (qualified formed.captured) (packet.observed.of_slots formed.slots) leadingFormed
      (reference_index captured code support) typed⟩,
    fun _ _ completed => Core.evaluation_deterministic completed formed.evaluated⟩

variable
  (cells : CellOrigins qualification headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile qualified in
/-- Selected Principal formation keeps the actual packet, transported to the
formed state, with direct cells over the copies and the represented result,
with its independently indexed receiving registry. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
        captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (carrier formed)) formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (carrier formed) code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner
          support.principal.named).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩,
        (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates
          ⟨initial, packet⟩ reached ∧
        Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
          function.context qualification profile code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure)) (.inRight .word (carrier formed)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (carrier formed) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code owner qualification profile support qualified prepared initial packet cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (carrier formed)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedPreparedNativeDirectCellOrigins.payload_static_member (registry := registry) profile member
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
    (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := after_expression
    (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, post, formed.heaps, represented⟩, determined⟩

end Principal
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectFormationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeads
/-! A finite raw compiler skeleton retains each accepted lambda or indirect
call before native body collection. The actual Named compilation and selected
caller evidence remain explicit. No lambda Site, native typing, JointBody,
completed Tree or semantic execution law is required by the producer. A later
refinement must use this same Tree and these same accepted compiler receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedPrincipalCompilerChildren
open CallableIndexedOwnedPreparedMixedCompilerHeads (extraForm extraChildren)
open RecursiveNamedExpressionCompilerCertificates
open RecursiveNamedCallSelectionCertificates CallableAncestryPairedLookup

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {readFuel : Nat}
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The same actual Named compiler owns both indirect actions. -/
structure IndirectReceipt (fuel : Nat) (id callee : ExpressionId) (ids : List ExpressionId)
    (metadata : IndirectCallResolution) (lowered : SourceCoreBasic.LoweredExpr) where
  compiler : CallableIndirectCallCertificates.Receipt root.selected.policy root.selected.lowerBody fuel
    (context compiled.indexed named) (source named) scope id callee ids metadata rootReasonAt lowered
  prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler compiled.indexed.ancestry.graph.inputs.callable
  sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler
  parentMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source named)
    id compiler.original compiler.type
  positions : compiler.entries.map Prod.fst = callee :: ids
  physicalCount : ids.length = compiler.codes.length
  generated : ∀ child code, (child, code) ∈ compiler.entries → ∃ childNode,
    (source named).lookupExpression? child = some childNode ∧
    ExpressionHasType (source named) sourceContext child childNode.type ∧
    SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody fuel
      (context compiled.indexed named) (source named) scope child rootReasonAt = .ok code

/-- Raw lambda leaves retain the literal accepted compiler action and its
Source read/type metadata. Indirect leaves retain their actual ordered actions.
The selected named evidence remains the same explicit inventory alternative. -/
inductive Head (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | named {childScope id lowered}
      (head : RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers
        (context compiled.indexed named) (source named) sourceContext children childScope id lowered) :
      Head children childScope id lowered
  | lambda {childFuel id lowered node parameters result statements reported}
      (allowed : expressionSyntax (source named) id)
      (found : (source named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed named) (source named) scope id node parameters result statements
        reported rootReasonAt lowered)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
        (context compiled.indexed named) (source named) scope id rootReasonAt = .ok lowered)
      (typed : ExpressionHasType (source named) sourceContext id node.type)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source named) id node lowered.type) :
      Head children scope id lowered
  | indirect {childFuel id lowered node callee ids metadata}
      (found : (source named).lookupExpression? id = some node)
      (form : node.form = .call callee ids (.indirect metadata))
      (receipt : IndirectReceipt root (sourceContext := sourceContext) (scope := scope)
        childFuel id callee ids metadata lowered)
      (ordered : ∀ child code, (child, code) ∈ receipt.compiler.entries → children scope child code) :
      Head children scope id lowered

theorem include_named {children childScope id lowered}
    (head : RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers
      (context compiled.indexed named) (source named) sourceContext children childScope id lowered) :
    Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope)
      children childScope id lowered := .named head

theorem projected {children childScope id lowered node}
    (head : Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope)
      children childScope id lowered)
    (found : (source named).lookupExpression? id = some node) :
    compiled.compatible.checked.catalog.project node.type = .ok lowered.type := by
  cases head with
  | named actual =>
      cases callerEvidence with
      | none =>
          cases actual with
          | named _ metadata _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              have same := Option.some.inj (metadata.found.symm.trans found)
              exact same ▸ metadata.projected
      | some evidence => exact RecursiveNamedCallEvidenceHeads.projected actual found
  | lambda _ actualFound _ _ _ _ metadata =>
      have same := Option.some.inj (actualFound.symm.trans found)
      exact same ▸ metadata.projected
  | indirect _ _ receipt _ =>
      have same := Option.some.inj (receipt.compiler.found.symm.trans found)
      have emitted := congrArg SourceCoreBasic.LoweredExpr.type receipt.compiler.output
      simpa only [same, emitted] using receipt.parentMetadata.projected

/-- Finite syntax, selected declaration and original policy obligations remain
static. No field requests a native child witness or a finished call Tree. -/
structure Domain : Prop where
  admission : AdmissionWith extraForm extraChildren (source named) (expressionSyntax (source named))
  coverage : ReachedCoverage headers (context compiled.indexed named) (source named)
    (expressionSyntax (source named))
  sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes headers sourceContext
  emptyEvidence : SelectedEmptyEvidence headers (context compiled.indexed named) (source named)
    (expressionSyntax (source named))
  order : ∀ id callee arguments instantiation node, expressionSyntax (source named) id →
    (source named).lookupExpression? id = some node → node.form = .call callee arguments (.declaration instantiation) →
    Ordered (context compiled.indexed named).plan instantiation
  constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw (source named) sourceContext
    (expressionSyntax (source named))
  fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw (source named) sourceContext
    (CompatibleExpressionBuiltins.Syntax (source named))
  selectedValid : SelectedDeclarationLaw headers (context compiled.indexed named) (source named)
    sourceContext (expressionSyntax (source named))
  basePolicy : PolicyForWith (headers := headers) callerEvidence root.selected.policy
    (context compiled.indexed named) readFuel (.initial compiled.compatible.checked)
    (source named) sourceContext scope rootReasonAt
    (CallableIndexedOwnedPreparedMixedCompilerCertificates.baseAdmitted
      (source named) (expressionSyntax (source named)))
  fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax (source named) id →
    (source named).lookupExpression? id = some node → node.coercions = []
  coercions : ∀ id node, expressionSyntax (source named) id →
    (source named).lookupExpression? id = some node → node.coercions = []
  empty : ∀ id node, expressionSyntax (source named) id →
    (source named).lookupExpression? id = some node → extraForm node.form → node.requirements = [] ∧ node.coercions = []
  ordinary : ∀ id node, expressionSyntax (source named) id →
    (source named).lookupExpression? id = some node → extraForm node.form →
    compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id node callee ids metadata, expressionSyntax (source named) id →
    (source named).lookupExpression? id = some node → node.form = .call callee ids (.indirect metadata) →
    metadata.argumentCoercions = []

private theorem extra_cases {form : ExpressionForm} (extra : extraForm form) :
    (∃ parameters result statements, form = .lambda parameters result statements) ∨
      ∃ callee ids metadata, form = .call callee ids (.indirect metadata) := by
  cases form <;> simp only [extraForm] at extra
  case lambda parameters result statements => exact .inl ⟨parameters, result, statements, rfl⟩
  case call callee ids resolution =>
    cases resolution <;> simp only at extra
    case indirect metadata => exact .inr ⟨callee, ids, metadata, rfl⟩

private theorem pointwise_extra
    (domain : Domain root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope) (readFuel := readFuel))
    {id : ExpressionId} {node : ExpressionNode} (allowed : expressionSyntax (source named) id)
    (found : (source named).lookupExpression? id = some node) (extra : extraForm node.form) :
    PointwiseFor root (source named) scope id rootReasonAt := by
  obtain ⟨requirements, coercions⟩ := domain.empty id node allowed found extra
  have ordinary := domain.ordinary id node allowed found extra
  rcases extra_cases extra with ⟨parameters, result, statements, form⟩ | ⟨callee, ids, metadata, form⟩
  · exact lambda_policy root found form requirements coercions ordinary
  · exact indirect_policy root found form requirements coercions (domain.arguments id node callee ids metadata allowed found form) ordinary

theorem policy_for_all
    (domain : Domain root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope) (readFuel := readFuel)) :
    PolicyForWith (headers := headers) callerEvidence root.selected.policy
      (context compiled.indexed named) readFuel (.initial compiled.compatible.checked)
      (source named) sourceContext scope rootReasonAt (expressionSyntax (source named)) where
  fragment := domain.basePolicy.fragment
  route := by
    intro id node allowed found
    by_cases extra : extraForm node.form
    · exact .inl (pointwise_extra root expressionSyntax callerEvidence headers domain allowed found extra).special
    · exact domain.basePolicy.route id node ⟨allowed, node, found, extra⟩ found
  read := by
    intro id allowed
    obtain ⟨node, found⟩ := domain.admission.base.found id allowed
    by_cases extra : extraForm node.form
    · exact (pointwise_extra root expressionSyntax callerEvidence headers domain allowed found extra).read
    · exact domain.basePolicy.read id ⟨allowed, node, found, extra⟩

private theorem accepted_read {childFuel : Nat} {id : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr}
    (found : (source named).lookupExpression? id = some node)
    (extra : extraForm node.form)
    (pointwise : PointwiseFor root (source named) scope id rootReasonAt)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (context compiled.indexed named) (source named) scope id rootReasonAt = .ok lowered) :
    ∃ actual reported, root.selected.policy.readExpression (source named) id = .ok (actual, reported) := by
  rcases extra_cases extra with ⟨parameters, result, statements, form⟩ | ⟨callee, ids, metadata, form⟩
  all_goals
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = (source named).owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, form, bind, Except.bind, pure, Except.pure] at accepted
      have bypass := pointwise.special (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
          (min budget childFuel) (context compiled.indexed named) childSource childScope childId childReasonAt) (childFuel + 1)
      cases hook : root.selected.policy.lowerSpecial? <;> simp only [hook] at accepted bypass
      all_goals try rw [bypass] at accepted
      all_goals
        obtain ⟨pair, read, _⟩ := bind_ok accepted
        exact ⟨pair.1, pair.2, read⟩
    · simp [owner, bind, Except.bind] at accepted

private theorem row_length {source : TypedSource} {current : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes source current ids types) : ids.length = types.length := by
  induction ids generalizing types with
  | nil => cases typed; rfl
  | cons head tail ih =>
      cases typed with
      | cons _ rest => exact congrArg Nat.succ (ih rest)

private theorem row_member {source : TypedSource} {current : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes source current ids types) {id : ExpressionId} (member : id ∈ ids) :
    ∃ type, ExpressionHasType source current id type := by
  induction ids generalizing types with
  | nil => cases member
  | cons head tail ih =>
      cases typed with
      | cons headTyped tailTyped =>
          rcases List.mem_cons.mp member with same | remaining
          · subst id; exact ⟨_, headTyped⟩
          · exact ih tailTyped remaining

private theorem zip_positions {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
    (length : ids.length = codes.length) : (ids.zip codes).map Prod.fst = ids := by
  induction ids generalizing codes with
  | nil => simp
  | cons head tail ih =>
      cases codes with
      | nil => simp at length
      | cons code rest =>
          simp only [List.length_cons, Nat.succ.injEq] at length
          simp only [List.zip_cons_cons, List.map_cons, ih length]

/-- Original indirect lowering and raw Source typing construct the receipt
internally; no Header-indexed factory or emitted type equality is supplied. -/
theorem indirect_of_accepted {childFuel : Nat} {id : ExpressionId} {node : ExpressionNode}
    {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (found : (source named).lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (pointwise : PointwiseFor root (source named) scope id rootReasonAt)
    (typed : ExpressionHasType (source named) sourceContext id node.type)
    (unique : NodeOccurrencesUnique (source named))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (context compiled.indexed named) (source named) scope id rootReasonAt = .ok lowered) :
    Nonempty (IndirectReceipt root (sourceContext := sourceContext) (scope := scope)
      childFuel id callee ids metadata lowered) := by
  obtain ⟨actual, reported, read⟩ := accepted_read root found (by simp only [form, extraForm]) pointwise accepted
  have actualMetadata := CompatibleExpressionReads.metadata_of_read (pointwise.read ▸ read)
  have nodeEq := Option.some.inj (actualMetadata.found.symm.trans found)
  subst actual
  obtain ⟨compiler⟩ := CallableIndirectCallCertificates.of_functions found form pointwise.special read form accepted
  have actualNode := Option.some.inj
    ((CompatibleExpressionReads.metadata_of_read (pointwise.read ▸ compiler.read)).found.symm.trans compiler.found)
  have parentMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source named)
      id compiler.original compiler.type := actualNode ▸ CompatibleExpressionReads.metadata_of_read (pointwise.read ▸ compiler.read)
  have nodeMetadata := CompatibleExpressionReads.metadata_of_read (pointwise.read ▸ compiler.read)
  have nodeId : compiler.node.id = id := (lookupExpression?_sound nodeMetadata.found).2
  obtain ⟨prepared⟩ := CallableIndexedOwnedIndirectSourceAdapters.Prepared.of_receipt compiler
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables nodeId
  obtain ⟨parameter, result, types, calleeTyped, argumentsTyped, application⟩ :=
    CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts unique found form typed
  have arity : ids.length = metadata.argumentCount := by
    cases application with
    | intro count _ _ _ => exact (row_length argumentsTyped).trans count.symm
  have sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler :=
    ⟨parentMetadata.requirements, parentMetadata.coercions, arity⟩
  obtain ⟨physicalCount, children⟩ := compiler.ordered_children
  have positions : compiler.entries.map Prod.fst = callee :: ids := by
    simp only [CallableIndirectCallCertificates.Receipt.entries, List.map_cons, zip_positions physicalCount]
  have generated : ∀ child code, (child, code) ∈ compiler.entries → ∃ childNode,
      (source named).lookupExpression? child = some childNode ∧
      ExpressionHasType (source named) sourceContext child childNode.type ∧
      SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed named) (source named) scope child rootReasonAt = .ok code := by
    intro child code member
    have childTyped : ∃ type, ExpressionHasType (source named) sourceContext child type := by
      rcases List.mem_cons.mp member with same | remaining
      · cases same; exact ⟨_, calleeTyped⟩
      · exact row_member argumentsTyped (List.of_mem_zip remaining).1
    obtain ⟨childType, typing⟩ := childTyped
    obtain ⟨childNode, contains, stored⟩ := typing.stored_type
    exact ⟨childNode, lookupExpression?_complete unique contains, (by rw [stored]; exact typing), children child code member⟩
  exact ⟨⟨compiler, prepared, sourceParent, parentMetadata, positions, physicalCount, generated⟩⟩

/-- The extra receipt is manufactured from this actual compiler branch.
Lambda bodies are deliberately not collected here; indirect children retain
one original receipt's callee-first physical vector and smaller child fuel. -/
theorem extra_receipts
    (domain : Domain root expressionSyntax callerEvidence headers (sourceContext := sourceContext)
      (scope := scope) (readFuel := readFuel))
    (unique : NodeOccurrencesUnique (source named))
    (childFuel : Nat) (id : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr)
    (allowed : expressionSyntax (source named) id) (found : (source named).lookupExpression? id = some node)
    (extra : extraForm node.form) (typed : ExpressionHasType (source named) sourceContext id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (context compiled.indexed named) (source named) scope id rootReasonAt = .ok lowered) :
    ∃ entries : List (ExpressionId × SourceCoreBasic.LoweredExpr),
      Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope)
        (CompatibleExpressionCalls.Entries scope entries) scope id lowered ∧
      entries.map Prod.fst = extraChildren node.form ∧
      ∀ child code, (child, code) ∈ entries → ∃ childNode,
        (source named).lookupExpression? child = some childNode ∧
        ExpressionHasType (source named) sourceContext child childNode.type ∧
        SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody childFuel
          (context compiled.indexed named) (source named) scope child rootReasonAt = .ok code := by
  have pointwise := pointwise_extra root expressionSyntax callerEvidence headers domain allowed found extra
  rcases extra_cases extra with ⟨parameters, result, statements, form⟩ | ⟨callee, ids, metadata, form⟩
  · obtain ⟨actual, reported, actualRead⟩ := accepted_read root found extra pointwise accepted
    have parentMetadata := CompatibleExpressionReads.metadata_of_read (pointwise.read ▸ actualRead)
    have same := Option.some.inj (parentMetadata.found.symm.trans found)
    subst actual
    have read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
        (source named) id = .ok (node, reported) := pointwise.read ▸ actualRead
    have special : DecoratedFunctionCode.SpecialPasses root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed named) (source named) scope id rootReasonAt := pointwise.special _ _
    obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted special parentMetadata.owner found
      (pointwise.read.trans read) form accepted
    have annotation := congrArg SourceCoreBasic.LoweredExpr.type certificate.emitted
    have metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source named) id node lowered.type :=
      annotation.symm ▸ parentMetadata
    refine ⟨[], .lambda allowed found form certificate accepted typed metadata, ?_, ?_⟩
    · simp only [List.map_nil, form, extraChildren]
    · intro child code member; cases member
  · obtain ⟨receipt⟩ := indirect_of_accepted root found form pointwise typed unique accepted
    exact ⟨receipt.compiler.entries, .indirect found form receipt (fun _ _ member => ⟨rfl, member⟩),
      by simpa only [form, extraChildren] using receipt.positions, receipt.generated⟩

/-- Original compiler-fuel induction constructs the finite same-source Tree
and its expression sites once. Neither a final Tree nor an arbitrary extra
receipt is a premise. A selected Principal instantiates Named/Compilation and
callerEvidence with its actual cached compilation and dictionary. -/
theorem tree_of_accepted
    (domain : Domain root expressionSyntax callerEvidence headers (sourceContext := sourceContext)
      (scope := scope) (readFuel := readFuel))
    (unique : NodeOccurrencesUnique (source named))
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : AcceptedAt root expressionSyntax readFuel (source named) sourceContext scope id lowered) :
    RuntimeExpressionsFor (Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope))
      readFuel (.initial compiled.compatible.checked) (source named) sourceContext
      (context compiled.indexed named).solvedRequirements rootReasonAt scope id lowered := by
  cases receipt with
  | intro found typed allowed declarations closed residual signatures accepted =>
      exact tree_of_functions_at_runtime_with_children (headers := headers)
        (values := .initial compiled.compatible.checked) (compilation := context compiled.indexed named)
        callerEvidence (Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope))
        (include_named root expressionSyntax callerEvidence headers) (projected root expressionSyntax callerEvidence headers)
        extraForm extraChildren domain.admission domain.coverage domain.sourceTypes domain.emptyEvidence domain.order
        unique declarations signatures domain.constructorValid domain.fragmentValid domain.selectedValid
        (policy_for_all root expressionSyntax callerEvidence headers domain) compiled.indexed.ancestry.graph.inputs.callable
        [] root.callables domain.fragmentCoercions domain.coercions
        (extra_receipts root expressionSyntax callerEvidence headers domain unique) allowed found typed accepted

section Principal
variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (principalRoot : RootPolicyReceipt (compiled := compiled) principal.named
    principal.cached.diagnostics principal.cached.code principal.cached.compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- Specialization retains the actual selected method and its dictionary. The
generic finite producer uses its cached compilation directly. -/
theorem tree_of_principal
    (domain : Domain principalRoot expressionSyntax (some principal.dictionary) headers
      (sourceContext := sourceContext) (scope := scope) (readFuel := readFuel))
    (unique : NodeOccurrencesUnique (source principal.named))
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : AcceptedAt principalRoot expressionSyntax readFuel (source principal.named)
      sourceContext scope id lowered) :
    RuntimeExpressionsFor (Head principalRoot expressionSyntax (some principal.dictionary) headers
      (sourceContext := sourceContext) (scope := scope)) readFuel (.initial compiled.compatible.checked)
      (source principal.named) sourceContext (context compiled.indexed principal.named).solvedRequirements
      rootReasonAt scope id lowered :=
  tree_of_accepted principalRoot expressionSyntax (some principal.dictionary) headers domain unique receipt

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedExpressionNativeChildren
/-! Actual native typing is pulled back through the literal one-level compiler
head. Child certificates retain that same local witness. Source metadata stays
in the original head; no Source authority or execution is inferred from typing.
The separate open call slot must supply its own authentic emission inversion.
This is a static strengthening used by the finite compiler skeleton fold. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedExpressionNativeChildren
open Core Frontend SourceInference
open CompatibleExpressionPrimitives
open CallableIndexedOwnedPreparedNativeAssignmentChildren (RawTyped packed_children)
open TypedLexicalWhile.Native (remove_front)

/-- Retain the original child receipt and its actual arbitrary native result. -/
def WithRaw (nativeContext : Core.Context) (definitions : DataEnvironment)
    (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => children scope id lowered ∧ RawTyped nativeContext lowered.expression definitions

variable {definitions : DataEnvironment} {nativeContext : Core.Context} {nativeType : Ty}

/-- Ordinary language-result operand insertion is removed syntactically. -/
theorem pair_children {leftType rightType : Ty} {left right : Expr}
    (typed : HasType nativeContext (LocalSequence.pair leftType rightType left right) nativeType definitions) :
    RawTyped nativeContext left definitions ∧ RawTyped nativeContext right definitions := by
  cases typed with
  | caseE first failure remaining =>
    cases remaining with
    | caseE second failure returned => exact ⟨⟨_, first⟩, ⟨_, remove_front second⟩⟩

/-- This also covers comparison bodies: only the two operand positions matter. -/
theorem binary_children {result : Ty} {left right body : Expr}
    (typed : HasType nativeContext (LocalPrimitiveResults.binaryWith result left right body) nativeType definitions) :
    RawTyped nativeContext left definitions ∧ RawTyped nativeContext right definitions := by
  cases typed with
  | caseE first failure remaining =>
    cases remaining with
    | caseE second failure returned => exact ⟨⟨_, first⟩, ⟨_, remove_front second⟩⟩

/-- Native branch typing exists for both branches, independently of which
branch a later actual evaluation takes. No branch evaluation is supplied. -/
theorem choose_children {result : Ty} {condition yes no : Expr}
    (typed : HasType nativeContext (LocalControl.choose result condition yes no) nativeType definitions) :
    RawTyped nativeContext condition definitions ∧ RawTyped nativeContext yes definitions ∧
      RawTyped nativeContext no definitions := by
  cases typed with
  | caseE condition failure selected =>
    cases selected with
    | ifE test yes no => exact ⟨⟨_, condition⟩, ⟨_, remove_front yes⟩, ⟨_, remove_front no⟩⟩

/-- The actual scalar profile decides strict or Boolean code shape. Short
circuiting changes evaluation, but both real child syntax typings remain. -/
theorem profiled_binary_children {operator : Syntax.BinaryOp} {operand result : TypeSystem.Ty}
    {mode : Mode} {left right : Expr}
    (profile : BinaryProfile operator operand result mode)
    (typed : HasType nativeContext (mode.binary operator left right) nativeType definitions) :
    RawTyped nativeContext left definitions ∧ RawTyped nativeContext right definitions := by
  cases profile with
  | word strict =>
    rw [Mode.binary_strict .word strict] at typed
    exact binary_children typed
  | integer strict =>
    rw [Mode.binary_strict .integer strict.toStrict] at typed
    exact binary_children typed
  | panicking panicking =>
    -- Unchecked `/` and `%` bind both operands before the checked body.
    have shape : Mode.word.binary operator left right =
        SourceCorePrimitive.binaryPanicking operator left right := by
      cases panicking <;> rfl
    rw [shape] at typed
    cases typed with
    | caseE first failure remaining =>
      cases remaining with
      | caseE second failure returned => exact ⟨⟨_, first⟩, ⟨_, remove_front second⟩⟩
  | logicalAnd =>
    have children := choose_children (show HasType nativeContext
      (LocalControl.choose .bool left right (LanguageResult.success (.bool false))) nativeType definitions from typed)
    exact ⟨children.1, children.2.1⟩
  | logicalOr =>
    have children := choose_children (show HasType nativeContext
      (LocalControl.choose .bool left (LanguageResult.success (.bool true)) right) nativeType definitions from typed)
    exact ⟨children.1, children.2.2⟩

/-- Actual contracted invocation contains the callee once and the packed
arguments after its two private inserted payloads. Gates supply no authority. -/
theorem contracted_call_children {gates : List CallableContract.Gate} {unknown : Word}
    {result : Ty} {callee arguments : Expr}
    (typed : HasType nativeContext (CallableContract.call gates unknown result callee arguments) nativeType definitions) :
    RawTyped nativeContext callee definitions ∧ RawTyped nativeContext arguments definitions := by
  cases typed with
  | caseE callee failure beforeArguments =>
    cases beforeArguments with
    | caseE firstGate failure arguments =>
      cases arguments with
      | caseE packed failure afterArguments =>
        exact ⟨⟨_, callee⟩, ⟨_, remove_front (remove_front packed)⟩⟩

/-- The tagged helper has one private callee slot. -/
theorem tagged_call_children {result : Ty} {callee arguments : Expr}
    (typed : HasType nativeContext (TaggedFunction.call result callee arguments) nativeType definitions) :
    RawTyped nativeContext callee definitions ∧ RawTyped nativeContext arguments definitions := by
  cases typed with
  | caseE callee failure arguments =>
    cases arguments with
    | caseE packed failure applied => exact ⟨⟨_, callee⟩, ⟨_, remove_front packed⟩⟩

/-- The real direct named helper evaluates its pack before the global cell. -/
theorem named_call_arguments {signature : SourceCoreCalls.Signature} {index : Nat}
    {arguments : Expr} {internalReason : Word}
    (typed : HasType nativeContext (SourceCoreCalls.call signature index arguments internalReason) nativeType definitions) :
    RawTyped nativeContext arguments definitions := by
  cases typed with
  | caseE arguments failure applied => exact ⟨_, arguments⟩

section Strengthen
variable {children : GenericExpressionMeaning.Certificate} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope}

/-- Original order, duplicates and Source lookup receipts are preserved. -/
theorem sequence_with_raw {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (sequence : DataExpressionSequence.Tree source children scope ids types codes)
    (raw : ∀ code, code ∈ codes → RawTyped nativeContext code.expression definitions) :
    DataExpressionSequence.Tree source (WithRaw nativeContext definitions children) scope ids types codes := by
  revert raw
  induction sequence with
  | nil => intro raw; exact .nil
  | single found generated =>
    intro raw
    exact .single found ⟨generated, raw _ (by simp)⟩
  | cons found generated tail ih =>
    intro raw
    exact .cons found ⟨generated, raw _ (by simp)⟩ (ih (fun code member => raw code (List.mem_cons_of_mem _ member)))

/-- Every actual primitive child gets its witness from the same emitted code. -/
theorem primitive_with_raw {checked : SourceCoreCompatibleCatalog.Checked}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : CompatibleExpressionTypedCompositions.Head checked source children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    CompatibleExpressionTypedCompositions.Head checked source (WithRaw nativeContext definitions children) scope id lowered := by
  cases head with
  | group metadata form found sourceType child =>
    exact .group metadata form found sourceType ⟨child, _, typed⟩
  | pair metadata form firstFound secondFound sourceType first second =>
    have native := pair_children typed
    exact .pair metadata form firstFound secondFound sourceType ⟨first, native.1⟩ ⟨second, native.2⟩
  | unary metadata form found inputType outputType profile child =>
    cases typed with
    | caseE operand failure returned =>
      exact .unary metadata form found inputType outputType profile ⟨child, _, operand⟩
  | binary metadata form firstFound secondFound firstType secondType outputType profile first second =>
    have native := profiled_binary_children profile typed
    exact .binary metadata form firstFound secondFound firstType secondType outputType profile
      ⟨first, native.1⟩ ⟨second, native.2⟩
  | conditional metadata form conditionFound yesFound noFound conditionType yesType noType condition yes no =>
    have native := choose_children typed
    exact .conditional metadata form conditionFound yesFound noFound conditionType yesType noType
      ⟨condition, native.1⟩ ⟨yes, native.2.1⟩ ⟨no, native.2.2⟩

/-- Builtin arguments keep the original pack and every actual child receipt. -/
theorem builtin_with_raw {values : SourceCoreCompatibleValues.Context}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : BuiltinCalls.Typed.Head values source children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    BuiltinCalls.Typed.Head values source (WithRaw nativeContext definitions children) scope id lowered := by
  cases head with
  | contracted metadata form sourceType sequence nativeTypes =>
    obtain ⟨_, pack⟩ := contracted_call_children typed
    obtain ⟨packType, packTyped⟩ := pack
    exact .contracted metadata form sourceType (sequence_with_raw sequence (packed_children packTyped)) nativeTypes

/-- The open call head is strengthened by its authentic one-level code
inversion. This is a static compiler operation, not an expression meaning law. -/
theorem head_with_raw {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
    {reasonAt : ExpressionId → Word}
    {calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate}
    (callChildren : ∀ {id lowered}, calls children scope id lowered →
      ∀ {result}, HasType nativeContext lowered.expression result definitions →
        calls (WithRaw nativeContext definitions children) scope id lowered)
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : CompatibleExpressionCalls.Head calls values source context reasonAt children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    CompatibleExpressionCalls.Head calls values source context reasonAt
      (WithRaw nativeContext definitions children) scope id lowered := by
  cases head with
  | primitive head => exact .primitive (primitive_with_raw head typed)
  | constructor receipt form valid sequence =>
    cases typed with
    | caseE pack failure constructed =>
      exact .constructor receipt form valid (sequence_with_raw sequence (packed_children pack))
  | member metadata baseMetadata form layout child =>
    cases typed with
    | caseE base failure projected =>
      exact .member metadata baseMetadata form layout ⟨child, _, base⟩
  | index header keyFound form sourceType base key =>
    cases typed with
    | caseE baseTyped failure remaining =>
      cases remaining with
      | caseE keyTyped failure lookup =>
        exact .index header keyFound form sourceType ⟨base, _, baseTyped⟩ ⟨key, _, remove_front keyTyped⟩
  | builtin head => exact .builtin (builtin_with_raw head typed)
  | call head => exact .call (callChildren head typed)
  | tuple receipt sequence =>
    exact .tuple receipt (sequence_with_raw sequence (packed_children typed))

end Strengthen
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedExpressionNativeChildren
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeadNativeChildren
/-! The actual raw compiler head supplies native witnesses only for its used
child slots. Ordinary and evidence calls retain their selected Header and exact
argument pack. Indirect calls retain the authentic prepared callsite and physical
callee-first entries. Lambda heads use no expression children. The same original
head is strengthened; no Source authority or body execution is inferred. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeadNativeChildren
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedRawCompilerHeads
open CallableIndexedOwnedPreparedExpressionNativeChildren
open CallableIndexedOwnedPreparedNativeAssignmentChildren (packed_children)

section Named
variable {checked : CallableAncestryPairedLookup.Checked}
  {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {nativeContext : Core.Context} {definitions : DataEnvironment} {nativeType : Ty}

/-- The original ordinary Emission identifies the literal named call pack. -/
theorem ordinary_with_raw {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : RecursiveNamedCatalog.Head headers compilation source context children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    RecursiveNamedCatalog.Head headers compilation source context
      (WithRaw nativeContext definitions children) scope id lowered := by
  cases head with
  | named member metadata sourceType form calleeFound calleeForm calleeRequirements calleeCoercions
      valid predicates evidence arity emission selectedSlot sequence nativeTypes =>
    rw [emission.equation.1] at typed
    obtain ⟨packType, packTyped⟩ := named_call_arguments typed
    exact .named member metadata sourceType form calleeFound calleeForm calleeRequirements calleeCoercions
      valid predicates evidence arity emission selectedSlot
      (sequence_with_raw sequence (packed_children packTyped)) nativeTypes

/-- The full RawCall preserves the real caller dictionary and selected row. -/
theorem evidence_with_raw {evidence : Dynamic.EvidenceEnvironment}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : RecursiveNamedCallEvidenceHeads.Head headers compilation source context evidence children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    RecursiveNamedCallEvidenceHeads.Head headers compilation source context evidence
      (WithRaw nativeContext definitions children) scope id lowered := by
  cases head with
  | ordinary actual => exact .ordinary (ordinary_with_raw actual typed)
  | direct receipt certified metadata =>
    have emitted := congrArg (fun code : SourceCoreBasic.LoweredExpr => code.expression)
      (certified.emitted receipt metadata.coercions)
    rw [emitted] at typed
    obtain ⟨packType, packTyped⟩ := named_call_arguments typed
    exact .direct receipt
      ⟨certified.selected, certified.sourceType, certified.calleeNode, certified.name,
        certified.calleeFound, certified.calleeForm, certified.calleeRequirements, certified.calleeCoercions,
        certified.valid, certified.dictionary,
        sequence_with_raw certified.sequence (packed_children packTyped), certified.nativeTypes⟩ metadata

/-- Both genuine optional-evidence alternatives use their actual emission. -/
theorem named_with_raw {callerEvidence : Option Dynamic.EvidenceEnvironment}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context
      children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context
      (WithRaw nativeContext definitions children) scope id lowered := by
  cases callerEvidence with
  | none => exact ordinary_with_raw head typed
  | some evidence => exact evidence_with_raw head typed

end Named

section Raw
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  {children : GenericExpressionMeaning.Certificate}
  {nativeContext : Core.Context} {definitions : DataEnvironment} {nativeType : Ty}

/-- Only actual used slots are strengthened. An arbitrary Entries list may
contain unused children; no native witness for those entries is requested. -/
theorem raw_children {childScope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (head : Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope)
      children childScope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope)
      (WithRaw nativeContext definitions children) childScope id lowered := by
  cases head with
  | named actual => exact .named (named_with_raw actual typed)
  | lambda allowed found form certificate accepted sourceTyped metadata =>
    exact .lambda allowed found form certificate accepted sourceTyped metadata
  | indirect found form receipt ordered =>
    have emitted := congrArg (fun code : SourceCoreBasic.LoweredExpr => code.expression) receipt.compiler.output
    rw [emitted, receipt.prepared.emitted] at typed
    obtain ⟨calleeRaw, packRaw⟩ := contracted_call_children typed
    obtain ⟨packType, packTyped⟩ := packRaw
    have argumentsRaw := packed_children packTyped
    refine .indirect found form receipt ?_
    intro child code member
    refine ⟨ordered child code member, ?_⟩
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      exact calleeRaw
    · exact argumentsRaw code (List.of_mem_zip remaining).2

/-- This discharges the original static call slot for the same raw compiler
family. Primitive/data/call heads all retain their original Source receipts. -/
theorem expression_head_with_raw {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : CompatibleExpressionCalls.Head
      (Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope))
      (.initial compiled.compatible.checked) (source named) sourceContext rootReasonAt children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    CompatibleExpressionCalls.Head
      (Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope))
      (.initial compiled.compatible.checked) (source named) sourceContext rootReasonAt
      (WithRaw nativeContext definitions children) scope id lowered := by
  exact CallableIndexedOwnedPreparedExpressionNativeChildren.head_with_raw
    (fun actual _nativeType actualTyped => raw_children root expressionSyntax callerEvidence headers actual actualTyped) head typed

end Raw
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeadNativeChildren
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelFormationBounds
/-! Formation uses an explicit receiving function model and a positive
closure constructor. The original functions-independent elementary producer
runs once, copying the captured cells, and the formed heap is represented
under that receiving model.
No weaker heap model is inverted into stronger global provenance. Reflection
retains its independent Source grade and exact dictionary-bearing packet. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelFormationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (StaticMember)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (qualification : Facet compiled)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (models : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (lift : ∀ {mapping world function native bindings parameter result},
    StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result →
    models.Represents registry mapping world (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result))

/-- This post uses the receiving function model directly. Formation preserves
the incoming heap and constructs only the positive closure representation. -/
structure Post
    {callerProtocol : ProtectedStateTransition.Protocol (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (context : SourceSemantics.Context) (sourceType : TypeSystem.Ty) (type : Ty)
    (outcome : Dynamic.ExpressionOutcome) (result : Core.Value)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  admission : PostAdmission bridge context sourceType outcome reached
  cells : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry models
    index.mapping index.world index.heap index.store
  result : FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models)
    index.mapping index.world sourceType type faults outcome result

namespace Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (qualified : ∀ environment, qualification.ordinary (code.recapture environment) (support.recapture environment))
  (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

local notation "history" => CallableIndexedOwnedPreparedDirectFormationReceipts.Ordinary.history_at
  captured code owner support initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

/-- The complete leaf output retains all real effects and the stronger facet
inside the original existential at the same reached packet. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        models)
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry models finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
      Post (models := models) (registry := registry) (faults := faults)
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        function.context code.sourceNode.type code.lowered.type outcome result reached ∧
      ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models) captured code history heap store owner.key.frameLocation,
        StaticMember qualification headers keys bodyRegistry faults finalMap finalWorld formed.closure
          (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
          code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

/-- The proved strong post is attached without selecting another state or
running formation again. Source admission belongs to that post's actual trace. -/
private theorem result_at_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models) captured code history heap store owner.key.frameLocation)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore)
    (member : StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore)
    {reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
      ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, canonical⟩}
    (related : (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached)
    (post : Post (models := models) (registry := registry) (faults := faults)
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      function.context code.sourceNode.type code.lowered.type
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) :
    ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (models := models) (support := support) (initial := initial) (packet := packet)
      (.value (.closure formed.closure)) formed.finalHeap (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore :=
  ⟨nativeTrace, formed.finalMap, formed.finalWorld, post.result, post.cells, formed.maps, formed.worlds, formed.frame,
    formed.copy.metadata_extends, reached, related, post, formed, member⟩

variable
  (cells : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry models mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include lift cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile qualified prefixContext observed in
private theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models) captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual))
        formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, canonical⟩,
        (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
        Post (models := models) (registry := registry) (faults := faults)
          (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller) function.context code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ :=
    CallableIndexedOwnedPreparedDirectFormationReceipts.Ordinary.formation_member
      captured code owner qualification profile support qualified prepared initial packet prefixContext observed
      cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models)
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact .function (lift member)
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller) (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner support.caller)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := after_expression (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, ⟨post, formed.heaps, represented⟩⟩, determined⟩

include profile lift qualified prefixContext observed prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- The actual Source value/fault head selects the authentic lambda. Exactly
one prepared formation establishes native completion and the stronger post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore,
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (models := models) (support := support) (initial := initial) (packet := packet)
        outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
      obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions evaluated
      obtain ⟨formed, _sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, _determined⟩ :=
        formation_post
          (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
          (support := support) (qualified := qualified) (prepared := prepared)
          (initial := initial) (packet := packet) (prefixContext := prefixContext) (observed := observed)
          (models := models) (lift := lift) (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
          (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
      obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
      exact ⟨_, formed.finalStore, result_at_formation (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (models := models) captured code owner qualification support initial packet formed nativeTrace member related post⟩
  | fault failed =>
      exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions failed)

include profile lift qualified prefixContext observed prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Native completion is compared with one genuine formation. Its own Source
grade is obtained from that factory trace; preservation is not invoked again. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (models := models) (support := support) (initial := initial) (packet := packet)
        outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, determined⟩ :=
    formation_post
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
      (support := support) (qualified := qualified) (prepared := prepared)
      (initial := initial) (packet := packet) (prefixContext := prefixContext) (observed := observed)
      (models := models) (lift := lift) (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
      (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, sized,
    result_at_formation (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (models := models) captured code owner qualification support initial packet formed nativeTrace member related post⟩

end Ordinary

namespace Principal
variable
  (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (qualified : ∀ environment, qualification.principal (code.recapture environment) (support.recapture environment))
  (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

local notation "history" => CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.history_at
  captured code owner support initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

/-- The selected-method leaf retains its own principal packet and dictionary.
The outer payload registry is independent of the retained body registry. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        models)
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry models finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
        ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩,
      (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
      Post (models := models) (registry := registry) (faults := faults)
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        function.context code.sourceNode.type code.lowered.type outcome result reached ∧
      ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models) captured code history heap store owner.key.frameLocation,
        StaticMember qualification headers keys bodyRegistry faults finalMap finalWorld formed.closure
          (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
          code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

private theorem result_at_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models) captured code history heap store owner.key.frameLocation)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore)
    (member : StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore)
    {reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
      ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩}
    (related : (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached)
    (post : Post (models := models) (registry := registry) (faults := faults)
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      function.context code.sourceNode.type code.lowered.type
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) :
    ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (models := models) (support := support) (initial := initial) (packet := packet)
      (.value (.closure formed.closure)) formed.finalHeap (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore :=
  ⟨nativeTrace, formed.finalMap, formed.finalWorld, post.result, post.cells, formed.maps, formed.worlds, formed.frame,
    formed.copy.metadata_extends, reached, related, post, formed, member⟩

variable
  (cells : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry models mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include lift cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile qualified in
private theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models) captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual))
        formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩,
        (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
        Post (models := models) (registry := registry) (faults := faults)
          (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) function.context code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ :=
    CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.formation_member
      captured code owner qualification profile support qualified prepared initial packet
      cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models)
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact .function (lift member)
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named) (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := after_expression (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, ⟨post, formed.heaps, represented⟩⟩, determined⟩

include profile lift qualified prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Source inversion keeps the actual selected principal, then invokes one
prepared method formation at its original dictionary-bearing packet. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore,
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (models := models) (support := support) (initial := initial) (packet := packet)
        outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
      obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions evaluated
      obtain ⟨formed, _sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, _determined⟩ :=
        formation_post
          (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
          (support := support) (qualified := qualified) (prepared := prepared)
          (initial := initial) (packet := packet)
          (models := models) (lift := lift) (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
          (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
      obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
      exact ⟨_, formed.finalStore, result_at_formation (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (models := models) captured code owner qualification support initial packet formed nativeTrace member related post⟩
  | fault failed =>
      exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions failed)

include profile lift qualified prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- The native grade is independent of the Source grade obtained from one
actual method factory trace. The same strong post and reached pool are retained. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (models := models) (support := support) (initial := initial) (packet := packet)
        outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, determined⟩ :=
    formation_post
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
      (support := support) (qualified := qualified) (prepared := prepared)
      (initial := initial) (packet := packet)
      (models := models) (lift := lift) (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
      (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, sized,
    result_at_formation (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (models := models) captured code owner qualification support initial packet formed nativeTrace member related post⟩

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelFormationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelPrincipalFormationPosts
/-! The exact principal formation post is exposed for caller restoration.
The original prepared formation runs once, copying the captured cells, and the
incoming pool is transported to the formed heap, mapping, world and store under
the receiving function model. The proof is the existing principal formation
proof with a public port. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelPrincipalFormationPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (StaticMember)
open CallableIndexedOwnedSourceAdmission

open CallableIndexedOwnedPreparedFunctionModelFormationBounds (Post)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (qualification : Facet compiled)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (models : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (lift : ∀ {mapping world function native bindings parameter result},
    StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result →
    models.Represents registry mapping world (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result))

variable
  (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (qualified : ∀ environment, qualification.principal (code.recapture environment) (support.recapture environment))
  (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

local notation "history" => CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.history_at
  captured code owner support initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

variable
  (cells : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry models mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include lift cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile qualified in
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models) captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual))
        formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩,
        (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
        Post (models := models) (registry := registry) (faults := faults)
          (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) function.context code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ :=
    CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.formation_member
      captured code owner qualification profile support qualified prepared initial packet
      cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models)
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact .function (lift member)
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named) (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := after_expression (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, ⟨post, formed.heaps, represented⟩⟩, determined⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelPrincipalFormationPosts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedQualifiedFormationBounds
/-! Genuine graded ordinary and selected-method formation leaves retain the
compiler-qualified member, cells and result inside their actual reached
packet. Source preservation inverts the original lambda head. Native reflection
compares one actual factory result and assigns its own finite Source grade.
Receiving registry is explicit on every local ResultAt use. No legacy output
port, equal-registry premise or second factory call is introduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedQualifiedFormationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualQualification (Facet StaticMember CellOrigins functions)
open CallableIndexedOwnedPreparedQualifiedExpressionOutputs (Post)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (qualification : Facet compiled)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

namespace Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (callerGlobals : support.caller.globals = compiled.indexed.base.globals.length)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  (qualified : ∀ environment, qualification.ordinary (code.recapture environment) (support.recapture environment))
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

local notation "plain" => CallableIndexedOwnedPreparedOrdinaryBodyProjection.plain support actualSites sites
local notation "history" => CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
  captured code plain owner initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

/-- The complete leaf output retains all real effects and the stronger facet
inside the original existential at the same reached packet. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CellOrigins qualification headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
      Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        function.context qualification profile code.sourceNode.type code.lowered.type outcome result reached ∧
      ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
            (functions qualification headers keys bodyRegistry faults profile)) captured code history heap store
          owner.key.frameLocation,
        StaticMember qualification headers keys bodyRegistry faults finalMap finalWorld formed.closure
          (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
          code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

/-- The proved strong post is attached without selecting another state or
running formation again. Source admission belongs to that post's actual trace. -/
private theorem result_at_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functions qualification headers keys bodyRegistry faults profile)) captured code history heap store
      owner.key.frameLocation)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore)
    (member : StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore)
    {reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
      ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, canonical⟩}
    (related : (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached)
    (post : Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      function.context qualification profile code.sourceNode.type code.lowered.type
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) :
    ResultAt (registry := registry) captured code owner qualification profile support actualSites sites initial packet
      (.value (.closure formed.closure)) formed.finalHeap (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore :=
  ⟨nativeTrace, formed.finalMap, formed.finalWorld, post.result, post.cells, formed.maps, formed.worlds, formed.frame,
    formed.copy.metadata_extends, reached, related, post, formed, member⟩

variable
  (cells : CellOrigins qualification headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include callerGlobals callerReceipt qualified prefixContext observed prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- The actual Source value/fault head selects the authentic lambda. Exactly
one prepared formation establishes native completion and the stronger post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore,
      ResultAt (registry := registry) captured code owner qualification profile support actualSites sites initial packet
        outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
      obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions evaluated
      obtain ⟨formed, _sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, _determined⟩ :=
        CallableIndexedOwnedPreparedQualifiedFormationReceipts.Ordinary.formation_post
          (registry := registry) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
          (support := support) (callerGlobals := callerGlobals) (callerReceipt := callerReceipt) (qualified := qualified) (actualSites := actualSites) (sites := sites) (prepared := prepared)
          (initial := initial) (packet := packet) (prefixContext := prefixContext) (observed := observed)
          (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
          (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
      obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
      exact ⟨_, formed.finalStore, result_at_formation (registry := registry)
        captured code owner qualification profile support actualSites sites initial packet formed nativeTrace member related post⟩
  | fault failed =>
      exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions failed)

include callerGlobals callerReceipt qualified prefixContext observed prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Native completion is compared with one genuine formation. Its own Source
grade is obtained from that factory trace; preservation is not invoked again. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) captured code owner qualification profile support actualSites sites initial packet
        outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, determined⟩ :=
    CallableIndexedOwnedPreparedQualifiedFormationReceipts.Ordinary.formation_post
      (registry := registry) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
      (support := support) (callerGlobals := callerGlobals) (callerReceipt := callerReceipt) (qualified := qualified) (actualSites := actualSites) (sites := sites) (prepared := prepared)
      (initial := initial) (packet := packet) (prefixContext := prefixContext) (observed := observed)
      (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
      (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, sized,
    result_at_formation (registry := registry)
      captured code owner qualification profile support actualSites sites initial packet formed nativeTrace member related post⟩

end Ordinary

namespace Principal
variable
  (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (qualified : ∀ environment, qualification.principal (code.recapture environment) (support.recapture environment))
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

local notation "plain" => support.plain actualSites sites
local notation "history" => CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
  captured code plain owner initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

/-- The selected-method leaf retains its own principal packet and dictionary.
The outer payload registry is independent of the retained body registry. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CellOrigins qualification headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
        ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩,
      (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
      Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        function.context qualification profile code.sourceNode.type code.lowered.type outcome result reached ∧
      ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
            (functions qualification headers keys bodyRegistry faults profile)) captured code history heap store
          owner.key.frameLocation,
        StaticMember qualification headers keys bodyRegistry faults finalMap finalWorld formed.closure
          (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
          code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

private theorem result_at_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functions qualification headers keys bodyRegistry faults profile)) captured code history heap store
      owner.key.frameLocation)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore)
    (member : StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore)
    {reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
      ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩}
    (related : (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached)
    (post : Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      function.context qualification profile code.sourceNode.type code.lowered.type
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) :
    ResultAt (registry := registry) captured code owner qualification profile support actualSites sites initial packet
      (.value (.closure formed.closure)) formed.finalHeap (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore :=
  ⟨nativeTrace, formed.finalMap, formed.finalWorld, post.result, post.cells, formed.maps, formed.worlds, formed.frame,
    formed.copy.metadata_extends, reached, related, post, formed, member⟩

variable
  (cells : CellOrigins qualification headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include qualified prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Source inversion keeps the actual selected principal, then invokes one
prepared method formation at its original dictionary-bearing packet. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore,
      ResultAt (registry := registry) captured code owner qualification profile support actualSites sites initial packet
        outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
      obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions evaluated
      obtain ⟨formed, _sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, _determined⟩ :=
        CallableIndexedOwnedPreparedQualifiedFormationReceipts.Principal.formation_post
          (registry := registry) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
          (support := support) (qualified := qualified) (actualSites := actualSites) (sites := sites) (prepared := prepared)
          (initial := initial) (packet := packet)
          (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
          (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
      obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
      exact ⟨_, formed.finalStore, result_at_formation (registry := registry)
        captured code owner qualification profile support actualSites sites initial packet formed nativeTrace member related post⟩
  | fault failed =>
      exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions failed)

include qualified prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- The native grade is independent of the Source grade obtained from one
actual method factory trace. The same strong post and reached pool are retained. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) captured code owner qualification profile support actualSites sites initial packet
        outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, determined⟩ :=
    CallableIndexedOwnedPreparedQualifiedFormationReceipts.Principal.formation_post
      (registry := registry) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
      (support := support) (qualified := qualified) (actualSites := actualSites) (sites := sites) (prepared := prepared)
      (initial := initial) (packet := packet)
      (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
      (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, sized,
    result_at_formation (registry := registry)
      captured code owner qualification profile support actualSites sites initial packet formed nativeTrace member related post⟩

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedQualifiedFormationBounds
end
