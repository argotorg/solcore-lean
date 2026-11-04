import Solcore.Test.SourceSemantics.CoreLowering.LexicalFailure
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionIssuance
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSessionDirectFailures
import Solcore.Test.SourceSemantics.CoreLowering.Named.Branches
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNamedBodyProducer
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
import Solcore.SourceSemantics.CoreLowering.CellAwareFaultingNamedProgramProfiles
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning
import Solcore.Test.SourceSemantics.Semantics
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.Dynamic.Fault
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
import Solcore.Test.SourceSemantics.CoreLowering.Selected.GeneralizedSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialStart
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionInitial
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedNamedSupport
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicFaultingFailureReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexSource
import Solcore.Frontend.SourceCompiler
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicInitialData

/-!
# Faulting selected tests

Selected bodies that fault, general keys and direct failures.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedDirectFailureMeaning
/-! The existing failed function is issued as a real retained handle. Its
packed failure and the later identity call keep the same complete history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreCertifiedLexicalFailure (First first_call eligible_row header_of_member header_types)
open Tests.SourceCoreDirectFailure (ObservedNamed ObservedFailure ObservedSuccess issuanceFuel failureOptions)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicPhysicalSessionState (SourceCall)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Profiled fixture.recipe}

theorem remember_named {stages : ObservedStages fixture observed.failedRow}
    {first : First fixture observed} (before : FirstMeaning issued stages first)
    (call : ObservedNamed first.returned observed.failedRow.row.key) :
    ∃ (entry : Entry) (global : Dynamic.GlobalFunction) (rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment),
      entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      entry.source = .global global ∧ NamedSourceAt before.initial.header rawD global ∧
      ∃ next : issued.toIssued.State before.initial.header call.completion.session [entry],
        next.heap = before.after.heap := by
  obtain ⟨input, packet, member, sameHeader⟩ := issued.catalog.rows.mem_headers before.initial.header
    before.initial.start.selected.member
  have headerEq : packet.header = before.actual.header := sameHeader.trans before.headerEq
  have issuance : first.returned.NamedIssuedAt packet.header.named.signature.key issuanceFuel call.completion := by
    rw [headerEq, before.actual.key]
    exact call.issued
  obtain ⟨entry, entryType, source, handle, _handleType, next, heap⟩ :=
    SelectedCompilationPublicSessionIssuance.State.remember_named issued.support issued.prepared
      before.after packet member issuance call.returned
  have sourceAt : NamedSourceAt before.initial.header input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)) :=
    sameHeader ▸ packet.sourceAt
  obtain ⟨facts, certificate⟩ := SelectedCompilationNamedArgumentRows.certified_at packet.sourceAt issued.support.bodyTyping
    (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected) packet.aligned
  have bindingTypes : packet.header.types = [] := by
    rw [headerEq, header_types, before.actual.failed_inputs]
  have shape := certificate.callable_type
  change packet.header.named.specialized.function.type = _ at shape
  rw [← packet.sourceAt.frame.result, bindingTypes, headerEq, before.actual.failed_result_type] at shape
  exact ⟨entry, _, _, entryType.trans (by simpa only [headerEq, TypeSystem.Ty.productMany] using shape), handle, source, sourceAt, next, heap⟩

theorem invoke
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.toIssued.State anchor session entries)
    (actual : ActualHeader fixture observed.failedRow.row)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function .unit .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (entrySource : entry.source = .global global) (sourceAt : NamedSourceAt actual.header rawD global)
    (call : ObservedFailure session handle) (ready : session.ExportsReady)
    (invocation : Staging.Recursive.Scope) :
    ∃ (after : issued.toIssued.State anchor call.returned entries) (location : Dynamic.Location),
      Dynamic.Heap.Allocates before.heap .word none location after.heap ∧
      Dynamic.Heap.Reads after.heap location {type := .word, value := none} ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram) entry.source 0 ∧
      SourceCall anchor actual.header invocation before.heap [] (.fault (.semantic (.uninitializedLocation location))) after.heap ∧
      RecursiveNamedPublicPhysicalSessionState.PlainFault anchor actual.header invocation before.heap []
        (.uninitializedLocation location) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics
        (.semantic (.uninitializedLocation location)) call.reason ∧
      ∃ checkpoint : SourceCoreExecution.Checkpoint artifact,
        session.startHandlePacked handle .unit failureOptions.inputValidationFuel = .ok checkpoint ∧
        SelectedCompilationPublicSessionDirectFailureForward.FailureForwardAt issued.catalog.rows anchor
          issued.initial issued.support.profile fixture.recipe entries (.semantic (.uninitializedLocation location)) checkpoint after.heap := by
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  have invoked : session.InvokeAt entry.handle .unit failureOptions (.ok (.failed call.reason call.returned)) := by
    rw [entryHandle]; exact call.executed
  obtain ⟨sources, packing, arity, failure, after, size, trace, plain, diagnostic⟩ :=
    issued.reflect_direct_failure_plain before entry member entryType input invoked invocation
  have noParameters : actual.header.function.parameters = [] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.failedShape.inputs]
  have sourceCount : sources.length = 0 := by
    have actualArity := entrySource ▸ arity
    have count := SelectedCompilationPackedNamedArguments.global_count actualArity
      issued.support.bodyTyping.function_ids sourceAt.frame.instantiated
    rw [← sourceAt.frame.parameters, noParameters] at count
    exact count.symm
  have noSources := List.eq_nil_of_length_eq_zero sourceCount
  subst sources
  have applied := entrySource ▸ trace
  obtain ⟨location, failureEq, allocated, absent⟩ := actual.failed_heap sourceAt applied
  obtain ⟨checkpoint, accepted, _resumed⟩ := invoked
  have forward := issued.forward_direct_failure before entry member entryType input accepted ready packing arity trace
  have sourceCall : SourceCall anchor actual.header invocation before.heap []
      (.fault (.semantic (.uninitializedLocation location))) after.heap :=
    ⟨rawD, global, size, sourceAt, failureEq ▸ applied⟩
  refine ⟨after, location, allocated, absent, arity, sourceCall, ?_, failureEq ▸ diagnostic,
    checkpoint, ?_, failureEq ▸ forward⟩
  · refine ⟨rawD, global, sourceAt, ?_⟩
    simpa only [entrySource, failureEq, SelectedCompilationCertifiedPublicSession.DirectFailureProjection,
      Staging.Recursive.callableEvidence] using plain
  · simpa only [entryHandle] using accepted

structure IdentityMeaning
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.toIssued.State anchor session entries)
    (stages : ObservedStages fixture observed.identityRow)
    (call : ObservedSuccess session observed.identityRow.row.key) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session observed.identityRow.row.key [.word seed]
    runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture observed.identityRow.row
  headerEq : request.header = actual.header
  after : issued.toIssued.State anchor call.completion.session entries
  parameter : Dynamic.Location
  allocated : Dynamic.Heap.Allocates before.heap .word (some (.word seed)) parameter after.heap
  trace : SourceCall anchor request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function) before.heap [.word seed]
    (.value (.word seed)) after.heap
  plain : RecursiveNamedPublicPhysicalSessionState.PlainValue anchor request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function) before.heap [.word seed]
    (.word seed) after.heap
  forward : SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := entries)
    issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe (.word seed)
    ⟨call.checkpoint, call.started⟩ after.heap

theorem identity
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.toIssued.State anchor session entries)
    (stages : ObservedStages fixture observed.identityRow)
    (call : ObservedSuccess session observed.identityRow.row.key) (ready : session.ExportsReady) :
    Nonempty (IdentityMeaning before stages call) := by
  let actualCall : RecursiveNamedPublicPhysicalSessionState.Call session observed.identityRow.row.key [.word seed] runOptions :=
    ⟨⟨call.checkpoint, call.started⟩, call.completion, call.executed⟩
  obtain ⟨row, sameRow⟩ := eligible_row observed.identityRow
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row before actualCall.toStartedCall row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.identityRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [← actualEq, actual.identity_inputs]
    exact .cons (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩) .nil
  have raw : request.header.function.resultType = .word := by rw [← actualEq]; exact actual.identity_result_type
  have native : request.header.output = .word := by rw [← actualEq]; exact actual.identity_output
  obtain ⟨after, trace⟩ := issued.toIssued.reflect_scalar before (.word seed) actualCall
    call.returned request inputs raw native (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  obtain ⟨parameter, allocated⟩ := actual.identity_heap (actualEq.symm ▸ sourceAt) applied
  have sourceCall : SourceCall anchor request.header
      (RecursiveStageRegistry.scope stages.sidecar [] request.header.function) before.heap [.word seed]
      (.value (.word seed)) after.heap := ⟨rawD, global, size, sourceAt, applied⟩
  exact ⟨⟨request, actual, actualEq.symm, after, parameter, allocated, sourceCall, sourceCall.value_plain,
    issued.toIssued.forward_scalar before (.word seed) actualCall.toStartedCall request
      inputs raw native ready sourceCall⟩⟩

end Tests.SourceCoreSelectedLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFailurePublicExecution
/-! The original lexical program preserves its real failure, retained handle,
second failure and scalar continuation through one selected public issuer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreCertifiedLexicalFailure (First FreshIdentity observeFreshIdentity)
open Tests.SourceCoreDirectFailure (ObservedSequence observeSequence failureOptions)
open SelectedCompilationCertifiedPublicSession (Profiled)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicPhysicalSessionState (SourceCall PlainFault)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

private theorem failure_ready
    {artifact : SourceCoreExecution.Artifact} {session returned : SourceCoreExecution.Session artifact}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} {reason : Core.Word}
    {issued : Profiled fixture.recipe}
    {anchor : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {entries : List Entry} (state : issued.toIssued.State anchor session entries)
    (run : session.InvokeAt handle argument options (.ok (.failed reason returned)))
    (ready : session.ExportsReady) : returned.ExportsReady := by
  obtain ⟨checkpoint, started, resumed⟩ := run
  obtain ⟨indexedCheckpoint, atCheckpoint, actualStart⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession started
  obtain ⟨_actual, _generation, _value, _store, _completed, failed, returnedAt⟩ := resumed.indexed_failed atCheckpoint
  exact returnedAt.exportsReady_iff.mpr
    (failed.exportsReady (actualStart.initial_registry.exportsReady
      (state.atSession.exportsReady_iff.mp ready)))

structure RetainedSequenceMeaning (issued : Profiled fixture.recipe)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) where
  first : FirstMeaning issued failedStages sequence.first
  entry : Entry
  sourceType : entry.sourceType = .function .unit .word
  handle : entry.handle = sequence.named.handle
  arity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram) entry.source 0
  named : issued.toIssued.State first.initial.header sequence.named.completion.session [entry]
  namedHeap : named.heap = first.after.heap
  failed : issued.toIssued.State first.initial.header sequence.failed.returned [entry]
  location : Dynamic.Location
  allocated : Dynamic.Heap.Allocates named.heap .word none location failed.heap
  absent : Dynamic.Heap.Reads failed.heap location {type := .word, value := none}
  trace : SourceCall first.initial.header first.actual.header
    (RecursiveStageRegistry.scope failedStages.sidecar [] first.actual.header.function) named.heap []
    (.fault (.semantic (.uninitializedLocation location))) failed.heap
  plain : PlainFault first.initial.header first.actual.header
    (RecursiveStageRegistry.scope failedStages.sidecar [] first.actual.header.function) named.heap []
    (.uninitializedLocation location) failed.heap
  diagnostic : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults failed.receiving.result.diagnostics
    (.semantic (.uninitializedLocation location)) sequence.failed.reason
  checkpoint : SourceCoreExecution.Checkpoint sequence.first.artifact
  started : sequence.named.completion.session.startHandlePacked sequence.named.handle .unit
    failureOptions.inputValidationFuel = .ok checkpoint
  forward : SelectedCompilationPublicSessionDirectFailureForward.FailureForwardAt issued.catalog.rows
    first.initial.header issued.initial issued.support.profile fixture.recipe [entry]
    (.semantic (.uninitializedLocation location)) checkpoint failed.heap
  identity : IdentityMeaning failed identityStages sequence.next
  firstKept : Dynamic.Heap.Reads identity.after.heap first.location {type := .word, value := none}
  secondKept : Dynamic.Heap.Reads identity.after.heap location {type := .word, value := none}

/-- Actual compiler profile and public receipts supply all body support and
registry preservation; no Source trace or completion callback is supplied. -/
theorem retained_sequence_meaning
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ issued : Profiled fixture.recipe,
      Nonempty (RetainedSequenceMeaning issued failedStages identityStages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning profile failedStages sequence.first
  obtain ⟨entry, global, rawD, sourceType, handle, source, sourceAt, named, namedHeap⟩ :=
    remember_named first sequence.named
  have ready := sequence.named.issued.exportsReady sequence.first.returned_exportsReady
  obtain ⟨failed, location, allocated, absent, arity, trace, plain, diagnostic, checkpoint, started, forward⟩ :=
    invoke named first.actual entry (by simp) sourceType handle source (first.headerEq ▸ sourceAt)
      sequence.failed ready (RecursiveStageRegistry.scope failedStages.sidecar [] first.actual.header.function)
  obtain ⟨after⟩ := identity failed identityStages sequence.next (failure_ready named sequence.failed.executed ready)
  exact ⟨issued, ⟨⟨first, entry, sourceType, handle, arity, named, namedHeap, failed, location,
    allocated, absent, trace, plain, diagnostic, checkpoint, started, forward, after,
    after.allocated.preserves_read (allocated.preserves_read (namedHeap.symm ▸ first.absent)),
    after.allocated.preserves_read absent⟩⟩⟩

theorem closed_outcomes
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) (fresh : FreshIdentity fixture observed) :
    (∃ issued : Profiled fixture.recipe,
      Nonempty (RetainedSequenceMeaning issued failedStages identityStages sequence)) ∧
    (∃ issued : Profiled fixture.recipe, Nonempty (FreshMeaning issued identityStages fresh)) :=
  ⟨retained_sequence_meaning profile failedStages identityStages sequence, fresh_meaning profile identityStages fresh⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← observeProfile fixture
  let failedStages ← observeStages fixture observed.failedRow
  let identityStages ← observeStages fixture observed.identityRow
  let sequence ← observeSequence fixture observed
  let fresh ← observeFreshIdentity fixture observed
  have _meaning := closed_outcomes profile failedStages identityStages sequence fresh
  IO.println "SELECTED_PROFILED_FAILURES_PASS: original checker1000/compiler100; initial fault; retained named handle; direct fault at output fuel0; identity37 keeps two absent cells and the handle; fresh identity37; exact Dynamic outcomes and forward bounds"

end Tests.SourceCoreSelectedLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalSource
/-! One unchanged original function captures an identity lambda as a generalized
local, stores its Word call result in an ordinary local, then reaches an absent ordinary cell before a later Bool call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function local(flag: Bool) returns (Word, Bool) { let f = lam(value) { return value; }; let y = f(11); let absent: Word; return (absent, f(flag)); }"}] }
def options : SourceCoreCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 300000, outputValidationFuel := 1000}

structure WordNode (source : TypedSource) where
  node : ExpressionNode
  literal : Syntax.CoreLiteralValue
  resolution : IntegerLiteralResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .integerLiteral literal resolution
  target : resolution.targetType = .word
  requirements : node.requirements = [resolution.requirement]
  coercions : node.coercions = []

theorem WordNode.evaluates {source : TypedSource} (node : WordNode source)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context node.node.id type) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id
      (.word (Word.ofNatModulo node.resolution.rawValue)) heap := by
  have valid : IntegerLiteralValid context node.literal node.resolution := by
    cases typed with
    | intro contains raw _ _ _ _ =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans node.found)
      rw [node.form] at raw
      cases raw with | integerLiteral valid => exact valid
  have constructs : Dynamic.ResolvedIntegerLiteralConstructs context node.literal node.resolution
      (.word (Word.ofNatModulo node.resolution.rawValue)) := by
    cases valid with
    | word meaning target evidence =>
      generalize resolutionEq : node.resolution = resolution at *
      cases resolution with
      | mk value type requirement =>
        dsimp only at target
        subst type
        exact .word meaning evidence
    | integer _ target _ => rw [node.target] at target; cases target
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]; exact .integerLiteral (by rw [node.requirements,node.coercions]; rfl) constructs
  · rw [node.coercions]; exact .nil

structure CallShape (source : TypedSource) (binder : TypedBinder)
    (argument : ExpressionId) (type : TypeSystem.Ty) where
  callee : Tests.SourceCoreNamedBranch.Read source binder (.function type type)
  node : ExpressionNode
  metadata : IndirectCallResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .call callee.node.id [argument] (.indirect metadata)
  arity : metadata.argumentCount = 1
  argumentCoercions : metadata.argumentCoercions = []
  requirements : node.requirements = []
  coercions : node.coercions = []

structure Shape (source : TypedSource) where
  flag : TypedBinder
  binder : TypedBinder
  parameter : TypedBinder
  typeVariable : TypeSystem.TypeVarId
  initialized : StatementNode
  lambda : ExpressionNode
  identityReturn : StatementNode
  parameterRead : Tests.SourceCoreNamedBranch.Read source parameter (.variable typeVariable)
  literal : WordNode source
  flagRead : Tests.SourceCoreNamedBranch.Read source flag .bool
  wordCall : CallShape source binder literal.node.id .word
  boolCall : CallShape source binder flagRead.node.id .bool
  valueBinder : TypedBinder
  valueInitialized : StatementNode
  absentBinder : TypedBinder
  absentDeclared : StatementNode
  absentRead : Tests.SourceCoreNamedBranch.Read source absentBinder .word
  tuple : ExpressionNode
  returned : StatementNode
  inputs : source.inputs = [flag]
  flagScheme : flag.scheme = .mono .bool
  scheme : binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) (.variable typeVariable)⟩
  schemeRequirements : binder.schemeRequirements = []
  parameterScheme : parameter.scheme = .mono (.variable typeVariable)
  parameterRequirements : parameter.schemeRequirements = []
  valueScheme : valueBinder.scheme = .mono .word
  absentScheme : absentBinder.scheme = .mono .word
  roots : source.roots = [.statement initialized.id, .statement valueInitialized.id, .statement absentDeclared.id, .statement returned.id]
  initializedFound : source.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl binder (some lambda.id)
  lambdaFound : source.lookupExpression? lambda.id = some lambda
  lambdaForm : lambda.form = .lambda [parameter] (.variable typeVariable) [identityReturn.id]
  lambdaRaw : lambda.rawType = binder.scheme.body
  lambdaType : lambda.type = binder.scheme.body
  lambdaRequirements : lambda.requirements = []
  lambdaCoercions : lambda.coercions = []
  identityFound : source.lookupStatement? identityReturn.id = some identityReturn
  identityForm : identityReturn.form = .returnStmt (some parameterRead.node.id)
  literalValue : literal.resolution.rawValue = 11
  valueFound : source.lookupStatement? valueInitialized.id = some valueInitialized
  valueForm : valueInitialized.form = .letDecl valueBinder (some wordCall.node.id)
  absentFound : source.lookupStatement? absentDeclared.id = some absentDeclared
  absentForm : absentDeclared.form = .letDecl absentBinder none
  tupleFound : source.lookupExpression? tuple.id = some tuple
  tupleForm : tuple.form = .tuple [absentRead.node.id, boolCall.node.id]
  tupleRequirements : tuple.requirements = []
  tupleCoercions : tuple.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some tuple.id)

def Shape.descriptor {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) : Dynamic.GeneralizedClosure :=
  Dynamic.GeneralizedClosure.ofDirectLambda context source environment shape.binder shape.lambda.id
    [shape.parameter] (.variable shape.typeVariable) [shape.identityReturn.id]

def Shape.allocatedHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨before.cells ++ [{ type := shape.binder.scheme.body, value := none, generalized := some (shape.descriptor context environment) }]⟩

theorem Shape.captures {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) :
    Dynamic.GeneralizedClosureCaptures context source environment shape.binder shape.lambda.id
      (shape.descriptor context environment) :=
  .directLambda (lookupExpression?_sound shape.lambdaFound) shape.lambdaForm
    shape.lambdaRaw shape.lambdaType shape.lambdaRequirements shape.lambdaCoercions

/-- The original let copies its environment once and stores one principal
descriptor over the copies. It performs no lambda body call and selects
neither the Word nor Bool instance at allocation. -/
theorem Shape.initializes {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context nextContext : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) {environment captured : Dynamic.Environment}
    {before middle : Dynamic.Heap}
    (snapshot : Dynamic.EnvironmentCopies source environment before captured middle)
    (extended : BinderExtends source.owner context shape.binder nextContext) :
    Dynamic.StatementExecutes program context evidence source environment before shape.initialized.id
      nextContext (.fallthrough ((shape.binder.id, ⟨middle.cells.length⟩) :: environment))
      (shape.allocatedHeap context captured middle) := by
  apply Dynamic.StatementExecutes.letInitializedGeneralized
    (lookupStatement?_sound shape.initializedFound) shape.initializedForm snapshot
    (shape.captures context captured) (by rw [shape.scheme]; simp) extended
  exact .append

end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

def compileFixture : IO CompiledFixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "generalized local artifact absent")
      | some cached =>
        match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError (reprStr error))
        | .ok recipe =>
          match facade : SourceCoreExecution.prepare source with
          | .error error => throw (IO.userError (reprStr error))
          | .ok publicCompiled =>
            have sameProgram : recipe.compiled.sourceProgram = program :=
              (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
                ((source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated))
            return {
              recipe := recipe
              checked := by rw [sameProgram]; exact checked
              seeds := seeds
              facade := publicCompiled
              accepted := by
                rw [sameProgram]
                simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
              selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade }


structure Row (fixture : CompiledFixture) where
  original : SourceSpecialization.SpecializedFunction
  member : original ∈ fixture.recipe.compiled.validationPlan.specializations
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = original.key
  substitution : original.parameterSubstitution = []
  ordinary : original.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ original.function.typedBody.inputs, binder.comptime = false

def observeRow (fixture : CompiledFixture) (name : String) : IO (Row fixture) := do
  let some signature := fixture.recipe.compiled.sourceProgram.signatures.functions.find? (fun signature => signature.name == name)
    | throw (IO.userError "generalized local original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "generalized local original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "generalized local global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "generalized local substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "generalized local ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "generalized local ordinary parameters"
      return {
        original := original
        member := List.mem_of_find?_eq_some found
        global := global
        index := index
        slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
        globalKey := globalKey
        substitution := substitution
        ordinary := ordinary
        ordinaryInputs := by
          intro binder member
          have selected := List.all_eq_true.mp ordinaryInputs binder member
          cases marker : binder.comptime <;> simp_all }
    | _ => throw (IO.userError "generalized local unique physical slot")

def observeCall (source : TypedSource) (binder : TypedBinder) (argument : ExpressionId)
    (type : TypeSystem.Ty) (callee node : ExpressionNode) : IO (CallShape source binder argument type) := do
  let read ← Tests.SourceCoreNamedBranch.observeRead source binder callee (.function type type)
  let .call _ _ (.indirect metadata) := node.form | throw (IO.userError "generalized original indirect call")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "generalized call identity"
  let ⟨form⟩ ← observed (node.form = .call read.node.id [argument] (.indirect metadata)) "generalized call order"
  let ⟨arity⟩ ← observed (metadata.argumentCount = 1) "generalized original arity"
  let ⟨argumentCoercions⟩ ← observed (metadata.argumentCoercions = []) "generalized argument coercions"
  let ⟨requirements⟩ ← observed (node.requirements = []) "generalized call requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "generalized call coercions"
  return ⟨read,node,metadata,found,form,arity,argumentCoercions,requirements,coercions⟩

def observeShape (source : TypedSource) : IO (Shape source) := do
  let [flag] := source.inputs | throw (IO.userError "generalized input")
  let [.expression parameterNode,.statement identityReturn,.expression lambda,.statement initialized,
       .expression literalNode,.expression wordCallee,.expression first,.statement valueInitialized,
       .statement absentDeclared,.expression absentNode,.expression flagNode,.expression boolCallee,.expression second,
       .expression tuple,.statement returned] := source.nodes
    | throw (IO.userError "generalized original graph")
  let .letDecl binder _ := initialized.form | throw (IO.userError "generalized original binder")
  let .lambda [parameter] (.variable typeVariable) _ := lambda.form
    | throw (IO.userError "generalized principal lambda")
  let .letDecl valueBinder _ := valueInitialized.form | throw (IO.userError "interleaved ordinary binder")
  let .letDecl absentBinder none := absentDeclared.form | throw (IO.userError "faulting absent binder")
  let absentRead ← Tests.SourceCoreNamedBranch.observeRead source absentBinder absentNode .word
  let parameterRead ← Tests.SourceCoreNamedBranch.observeRead source parameter parameterNode (.variable typeVariable)
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead source flag flagNode .bool
  let .integerLiteral raw resolution := literalNode.form | throw (IO.userError "generalized original literal")
  let ⟨literalFound⟩ ← observed (source.lookupExpression? literalNode.id = some literalNode) "generalized literal identity"
  let ⟨literalForm⟩ ← observed (literalNode.form = .integerLiteral raw resolution) "generalized literal form"
  let ⟨literalTarget⟩ ← observed (resolution.targetType = .word) "generalized literal Word"
  let ⟨literalRequirements⟩ ← observed (literalNode.requirements = [resolution.requirement]) "generalized literal requirements"
  let ⟨literalCoercions⟩ ← observed (literalNode.coercions = []) "generalized literal coercions"
  let literal : WordNode source :=
    ⟨literalNode,raw,resolution,literalFound,literalForm,literalTarget,literalRequirements,literalCoercions⟩
  let wordCall ← observeCall source binder literalNode.id .word wordCallee first
  let boolCall ← observeCall source binder flagRead.node.id .bool boolCallee second
  let ⟨inputs⟩ ← observed (source.inputs = [flag]) "generalized original inputs"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "generalized Bool input"
  let ⟨scheme⟩ ← observed (binder.scheme = ⟨[typeVariable], .function (.variable typeVariable) (.variable typeVariable)⟩) "generalized principal scheme"
  let ⟨schemeRequirements⟩ ← observed (binder.schemeRequirements = []) "generalized principal requirements"
  let ⟨parameterScheme⟩ ← observed (parameter.scheme = .mono (.variable typeVariable)) "generalized principal parameter"
  let ⟨parameterRequirements⟩ ← observed (parameter.schemeRequirements = []) "generalized parameter requirements"
  let ⟨valueScheme⟩ ← observed (valueBinder.scheme = .mono .word) "interleaved ordinary scheme"
  let ⟨absentScheme⟩ ← observed (absentBinder.scheme = .mono .word) "faulting absent scheme"
  let ⟨roots⟩ ← observed (source.roots = [.statement initialized.id,.statement valueInitialized.id,.statement absentDeclared.id,.statement returned.id]) "generalized original root order"
  let ⟨initializedFound⟩ ← observed (source.lookupStatement? initialized.id = some initialized) "generalized let identity"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl binder (some lambda.id)) "generalized let initializer"
  let ⟨lambdaFound⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "generalized lambda identity"
  let ⟨lambdaForm⟩ ← observed (lambda.form = .lambda [parameter] (.variable typeVariable) [identityReturn.id]) "generalized original lambda body"
  let ⟨lambdaRaw⟩ ← observed (lambda.rawType = binder.scheme.body) "generalized principal raw type"
  let ⟨lambdaType⟩ ← observed (lambda.type = binder.scheme.body) "generalized principal result type"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "generalized initializer requirements"
  let ⟨lambdaCoercions⟩ ← observed (lambda.coercions = []) "generalized initializer coercions"
  let ⟨identityFound⟩ ← observed (source.lookupStatement? identityReturn.id = some identityReturn) "generalized identity return lookup"
  let ⟨identityForm⟩ ← observed (identityReturn.form = .returnStmt (some parameterRead.node.id)) "generalized identity return form"
  let ⟨literalValue⟩ ← observed (literal.resolution.rawValue = 11) "generalized original literal value"
  let ⟨valueFound⟩ ← observed (source.lookupStatement? valueInitialized.id = some valueInitialized) "interleaved ordinary let identity"
  let ⟨valueForm⟩ ← observed (valueInitialized.form = .letDecl valueBinder (some wordCall.node.id)) "interleaved ordinary initializer"
  let ⟨absentFound⟩ ← observed (source.lookupStatement? absentDeclared.id = some absentDeclared) "faulting absent lookup"
  let ⟨absentForm⟩ ← observed (absentDeclared.form = .letDecl absentBinder none) "faulting absent declaration"
  let ⟨tupleFound⟩ ← observed (source.lookupExpression? tuple.id = some tuple) "generalized tuple lookup"
  let ⟨tupleForm⟩ ← observed (tuple.form = .tuple [absentRead.node.id,boolCall.node.id]) "generalized ordered calls"
  let ⟨tupleRequirements⟩ ← observed (tuple.requirements = []) "generalized tuple requirements"
  let ⟨tupleCoercions⟩ ← observed (tuple.coercions = []) "generalized tuple coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "generalized outer return lookup"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some tuple.id)) "generalized outer return form"
  return ⟨flag,binder,parameter,typeVariable,initialized,lambda,identityReturn,parameterRead,literal,flagRead,
    wordCall,boolCall,valueBinder,valueInitialized,absentBinder,absentDeclared,absentRead,tuple,returned,inputs,flagScheme,scheme,schemeRequirements,parameterScheme,
    parameterRequirements,valueScheme,absentScheme,roots,initializedFound,initializedForm,lambdaFound,lambdaForm,lambdaRaw,
    lambdaType,lambdaRequirements,lambdaCoercions,identityFound,identityForm,literalValue,
    valueFound,valueForm,absentFound,absentForm,tupleFound,tupleForm,tupleRequirements,tupleCoercions,returnedFound,returnedForm⟩


end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalProgramProfile
/-! The unchanged original program retains a profile for every actual cached
named row. This packet certifies compiler syntax and preparation; original
declarative program typing remains a separate proof obligation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 1
  cached : original.recipe.compiled.indexed.base.functions.length = 1
  profiles : CellAwareFaultingNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  if originals : original.recipe.compiled.sourceProgram.functions.length = 1 then
    if cached : original.recipe.compiled.indexed.base.functions.length = 1 then
      match CellAwareFaultingNamedProgramProfiles.profile? original.recipe.compiled.indexed with
      | none => throw (IO.userError "original generalized program profile rejected")
      | some profiles => pure ⟨original, originals, cached, profiles⟩
    else throw (IO.userError "original generalized full cache changed")
  else throw (IO.userError "original generalized source count changed")

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

theorem ProfiledFixture.body (fixture : ProfiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared fixture.original.recipe.compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.original.recipe.compiled
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    {entry : SourceCoreCallableIndexedPrograms.Entry fixture.original.recipe.compiled.indexed.layouts}
    (member : entry ∈ fixture.original.recipe.compiled.indexed.entries) :
    Nonempty (CellAwareFaultingNamedBodySupport.Body prepared.compilation
      (CellAwareNamedBodyProducer.Certificate prepared.compilation)
      (RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial fixture.original.recipe.compiled.compatible.checked) header)
      header.context header.function.resultType) := by
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  exact CellAwareFaultingNamedBodyReceipt.of_header prepared aligned fixture.ready wellFormed member
    (profile.for_compilation prepared.compilation)

def checkProgramProfile : IO Unit := do
  let _fixture ← compileProfiledFixture
  IO.println "INTERLEAVED_LOCAL_COMPLETE_STATIC_INVENTORY: originals1/cache1/profile1"

end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalInventory
/-! The actual original row supplies the complete one-position named inventory.
Its selected compiler packet is retained through public root selection; no
other cached row is removed or replaced by a body execution assumption. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure SelectedInventory (fixture : ProfiledFixture) (row : Row fixture.original) where
  input : Input fixture.original.recipe.compiled
  original : input.row = row.original
  packet : Issued input
  position : input.prepared.index = 0
  complete : fixture.original.recipe.compiled.indexed.base.functions = [input.prepared.named]

def SelectedInventory.rows {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) : Inventory [selected.input] :=
  .cons selected.packet .nil

theorem SelectedInventory.distinct {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    ([selected.input].map (fun input => input.prepared.index)).Nodup := by
  simp

theorem ProfiledFixture.inventory (fixture : ProfiledFixture) (row : Row fixture.original)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)) :
    Nonempty (SelectedInventory fixture row) := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile
    fixture.original.accepted fixture.original.selected row.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.original.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]
    intro name value found
    cases found
  let input : Input fixture.original.recipe.compiled := {
    row := row.original
    prepared := prepared
    range := range
    ordinaryReturn := row.ordinary
    ordinaryParameters := fun binder member => row.ordinaryInputs binder member
    target := by
      have target := SelectedCompilationCatalog.retained_target fixture.original.recipe.compiled
        wellFormed.signatures prepared.selected (prepared.same.symm ▸ prepared.origin)
      simpa only [prepared.same] using target
    slot := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot
      fixture.original.recipe.compiled prepared.selected }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue wellFormed input
  have bound := (List.getElem?_eq_some_iff.mp prepared.selected).1
  rw [fixture.cached] at bound
  have position : prepared.index = 0 := by omega
  obtain ⟨named, complete⟩ := List.length_eq_one_iff.mp fixture.cached
  have selected := prepared.selected
  rw [complete, position] at selected
  have same : named = prepared.named := Option.some.inj selected
  exact ⟨⟨input, rfl, packet, position, by simpa only [same] using complete⟩⟩

theorem SelectedInventory.root_selection {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row)
    {root : SourceCoreIndexedSession.Root fixture.original.recipe.compiled}
    (member : root ∈ fixture.original.recipe.roots) :
    RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial fixture.original.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.original.recipe.compiled.indexed)
      (program := Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      (headers selected.rows) root selected.packet.header := by
  obtain ⟨entry, present, shape⟩ := SourceCoreIndexedSession.Recipe.prepare_roots fixture.ready member
  obtain ⟨named, index, found, rest⟩ := shape
  have atIndex : fixture.original.recipe.compiled.indexed.base.functions[index]? = some named :=
    List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have bound := (List.getElem?_eq_some_iff.mp atIndex).1
  rw [fixture.cached] at bound
  have indexEq : index = 0 := by omega
  have sourceSelected := selected.input.prepared.selected
  rw [selected.position] at sourceSelected
  rw [indexEq] at atIndex
  have same : selected.input.prepared.named = named := Option.some.inj (sourceSelected.symm.trans atIndex)
  refine ⟨by exact List.mem_cons_self, entry, present, ⟨named, index, found, rest⟩, ?_⟩
  rw [selected.packet.aligned.named, selected.packet.aligned.slot]
  change _ = some (selected.input.prepared.named, selected.input.prepared.index)
  simpa only [selected.position, same, indexEq] using found

theorem SelectedInventory.header_original {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    selected.packet.header.named.specialized = row.original :=
  (congrArg (·.specialized) selected.packet.aligned.named).trans
    (selected.input.prepared.same.trans selected.original)

end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalTrace
/-! Independent Source execution of the original identity body after a genuine
local-scheme instance has been selected. No target execution is a premise.
Closures capture by value: the generalized `let` copies the function's
environment once, and each instance call copies the descriptor's captures
again before allocating its parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceSemanticsCaptureCopies

/-- The exact materialized body copies the descriptor's captures, reads its
newly allocated parameter and returns it. The supplied frame is static Source
code/evidence validity. -/
theorem Shape.identity_applies {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence callerEvidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (argument : Dynamic.Value)
    {entry : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured before entry copied)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution evidence)) :
    Dynamic.CallableApplies program context callerEvidence evidence before
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution evidence))
      [argument] argument
      ⟨copied.cells ++ [{type := (shape.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  let function := (shape.descriptor definitionContext captured).instantiate substitution evidence
  let parameter := shape.parameter.applySubstitution substitution
  let after : Dynamic.Heap := ⟨copied.cells ++ [{type := parameter.scheme.body, value := some argument}]⟩
  have allocation : Dynamic.Heap.Allocates copied parameter.scheme.body (some argument)
      ⟨copied.cells.length⟩ after := .append
  have read : Dynamic.ExpressionEvaluates program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨copied.cells.length⟩) :: entry)
      after shape.parameterRead.node.id argument after := by
    apply Dynamic.ExpressionEvaluates.intro
      (FlexibleSubstitution.ContainsExpression.applySubstitution substitution
        (lookupExpression?_sound shape.parameterRead.found))
    · simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
        shape.parameterRead.form, shape.parameterRead.requirements, shape.parameterRead.coercions]
      exact .local rfl .head allocation.reads_new rfl rfl
    · simp only [ExpressionNode.applySubstitution, shape.parameterRead.coercions, List.map_nil]
      exact .nil
  have returned : Dynamic.StatementExecutes program
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      evidence function.source ((parameter.id, ⟨copied.cells.length⟩) :: entry)
      after shape.identityReturn.id
      (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements)
      (.returned argument) after := by
    exact .returnValue
      (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
        (lookupStatement?_sound shape.identityFound))
      (by simp only [StatementNode.applySubstitution, shape.identityForm,
        StatementForm.applySubstitution]) read
  have parameters : ∃ types callContext,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext := by
    rcases frame.code.occurrence with ⟨id, node, _contains, form, _raw, typed⟩
    rw [form] at typed
    generalize rawEq : TypeSystem.Ty.function
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)))
      function.resultType = raw at typed
    cases typed with
    | lambda names parameters body completes => exact ⟨_, _, parameters⟩
  obtain ⟨types, callContext, parameters⟩ := parameters
  have parameterList : function.parameters = [parameter] := rfl
  rw [parameterList] at parameters
  cases parameters with
  | cons scheme extended tail =>
    cases tail
    cases extended with
    | intro wellformed fresh =>
      apply Dynamic.CallableApplies.closure rfl frame
        (parameterList.symm ▸ MonoBindersExtend.cons scheme (.intro wellformed fresh) (.nil _)) copy
      · exact .cons allocation (.nil _ _)
      · apply Dynamic.FunctionStatementsExecute.singleton
          (FlexibleSubstitution.ContainsStatement.applySubstitution substitution
            (lookupStatement?_sound shape.identityFound))
        · intro expression impossible
          simp only [StatementNode.applySubstitution, shape.identityForm,
            StatementForm.applySubstitution] at impossible
          cases impossible
        · exact returned
      · rfl

/-- A read selects the actual instance before the ordered argument evaluation.
The call copies the captures and allocates the identity parameter only after
that argument finishes. -/
theorem Shape.invoke {source : TypedSource} (shape : Shape source)
    {argumentId : ExpressionId} {type : TypeSystem.Ty}
    (call : CallShape source shape.binder argumentId type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence produced : Dynamic.EvidenceEnvironment)
    {before argumentsHeap : Dynamic.Heap} {argument : Dynamic.Value}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment shape.binder.id location)
    (read : Dynamic.Heap.Reads before location cell)
    (descriptor : cell.generalized = some (shape.descriptor definitionContext captured))
    (fields : Dynamic.RuntimeContextFields definitionContext context)
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type type) [] substitution produced)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution)))
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before argumentId argument argumentsHeap)
    {entry : Dynamic.Environment} {copied : Dynamic.Heap}
    (copy : Dynamic.EnvironmentCopies (source.applySubstitution substitution) captured argumentsHeap entry copied) :
    Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      argument ⟨copied.cells ++ [{type := (shape.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  have callee : Dynamic.ExpressionEvaluates program context evidence source environment before
      call.callee.node.id
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution))) before := by
    apply Dynamic.ExpressionEvaluates.generalizedLocal (owned := [])
      (lookupExpression?_sound call.callee.found) call.callee.form
      (by rw [call.callee.requirements, call.callee.coercions]; rfl)
      lookup read descriptor fields
    · rw [call.callee.raw]; exact instantiation
    · rw [call.callee.coercions]; exact .nil
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound call.found)
  · rw [call.form]
    exact .indirectCall
      (by rw [call.requirements, call.argumentCoercions, call.coercions]; rfl)
      callee (.cons argumentTrace .nil) (.singleton argument)
      (by rw [call.argumentCoercions]; exact .nil) (.singleton argument)
      (by rw [call.arity]; rfl) (by rw [call.arity]; rfl)
      (shape.identity_applies captured substitution _ evidence argumentsHeap argument copy frame)
  · rw [call.coercions]; exact .nil

/-- The two runtime instances use an exact singleton substitution. Original
scheme validity and the requested ground type are the only typing inputs. -/
theorem Shape.instance {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    {type : TypeSystem.Ty} (wellformed : SchemeWellFormed context shape.binder.scheme)
    (ground : TypeWellFormed context type) :
    Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type type) [] [(shape.typeVariable, type)] [] := by
  refine ⟨LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements,
    wellformed, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · rw [shape.scheme]; exact ExactSubstitution.singleton _ _
  · intro typeVariable replacement member
    have same := List.mem_singleton.mp member
    cases same
    exact ground
  · simp [shape.scheme, TypeSystem.Substitution.apply, TypeSystem.Substitution.lookup?]
  · intro id member; cases member
  · rw [instantiateLocalSchemePredicates, shape.schemeRequirements]
    exact .nil

/-- Deep typing of the actual captured descriptor supplies the static invocation
frame for each instance, independently of executing either call. -/
theorem Shape.frame {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context nextContext : SourceSemantics.Context}
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (evidence : Dynamic.EvidenceEnvironment) {type : TypeSystem.Ty}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : Dynamic.GeneralizedClosureWellTyped nextContext heap (shape.descriptor context environment))
    (fields : Dynamic.RuntimeContextFields context nextContext)
    (signatures : nextContext.signatures = program.signatures)
    (covers : evidence.Covers nextContext)
    (wellformed : SchemeWellFormed nextContext shape.binder.scheme)
    (ground : TypeWellFormed nextContext type) :
    Dynamic.ClosureFrame program
      ((shape.descriptor context environment).instantiate [(shape.typeVariable, type)]
        (evidence.applySubstitution [(shape.typeVariable, type)])) := by
  have materialized := Dynamic.GeneralizedClosureWellTyped.instantiateHasType
    catalog typed fields covers (shape.instance evidence wellformed ground)
  obtain ⟨_parameter, _result, same, code, closed, _captured⟩ := materialized.closure_function_inv
  exact ⟨same.trans signatures, code.owner, code, code.requirement_ledger.idsUnique, closed⟩

/-- The heap after the generalized `let`: the copies of the function's
environment, then the principal descriptor over those copies. -/
def Shape.declaredHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  shape.allocatedHeap context (copies source environment before).1 (copies source environment before).2

/-- The Word call copies the descriptor's captures, then allocates its
parameter. -/
def Shape.wordHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(copies source (copies source environment before).1 (shape.declaredHeap context environment before)).2.cells ++
    [{type := (shape.parameter.applySubstitution [(shape.typeVariable, .word)]).scheme.body, value := some (.word (Core.Word.ofNatModulo 11))}]⟩

def Shape.valueHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(shape.wordHeap context environment before).cells ++
    [{type := shape.valueBinder.scheme.body, value := some (.word (Core.Word.ofNatModulo 11))}]⟩

def Shape.finalHeap {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(shape.valueHeap context environment before).cells ++
    [{type := shape.absentBinder.scheme.body, value := none}]⟩

def Shape.failure {source : TypedSource} (shape : Shape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) : Dynamic.SemanticFault :=
  .uninitializedLocation ⟨(shape.valueHeap context environment before).cells.length⟩

/-- The environment copies, the Word call with its own copies and the ordinary
allocation occur before the absent read. The later Bool call, and so its copies,
is not evaluated after the first tuple element fails. -/
theorem Shape.body_trace {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context nextContext valueContext finalContext : SourceSemantics.Context}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)
    (before : Dynamic.Heap)
    (unique : NodeOccurrencesUnique source)
    (extended : BinderExtends source.owner context shape.binder nextContext)
    (valueExtended : BinderExtends source.owner nextContext shape.valueBinder valueContext)
    (absentExtended : BinderExtends source.owner valueContext shape.absentBinder finalContext)
    (fields : Dynamic.RuntimeContextFields context nextContext)
    (wellformed : SchemeWellFormed nextContext shape.binder.scheme)
    (word : TypeWellFormed nextContext .word)
    {literalType : TypeSystem.Ty}
    (literal : ExpressionHasType source nextContext shape.literal.node.id literalType)
    (readable : Readable before environment)
    (wordFrame : Dynamic.ClosureFrame program
      ((shape.descriptor context (copies source environment before).1).instantiate [(shape.typeVariable, .word)]
        (evidence.applySubstitution [(shape.typeVariable, .word)]))) :
    Dynamic.FunctionStatementsFault program context evidence source environment before
      [shape.initialized.id, shape.valueInitialized.id, shape.absentDeclared.id, shape.returned.id] finalContext
      (shape.failure context environment before) (shape.finalHeap context environment before) := by
  let captured := (copies source environment before).1
  let middle := (copies source environment before).2
  have snapshot : Dynamic.EnvironmentCopies source environment before captured middle :=
    copies_spec source readable
  let allocated := shape.declaredHeap context environment before
  let first := shape.wordHeap context environment before
  let bound := shape.valueHeap context environment before
  let after := shape.finalHeap context environment before
  let locals := (shape.binder.id, ⟨middle.cells.length⟩) :: environment
  have allocation : Dynamic.Heap.AllocatesGeneralized middle (shape.descriptor context captured)
      ⟨middle.cells.length⟩ allocated := .append
  have capturedAllocated : Readable allocated captured :=
    (Readable.of_copies snapshot readable).mono (Dynamic.HeapMetadataExtend.of_generalized_allocation allocation)
  have wordCopy := copies_spec_applySubstitution [(shape.typeVariable, .word)] source capturedAllocated
  have literalTrace : Dynamic.ExpressionEvaluates program nextContext evidence source locals
      allocated shape.literal.node.id (.word (Core.Word.ofNatModulo 11)) allocated := by
    simpa only [shape.literalValue] using shape.literal.evaluates evidence locals allocated unique literal
  have firstTrace := shape.invoke shape.wordCall captured locals [(shape.typeVariable, .word)] evidence []
    Dynamic.Environment.LooksUp.head allocation.reads_new rfl fields
    (shape.instance evidence wellformed word) wordFrame literalTrace wordCopy
  have valueAllocation : Dynamic.Heap.Allocates first shape.valueBinder.scheme.body
      (some (.word (Core.Word.ofNatModulo 11))) ⟨first.cells.length⟩ bound := .append
  let valueLocals := (shape.valueBinder.id, ⟨first.cells.length⟩) :: locals
  have initialized : Dynamic.StatementExecutes program nextContext evidence source locals allocated shape.valueInitialized.id
      valueContext (.fallthrough valueLocals) bound :=
    .letInitialized (lookupStatement?_sound shape.valueFound) shape.valueForm firstTrace
      (by rw [shape.valueScheme]; rfl) valueExtended valueAllocation
  have absentAllocation : Dynamic.Heap.Allocates bound shape.absentBinder.scheme.body none
      ⟨bound.cells.length⟩ after := .append
  let absentLocals := (shape.absentBinder.id, ⟨bound.cells.length⟩) :: valueLocals
  have absent : Dynamic.StatementExecutes program valueContext evidence source valueLocals bound
      shape.absentDeclared.id finalContext (.fallthrough absentLocals) after :=
    .letUninitialized (lookupStatement?_sound shape.absentFound) shape.absentForm
      (by rw [shape.absentScheme]; rfl) absentExtended absentAllocation
  have absentFault : Dynamic.ExpressionFaults program finalContext evidence source absentLocals after
      shape.absentRead.node.id (shape.failure context environment before) after := by
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound shape.absentRead.found)
    rw [shape.absentRead.form]
    exact .localUninitialized (owned := []) (by rw [shape.absentRead.requirements, shape.absentRead.coercions]; rfl)
      .head absentAllocation.reads_new rfl rfl (by simp [shape.absentScheme, TypeSystem.Scheme.mono, TypeSystem.Ty.word ])
  have tupleFault : Dynamic.ExpressionFaults program finalContext evidence source absentLocals after
      shape.tuple.id (shape.failure context environment before) after := by
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound shape.tupleFound)
    rw [shape.tupleForm]
    exact .tuple (by rw [shape.tupleRequirements, shape.tupleCoercions]; rfl) (.head absentFault)
  exact .tail (shape.initializes evidence snapshot extended)
    (.tail initialized (.tail absent (.singleton
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tupleFault))))

end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalSourceFirst
/-! Original checker typing supplies both materialized closure frames before
the independent Source execution. No completed native call is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceSemanticsCaptureCopies

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

private theorem Shape.literal_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context shape.wordCall.node.id type) :
    ∃ literalType, ExpressionHasType source context shape.literal.node.id literalType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.wordCall.found)
    rw [shape.wordCall.form] at raw
    cases raw with
    | indirectCall _ arguments _ =>
      cases arguments with
      | cons literal _ => exact ⟨_, literal⟩

/-- Original declaration typing supplies the actual Word instance frame over
the copies of the lexical environment and both ordinary binder extensions
before the independent fault trace is built. -/
theorem Shape.body_from_source {source : TypedSource} (shape : Shape source)
    {program : SourceSemantics.Program} {context final : SourceSemantics.Context}
    {control : ControlContext} {facts : BodyFacts}
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)
    (before : Dynamic.Heap)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (typed : StatementsHaveType source control context
      [shape.initialized.id, shape.valueInitialized.id, shape.absentDeclared.id, shape.returned.id] final facts) :
    ∃ nextContext, Dynamic.FunctionStatementsFault program context evidence source environment before
      [shape.initialized.id, shape.valueInitialized.id, shape.absentDeclared.id, shape.returned.id] nextContext
      (shape.failure context environment before) (shape.finalHeap context environment before) := by
  have unique := runtime.graph.nodeOccurrencesUnique
  obtain ⟨next, _, _, first, rest⟩ := head_tail typed
  have original := form_at unique shape.initializedFound first
  rw [shape.initializedForm] at original
  cases original with
  | letInitialized _ monomorphic _ =>
    rw [shape.scheme] at monomorphic
    cases monomorphic
  | letInitializedGeneralized polymorphic requirements generalizes initializer extended =>
    have readable := Readable.of_agrees locals
    have snapshot := copies_spec source readable
    have descriptorTyped := (shape.captures context (copies source environment before).1).wellTyped runtime
      (snapshot.agrees locals) polymorphic requirements generalizes initializer extended
    have fields := Dynamic.RuntimeContextFields.ofBinderExtends extended
    obtain ⟨valueContext, _, _, valueStatement, absentRest⟩ := head_tail rest
    have originalValue := form_at unique shape.valueFound valueStatement
    rw [shape.valueForm] at originalValue
    cases originalValue with
    | letInitializedGeneralized impossible _ _ _ _ =>
      exact False.elim (impossible (by rw [shape.valueScheme]; rfl))
    | letInitialized valueTyped _ valueExtended =>
      obtain ⟨literalType, literal⟩ := shape.literal_typed unique valueTyped
      obtain ⟨absentContext, _, _, absentStatement, _remaining⟩ := head_tail absentRest
      have originalAbsent := form_at unique shape.absentFound absentStatement
      rw [shape.absentForm] at originalAbsent
      cases originalAbsent with
      | letUninitialized _ absentExtended =>
        cases extended with
        | intro wellformed fresh =>
          have scheme : SchemeWellFormed
              (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements)
              shape.binder.scheme := {
            binders := wellformed.scheme.binders.withLocal _ _ _
            quantified_nodup := wellformed.scheme.quantified_nodup
            body := wellformed.scheme.body.withLocal _ _ _
          }
          have word : TypeWellFormed
              (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements) .word :=
            ⟨scheme.binders, .builtin .word⟩
          have descriptorNext : Dynamic.GeneralizedClosureWellTyped
              (context.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements)
              (copies source environment before).2 (shape.descriptor context (copies source environment before).1) :=
            ⟨descriptorTyped.same_signatures, descriptorTyped.code, descriptorTyped.captures⟩
          exact ⟨_, shape.body_trace evidence environment before unique (.intro wellformed fresh)
            valueExtended absentExtended fields scheme word literal readable
            (shape.frame _ _ evidence catalog descriptorNext fields runtime.signatures
              (fields.covers covers) scheme word)⟩

end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalSelectedSource
/-! The selected actual header receives the original Bool argument by Source
allocation. Original program typing then constructs the complete Source body
execution, before any target execution is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.source_eq (selected : SelectedInventory fixture row) :
    selected.packet.header.function.source = row.original.function.typedBody :=
  selected.packet.header.agreement.source.trans
    (congrArg (fun named => named.function.typedBody) selected.header_original)

def SelectedInventory.shape (selected : SelectedInventory fixture row)
    (original : Shape row.original.function.typedBody) :
    Shape selected.packet.header.function.source :=
  selected.source_eq.symm ▸ original

theorem SelectedInventory.parameters (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.parameters = [shape.flag] :=
  selected.packet.header.parameters.trans (selected.packet.header.inputs.symm.trans shape.inputs)

theorem SelectedInventory.input_types (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.types = [.bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq selected.packet.header.extended
  simpa only [selected.parameters shape, List.map_cons, List.map_nil,
    shape.flagScheme, TypeSystem.Scheme.mono] using types.symm

theorem SelectedInventory.statements (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source) :
    selected.packet.header.function.body = [shape.initialized.id, shape.valueInitialized.id, shape.absentDeclared.id, shape.returned.id] :=
  roots_injective (selected.packet.header.agreement.roots.symm.trans shape.roots)

def flagHeap (before : Dynamic.Heap) (flag : Bool) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := .bool, value := some (.bool flag)}]⟩

def flagEnvironment (binder : TypedBinder) (before : Dynamic.Heap) : Dynamic.Environment :=
  [(binder.id, ⟨before.cells.length⟩)]

/-- Source parameters and the complete independent body are obtained from the
actual selected Header and the original program typing certificate. -/
theorem SelectedInventory.source_body (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) ∧
    ∃ final, Dynamic.FunctionStatementsFault
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (flagEnvironment shape.flag before) (flagHeap before flag)
      selected.packet.header.function.body final
      (shape.failure selected.packet.header.context (flagEnvironment shape.flag before) (flagHeap before flag))
      (shape.finalHeap selected.packet.header.context (flagEnvironment shape.flag before)
        (flagHeap before flag)) := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (flagHeap before flag) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) := by
    rw [selected.parameters shape]
    exact .cons (by simpa only [shape.flagScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have initialLocals : header.function.context.locals = [] := by
    rw [header.frame.context]
    cases header.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq => rw [contextEq]; rfl
  have locals : Dynamic.EnvironmentAgrees (flagHeap before flag) header.context.locals
      (flagEnvironment shape.flag before) := by
    rw [header.extended.locals_eq, selected.parameters shape, initialLocals]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
      List.append_nil]
    exact .cons allocation.reads_new (by rw [shape.flagScheme]; rfl)
      (.ordinary (by rw [shape.flagScheme]; rfl) rfl) .nil
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields header.extended
  have runtime := certified.runtime.transport fields
  have catalog : SignatureCatalogWellFormed header.context.signatures :=
    runtime.signatures.symm ▸ wellFormed.signatures
  have covers : header.function.evidence.Covers header.context :=
    fields.covers (header.frame.context.symm ▸ header.frame.covers)
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.statements shape] at typed
  obtain ⟨next, body⟩ := shape.body_from_source header.function.evidence
    (flagEnvironment shape.flag before) (flagHeap before flag) runtime catalog covers locals typed
  exact ⟨bound, next, selected.statements shape ▸ body⟩

end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalTyping
/-! The actual original generalized identity body receives independent
declarative typing, including its principal initializer and both instances.
The observer checks finite metadata and constructs every typing rule. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

def resultType : TypeSystem.Ty := .product .word .bool

def returnFacts (type : TypeSystem.Ty) : StatementFacts :=
  {type, hasValue := true, sawReturn := true, control := .returned}

def localFacts : StatementFacts :=
  {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}

def bodyFacts : BodyFacts := .cons localFacts (.cons localFacts (.cons localFacts (.singleton (returnFacts resultType))))

structure BodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) where
  statements : List StatementId
  roots : function.typedBody.roots = statements.map NodeId.statement
  context : SourceSemantics.Context
  finalContext : SourceSemantics.Context
  inputs : MonoBindersExtend signature.id (checkedBodyContext signatures signature function)
    function.typedBody.inputs signature.parameterTypes context
  typed : StatementsHaveType function.typedBody {returnType := resultType} context statements finalContext bodyFacts
  result : TypeSystem.Ty.productMany signature.returnTypes = resultType

private theorem roots_injective_variant {left right : List StatementId}
    (mapped : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
    cases right with
    | nil => simp at mapped
    | cons other rest =>
      simp only [List.map_cons, List.cons.injEq] at mapped
      have headEq := NodeId.statement.inj mapped.1
      have tailEq := ih mapped.2
      rw [headEq, tailEq]

theorem BodyTyping.statements_typed {signatures : ProgramSignatures} {function : CheckedFunction}
    {signature : ProgramFunctionSignature} (certificate : BodyTyping signatures function signature) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = certificate.statements := roots_injective_variant (roots.symm.trans certificate.roots)
  subst statements
  refine ⟨bodyFacts, ?_, ?_⟩
  · rw [certificate.result]; rfl
  · intro context extension
    have same := certificate.inputs.functional extension
    subst context
    exact ⟨certificate.finalContext, by simpa only [certificate.result] using certificate.typed⟩

private def originalCall {source : TypedSource} {binder : TypedBinder} {argument : ExpressionId} {type : TypeSystem.Ty}
    (shape : CallShape source binder argument type) :
    Tests.SourceCoreSelectedGeneralizedLocal.CallShape source binder argument type :=
  ⟨shape.callee, shape.node, shape.metadata, shape.found, shape.form, shape.arity,
    shape.argumentCoercions, shape.requirements, shape.coercions⟩

private def originalWord {source : TypedSource} (shape : WordNode source) :
    Tests.SourceCoreSelectedGeneralizedLocal.WordNode source :=
  ⟨shape.node, shape.literal, shape.resolution, shape.found, shape.form, shape.target,
    shape.requirements, shape.coercions⟩

def observeBodyTyping (signatures : ProgramSignatures) (function : CheckedFunction)
    (signature : ProgramFunctionSignature) : IO (BodyTyping signatures function signature) := do
  let shape ← observeShape function.typedBody
  let ⟨inputTypes⟩ ← observe (signature.parameterTypes = [.bool]) "generalized original signature input"
  let ⟨result⟩ ← observe (TypeSystem.Ty.productMany signature.returnTypes = resultType)
    "generalized original signature result"
  let base := checkedBodyContext signatures signature function
  let lexical := base.withLocal shape.flag.id shape.flag.scheme shape.flag.schemeRequirements
  let ⟨flagExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder base signature.id shape.flag
  let ⟨flagRequirements⟩ ← observe (shape.flag.schemeRequirements = []) "generalized input requirements"
  have inputs : MonoBindersExtend signature.id base function.typedBody.inputs signature.parameterTypes lexical := by
    rw [shape.inputs, inputTypes]
    exact .cons shape.flagScheme flagExtended (.nil _)
  let principal := localSchemeInitializerContext lexical shape.binder
  let parameterContext := principal.withLocal shape.parameter.id shape.parameter.scheme shape.parameter.schemeRequirements
  let ⟨parameterExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder principal function.typedBody.owner shape.parameter
  let ⟨parameterTyped⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.parameterRead parameterContext
    parameterExtended.local_self parameterExtended.local_scheme_requirements_self
  let ⟨identityType⟩ ← observe (shape.identityReturn.type = .variable shape.typeVariable)
    "generalized original identity return type"
  have identity : StatementHasType function.typedBody {returnType := .variable shape.typeVariable}
      parameterContext shape.identityReturn.id parameterContext (returnFacts (.variable shape.typeVariable)) :=
    .returnValue (lookupStatement?_sound shape.identityFound) shape.identityForm parameterTyped identityType
  have parameterInputs : MonoBindersExtend function.typedBody.owner principal [shape.parameter]
      [.variable shape.typeVariable] parameterContext :=
    .cons shape.parameterScheme parameterExtended (.nil _)
  have lambdaForm : ExpressionFormHasRawType function.typedBody principal shape.lambda.form
      (.function (.variable shape.typeVariable) (.variable shape.typeVariable)) (.ordinary []) := by
    rw [shape.lambdaForm]
    exact .lambda (by simp) parameterInputs (.singleton identity) (by simp [BodyCompletes, BodyFacts.singleton, returnFacts, ControlSummary.returned])
  let ⟨initializerTyped⟩ ← uncoerced principal shape.lambda
    (.function (.variable shape.typeVariable) (.variable shape.typeVariable)) shape.lambdaFound lambdaForm
  let generalizedContext := lexical.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements
  let ⟨localExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder lexical function.typedBody.owner shape.binder
  let ⟨generalized⟩ ← generalizes lexical shape.binder
  let ⟨initializedType⟩ ← observe (shape.initialized.type = .unit) "generalized original let type"
  have initialized : StatementHasType function.typedBody {returnType := resultType} lexical
      shape.initialized.id generalizedContext localFacts := by
    refine .letInitializedGeneralized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      (by rw [shape.scheme]; simp) (LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements)
      generalized ?_ localExtended initializedType
    simpa only [shape.scheme] using initializerTyped
  let ⟨wordRead⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.wordCall.callee generalizedContext
    localExtended.local_self localExtended.local_scheme_requirements_self
  let ⟨literalTyped⟩ ← word (originalWord shape.literal) generalizedContext
  let ⟨wordCall⟩ ← call (originalCall shape.wordCall) generalizedContext wordRead literalTyped
  let valueContext := generalizedContext.withLocal shape.valueBinder.id shape.valueBinder.scheme shape.valueBinder.schemeRequirements
  let ⟨valueExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder generalizedContext function.typedBody.owner shape.valueBinder
  let ⟨valueType⟩ ← observe (shape.valueInitialized.type = .unit) "interleaved ordinary initialized type"
  let valueGeneralizes : PLift (SchemeGeneralizes generalizedContext shape.valueBinder.scheme) ←
    match accepted : validateSchemeGeneralizes generalizedContext shape.valueBinder.scheme with
    | .error _ => throw (IO.userError "interleaved exact ordinary generalization")
    | .ok () => pure ⟨validateSchemeGeneralizes_success accepted⟩
  have valueInitialized : StatementHasType function.typedBody {returnType := resultType} generalizedContext
      shape.valueInitialized.id valueContext localFacts :=
    .letInitialized (lookupStatement?_sound shape.valueFound) shape.valueForm
      (by simpa only [shape.valueScheme, originalCall, TypeSystem.Scheme.mono] using wordCall)
      (by rw [shape.valueScheme]; rfl) valueGeneralizes.down valueExtended valueType
  let finalContext := valueContext.withLocal shape.absentBinder.id shape.absentBinder.scheme shape.absentBinder.schemeRequirements
  let ⟨absentExtended⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.binder valueContext function.typedBody.owner shape.absentBinder
  let ⟨absentType⟩ ← observe (shape.absentDeclared.type = .unit) "faulting absent declaration type"
  let absentGeneralizes : PLift (SchemeGeneralizes valueContext shape.absentBinder.scheme) ←
    match accepted : validateSchemeGeneralizes valueContext shape.absentBinder.scheme with
    | .error _ => throw (IO.userError "faulting absent generalization")
    | .ok () => pure ⟨validateSchemeGeneralizes_success accepted⟩
  have absentDeclared : StatementHasType function.typedBody {returnType := resultType} valueContext
      shape.absentDeclared.id finalContext localFacts :=
    .letUninitialized (lookupStatement?_sound shape.absentFound) shape.absentForm
      (by rw [shape.absentScheme]; rfl) absentGeneralizes.down absentExtended absentType
  let ⟨absentDifferent⟩ ← observe (shape.absentBinder.id ≠ shape.binder.id) "faulting distinct generalized and absent binders"
  let ⟨absentFlagDifferent⟩ ← observe (shape.absentBinder.id ≠ shape.flag.id) "faulting distinct input and absent binder"
  let ⟨different⟩ ← observe (shape.binder.id ≠ shape.flag.id) "interleaved distinct input and generalized local"
  let ⟨valueDifferent⟩ ← observe (shape.valueBinder.id ≠ shape.binder.id) "interleaved distinct local binders"
  let ⟨flagDifferent⟩ ← observe (shape.valueBinder.id ≠ shape.flag.id) "interleaved distinct input and ordinary local"
  let ⟨boolRead⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.boolCall.callee finalContext
    (.tail absentDifferent (.tail valueDifferent localExtended.local_self))
    (.tail absentDifferent (.tail valueDifferent localExtended.local_scheme_requirements_self))
  let ⟨flagRead⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.flagRead finalContext
    (.tail absentFlagDifferent (.tail flagDifferent (.tail different flagExtended.local_self)))
    (.tail absentFlagDifferent (.tail flagDifferent (.tail different flagExtended.local_scheme_requirements_self)))
  let ⟨absentRead⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.read shape.absentRead finalContext
    absentExtended.local_self absentExtended.local_scheme_requirements_self
  let ⟨boolCall⟩ ← call (originalCall shape.boolCall) finalContext boolRead flagRead
  have tupleForm : ExpressionFormHasRawType function.typedBody finalContext shape.tuple.form resultType (.ordinary []) := by
    rw [shape.tupleForm]
    exact .tuple (.cons absentRead (.cons boolCall (.nil _)))
  let ⟨tupleTyped⟩ ← uncoerced finalContext shape.tuple resultType shape.tupleFound tupleForm
  let ⟨returnedType⟩ ← observe (shape.returned.type = resultType) "generalized original return type"
  have returned : StatementHasType function.typedBody {returnType := resultType} finalContext
      shape.returned.id finalContext (returnFacts resultType) :=
    .returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm tupleTyped returnedType
  return {
    statements := [shape.initialized.id, shape.valueInitialized.id, shape.absentDeclared.id, shape.returned.id]
    roots := shape.roots
    context := lexical
    finalContext := finalContext
    inputs := inputs
    typed := .cons initialized (.cons valueInitialized (.cons absentDeclared (.singleton returned)))
    result := result }

end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalWellFormed
/-! Whole-program validity of the unchanged one-function regression follows
from its actual checker result and the constructed declarative body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation

structure OriginalTyping (fixture : CompiledFixture) where
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : fixture.recipe.compiled.sourceProgram.functions = [function]
  methods : fixture.recipe.compiled.sourceProgram.methods = []
  member : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions
  owner : function.declaration = signature.id
  body : BodyTyping fixture.recipe.compiled.sourceProgram.signatures function signature

theorem OriginalTyping.wellFormed {fixture : CompiledFixture} (original : OriginalTyping fixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  apply programWellFormed_ofCheckProgram_statements fixture.checked
  constructor
  · intro function member signature signatureMember accepted
    rw [original.functions] at member
    have same := List.mem_singleton.mp member
    subst function
    have signatureEq : signature = original.signature := by
      apply eq_of_mem_of_nodup_map (SignatureCatalogWellFormed.ofCheckProgram fixture.checked).function_ids
        signatureMember original.member
      exact (checkFunctionBody_success_declaration accepted).symm.trans original.owner
    subst signature
    exact original.body.statements_typed
  · intro method member
    rw [original.methods] at member
    cases member

def observeOriginalTyping (fixture : CompiledFixture) : IO (OriginalTyping fixture) := do
  match functions : fixture.recipe.compiled.sourceProgram.functions with
  | [function] =>
    let ⟨methodCount⟩ ← observe (fixture.recipe.compiled.sourceProgram.methods.length = 0)
      "generalized full original method list"
    match found : fixture.recipe.compiled.sourceProgram.signatures.functions.find?
        (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "generalized original signature membership")
    | some signature =>
      let body ← observeBodyTyping fixture.recipe.compiled.sourceProgram.signatures function signature
      return {
        function := function
        signature := signature
        functions := functions
        methods := List.length_eq_zero_iff.mp methodCount
        member := List.mem_of_find?_eq_some found
        owner := (of_decide_eq_true (List.find?_some
          (p := fun signature : ProgramFunctionSignature => decide (signature.id = function.declaration)) found)).symm
        body := body }
  | _ => throw (IO.userError "generalized original single function")

def typingProbe : IO Unit := do
  let fixture ← compileFixture
  let original ← observeOriginalTyping fixture
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := original.wellFormed
  unless fixture.recipe.compiled.indexed.base.functions.length == 1 do
    throw (IO.userError "generalized original complete cache size")
  IO.println "INTERLEAVED_LOCAL_ORIGINAL_TYPING: originals1/cache1"
  IO.println "INTERLEAVED_LOCAL_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalPublicStart
/-! Actual opening, export-aware bootstrap and public input receipt, recorded
before resuming the selected function. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

structure Started (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session key arguments runOptions

def observeStarted (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "generalized local bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩


end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalPublic
/-! A genuine absent read follows generalized materialization and ordinary
allocation. Independent Source failure is connected before public resume;
the returned failed session retains the reached descriptor heap and history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
variable {fixture : ProfiledFixture} {row : Row fixture.original}

theorem SelectedInventory.invocation (selected : SelectedInventory fixture row) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar fixture.original.recipe.compiled.indexed.base.plan
        selected.packet.header.named.signature.key = .ok sidecar ∧
      (SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).Closure
        selected.packet.header.function (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) := by
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts selected.rows).receipts
      selected.packet.header (by exact List.mem_cons_self)
  obtain ⟨descriptor⟩ := SelectedCompilationCertifiedPublicSession.header_descriptor selected.packet.header
  obtain ⟨sidecar, issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected)
      selected.packet.aligned (SelectedCompilationPhysicalProgramSupport.stagePrepared fixture.original.recipe.compiled)
      descriptor
  refine ⟨sidecar, ?_, ?_⟩
  · simpa only [selected.packet.aligned.named, CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued,
      RecursiveNamedPreparedCallEvidence.Prepared.signature_key selected.input.prepared] using issued
  · rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected

namespace FailureBridge

structure InitialForward (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) where
  start : SelectedCompilationPublicSessionInitial.Started selected.rows fixture.ready selected.packet.header started.call
  origin : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.original.recipe.compiled.indexed
  initial : CellAwarePublicInitialStart.Ready callableProfile origin.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics) start [.bool flag]
  forward : CellAwarePublicFaultingFailureForward.FailureForward callableProfile
    (completion := initial.receiving) (header := selected.packet.header)
    (bodyRegistry := origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) initial.caller.base.val
    (payloads := start.native) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := started.call.checkpoint)
    (.semantic ((selected.shape shape).failure selected.packet.header.context
      (flagEnvironment (selected.shape shape).flag ⟨[]⟩) (flagHeap ⟨[]⟩ flag)))
    ((selected.shape shape).finalHeap selected.packet.header.context
      (flagEnvironment (selected.shape shape).flag ⟨[]⟩) (flagHeap ⟨[]⟩ flag)) ∨
    ∃ originId call reason reached, CellAwarePublicFaultingFailureForward.FailureForward callableProfile
    (completion := initial.receiving) (header := selected.packet.header)
    (bodyRegistry := origin.result.context.registry)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (owner fixture.original.recipe.compiled) initial.caller.base.val
    (payloads := start.native) (nativeCheckpoint := start.checkpoint)
    (publicCheckpoint := started.call.checkpoint)
    (.stage originId call reason) reached

/-- Every premise is an original checked/static observation or an actual public
start. Source execution is constructed inside, before the target is resumed. -/
theorem initial_from_source (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨start⟩ := CellAwarePublicInitialStart.from_call
    (rows := selected.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member => selected.root_selection member)
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started selected.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    (SelectedCompilationBodyTyping.Bodies.of_program typing.wellFormed) start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.source_body actualShape typing.wellFormed ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.fault sourceTrace)
  have forward := CellAwarePublicFaultingFailureForward.first_fault callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic typing.wellFormed
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, forward⟩⟩

/-- The complete original inventory is produced from its actual declarative
proof before the public call is resumed. -/
theorem complete_from_source (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    ∃ selected : SelectedInventory fixture row, Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨selected⟩ := fixture.inventory row typing.wellFormed
  exact ⟨selected, initial_from_source selected shape flag typing started callableProfile⟩

def publicProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "local"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  let ⟨profile⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.observe
    (fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "interleaved actual callable profile"
  for flag in [true, false] do
    let started ← observeStarted fixture.original row.original.key [.bool flag]
    let _proof := complete_from_source fixture row shape flag typing started profile
    match ← started.call.checkpoint.resume runOptions.executionFuel runOptions.outputValidationFuel with
    | .failed token returned =>
      unless returned.heapSize > started.session.heapSize do
        throw (IO.userError "faulting Source-first heap effects missing")
      IO.println s!"FAULTING_LOCAL_PUBLIC_FAILURE: flag={flag}, token={token.toNat}, heap={returned.heapSize}"
    | _ => throw (IO.userError "faulting Source-first call did not fail")
  IO.println "FAULTING_LOCAL_COMPLETE_OUTCOME: originals1/cache1/typing1/profile1"
  IO.println "FAULTING_LOCAL_COMPLETE_OUTCOME_PASS"

end FailureBridge
end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalSelectedRegistry
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
theorem OriginalTyping.selected_bodies {fixture : CompiledFixture} (original : OriginalTyping fixture) :
    SelectedCompilationBodyTyping.Bodies fixture.recipe.compiled := by
  let catalog := SignatureCatalogWellFormed.ofCheckProgram fixture.checked
  obtain ⟨functionIds,methodIds⟩ := Frontend.checkProgram_success_ids fixture.checked
  refine ⟨catalog, ?_, ?_, ?_, ?_⟩
  · simp only [Program.ofChecked,List.map_map,Function.comp_def,FunctionDefinition.ofChecked,BodyDefinition.ofChecked]
    rw [functionIds]
    exact catalog.function_ids
  · simp only [Program.ofChecked,List.map_map,Function.comp_def,MethodDefinition.ofChecked]
    rw [methodIds]
    exact catalog.implementation_method_ids
  · intro function selected
    obtain ⟨_,_,_,_,_,_,member,_⟩ := selected
    apply functionDefinitionValid_ofCheckProgram fixture.checked member
    intro signature signatureMember accepted
    rw [original.functions] at member
    have same := List.mem_singleton.mp member
    subst function
    let typed := original
    have same : signature = typed.signature := by
      apply eq_of_mem_of_nodup_map catalog.function_ids signatureMember typed.member
      exact (checkFunctionBody_success_declaration accepted).symm.trans typed.owner
    subst signature
    apply checkedBodyHasType_ofStatements accepted
    exact typed.body.statements_typed
  · intro method selected
    obtain ⟨_,_,_,_,_,_,member,_,_⟩ := selected
    rw [original.methods] at member
    cases member

theorem SelectedInventory.ranges {fixture : ProfiledFixture} {row : Row fixture.original}
    (selected : SelectedInventory fixture row) :
    SelectedCompilationRegistryMethodCertificates.Ranges fixture.original.recipe.compiled := by
  intro index named cached
  have member := List.mem_of_getElem? cached
  rw [selected.complete] at member
  have same : named = selected.input.prepared.named := List.mem_singleton.mp member
  rw [same, selected.input.prepared.same, selected.original, row.substitution]
  intro name value found
  cases found

theorem OriginalTyping.checked_registry {fixture : ProfiledFixture} {row : Row fixture.original}
    (original : OriginalTyping fixture.original) (selected : SelectedInventory fixture row) :
    SelectedCompilationCheckedRegistry.Certificate fixture.original.recipe.compiled :=
  SelectedCompilationCheckedRegistry.of_checked fixture.original.checked original.selected_bodies selected.ranges

end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalSelectedPlan
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
theorem ProfiledFixture.inventory_selected (fixture : ProfiledFixture) (row : Row fixture.original)
    (bodies : SelectedCompilationBodyTyping.Bodies fixture.original.recipe.compiled) :
    Nonempty (SelectedInventory fixture row) := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile
    fixture.original.accepted fixture.original.selected row.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.original.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]
    intro name value found
    cases found
  let input : Input fixture.original.recipe.compiled := {
    row := row.original
    prepared := prepared
    range := range
    ordinaryReturn := row.ordinary
    ordinaryParameters := fun binder member => row.ordinaryInputs binder member
    target := by
      have target := SelectedCompilationCatalog.retained_target fixture.original.recipe.compiled
        bodies.signatures prepared.selected (prepared.same.symm ▸ prepared.origin)
      simpa only [prepared.same] using target
    slot := CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_slot
      fixture.original.recipe.compiled prepared.selected }
  obtain ⟨packet⟩ := SelectedCompilationCatalog.exists_issued input bodies
  have bound := (List.getElem?_eq_some_iff.mp prepared.selected).1
  rw [fixture.cached] at bound
  have position : prepared.index = 0 := by omega
  obtain ⟨named, complete⟩ := List.length_eq_one_iff.mp fixture.cached
  have selected := prepared.selected
  rw [complete, position] at selected
  have same : named = prepared.named := Option.some.inj selected
  exact ⟨⟨input, rfl, packet, position, by simpa only [same] using complete⟩⟩

variable {fixture : ProfiledFixture} {row : Row fixture.original}
theorem SelectedInventory.source_body_selected (selected : SelectedInventory fixture row)
    (shape : Shape selected.packet.header.function.source)
    (bodies : SelectedCompilationBodyTyping.Bodies fixture.original.recipe.compiled)
    (before : Dynamic.Heap) (flag : Bool) :
    Dynamic.BindersAllocate [] before selected.packet.header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) ∧
    ∃ final, Dynamic.FunctionStatementsFault
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
      selected.packet.header.context selected.packet.header.function.evidence
      selected.packet.header.function.source (flagEnvironment shape.flag before) (flagHeap before flag)
      selected.packet.header.function.body final
      (shape.failure selected.packet.header.context (flagEnvironment shape.flag before) (flagHeap before flag))
      (shape.finalHeap selected.packet.header.context (flagEnvironment shape.flag before)
        (flagHeap before flag)) := by
  let header := selected.packet.header
  have allocation : Dynamic.Heap.Allocates before .bool (some (.bool flag))
      ⟨before.cells.length⟩ (flagHeap before flag) := .append
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [.bool flag]
      (flagEnvironment shape.flag before) (flagHeap before flag) := by
    rw [selected.parameters shape]
    exact .cons (by simpa only [shape.flagScheme, TypeSystem.Scheme.mono] using allocation) (.nil _ _)
  have initialLocals : header.function.context.locals = [] := by
    rw [header.frame.context]
    cases header.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq => rw [contextEq]; rfl
  have locals : Dynamic.EnvironmentAgrees (flagHeap before flag) header.context.locals
      (flagEnvironment shape.flag before) := by
    rw [header.extended.locals_eq, selected.parameters shape, initialLocals]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
      List.append_nil]
    exact .cons allocation.reads_new (by rw [shape.flagScheme]; rfl)
      (.ordinary (by rw [shape.flagScheme]; rfl) rfl) .nil
  have certified : SelectedCompilationNamedSourceTyping.Certified header :=
    SelectedCompilationHeaderCertificates.certified bodies header
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields header.extended
  have runtime := certified.runtime.transport fields
  have catalog : SignatureCatalogWellFormed header.context.signatures :=
    runtime.signatures.symm ▸ bodies.signatures
  have covers : header.function.evidence.Covers header.context :=
    fields.covers (header.frame.context.symm ▸ header.frame.covers)
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [selected.statements shape] at typed
  obtain ⟨next, body⟩ := shape.body_from_source header.function.evidence
    (flagEnvironment shape.flag before) (flagHeap before flag) runtime catalog covers locals typed
  exact ⟨bound, next, selected.statements shape ▸ body⟩

end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalSelectedPublic
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreSelectedFaultingLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
variable {fixture : ProfiledFixture} {row : Row fixture.original}
namespace FailureBridge
theorem initial_from_source_selected (selected : SelectedInventory fixture row)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨start⟩ := CellAwarePublicInitialStart.from_call
    (rows := selected.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member => selected.root_selection member)
  let actualShape := selected.shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started selected.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    typing.selected_bodies start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  obtain ⟨allocated, final, sourceTrace⟩ := selected.source_body_selected actualShape typing.selected_bodies ⟨[]⟩ flag
  obtain ⟨sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.fault sourceTrace)
  have forward := CellAwarePublicFaultingFailureForward.first_fault_selected callableProfile initial.issued initial.extension
    prepared selected.packet.aligned fixture.ready diagnostic (typing.checked_registry selected).namedSupport
    (profile.for_compilation prepared.compilation) start.selected
    (owner fixture.original.recipe.compiled) initial.caller.base.val initial.globalReference initial.keyPhysical
    initial.caller.physical initial.stable initial.heapTyped initial.argumentsTyped issued bodySelected
    initial.represented initial.heaps rfl start.started start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated measured
  exact ⟨⟨start, origin, initial, forward⟩⟩

/-- The complete original inventory is produced from its actual declarative
proof before the public call is resumed. -/
theorem complete_from_source_selected (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody) (flag : Bool)
    (typing : OriginalTyping fixture.original)
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    ∃ selected : SelectedInventory fixture row, Nonempty (InitialForward selected shape flag started callableProfile) := by
  obtain ⟨selected⟩ := fixture.inventory_selected row typing.selected_bodies
  exact ⟨selected, initial_from_source_selected selected shape flag typing started callableProfile⟩

def selectedPublicProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "local"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  let ⟨profile⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.observe
    (fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "interleaved actual callable profile"
  for flag in [true, false] do
    let started ← observeStarted fixture.original row.original.key [.bool flag]
    let _proof := complete_from_source_selected fixture row shape flag typing started profile
    match ← started.call.checkpoint.resume runOptions.executionFuel runOptions.outputValidationFuel with
    | .failed token returned =>
      unless returned.heapSize > started.session.heapSize do
        throw (IO.userError "faulting Source-first heap effects missing")
      IO.println s!"FAULTING_LOCAL_SELECTED_PUBLIC_FAILURE: flag={flag}, token={token.toNat}, heap={returned.heapSize}"
    | _ => throw (IO.userError "faulting Source-first call did not fail")
  IO.println "FAULTING_LOCAL_SELECTED_COMPLETE_OUTCOME: originals1/cache1/typing1/profile1"
  IO.println "FAULTING_LOCAL_SELECTED_COMPLETE_OUTCOME_PASS"

end FailureBridge
end Tests.SourceCoreSelectedFaultingLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalSelectedReflection
/-! Actual failed public outcomes recover the ordinary Source failure and its
reached heap, and establish a reusable history from selected original rows. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreSelectedFaultingLocal.FailureBridge
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row}
  {shape : Shape row.original.function.typedBody} {flag : Bool}
  {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}

def ReflectedMeaning (first : InitialForward selected shape flag started callableProfile)
    (executionFuel : Nat) (token : Word) (returned : SourceCoreExecution.Session started.artifact) : Prop :=
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
    ∃ observed : CellAwarePublicFaultingFailureReflection.Reflected
      (completion := first.initial.receiving) (header := selected.packet.header)
      (bodyRegistry := first.origin.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults first.origin.result.diagnostics)
      (payloads := first.start.native) (arguments := [.bool flag])
      (nativeCheckpoint := first.start.checkpoint) (sidecar := sidecar)
      callableProfile (owner fixture.original.recipe.compiled) first.initial.caller.base.val
      executionFuel token returned,
    ∃ reached : CellAwarePublicFunctionHistory.Caller (headers selected.rows)
      (keys fixture.original.recipe.compiled) observed.finalMap observed.finalWorld observed.after observed.finalStore,
      CallableIndexedOwnedFunctionState.Relates first.initial.caller.base.val reached ∧
      CellAwarePublicPhysicalHistory.History
        (functions := CellAwarePhysicalFunctionOrigins.functions (headers selected.rows)
          (keys fixture.original.recipe.compiled) first.origin.result.context.registry
          (CallableIndexedOwnedPublicDecodedCallFaults.faults first.origin.result.diagnostics) callableProfile)
        (cells := GeneralizedLocalDescriptorHeap.cellModel
          (CompatibleAmbientHeap.payloadModel fixture.original.recipe.compiled.compatible.checked
            first.initial.receiving.result.context.registry
            (CellAwarePhysicalFunctionOrigins.functions (headers selected.rows)
              (keys fixture.original.recipe.compiled) first.origin.result.context.registry
              (CallableIndexedOwnedPublicDecodedCallFaults.faults first.origin.result.diagnostics) callableProfile))
          (GeneralizedLocalInstanceValues.model fixture.original.recipe.compiled.indexed))
        (receiving := first.initial.receiving.result.context.registry) (anchor := selected.packet.header)
        observed.actual observed.finalMap observed.finalWorld observed.after observed.finalStore reached []

theorem InitialForward.reflected_selected
    (first : InitialForward selected shape flag started callableProfile)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {token : Word}
    {returned : SourceCoreExecution.Session started.artifact}
    (resumed : started.call.checkpoint.ResumeAt executionFuel outputFuel (.failed token returned)) :
    ReflectedMeaning first executionFuel token returned := by
  unfold ReflectedMeaning
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  obtain ⟨sidecar, issued, bodySelected⟩ := selected.invocation
  let support := (typing.checked_registry selected).namedSupport
  obtain ⟨observed⟩ := CellAwarePublicFaultingFailureReflection.reflect_selected callableProfile
    first.initial.issued first.initial.extension prepared selected.packet.aligned fixture.ready diagnostic support
    (profile.for_compilation prepared.compilation) first.start.selected
    (owner fixture.original.recipe.compiled) first.initial.caller.base.val first.initial.globalReference
    first.initial.keyPhysical first.initial.caller.physical first.initial.stable
    first.initial.heapTyped first.initial.argumentsTyped issued bodySelected first.initial.represented
    first.initial.heaps rfl first.start.started first.start.atCheckpoint
    (congrArg SourceCoreCompatibleValues.Context.registry first.initial.contextAt)
    first.initial.exportsReady resumed
  obtain ⟨reached, related, history⟩ :=
    CellAwarePublicFaultingFailureReflection.Reflected.first_history_selected
      callableProfile support first.start.selected (owner fixture.original.recipe.compiled)
      first.initial.caller.base.val first.initial.caller.physical rfl first.start.started observed
  exact ⟨sidecar, observed, reached, related, history⟩

theorem reflect_complete
    (typing : OriginalTyping fixture.original)
    (plan : ∃ selected : SelectedInventory fixture row,
      Nonempty (InitialForward selected shape flag started callableProfile))
    {executionFuel outputFuel : Nat} {token : Word}
    {returned : SourceCoreExecution.Session started.artifact}
    (resumed : started.call.checkpoint.ResumeAt executionFuel outputFuel (.failed token returned)) :
    ∃ selected : SelectedInventory fixture row,
    ∃ first : InitialForward selected shape flag started callableProfile,
      ReflectedMeaning first executionFuel token returned := by
  obtain ⟨selected, ⟨first⟩⟩ := plan
  exact ⟨selected, first, first.reflected_selected typing resumed⟩

end Tests.SourceCoreSelectedFaultingLocal.FailureBridge
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedFaultingLocalSelectedRuntime
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal.FailureBridge
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

def selectedRuntime : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "local"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  let ⟨profile⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.observe
    (fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "faulting selected callable profile"
  let mut heaps : List Nat := []
  for flag in [true, false] do
    let started ← observeStarted fixture.original row.original.key [.bool flag]
    have sourcePlan := complete_from_source_selected fixture row shape flag typing started profile
    let actual ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match same : actual.val with
    | .failed token returned =>
      have _reflected := reflect_complete typing sourcePlan (same ▸ actual.property)
      unless returned.heapSize > started.session.heapSize do
        throw (IO.userError "selected Source-first fault lost heap effects")
      let .ok (some diagnostic) := returned.diagnostic row.original.key token
        | throw (IO.userError "selected Source-first fault diagnostic missing")
      unless (match diagnostic.error with | .uninitializedLocal _ => true | _ => false) do
        throw (IO.userError "selected Source-first absent-cell fault changed")
      heaps := heaps ++ [started.session.heapSize, returned.heapSize]
      IO.println s!"FAULTING_SELECTED_SOURCE_PUBLIC: flag={flag}, token={token.toNat}, heap={returned.heapSize}"
    | _ => throw (IO.userError "selected Source-first call did not fail")
  unless heaps == [2,23,2,23] do
    throw (IO.userError "selected Source-first exact public heaps changed")
  IO.println s!"FAULTING_SELECTED_SOURCE_HEAPS: {heaps}"
  IO.println "FAULTING_SELECTED_SOURCE_PUBLIC_PASS: originals1/cache1/selected-body1/checked-registry; Source-before-resume; semantic fault/reflection/reached heap/first history"

end Tests.SourceCoreSelectedFaultingLocal.FailureBridge
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralKeySource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedGeneralKey
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue)

/-- The complete original probe program is retained, with every function seeded. -/
def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Key { Key(Bool) }",
    "function pairRead(table: mapping((Bool, Bool) => Word)) returns (Word) { return table[(true, false)]; }",
    "function pairWrite(table: mapping((Bool, Bool) => Word)) returns (mapping((Bool, Bool) => Word)) { table[(true, false)] += 3; return table; }",
    "function proxyRead(table: mapping(@Word => Word)) returns (Word) { return table[@Word]; }",
    "function proxyWrite(table: mapping(@Word => Word)) returns (mapping(@Word => Word)) { table[@Word] += 3; return table; }",
    "function nominalRead(table: mapping(Key => Word)) returns (Word) { return table[Key(true)]; }"]}] }
def options : SourceCompiler.Options :=
  {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 128}
def runOptions : SourceCoreExecution.RunOptions :=
  {executionFuel := 100000, outputValidationFuel := 1000}

inductive Key where
  | pair (left right : Bool)
  | proxy (inner : TypeSystem.Ty)
  | nominal (metadata : DataConstructorInstantiation) (argument : Bool)

def Key.type : Key → TypeSystem.Ty
  | .pair .. => .product .bool .bool
  | .proxy inner => .proxy inner
  | .nominal metadata _ => metadata.resultType

def Key.value : Key → Dynamic.Value
  | .pair left right => .product (.bool left) (.bool right)
  | .proxy inner => .proxy inner
  | .nominal metadata argument => .constructed metadata [.bool argument]

def Key.Valid (context : SourceSemantics.Context) : Key → Prop
  | .pair .. | .proxy .. => True
  | .nominal metadata _ => DataConstructorInstantiation.Valid context metadata

def Key.Simple : Key → Prop
  | .pair .. | .proxy .. => True
  | .nominal .. => False

theorem Key.simple_valid (key : Key) (simple : key.Simple) (context : SourceSemantics.Context) :
    key.Valid context := by
  cases key with
  | pair | proxy => trivial
  | nominal => exact False.elim simple

theorem Key.comparable (key : Key) : Dynamic.ValueComparable key.value := by
  cases key with
  | pair left right => exact .product (.bool left) (.bool right)
  | proxy inner => exact .proxy inner
  | nominal metadata argument =>
    exact .constructed metadata [.bool argument] (by intro value member; cases List.mem_singleton.mp member; exact .bool argument)

structure BoolNode (source : TypedSource) (value : Bool) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  name : String
  form : node.form = .reference name (.builtinBoolean value)
  requirements : node.requirements = []
  coercions : node.coercions = []

inductive KeyForm (source : TypedSource) : ExpressionNode → Key → Type where
  | pair {node left right} (first : BoolNode source left) (second : BoolNode source right)
      (form : node.form = .tuple [first.node.id,second.node.id]) : KeyForm source node (.pair left right)
  | proxy {node inner} (form : node.form = .proxy inner) : KeyForm source node (.proxy inner)
  | nominal {node metadata argument} (child : BoolNode source argument)
      (form : node.form = .constructor metadata [child.node.id])
      (substitution : metadata.parameterSubstitution = [])
      (payload : metadata.payloadTypes = [.bool]) : KeyForm source node (.nominal metadata argument)

structure KeyNode (source : TypedSource) (key : Key) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  type : node.type = key.type
  requirements : node.requirements = []
  coercions : node.coercions = []
  shape : KeyForm source node key

private theorem bool_evaluates {source : TypedSource} {value : Bool} (node : BoolNode source value)
    {program : SourceSemantics.Program} (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id (.bool value) heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]; exact .builtinBoolean (by rw [node.requirements,node.coercions]; rfl)
  · rw [node.coercions]; exact .nil

/-- Key execution follows the original literal/tuple/constructor nodes. -/
theorem KeyNode.evaluates {source : TypedSource} {key : Key} (node : KeyNode source key)
    {program : SourceSemantics.Program} (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) (valid : key.Valid context) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id key.value heap := by
  cases node.shape with
  | pair first second form =>
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
    · rw [form]; exact .tuple (by rw [node.requirements,node.coercions]; rfl)
        (.cons (bool_evaluates first _ _ _ _) (.cons (bool_evaluates second _ _ _ _) .nil)) (.cons (.singleton _))
    · rw [node.coercions]; exact .nil
  | proxy form =>
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
    · rw [form]; exact .proxy (by rw [node.requirements,node.coercions]; rfl)
    · rw [node.coercions]; exact .nil
  | nominal child form _ _ =>
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
    · rw [form]; exact .constructor (by rw [node.requirements,node.coercions]; rfl)
        valid (.cons (bool_evaluates child _ _ _ _) .nil)
    · rw [node.coercions]; exact .nil

/-- Nominal validity comes from the checked original key typing. -/
theorem KeyNode.valid {source : TypedSource} {key : Key} (node : KeyNode source key)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context node.node.id type) :
    key.Valid context := by
  cases node.shape with
  | pair | proxy => trivial
  | nominal child form substitution _ =>
    cases typed with
    | intro contains raw _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans node.found)
      cases same
      rw [form] at raw
      cases raw with
      | constructor valid _ =>
        cases valid with
        | intro dataType signature dataMember signatureMember owner constructorEq exact range payload result =>
          exact .intro dataType signature dataMember signatureMember owner constructorEq exact
            (by rw [substitution]; intro parameter replacement impossible; cases impossible) payload result

def mappingType (key : Key) : TypeSystem.Ty := .mapping key.type .word
def mappingValue (key : Key) (entries : List (Dynamic.Value × Dynamic.Value)) : Dynamic.Value :=
  .mapping key.type .word entries
def mappingHeap (before : Dynamic.Heap) (key : Key) (entries : List (Dynamic.Value × Dynamic.Value)) : Dynamic.Heap :=
  ⟨before.cells ++ [⟨mappingType key, some (mappingValue key entries), none⟩]⟩
def location (before : Dynamic.Heap) : Dynamic.Location := ⟨before.cells.length⟩

structure ReadShape (source : TypedSource) (key : Key) where
  binder : TypedBinder
  keyNode : KeyNode source key
  base : Tests.SourceCoreNamedBranch.Read source binder (mappingType key)
  index : ExpressionNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  scheme : binder.scheme = .mono (mappingType key)
  roots : source.roots = [.statement returned.id]
  indexFound : source.lookupExpression? index.id = some index
  indexForm : index.form = .index base.node.id keyNode.node.id
  indexRequirements : index.requirements = []
  indexCoercions : index.coercions = []
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some index.id)

private theorem roots_injective {left right : List StatementId}
    (same : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at same ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons,List.cons.injEq] at same
      cases same.1
      exact congrArg (List.cons head) (ih same.2)

private theorem read_value {source : TypedSource} {binder : TypedBinder} {type : TypeSystem.Ty}
    (node : Tests.SourceCoreNamedBranch.Read source binder type)
    {program : SourceSemantics.Program} (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) (loc : Dynamic.Location) (value : Dynamic.Value)
    (lookup : Dynamic.Environment.LooksUp environment binder.id loc)
    (reads : Dynamic.Heap.Reads heap loc ⟨type,some value,none⟩) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id value heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]; exact .local (by rw [node.requirements,node.coercions]; rfl) lookup reads rfl rfl
  · rw [node.coercions]; exact .nil

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))

theorem read_input_types {key : Key} (shape : ReadShape header.function.source key) :
    header.types = [mappingType key] := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params,List.map_cons,List.map_nil,shape.scheme,TypeSystem.Scheme.mono] using types.symm

theorem read_key_valid {key : Key} (shape : ReadShape header.function.source key)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) : key.Valid header.context := by
  obtain ⟨final,facts,statements,_⟩ := certified.statements
  have roots : header.function.body = [shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  rw [roots] at statements
  cases statements with
  | singleton statement =>
    cases statement with
    | returnValue contains form expression _ =>
      have same := Option.some.inj ((lookupStatement?_complete header.unique contains).symm.trans shape.returnedFound)
      cases same
      rw [shape.returnedForm] at form
      cases Option.some.inj (StatementForm.returnStmt.inj form)
      have originalTyped := expression
      obtain ⟨actual, actualContains, actualType⟩ := expression.stored_type
      have same := Option.some.inj ((lookupExpression?_complete header.unique actualContains).symm.trans shape.indexFound)
      cases same
      rw [← actualType] at originalTyped
      obtain ⟨_,_,keyTyped⟩ := CompatibleExpressionIndices.index_source_types header.unique shape.indexFound
        shape.indexForm shape.indexCoercions originalTyped
      exact shape.keyNode.valid header.unique keyTyped
    | _ =>
      have same := Option.some.inj ((lookupStatement?_complete header.unique (by assumption)).symm.trans shape.returnedFound)
      cases same
      simp_all [shape.returnedForm]

/-- First-match lookup keeps later duplicate entries and the parameter heap. -/
theorem read_plain {key : Key} (shape : ReadShape header.function.source key)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (first : Word)
    (tail : List (Dynamic.Value × Dynamic.Value)) :
    PlainValue anchor header invocation before [mappingValue key ((key.value,.word first)::tail)] (.word first)
      (mappingHeap before key ((key.value,.word first)::tail)) := by
  let entries := (key.value,.word first)::tail
  let value := mappingValue key entries
  let after := mappingHeap before key entries
  let environment := [(shape.binder.id,location before)]
  have allocated : Dynamic.Heap.Allocates before (mappingType key) (some value) (location before) after := .append
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [value] environment after := by
    rw [params]; exact .cons (by rw [shape.scheme]; exact allocated) (.nil _ _)
  have expression : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment after shape.index.id (.word first) after := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.indexFound)
    · rw [shape.indexForm]
      exact .indexFound (by rw [shape.indexRequirements,shape.indexCoercions]; rfl)
        (read_value shape.base _ _ _ _ _ _ .head allocated.reads_new)
        (shape.keyNode.evaluates _ _ _ _ (read_key_valid header shape certified)) (.head (Dynamic.ValueEquivalent.refl key.comparable))
    · rw [shape.indexCoercions]; exact .nil
  have roots : header.function.body = [shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment after header.function.body
      header.context (.returned (.word first)) after := by
    rw [roots]
    exact .singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm expression)
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD,global,sourceAt,.global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedGeneralKey
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralKeyWriteSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedGeneralKey
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue)

structure WordNode (source : TypedSource) where
  node : ExpressionNode
  literal : Syntax.CoreLiteralValue
  resolution : IntegerLiteralResolution
  found : source.lookupExpression? node.id = some node
  form : node.form = .integerLiteral literal resolution
  target : resolution.targetType = .word
  requirements : node.requirements = [resolution.requirement]
  coercions : node.coercions = []

theorem WordNode.evaluates {source : TypedSource} (node : WordNode source)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context node.node.id type) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id
      (.word (Word.ofNatModulo node.resolution.rawValue)) heap := by
  have valid : IntegerLiteralValid context node.literal node.resolution := by
    cases typed with
    | intro contains raw _ _ _ _ =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans node.found)
      rw [node.form] at raw
      cases raw with | integerLiteral valid => exact valid
  have constructs : Dynamic.ResolvedIntegerLiteralConstructs context node.literal node.resolution
      (.word (Word.ofNatModulo node.resolution.rawValue)) := by
    cases valid with
    | word meaning target evidence =>
      generalize resolutionEq : node.resolution = resolution at *
      cases resolution with
      | mk value type requirement =>
        dsimp only at target
        subst type
        exact .word meaning evidence
    | integer _ target _ => rw [node.target] at target; cases target
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]; exact .integerLiteral (by rw [node.requirements,node.coercions]; rfl) constructs
  · rw [node.coercions]; exact .nil

structure WriteShape (source : TypedSource) (key : Key) where
  binder : TypedBinder
  keyNode : KeyNode source key
  simple : key.Simple
  right : WordNode source
  result : Tests.SourceCoreNamedBranch.Read source binder (mappingType key)
  assignment : AssignmentResolution
  assigned : StatementNode
  returned : StatementNode
  inputs : source.inputs = [binder]
  scheme : binder.scheme = .mono (mappingType key)
  roots : source.roots = [.statement assigned.id,.statement returned.id]
  assignedFound : source.lookupStatement? assigned.id = some assigned
  assignedForm : assigned.form = .assignValue assignment .add right.node.id
  targetRoot : assignment.target.root = binder.id
  targetProjections : assignment.target.projections = [.index keyNode.node.id]
  targetType : assignment.target.type = .word
  returnedFound : source.lookupStatement? returned.id = some returned
  returnedForm : returned.form = .returnStmt (some result.node.id)

private theorem write_append (previousCells : List Dynamic.Cell) (old next : Dynamic.Cell) :
    Dynamic.Heap.CellsWrite (previousCells ++ [old]) previousCells.length next (previousCells ++ [next]) := by
  induction previousCells with
  | nil => exact .head
  | cons head rest ih => exact .tail ih

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))

theorem write_input_types {key : Key} (shape : WriteShape header.function.source key) :
    header.types = [mappingType key] := by
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  simpa only [params,List.map_cons,List.map_nil,shape.scheme,TypeSystem.Scheme.mono] using types.symm

theorem write_rhs_typed {key : Key} (shape : WriteShape header.function.source key)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ExpressionHasType header.function.source header.context shape.right.node.id .word := by
  obtain ⟨final,facts,statements,_⟩ := certified.statements
  have roots : header.function.body = [shape.assigned.id,shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  rw [roots] at statements
  cases statements with
  | cons statement _ =>
    cases statement with
    | assignValue contains form assigned _ =>
      cases Option.some.inj ((lookupStatement?_complete header.unique contains).symm.trans shape.assignedFound)
      rw [shape.assignedForm] at form
      cases form
      cases assigned with | wordCompound _ _ typed _ => exact typed
    | _ =>
      have same := Option.some.inj ((lookupStatement?_complete header.unique (by assumption)).symm.trans shape.assignedFound)
      cases same
      simp_all [shape.assignedForm]

/-- The original key and literal RHS are evaluated before first-match update;
no later duplicate entry is replaced. -/
theorem write_plain {key : Key} (shape : WriteShape header.function.source key)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (first : Word)
    (tail : List (Dynamic.Value × Dynamic.Value)) :
    PlainValue anchor header invocation before [mappingValue key ((key.value,.word first)::tail)]
      (mappingValue key ((key.value,.word (first + Word.ofNatModulo shape.right.resolution.rawValue))::tail))
      (mappingHeap before key ((key.value,.word (first + Word.ofNatModulo shape.right.resolution.rawValue))::tail)) := by
  let original := mappingValue key ((key.value,.word first)::tail)
  let updated := first + Word.ofNatModulo shape.right.resolution.rawValue
  let replacement := mappingValue key ((key.value,.word updated)::tail)
  let current := mappingHeap before key ((key.value,.word first)::tail)
  let after := mappingHeap before key ((key.value,.word updated)::tail)
  let environment := [(shape.binder.id,location before)]
  have allocation : Dynamic.Heap.Allocates before (mappingType key) (some original) (location before) current := .append
  have rootRead := allocation.reads_new
  have params : header.function.parameters = [shape.binder] :=
    header.parameters.trans (header.inputs.symm.trans shape.inputs)
  have bound : Dynamic.BindersAllocate [] before header.function.parameters [original] environment current := by
    rw [params]; exact .cons (by rw [shape.scheme]; exact allocation) (.nil _ _)
  have resolve : Dynamic.SourcePlaceResolves (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current shape.assignment.target
      {location := location before,rootType := mappingType key,valueType := shape.assignment.target.type,
        projections := [.index key.value],selected := some (.word first)} current := by
    apply Dynamic.SourcePlaceResolves.intro
      (initialCell := ⟨mappingType key,some original,none⟩) (currentCell := ⟨mappingType key,some original,none⟩)
    · rw [shape.targetRoot]; exact .head
    · exact rootRead
    · rw [shape.targetProjections]
      exact .index (shape.keyNode.evaluates _ _ _ _ (key.simple_valid shape.simple _)) .nil
    · exact rootRead
    · exact .initialized
    · exact .indexFound (.head (Dynamic.ValueEquivalent.refl key.comparable)) .nil
  have write : Dynamic.Heap.Writes current (location before) (some replacement) after := by
    apply Dynamic.Heap.Writes.intro rootRead
    exact write_append before.cells ⟨mappingType key,some original,none⟩ ⟨mappingType key,some replacement,none⟩
  have assigned : Dynamic.StatementExecutes (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current shape.assigned.id
      header.context (.fallthrough environment) after := by
    apply Dynamic.StatementExecutes.assignValue (updatedRoot := replacement)
      (lookupStatement?_sound shape.assignedFound) shape.assignedForm
    refine .intro resolve (shape.right.evaluates _ _ _ header.unique (write_rhs_typed header shape certified)) ?_
    exact .intro rootRead rfl .initialized
      (.indexFound (.head (Dynamic.ValueEquivalent.refl key.comparable)) (.leaf (.add (.wordAdd _ _)))
        (.update (.head (Dynamic.ValueEquivalent.refl key.comparable)))) write
  have finalRootRead : Dynamic.Heap.Reads after (location before) ⟨mappingType key,some replacement,none⟩ := by
    obtain ⟨cell,readBefore,readAfter⟩ := write.reads_updated
    cases readBefore.functional rootRead
    exact readAfter
  have result : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment after shape.result.node.id replacement after := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.result.found)
    · rw [shape.result.form]
      exact .local (by rw [shape.result.requirements,shape.result.coercions]; rfl) .head finalRootRead rfl rfl
    · rw [shape.result.coercions]; exact .nil
  have roots : header.function.body = [shape.assigned.id,shape.returned.id] :=
    roots_injective (header.agreement.roots.symm.trans shape.roots)
  have body : Dynamic.FunctionStatementsExecute (Program.ofChecked compiled.sourceProgram)
      header.context header.function.evidence header.function.source environment current header.function.body
      header.context (.returned replacement) after := by
    rw [roots]
    exact .cons assigned (.singleton (lookupStatement?_sound shape.returnedFound)
      (by rw [shape.returnedForm]; intro id impossible; cases impossible)
      (.returnValue (lookupStatement?_sound shape.returnedFound) shape.returnedForm result))
  have invoked := sourceAt.frame.body_of_trace header.extended bound (FunctionCallBody.Trace.returned body)
  cases invoked with
  | value invoked => exact ⟨rawD,global,sourceAt,.global sourceAt.frame.instantiated rfl
      (sourceAt.dictionary ▸ sourceAt.frame.covers) (sourceAt.dictionary ▸ invoked)⟩

end Tests.SourceCoreSelectedGeneralKey
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralKeyFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralKey
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure CompiledFixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram workspace options.checkingFuel = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe

def compileFixture : IO CompiledFixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let seeds := program.signatures.functions.map (fun signature => SourceCompiler.Seed.declaration signature.id)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match present : source.artifact? with
      | none => throw (IO.userError "general key artifact absent")
      | some cached =>
        match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError (reprStr error))
        | .ok recipe =>
          match facade : SourceCoreExecution.prepare source with
          | .error error => throw (IO.userError (reprStr error))
          | .ok publicCompiled =>
            have sameProgram : recipe.compiled.sourceProgram = program :=
              (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
                ((source.artifact_fields present).1.trans (SourceCoreCompiler.compileChecked_program generated))
            return {
              recipe := recipe
              checked := by rw [sameProgram]; exact checked
              seeds := seeds
              facade := publicCompiled
              accepted := by
                rw [sameProgram]
                simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
              selected := RecursiveNamedPreparedStageContracts.public_preparation present prepared facade }


structure Row (fixture : CompiledFixture) where
  original : SourceSpecialization.SpecializedFunction
  member : original ∈ fixture.recipe.compiled.validationPlan.specializations
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = original.key
  substitution : original.parameterSubstitution = []
  ordinary : original.function.returnComptime = false
  ordinaryInputs : ∀ binder ∈ original.function.typedBody.inputs, binder.comptime = false

def observeRow (fixture : CompiledFixture) (name : String) : IO (Row fixture) := do
  let some signature := fixture.recipe.compiled.sourceProgram.signatures.functions.find? (fun signature => signature.name == name)
    | throw (IO.userError "general key original signature")
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "general key original row")
  | some original =>
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun pair => decide (pair.1.key = original.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = original.key) "general key global key"
      let ⟨substitution⟩ ← observed (original.parameterSubstitution = []) "general key substitution"
      let ⟨ordinary⟩ ← observed (original.function.returnComptime = false) "general key ordinary return"
      let ⟨ordinaryInputs⟩ ← observed (original.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "general key ordinary parameters"
      return {
        original := original
        member := List.mem_of_find?_eq_some found
        global := global
        index := index
        slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
        globalKey := globalKey
        substitution := substitution
        ordinary := ordinary
        ordinaryInputs := by
          intro binder member
          have selected := List.all_eq_true.mp ordinaryInputs binder member
          cases marker : binder.comptime <;> simp_all }
    | _ => throw (IO.userError "general key unique physical slot")

theorem Row.eligible {fixture : CompiledFixture} (row : Row fixture) :
    ∃ eligible : SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled row.original.key,
      eligible.named.specialized = row.original ∧ eligible.named.signature = row.global := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.selected row.member
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
    simp only [row.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared, decide_true]
  rw [row.slot] at member
  obtain ⟨signatureEq, indexEq⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  have range : ParameterSubstitution.RangeWellFormed (SourceSemantics.Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures)
      row.original.parameterSubstitution := by
    rw [row.substitution]; intro parameter replacement impossible; cases impossible
  refine ⟨⟨prepared.named, prepared.index, row.global, prepared.selected, ?_, row.globalKey, ?_⟩, prepared.same, signatureEq⟩
  · rw [indexEq]; exact row.slot
  · rw [prepared.same]; exact ⟨prepared.origin, range, row.ordinary, row.ordinaryInputs⟩

def observeBool (source : TypedSource) (id : ExpressionId) : IO ((value : Bool) × BoolNode source value) := do
  let some node := source.lookupExpression? id | throw (IO.userError "general key boolean node")
  let .reference name (.builtinBoolean value) := node.form | throw (IO.userError "general key boolean form")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "general key boolean identity"
  let ⟨form⟩ ← observed (node.form = .reference name (.builtinBoolean value)) "general key boolean form identity"
  let ⟨requirements⟩ ← observed (node.requirements = []) "general key boolean requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "general key boolean coercions"
  return ⟨value,node,found,name,form,requirements,coercions⟩

def observeKey (source : TypedSource) (id : ExpressionId) : IO ((key : Key) × KeyNode source key) := do
  let some node := source.lookupExpression? id | throw (IO.userError "general key node")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "general key identity"
  let ⟨requirements⟩ ← observed (node.requirements = []) "general key requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "general key coercions"
  match form : node.form with
  | .tuple [first,second] =>
    let ⟨left,leftNode⟩ ← observeBool source first
    let ⟨right,rightNode⟩ ← observeBool source second
    let ⟨actualForm⟩ ← observed (node.form = .tuple [leftNode.node.id,rightNode.node.id]) "general key tuple child order"
    let ⟨type⟩ ← observed (node.type = (.product .bool .bool)) "general key tuple raw type"
    return ⟨.pair left right,node,found,type,requirements,coercions,.pair leftNode rightNode actualForm⟩
  | .proxy inner =>
    let ⟨type⟩ ← observed (node.type = .proxy inner) "general key proxy raw type"
    return ⟨.proxy inner,node,found,type,requirements,coercions,.proxy form⟩
  | .constructor metadata [argument] =>
    let ⟨value,child⟩ ← observeBool source argument
    let ⟨actualForm⟩ ← observed (node.form = .constructor metadata [child.node.id]) "general key nominal child identity"
    let ⟨type⟩ ← observed (node.type = metadata.resultType) "general key nominal raw type"
    let ⟨substitution⟩ ← observed (metadata.parameterSubstitution = []) "general key nominal substitution"
    let ⟨payload⟩ ← observed (metadata.payloadTypes = [.bool]) "general key nominal payload"
    return ⟨.nominal metadata value,node,found,type,requirements,coercions,.nominal child actualForm substitution payload⟩
  | _ => throw (IO.userError s!"general key form changed: {reprStr node.form}")

def observeRead (source : TypedSource) : IO ((key : Key) × ReadShape source key) := do
  let [binder] := source.inputs | throw (IO.userError "general key read input")
  let [.statement id] := source.roots | throw (IO.userError "general key read root")
  let some returned := source.lookupStatement? id | throw (IO.userError "general key read return")
  let .returnStmt (some expression) := returned.form | throw (IO.userError "general key read returned expression")
  let some index := source.lookupExpression? expression | throw (IO.userError "general key index lookup")
  let .index baseId keyId := index.form | throw (IO.userError "general key index form")
  let some baseNode := source.lookupExpression? baseId | throw (IO.userError "general key base lookup")
  let ⟨key,keyNode⟩ ← observeKey source keyId
  let base ← Tests.SourceCoreNamedBranch.observeRead source binder baseNode (mappingType key)
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "general key read input identity"
  let ⟨scheme⟩ ← observed (binder.scheme = .mono (mappingType key)) "general key read raw input type"
  let ⟨roots⟩ ← observed (source.roots = [.statement returned.id]) "general key read root identity"
  let ⟨indexFound⟩ ← observed (source.lookupExpression? index.id = some index) "general key index identity"
  let ⟨indexForm⟩ ← observed (index.form = .index base.node.id keyNode.node.id) "general key ordered index children"
  let ⟨requirements⟩ ← observed (index.requirements = []) "general key index requirements"
  let ⟨coercions⟩ ← observed (index.coercions = []) "general key index coercions"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "general key return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some index.id)) "general key return child"
  return ⟨key,binder,keyNode,base,index,returned,inputs,scheme,roots,indexFound,indexForm,requirements,coercions,returnedFound,returnedForm⟩

def observeWord (source : TypedSource) (id : ExpressionId) : IO (WordNode source) := do
  let some node := source.lookupExpression? id | throw (IO.userError "general key RHS lookup")
  let .integerLiteral literal resolution := node.form | throw (IO.userError "general key RHS original literal")
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "general key RHS identity"
  let ⟨form⟩ ← observed (node.form = .integerLiteral literal resolution) "general key RHS form"
  let ⟨target⟩ ← observed (resolution.targetType = .word) "general key RHS target"
  let ⟨requirements⟩ ← observed (node.requirements = [resolution.requirement]) "general key RHS requirement identity"
  let ⟨coercions⟩ ← observed (node.coercions = []) "general key RHS coercions"
  return ⟨node,literal,resolution,found,form,target,requirements,coercions⟩

private def observeSimple (key : Key) : IO (PLift key.Simple) :=
  match key with
  | .pair .. | .proxy .. => pure ⟨True.intro⟩
  | .nominal .. => throw (IO.userError "general key write key form")

def observeWrite (source : TypedSource) : IO ((key : Key) × WriteShape source key) := do
  let [binder] := source.inputs | throw (IO.userError "general key write input")
  let [.statement assignId,.statement returnId] := source.roots | throw (IO.userError "general key write roots")
  let some assigned := source.lookupStatement? assignId | throw (IO.userError "general key assignment lookup")
  let .assignValue assignment .add rhsId := assigned.form | throw (IO.userError "general key actual compound assignment")
  let [.index keyId] := assignment.target.projections | throw (IO.userError "general key mapping projection")
  let ⟨key,keyNode⟩ ← observeKey source keyId
  let ⟨simple⟩ ← observeSimple key
  let right ← observeWord source rhsId
  let some returned := source.lookupStatement? returnId | throw (IO.userError "general key write return lookup")
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "general key write return")
  let some resultNode := source.lookupExpression? resultId | throw (IO.userError "general key write read lookup")
  let result ← Tests.SourceCoreNamedBranch.observeRead source binder resultNode (mappingType key)
  let ⟨inputs⟩ ← observed (source.inputs = [binder]) "general key write input identity"
  let ⟨scheme⟩ ← observed (binder.scheme = .mono (mappingType key)) "general key write raw input type"
  let ⟨roots⟩ ← observed (source.roots = [.statement assigned.id,.statement returned.id]) "general key write ordered roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "general key assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignValue assignment .add right.node.id) "general key RHS order"
  let ⟨targetRoot⟩ ← observed (assignment.target.root = binder.id) "general key original root binder"
  let ⟨targetProjections⟩ ← observed (assignment.target.projections = [.index keyNode.node.id]) "general key ordered projection"
  let ⟨targetType⟩ ← observed (assignment.target.type = .word) "general key selected raw Word"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "general key write return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "general key write return child"
  return ⟨key,binder,keyNode,simple,right,result,assignment,assigned,returned,inputs,scheme,roots,
    assignedFound,assignedForm,targetRoot,targetProjections,targetType,returnedFound,returnedForm⟩

structure Started (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : StartedCall session key arguments runOptions

def observeStarted (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facade.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "general key bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
        bootstrap.property.2, session, ready, checkpoint, started⟩

end Tests.SourceCoreSelectedGeneralKey
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralKeySourceFirst
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralKey
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)

/-- Actual compiler selection and fresh bootstrap determine the public issuer
and original source. No body execution or completed public call is assumed. -/
structure Selection {fixture : CompiledFixture} (row : Row fixture)
    {arguments : List SourceCorePublicValues.Value} (started : Started fixture row.original.key arguments) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  sourceEq : initial.header.function.source = row.original.function.typedBody

theorem selection {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    {arguments : List SourceCorePublicValues.Value} (started : Started fixture row.original.key arguments) :
    Nonempty (Selection row started) := by
  obtain ⟨eligible, rowSame, _signatureSame⟩ := row.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) eligible
  have sourceEq := initial.header.agreement.source.trans
    ((congrArg (fun named => named.specialized.function.typedBody) namedEq).trans
      (congrArg (fun original => original.function.typedBody) rowSame))
  exact ⟨⟨issued, initial, sourceEq⟩⟩

/-- The final public conclusion retains the whole Source value, authentic
encoding and retained history, or an actual earlier stage rejection. -/
structure InitialOutput {fixture : CompiledFixture} (row : Row fixture)
    {publicArguments : List SourceCorePublicValues.Value}
    (started : Started fixture row.original.key publicArguments)
    (arguments : List Dynamic.Value) (value : Dynamic.Value) (after : Dynamic.Heap) extends Selection row started where
  plain : ∀ invocation, RecursiveNamedPublicPhysicalSessionState.PlainValue
    initial.header initial.header invocation ⟨[]⟩ arguments value after
  forward : ∀ invocation,
    (SelectedCompilationPublicSessionState.SourceCall initial.header initial.header invocation
        ⟨[]⟩ arguments (.value value) after ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows initial.header issued.initial
        issued.support.profile fixture.recipe [] initial.header.function.resultType started.call.checkpoint value after) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation arguments

def Key.carrier : Key → SourceCoreDataValues.Value
  | .pair left right => .product (.bool left) (.bool right)
  | .proxy inner => .proxy inner
  | .nominal metadata argument => .constructed metadata [.bool argument]

def entries (key : Key) (first later : Word) : List (Dynamic.Value × Dynamic.Value) :=
  [(key.value,.word first),(key.value,.word later)]
def mapCarrier (key : Key) (first later : Word) : SourceCoreDataValues.Value :=
  .mapping key.type .word [(key.carrier,.word first),(key.carrier,.word later)]
def publicMap (key : Key) (first later : Word) : SourceCorePublicValues.Value :=
  SourceCoreIndexedSession.DataInput.publicValue (mapCarrier key first later)

theorem Key.means (key : Key) : DataPayloadEncoding.Means key.carrier key.value := by
  cases key with
  | pair left right => exact .product (.bool left) (.bool right)
  | proxy inner => exact .proxy inner
  | nominal metadata argument => exact .constructed (.cons (.bool argument) .nil)

theorem KeyNode.input_typed {source : TypedSource} {key : Key} (node : KeyNode source key)
    {context : SourceSemantics.Context} (valid : key.Valid context) :
    RecursiveNamedPublicDataArgumentReceipts.DataTyped context key.carrier key.type := by
  cases node.shape with
  | pair => exact .product (.bool _) (.bool _)
  | proxy => exact .proxy _
  | nominal child _ _ payload =>
    exact .constructed valid (by rw [payload]; exact .cons (.bool _) .nil)

private theorem key_valid_at {source : TypedSource} {key : Key} (node : KeyNode source key)
    {context target : SourceSemantics.Context} (valid : key.Valid context)
    (same : context.signatures = target.signatures) : key.Valid target := by
  cases node.shape with
  | pair | proxy => trivial
  | nominal _ _ substitution _ =>
    cases valid with
    | intro dataType signature dataMember signatureMember owner constructorEq exact range payload result =>
      exact .intro dataType signature (by rw [← same]; exact dataMember) signatureMember owner constructorEq exact
        (by rw [substitution]; intro parameter replacement impossible; cases impossible) payload result

private theorem cast_right {source target : TypedSource} {key : Key} (same : source = target)
    (shape : WriteShape source key) :
    (same ▸ shape).right.resolution.rawValue = shape.right.resolution.rawValue := by cases same; rfl

theorem map_meanings (key : Key) (first later : Word) :
    RecursiveNamedPublicDataInputs.Meanings [publicMap key first later]
      [mappingValue key (entries key first later)] := by
  exact .cons ⟨mapCarrier key first later,rfl,
    .mapping (.prepend key.means (.word first) (.prepend key.means (.word later) .empty))⟩ .nil

theorem map_types {source : TypedSource} {key : Key} (node : KeyNode source key)
    {context : SourceSemantics.Context} (valid : key.Valid context) (first later : Word) :
    RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes context [publicMap key first later] [mappingType key] := by
  exact .cons ⟨mapCarrier key first later,rfl,
    .mapping (.entry (node.input_typed valid) (.word first)
      (.entry (node.input_typed valid) (.word later) (.empty _ _)))⟩ .nil

/-- The checker, full compile receipt and startup produce the actual public
issuer. Original ordered key execution is established before public completion. -/
theorem read_from_source {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    {key : Key} (shape : ReadShape row.original.function.typedBody key)
    (first later : Word) (started : Started fixture row.original.key [publicMap key first later]) :
    Nonempty (InitialOutput row started [mappingValue key (entries key first later)] (.word first)
      (mappingHeap ⟨[]⟩ key (entries key first later))) := by
  obtain ⟨chosen⟩ := selection row profile started
  have actual : ReadShape chosen.initial.header.function.source key := by rw [chosen.sourceEq]; exact shape
  have certified := chosen.issued.support.certificates chosen.initial.header chosen.initial.start.selected.member
  obtain ⟨rawD,global,sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts chosen.issued.catalog.rows).receipts
      chosen.initial.header chosen.initial.start.selected.member
  have plain := fun invocation => read_plain chosen.initial.header actual certified sourceAt
    chosen.initial.header invocation ⟨[]⟩ first [(key.value,.word later)]
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes chosen.initial.header.function.context
      [publicMap key first later] chosen.initial.header.types := by
    rw [read_input_types chosen.initial.header actual]
    exact map_types actual.keyNode
      (key_valid_at actual.keyNode (read_key_valid chosen.initial.header actual certified)
        (Dynamic.MonoBindersExtend.runtimeContextFields chosen.initial.header.extended).signatures) first later
  exact ⟨{
    toSelection := chosen
    plain := by simpa only [entries] using plain
    forward := fun invocation => by
      simpa only [entries] using chosen.initial.forward_data_output_plain types (map_meanings key first later) (plain invocation) }⟩

/-- Compound update preserves later duplicate entries and returns the complete
mapping representation, from a fresh metadata-bearing public input. -/
theorem write_from_source {fixture : CompiledFixture} (row : Row fixture)
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    {key : Key} (shape : WriteShape row.original.function.typedBody key)
    (first later : Word) (started : Started fixture row.original.key [publicMap key first later]) :
    Nonempty (InitialOutput row started [mappingValue key (entries key first later)]
      (mappingValue key (entries key (first + Word.ofNatModulo shape.right.resolution.rawValue) later))
      (mappingHeap ⟨[]⟩ key (entries key (first + Word.ofNatModulo shape.right.resolution.rawValue) later))) := by
  obtain ⟨chosen⟩ := selection row profile started
  let actual : WriteShape chosen.initial.header.function.source key := chosen.sourceEq.symm ▸ shape
  have certified := chosen.issued.support.certificates chosen.initial.header chosen.initial.start.selected.member
  obtain ⟨rawD,global,sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts chosen.issued.catalog.rows).receipts
      chosen.initial.header chosen.initial.start.selected.member
  have plain := fun invocation => write_plain chosen.initial.header actual certified sourceAt
    chosen.initial.header invocation ⟨[]⟩ first [(key.value,.word later)]
  have types : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes chosen.initial.header.function.context
      [publicMap key first later] chosen.initial.header.types := by
    rw [write_input_types chosen.initial.header actual]
    exact map_types actual.keyNode (key.simple_valid actual.simple _) first later
  have rightEq : actual.right.resolution.rawValue = shape.right.resolution.rawValue :=
    cast_right chosen.sourceEq.symm shape
  refine ⟨{ toSelection := chosen
            plain := ?_
            forward := ?_ }⟩
  · simpa only [rightEq, entries] using plain
  · intro invocation
    have forward := chosen.initial.forward_data_output_plain types (map_meanings key first later) (plain invocation)
    simpa only [rightEq, entries] using forward

end Tests.SourceCoreSelectedGeneralKey
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedGeneralKeyProfile
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralKey
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def word (value : Nat) : Word := Word.ofNatModulo value

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

/-- The unchanged five-function program is checked and compiled with every
original function seeded. Independent Source proofs precede all first results;
exported mapping reuse is an additional native runtime check. -/
def run : IO Unit := do
  let fixture ← compileFixture
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      fixture.recipe.compiled fixture.checked
    | throw (IO.userError "general key complete checked profile rejected")
  require (fixture.recipe.compiled.sourceProgram.functions.length == 5 &&
      fixture.recipe.compiled.indexed.base.functions.length == 5 && profile.table.rows.length == 5)
    "general key original/cache/profile rows changed"
  let mut readHeaps := []
  for name in ["pairRead","proxyRead","nominalRead"] do
    let row ← observeRow fixture name
    let ⟨key,shape⟩ ← observeRead row.original.function.typedBody
    let started ← observeStarted fixture row.original.key [publicMap key (word 7) (word 90)]
    have _sourceFirst := read_from_source row profile shape (word 7) (word 90) started
    let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
      | throw (IO.userError "general key read zero fuel did not suspend")
    let .succeeded completed ← suspended.resume 100000 1000
      | throw (IO.userError s!"general key {name} failed")
    require (completed.value == .word (word 7)) "general key first-match lookup changed"
    readHeaps := readHeaps ++ [started.session.heapSize,completed.session.heapSize]
  require (readHeaps == [6,15,6,15,6,15]) "general key exact read heaps changed"
  let mut writeHeaps := []
  for (name,reader) in [("pairWrite","pairRead"),("proxyWrite","proxyRead")] do
    let row ← observeRow fixture name
    let readRow ← observeRow fixture reader
    let ⟨key,shape⟩ ← observeWrite row.original.function.typedBody
    require (shape.right.resolution.rawValue == 3) "general key original RHS value changed"
    let started ← observeStarted fixture row.original.key [publicMap key (word 7) (word 90)]
    have _sourceFirst := write_from_source row profile shape (word 7) (word 90) started
    let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
      | throw (IO.userError "general key write zero fuel did not suspend")
    let .succeeded completed ← suspended.resume 100000 1000
      | throw (IO.userError s!"general key {name} failed")
    require (completed.value == publicMap key (word 10) (word 90)) "general key first-match write changed later duplicate"
    let again ← get "general key exported mapping reuse" (completed.session.start row.original.key [completed.value])
    let .succeeded reused ← again.resume 100000 1000
      | throw (IO.userError "general key repeated compound write failed")
    require (reused.value == publicMap key (word 13) (word 90)) "general key repeated write changed ordered entries"
    let read ← get "general key updated mapping read" (reused.session.start readRow.original.key [reused.value])
    let .succeeded readBack ← read.resume 100000 1000
      | throw (IO.userError "general key read after write failed")
    require (readBack.value == .word (word 13)) "general key read after reuse changed"
    writeHeaps := writeHeaps ++ [started.session.heapSize,completed.session.heapSize,reused.session.heapSize,readBack.session.heapSize]
  require (writeHeaps == [6,27,48,57,6,27,48,57]) "general key exact write/reuse heaps changed"
  IO.println s!"GENERAL_KEY_COMPLETE_CACHE: originals5/cache5/table{profile.table.rows.length}"
  IO.println s!"GENERAL_KEY_READ_NATIVE_HEAPS: {readHeaps}"
  IO.println s!"GENERAL_KEY_WRITE_REUSE_NATIVE_HEAPS: {writeHeaps}"
  IO.println "GENERAL_KEY_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedGeneralKey
end
