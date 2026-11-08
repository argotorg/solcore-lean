import Solcore.Test.SourceSemantics.CoreLowering.Evidence.Method
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalMixedFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.Test.SourceSemantics.CoreLowering.Method.Closure
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.Test.SourceSemantics.CoreLowering.Method.DirectEvidence
import Solcore.Test.SourceSemantics.CoreLowering.Method.GenericSubstitution
import Solcore.Test.SourceSemantics.CoreLowering.Method.ImplementationScoped
import Solcore.Test.SourceSemantics.CoreLowering.Method.NamedScoped
import Solcore.Test.SourceSemantics.CoreLowering.Method.OwnEvidence
import Solcore.Test.SourceSemantics.CoreLowering.Method.Scoped

/-!
# Method public sequence tests

The closure family, public execution and call sequences of the method features, one section per feature.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (receiver : ObservedReceiver fixture observed)
  (support : StaticSupportPackage fixture observed receiver.completion)
  (bodies : MethodBodies fixture)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "initialFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
local notation "functions" => support.toOrdinaryInventory.functions receiver

include receiver support bodies in
theorem StaticSupportPackage.method_supports :
    CallableIndexedOwnedPreparedStagedPhysicalCallerFamily.MethodSupports
      (compiled := fixture.recipe.compiled) (headers := headers support.toOrdinaryInventory.rows)
      (stages := actualRegistry) (semanticFaults := initialFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  exact bodies.support observed port.principal port.sourceAt ⟨port.diagnostics⟩ receiver.issued
    (headers support.toOrdinaryInventory.rows) actualRegistry

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry)

include receiver extension in
private theorem static_extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.recipe.compiled.compatible.checked).registry
    receiving.result.context.registry := by
  change SourceCoreRawMetadata.Extends fixture.recipe.compiled.compatible.checked.staticRegistry _
  rw [← receiver.registry]
  exact extension

include receiver support issued extension in
private theorem semantic_extension : ∀ reason token, initialFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
  obtain ⟨program, present, _⟩ := support.wordHeader.diagnostic.actual
  intro reason token represented
  exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
    receiver.issued issued present extension represented

include receiver support bodies issued extension in
/-- Both body families are derived at the real reached metadata registry. -/
theorem preserves_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget :=
  CallableIndexedOwnedPreparedStagedPhysicalNamedFamilyPorts.preserves issued observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.terminals support.supports (StaticSupportPackage.method_supports receiver support bodies) header member selected budget

include receiver support bodies issued extension in
theorem reflects_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget :=
  CallableIndexedOwnedPreparedStagedPhysicalNamedFamilyPorts.reflects issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.terminals support.supports (StaticSupportPackage.method_supports receiver support bodies) rfl header member selected budget

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodPublicExecution
/-! Four original public calls share their exact successive sessions, complete
Source heaps and physical method captures. Every body law is derived from the
actual compiler packets by the common numeric induction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (before : RetainedState support.toOrdinaryInventory receiver session [])
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments scalar.publicValue)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session []
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value scalar.source) after.heap

theorem RetainedState.word_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (bodies : MethodBodies fixture)
    (state : RetainedState support.toOrdinaryInventory receiver session [])
    (word : Core.Word)
    (call : ObservedCall session observed.wordRow.row.key [.word word] (.word word))
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.wordHeader.header (.word word) call [.word word] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.viaWordInput, support.viaBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.viaWordHeader support.viaBoolHeader
      support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_inputs word
  have raw : request.header.function.resultType = (.word word : ScalarOutput).sourceType := by
    rw [selected, support.wordHeader.word_result_type]; rfl
  have native : request.header.output = (.word word : ScalarOutput).nativeType := by
    rw [selected, support.wordHeader.word_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact stages.descriptor_at support.wordHeader
  obtain ⟨after, trace⟩ := state.finished_call (.word word) call request inputs
    (word_simple word) raw native descriptor (support.terminals request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support bodies state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, native, after, by rw [← selected]; exact trace⟩⟩

theorem RetainedState.bool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (bodies : MethodBodies fixture)
    (state : RetainedState support.toOrdinaryInventory receiver session [])
    (flag : Bool)
    (call : ObservedCall session observed.boolRow.row.key [.bool flag] (.bool flag))
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.boolHeader.header (.bool flag) call [.bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.viaWordInput, support.viaBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.viaWordHeader support.viaBoolHeader
      support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool flag] [.bool flag] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_inputs flag
  have raw : request.header.function.resultType = (.bool flag : ScalarOutput).sourceType := by
    rw [selected, support.boolHeader.bool_result_type]; rfl
  have native : request.header.output = (.bool flag : ScalarOutput).nativeType := by
    rw [selected, support.boolHeader.bool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact stages.descriptor_at support.boolHeader
  obtain ⟨after, trace⟩ := state.finished_call (.bool flag) call request inputs
    (bool_simple flag) raw native descriptor (support.terminals request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support bodies state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session []
  firstTrace : SourceCall support.toOrdinaryInventory support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed] (.value (.word seed)) initial.heap
  secondMeaning : CallMeaning initial support.boolHeader.header (.bool false) sequence.second
    [.bool false]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  thirdMeaning : CallMeaning secondMeaning.after support.wordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.third
    [.word (Core.Word.ofNatModulo 33)]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  fourthMeaning : CallMeaning thirdMeaning.after support.boolHeader.header (.bool true) sequence.fourth
    [.bool true]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (bodies : MethodBodies fixture)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed wordStages boolStages methods receiver.issued
  obtain ⟨initial, firstTrace⟩ := first_meaning support.toOrdinaryInventory support.distinct
    (support.terminals support.wordHeader.header support.toOrdinaryInventory.word_member)
    (fun budget {child} selected => reflects_bodies receiver support bodies receiver.issued (.refl _)
      support.wordHeader.header support.toOrdinaryInventory.word_member selected budget) wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_meaning support bodies initial false sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_meaning support bodies second.after (Core.Word.ofNatModulo 33) sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨fourth⟩ := RetainedState.bool_meaning support bodies third.after true sequence.fourth boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  exact ⟨⟨support, initial, firstTrace, second, third, fourth⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (bodies : MethodBodies fixture)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages methods bodies sequence receiver⟩

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreEvidenceMethodSequenceForward
/-! The actual four-call method program closes both directions through the
same physical family. Every call retains its Source heap and obtains sufficient
execution and output fuel at its original public checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {before : RetainedState support.toOrdinaryInventory receiver session []}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments scalar.publicValue}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (bodies : MethodBodies fixture)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (ready : session.ExportsReady) :
    ForwardAt (entries := []) support.toOrdinaryInventory receiver scalar call meaning.after.heap := by
  apply forward_call before scalar call meaning.request meaning.inputs simple meaning.rawType meaning.nativeType ready
    (support.terminals meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support bodies before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support.toOrdinaryInventory receiver sequence.first meaning.initial.heap
  second : ForwardAt (entries := []) meaning.support.toOrdinaryInventory receiver (.bool false)
    sequence.second meaning.secondMeaning.after.heap
  third : ForwardAt (entries := []) meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33))
    sequence.third meaning.thirdMeaning.after.heap
  fourth : ForwardAt (entries := []) meaning.support.toOrdinaryInventory receiver (.bool true)
    sequence.fourth meaning.fourthMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver)
    (bodies : MethodBodies fixture) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have thirdReady := sequence.third.executed.exportsReady secondReady
  exact ⟨forward_initial meaning.support.toOrdinaryInventory meaning.support.distinct sequence.first
      (meaning.support.terminals meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member)
      (fun budget {child} selected => preserves_bodies receiver meaning.support bodies receiver.issued (.refl _)
        meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member selected budget)
      meaning.firstTrace,
    meaning.secondMeaning.forward bodies (bool_simple false) firstReady,
    meaning.thirdMeaning.forward bodies (word_simple (Core.Word.ofNatModulo 33)) secondReady,
    meaning.fourthMeaning.forward bodies (bool_simple true) thirdReady⟩

theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (bodies : MethodBodies fixture)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed wordStages boolStages methods bodies sequence
  exact ⟨receiver, meaning, meaning.forward bodies⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let ⟨methods⟩ ← observeMethodCatalog fixture
  let ⟨bodies⟩ ← observeMethodBodies fixture
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed wordStages boolStages methods bodies sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.third.completion.session.heapSize,
    sequence.fourth.completion.session.heapSize]
  unless stores == [7, 16, 25, 34, 43] do
    throw (IO.userError s!"method session stores changed: {reprStr stores}")
  IO.println "EVIDENCE_METHOD_FORWARD_PASS: Word11, BoolFalse, Word33, BoolTrue; four Source histories and sufficient public fuel; stores7/16/25/34/43"

end Tests.SourceCoreEvidenceMethod
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodClosureFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (receiver : ObservedReceiver fixture observed)
  (support : StaticSupportPackage fixture observed receiver.completion)
  (sources : ObservedClosureSources fixture observed)
  (bodies : MethodBodies fixture)
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "initialFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
local notation "functions" => support.toOrdinaryInventory.functions receiver

include receiver support bodies in
theorem StaticSupportPackage.method_supports :
    CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.MethodSupports
      (compiled := fixture.recipe.compiled) (headers := headers support.toOrdinaryInventory.rows)
      (stages := actualRegistry) (semanticFaults := initialFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  exact bodies.support observed port.principal port.sourceAt ⟨port.diagnostics⟩ receiver.issued
    (headers support.toOrdinaryInventory.rows) actualRegistry

include support in
private theorem owners_physical : ∀ selected : CallableIndexedOwnedFunctionValues.OwnedKey (keys fixture.recipe.compiled),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical selected.key (headers support.toOrdinaryInventory.rows) := by
  intro selected
  have same : selected = CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled := by
    cases selected with
    | mk position =>
      have samePosition : position = (CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled).position := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < 1 at bound
        change position.val = 0
        omega
      cases samePosition
      rfl
  rw [same]
  exact CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry)

include receiver extension in
private theorem static_extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.recipe.compiled.compatible.checked).registry
    receiving.result.context.registry := by
  change SourceCoreRawMetadata.Extends fixture.recipe.compiled.compatible.checked.staticRegistry _
  rw [← receiver.registry]
  exact extension

include receiver support issued extension in
private theorem semantic_extension : ∀ reason token, initialFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
  obtain ⟨program, present, _⟩ := support.wordHeader.diagnostic.actual
  intro reason token represented
  exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
    receiver.issued issued present extension represented

include receiver support sources bodies methods issued extension in
/-- Both body families are derived at the real reached metadata registry. -/
theorem preserves_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory.rows
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.preserves issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.terminals support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) header member selected budget

include receiver support sources bodies methods issued extension in
theorem reflects_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory.rows
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.reflects issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.terminals support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) rfl header member selected budget

end Tests.SourceCoreMethodClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodClosurePublicExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  registry : request.encodedValues.registry = before.receiving.result.context.registry
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session entries
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value scalar.source) after.heap

structure FactoryMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (resultType : TypeSystem.Ty) (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session (entries ++ [entry])
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value entry.source) after.heap

theorem RetainedState.word_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value : Core.Word)
    (call : ObservedFunctionCall session observed.wordRow.row.key [.word value])
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.wordHeader.header call .word [.word value] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value] [.word value] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_inputs value
  have raw : request.header.function.resultType = closureType .word := by
    rw [selected, support.wordHeader.word_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.wordHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (word_simple value) descriptor (support.terminals request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.bool_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value : Bool)
    (call : ObservedFunctionCall session observed.boolRow.row.key [.bool value])
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.boolHeader.header call .bool [.bool value] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value] [.bool value] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_inputs value
  have raw : request.header.function.resultType = closureType .bool := by
    rw [selected, support.boolHeader.bool_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.boolHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (bool_simple value) descriptor (support.terminals request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useWord_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useWordRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useWordHeader.header (.word value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useWordHeader.header :=
    selected_useWord_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useWordHeader.useWord_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [selected, support.useWordHeader.useWord_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [selected, support.useWordHeader.useWord_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useWordHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.word value) call returned request inputs registry raw native descriptor
    (support.terminals request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useBool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .bool)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Bool) (call : ObservedCall session observed.useBoolRow.row.key [.function handle])
    (returned : call.completion.value = .bool value)
    (stages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useBoolHeader.header (.bool value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useBoolHeader.header :=
    selected_useBool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useBoolHeader.useBool_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.bool value : ScalarOutput).sourceType := by
    rw [selected, support.useBoolHeader.useBool_result_type]; rfl
  have native : request.header.output = (.bool value : ScalarOutput).nativeType := by
    rw [selected, support.useBoolHeader.useBool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useBoolHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.bool value) call returned request inputs registry raw native descriptor
    (support.terminals request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  firstEntry : Entry
  firstType : firstEntry.sourceType = closureType .word
  firstHandle : firstEntry.handle = sequence.first.handle
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session [firstEntry]
  firstTrace : SourceCall support.toOrdinaryInventory support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed] (.value firstEntry.source) initial.heap
  secondMeaning : FactoryMeaning initial support.boolHeader.header sequence.second .bool [.bool false]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  firstReadMeaning : CallMeaning secondMeaning.after support.useWordHeader.header (.word seed) sequence.firstRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdMeaning : FactoryMeaning firstReadMeaning.after support.wordHeader.header sequence.third .word [.word (Core.Word.ofNatModulo 33)]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  secondReadMeaning : CallMeaning thirdMeaning.after support.useBoolHeader.header (.bool false) sequence.secondRead [secondMeaning.entry.source]
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  repeatedReadMeaning : CallMeaning secondReadMeaning.after support.useWordHeader.header (.word seed) sequence.repeatedRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdReadMeaning : CallMeaning repeatedReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.thirdRead [thirdMeaning.entry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)

theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) :
    meaning.firstEntry.handle ≠ meaning.secondMeaning.entry.handle ∧
      meaning.firstEntry.handle ≠ meaning.thirdMeaning.entry.handle ∧
      meaning.secondMeaning.entry.handle ≠ meaning.thirdMeaning.entry.handle := by
  rw [meaning.firstHandle, meaning.secondMeaning.handleEq, meaning.thirdMeaning.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed factories methods receiver.issued
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    (support.terminals support.wordHeader.header support.toOrdinaryInventory.word_member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods receiver.issued (.refl _)
      support.wordHeader.header support.toOrdinaryInventory.word_member selected budget) wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_factory_meaning support sources bodies methods initial false sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.useWord_meaning support sources bodies methods second.after firstEntry
    (by simp) firstType firstHandle seed sequence.firstRead sequence.firstValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_factory_meaning support sources bodies methods firstRead.after
    (Core.Word.ofNatModulo 33) sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.useBool_meaning support sources bodies methods third.after second.entry
    (by simp) second.entryType second.handleEq false sequence.secondRead sequence.secondValue useBoolStages
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.useWord_meaning support sources bodies methods secondRead.after firstEntry
    (by simp) firstType firstHandle seed sequence.repeatedRead sequence.repeatedValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.useWord_meaning support sources bodies methods repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 33) sequence.thirdRead sequence.thirdValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages useWordStages useBoolStages factories sources bodies methods sequence receiver⟩

end Tests.SourceCoreMethodClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodClosureSequenceForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (ready : session.ExportsReady) :
    ForwardAt (entries := entries) support.toOrdinaryInventory receiver scalar call meaning.after.heap := by
  apply forward_call before scalar call meaning.request meaning.inputs meaning.registry meaning.rawType meaning.nativeType ready
    (support.terminals meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

theorem FactoryMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFunctionCall session key publicArguments} {resultType : TypeSystem.Ty}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : FactoryMeaning before header call resultType arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (ready : session.ExportsReady) :
    FactoryForwardAt (entries := entries) support.toOrdinaryInventory receiver call resultType meaning.entry.source meaning.after.heap := by
  apply forward_factory before call meaning.request meaning.inputs simple meaning.rawType ready
    (support.terminals meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support.toOrdinaryInventory receiver sequence.first meaning.firstEntry.source meaning.initial.heap
  second : FactoryForwardAt (entries := [meaning.firstEntry]) meaning.support.toOrdinaryInventory receiver sequence.second .bool
    meaning.secondMeaning.entry.source meaning.secondMeaning.after.heap
  firstRead : ForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word seed) sequence.firstRead meaning.firstReadMeaning.after.heap
  third : FactoryForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry]) meaning.support.toOrdinaryInventory receiver
    sequence.third .word meaning.thirdMeaning.entry.source meaning.thirdMeaning.after.heap
  secondRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.bool false) sequence.secondRead meaning.secondReadMeaning.after.heap
  repeatedRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word seed) sequence.repeatedRead meaning.repeatedReadMeaning.after.heap
  thirdRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.thirdRead meaning.thirdReadMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨forward_initial meaning.support.toOrdinaryInventory meaning.support.distinct sequence.first
      (meaning.support.terminals meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member)
      (fun budget {child} selected => preserves_bodies receiver meaning.support sources bodies methods receiver.issued (.refl _)
        meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member selected budget)
      meaning.firstTrace,
    meaning.secondMeaning.forward sources bodies methods (bool_simple false) firstReady,
    meaning.firstReadMeaning.forward sources bodies methods secondReady,
    meaning.thirdMeaning.forward sources bodies methods (word_simple (Core.Word.ofNatModulo 33)) firstReadReady,
    meaning.secondReadMeaning.forward sources bodies methods thirdReady,
    meaning.repeatedReadMeaning.forward sources bodies methods secondReadReady,
    meaning.thirdReadMeaning.forward sources bodies methods repeatedReady⟩

theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  exact ⟨receiver, meaning, meaning.forward sources bodies methods⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let factories ← observeFactories fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let ⟨sources⟩ ← observeClosureSources fixture observed
  let ⟨bodies⟩ ← observeMethodBodies fixture
  let ⟨methods⟩ ← observeMethodCatalog fixture
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [9,18,27,36,45,54,63,72] do
    throw (IO.userError s!"method closure stores changed: {reprStr stores}")
  IO.println "METHOD_CLOSURE_FORWARD_PASS: seven Source calls; all seven sufficient public fuel bounds; three retained closures; scalar11/false/11/33"

end Tests.SourceCoreMethodClosure
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodDirectEvidenceFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodDirectEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (receiver : ObservedReceiver fixture observed)
  (support : StaticSupportPackage fixture observed receiver.completion)
  (sources : ObservedClosureSources fixture observed)
  (bodies : MethodBodies fixture)
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "initialFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
local notation "functions" => support.toOrdinaryInventory.functions receiver

include receiver support bodies in
theorem StaticSupportPackage.method_supports :
    CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.MixedMethodSupports
      (compiled := fixture.recipe.compiled) (headers := headers support.toOrdinaryInventory.rows)
      (stages := actualRegistry) (semanticFaults := initialFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  exact bodies.support observed port.principal port.sourceAt ⟨port.diagnostics⟩ receiver.issued
    support.toOrdinaryInventory actualRegistry

include support in
private theorem owners_physical : ∀ selected : CallableIndexedOwnedFunctionValues.OwnedKey (keys fixture.recipe.compiled),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical selected.key (headers support.toOrdinaryInventory.rows) := by
  intro selected
  have same : selected = CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled := by
    cases selected with
    | mk position =>
      have samePosition : position = (CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled).position := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < 1 at bound
        change position.val = 0
        omega
      cases samePosition
      rfl
  rw [same]
  exact CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry)

include receiver extension in
private theorem static_extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.recipe.compiled.compatible.checked).registry
    receiving.result.context.registry := by
  change SourceCoreRawMetadata.Extends fixture.recipe.compiled.compatible.checked.staticRegistry _
  rw [← receiver.registry]
  exact extension

include receiver support issued extension in
private theorem semantic_extension : ∀ reason token, initialFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
  obtain ⟨program, present, _⟩ := support.wordHeader.diagnostic.actual
  intro reason token represented
  exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
    receiver.issued issued present extension represented

include receiver support sources bodies methods issued extension in
/-- Both body families are derived at the real reached metadata registry. -/
theorem preserves_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.preserves_with_methods issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.bodies support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) header member selected budget

include receiver support sources bodies methods issued extension in
theorem reflects_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.reflects_with_methods issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.bodies support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) rfl header member selected budget

end Tests.SourceCoreMethodDirectEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodDirectEvidencePublicExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodDirectEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  registry : request.encodedValues.registry = before.receiving.result.context.registry
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session entries
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value scalar.source) after.heap

structure FactoryMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (resultType : TypeSystem.Ty) (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session (entries ++ [entry])
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value entry.source) after.heap

theorem RetainedState.word_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Core.Word) (flag : Bool)
    (call : ObservedFunctionCall session observed.wordRow.row.key [.word value, .word next, .bool flag])
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.wordHeader.header call .word [.word value, .word next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_inputs value next flag
  have raw : request.header.function.resultType = closureType .word := by
    rw [selected, support.wordHeader.word_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.wordHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (word_simple value next flag) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.bool_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Bool) (flag : Bool)
    (call : ObservedFunctionCall session observed.boolRow.row.key [.bool value, .bool next, .bool flag])
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.boolHeader.header call .bool [.bool value, .bool next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_inputs value next flag
  have raw : request.header.function.resultType = closureType .bool := by
    rw [selected, support.boolHeader.bool_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.boolHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (bool_simple value next flag) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useWord_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useWordRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useWordHeader.header (.word value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useWordHeader.header :=
    selected_useWord_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useWordHeader.useWord_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [selected, support.useWordHeader.useWord_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [selected, support.useWordHeader.useWord_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useWordHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.word value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useBool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .bool)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Bool) (call : ObservedCall session observed.useBoolRow.row.key [.function handle])
    (returned : call.completion.value = .bool value)
    (stages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useBoolHeader.header (.bool value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useBoolHeader.header :=
    selected_useBool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useBoolHeader.useBool_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.bool value : ScalarOutput).sourceType := by
    rw [selected, support.useBoolHeader.useBool_result_type]; rfl
  have native : request.header.output = (.bool value : ScalarOutput).nativeType := by
    rw [selected, support.useBoolHeader.useBool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useBoolHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.bool value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  firstEntry : Entry
  firstType : firstEntry.sourceType = closureType .word
  firstHandle : firstEntry.handle = sequence.first.handle
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session [firstEntry]
  firstTrace : SourceCall support.toOrdinaryInventory support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value firstEntry.source) initial.heap
  secondMeaning : FactoryMeaning initial support.boolHeader.header sequence.second .bool [.bool false, .bool true, .bool true]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  firstReadMeaning : CallMeaning secondMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.firstRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdMeaning : FactoryMeaning firstReadMeaning.after support.wordHeader.header sequence.third .word [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  secondReadMeaning : CallMeaning thirdMeaning.after support.useBoolHeader.header (.bool true) sequence.secondRead [secondMeaning.entry.source]
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  repeatedReadMeaning : CallMeaning secondReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdReadMeaning : CallMeaning repeatedReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead [thirdMeaning.entry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)

theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) :
    meaning.firstEntry.handle ≠ meaning.secondMeaning.entry.handle ∧
      meaning.firstEntry.handle ≠ meaning.thirdMeaning.entry.handle ∧
      meaning.secondMeaning.entry.handle ≠ meaning.thirdMeaning.entry.handle := by
  rw [meaning.firstHandle, meaning.secondMeaning.handleEq, meaning.thirdMeaning.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed factories methods receiver.issued
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    (support.bodies support.wordHeader.header support.toOrdinaryInventory.word_member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods receiver.issued (.refl _)
      support.wordHeader.header support.toOrdinaryInventory.word_member selected budget) wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_factory_meaning support sources bodies methods initial false true true sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.useWord_meaning support sources bodies methods second.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.firstRead sequence.firstValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_factory_meaning support sources bodies methods firstRead.after
    (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.useBool_meaning support sources bodies methods third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.useWord_meaning support sources bodies methods secondRead.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.repeatedRead sequence.repeatedValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.useWord_meaning support sources bodies methods repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55) sequence.thirdRead sequence.thirdValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages useWordStages useBoolStages factories sources bodies methods sequence receiver⟩

end Tests.SourceCoreMethodDirectEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodDirectEvidenceSequenceForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodDirectEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (ready : session.ExportsReady) :
    ForwardAt (entries := entries) support.toOrdinaryInventory receiver scalar call meaning.after.heap := by
  apply forward_call before scalar call meaning.request meaning.inputs meaning.registry meaning.rawType meaning.nativeType ready
    (support.bodies meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

theorem FactoryMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFunctionCall session key publicArguments} {resultType : TypeSystem.Ty}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : FactoryMeaning before header call resultType arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (ready : session.ExportsReady) :
    FactoryForwardAt (entries := entries) support.toOrdinaryInventory receiver call resultType meaning.entry.source meaning.after.heap := by
  apply forward_factory before call meaning.request meaning.inputs simple meaning.rawType ready
    (support.bodies meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support.toOrdinaryInventory receiver sequence.first meaning.firstEntry.source meaning.initial.heap
  second : FactoryForwardAt (entries := [meaning.firstEntry]) meaning.support.toOrdinaryInventory receiver sequence.second .bool
    meaning.secondMeaning.entry.source meaning.secondMeaning.after.heap
  firstRead : ForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.firstRead meaning.firstReadMeaning.after.heap
  third : FactoryForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry]) meaning.support.toOrdinaryInventory receiver
    sequence.third .word meaning.thirdMeaning.entry.source meaning.thirdMeaning.after.heap
  secondRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.bool true) sequence.secondRead meaning.secondReadMeaning.after.heap
  repeatedRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead meaning.repeatedReadMeaning.after.heap
  thirdRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead meaning.thirdReadMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨forward_initial meaning.support.toOrdinaryInventory meaning.support.distinct sequence.first
      (meaning.support.bodies meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member)
      (fun budget {child} selected => preserves_bodies receiver meaning.support sources bodies methods receiver.issued (.refl _)
        meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member selected budget)
      meaning.firstTrace,
    meaning.secondMeaning.forward sources bodies methods (bool_simple false true true) firstReady,
    meaning.firstReadMeaning.forward sources bodies methods secondReady,
    meaning.thirdMeaning.forward sources bodies methods (word_simple (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false) firstReadReady,
    meaning.secondReadMeaning.forward sources bodies methods thirdReady,
    meaning.repeatedReadMeaning.forward sources bodies methods secondReadReady,
    meaning.thirdReadMeaning.forward sources bodies methods repeatedReady⟩

theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  exact ⟨receiver, meaning, meaning.forward sources bodies methods⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let factories ← observeFactories fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let ⟨sources⟩ ← observeClosureSources fixture observed
  let ⟨bodies⟩ ← observeMethodBodies fixture
  let ⟨methods⟩ ← observeMethodCatalog fixture
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,40,67,149,176,258,340,403] do
    throw (IO.userError s!"method scoped stores changed: {reprStr stores}")
  IO.println "METHOD_DIRECT_EVIDENCE_FORWARD_PASS: seven Source calls; all seven sufficient public fuel bounds; three retained closures; scalar33/true/33/55; constrained named relay and implementation method direct calls with actual Mark evidence"

end Tests.SourceCoreMethodDirectEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodGenericSubstitutionFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodGenericSubstitution
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (receiver : ObservedReceiver fixture observed)
  (support : StaticSupportPackage fixture observed receiver.completion)
  (sources : ObservedClosureSources fixture observed)
  (bodies : MethodBodies fixture)
  (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "initialFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
local notation "functions" => support.toOrdinaryInventory.functions receiver

include receiver support bodies in
theorem StaticSupportPackage.method_supports :
    CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.MixedMethodSupports
      (compiled := fixture.recipe.compiled) (headers := headers support.toOrdinaryInventory.rows)
      (stages := actualRegistry) (semanticFaults := initialFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  exact bodies.support observed port.principal port.sourceAt ⟨port.diagnostics⟩ receiver.issued
    support.toOrdinaryInventory actualRegistry

include support in
private theorem owners_physical : ∀ selected : CallableIndexedOwnedFunctionValues.OwnedKey (keys fixture.recipe.compiled),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical selected.key (headers support.toOrdinaryInventory.rows) := by
  intro selected
  have same : selected = CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled := by
    cases selected with
    | mk position =>
      have samePosition : position = (CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled).position := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < 1 at bound
        change position.val = 0
        omega
      cases samePosition
      rfl
  rw [same]
  exact CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry)

include receiver extension in
private theorem static_extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.recipe.compiled.compatible.checked).registry
    receiving.result.context.registry := by
  change SourceCoreRawMetadata.Extends fixture.recipe.compiled.compatible.checked.staticRegistry _
  rw [← receiver.registry]
  exact extension

include receiver support issued extension in
private theorem semantic_extension : ∀ reason token, initialFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
  obtain ⟨program, present, _⟩ := support.wordHeader.diagnostic.actual
  intro reason token represented
  exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
    receiver.issued issued present extension represented

include receiver support sources bodies methods issued extension in
/-- Both body families are derived at the real reached metadata registry. -/
theorem preserves_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.preserves_with_methods issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.bodies support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) header member selected budget

include receiver support sources bodies methods issued extension in
theorem reflects_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.reflects_with_methods issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.bodies support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) rfl header member selected budget

end Tests.SourceCoreMethodGenericSubstitution
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodGenericSubstitutionPublicExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodGenericSubstitution
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  registry : request.encodedValues.registry = before.receiving.result.context.registry
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session entries
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value scalar.source) after.heap

structure FactoryMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (resultType : TypeSystem.Ty) (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session (entries ++ [entry])
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value entry.source) after.heap

theorem RetainedState.word_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Core.Word) (flag : Bool)
    (call : ObservedFunctionCall session observed.wordRow.row.key [.word value, .word next, .bool flag])
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.wordHeader.header call .word [.word value, .word next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_inputs value next flag
  have raw : request.header.function.resultType = closureType .word := by
    rw [selected, support.wordHeader.word_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.wordHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (word_simple value next flag) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.bool_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Bool) (flag : Bool)
    (call : ObservedFunctionCall session observed.boolRow.row.key [.bool value, .bool next, .bool flag])
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.boolHeader.header call .bool [.bool value, .bool next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_inputs value next flag
  have raw : request.header.function.resultType = closureType .bool := by
    rw [selected, support.boolHeader.bool_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.boolHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (bool_simple value next flag) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useWord_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useWordRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useWordHeader.header (.word value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useWordHeader.header :=
    selected_useWord_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useWordHeader.useWord_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [selected, support.useWordHeader.useWord_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [selected, support.useWordHeader.useWord_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useWordHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.word value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useBool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .bool)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Bool) (call : ObservedCall session observed.useBoolRow.row.key [.function handle])
    (returned : call.completion.value = .bool value)
    (stages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useBoolHeader.header (.bool value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useBoolHeader.header :=
    selected_useBool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useBoolHeader.useBool_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.bool value : ScalarOutput).sourceType := by
    rw [selected, support.useBoolHeader.useBool_result_type]; rfl
  have native : request.header.output = (.bool value : ScalarOutput).nativeType := by
    rw [selected, support.useBoolHeader.useBool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useBoolHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.bool value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  firstEntry : Entry
  firstType : firstEntry.sourceType = closureType .word
  firstHandle : firstEntry.handle = sequence.first.handle
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session [firstEntry]
  firstTrace : SourceCall support.toOrdinaryInventory support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value firstEntry.source) initial.heap
  secondMeaning : FactoryMeaning initial support.boolHeader.header sequence.second .bool [.bool false, .bool true, .bool true]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  firstReadMeaning : CallMeaning secondMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.firstRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdMeaning : FactoryMeaning firstReadMeaning.after support.wordHeader.header sequence.third .word [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  secondReadMeaning : CallMeaning thirdMeaning.after support.useBoolHeader.header (.bool true) sequence.secondRead [secondMeaning.entry.source]
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  repeatedReadMeaning : CallMeaning secondReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdReadMeaning : CallMeaning repeatedReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead [thirdMeaning.entry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)

theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) :
    meaning.firstEntry.handle ≠ meaning.secondMeaning.entry.handle ∧
      meaning.firstEntry.handle ≠ meaning.thirdMeaning.entry.handle ∧
      meaning.secondMeaning.entry.handle ≠ meaning.thirdMeaning.entry.handle := by
  rw [meaning.firstHandle, meaning.secondMeaning.handleEq, meaning.thirdMeaning.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed factories methods receiver.issued
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    (support.bodies support.wordHeader.header support.toOrdinaryInventory.word_member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods receiver.issued (.refl _)
      support.wordHeader.header support.toOrdinaryInventory.word_member selected budget) wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_factory_meaning support sources bodies methods initial false true true sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.useWord_meaning support sources bodies methods second.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.firstRead sequence.firstValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_factory_meaning support sources bodies methods firstRead.after
    (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.useBool_meaning support sources bodies methods third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.useWord_meaning support sources bodies methods secondRead.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.repeatedRead sequence.repeatedValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.useWord_meaning support sources bodies methods repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55) sequence.thirdRead sequence.thirdValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages useWordStages useBoolStages factories sources bodies methods sequence receiver⟩

end Tests.SourceCoreMethodGenericSubstitution
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodGenericSubstitutionSequenceForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodGenericSubstitution
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (ready : session.ExportsReady) :
    ForwardAt (entries := entries) support.toOrdinaryInventory receiver scalar call meaning.after.heap := by
  apply forward_call before scalar call meaning.request meaning.inputs meaning.registry meaning.rawType meaning.nativeType ready
    (support.bodies meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

theorem FactoryMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFunctionCall session key publicArguments} {resultType : TypeSystem.Ty}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : FactoryMeaning before header call resultType arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (ready : session.ExportsReady) :
    FactoryForwardAt (entries := entries) support.toOrdinaryInventory receiver call resultType meaning.entry.source meaning.after.heap := by
  apply forward_factory before call meaning.request meaning.inputs simple meaning.rawType ready
    (support.bodies meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support.toOrdinaryInventory receiver sequence.first meaning.firstEntry.source meaning.initial.heap
  second : FactoryForwardAt (entries := [meaning.firstEntry]) meaning.support.toOrdinaryInventory receiver sequence.second .bool
    meaning.secondMeaning.entry.source meaning.secondMeaning.after.heap
  firstRead : ForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.firstRead meaning.firstReadMeaning.after.heap
  third : FactoryForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry]) meaning.support.toOrdinaryInventory receiver
    sequence.third .word meaning.thirdMeaning.entry.source meaning.thirdMeaning.after.heap
  secondRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.bool true) sequence.secondRead meaning.secondReadMeaning.after.heap
  repeatedRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead meaning.repeatedReadMeaning.after.heap
  thirdRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead meaning.thirdReadMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨forward_initial meaning.support.toOrdinaryInventory meaning.support.distinct sequence.first
      (meaning.support.bodies meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member)
      (fun budget {child} selected => preserves_bodies receiver meaning.support sources bodies methods receiver.issued (.refl _)
        meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member selected budget)
      meaning.firstTrace,
    meaning.secondMeaning.forward sources bodies methods (bool_simple false true true) firstReady,
    meaning.firstReadMeaning.forward sources bodies methods secondReady,
    meaning.thirdMeaning.forward sources bodies methods (word_simple (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false) firstReadReady,
    meaning.secondReadMeaning.forward sources bodies methods thirdReady,
    meaning.repeatedReadMeaning.forward sources bodies methods secondReadReady,
    meaning.thirdReadMeaning.forward sources bodies methods repeatedReady⟩

theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  exact ⟨receiver, meaning, meaning.forward sources bodies methods⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let factories ← observeFactories fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let ⟨sources⟩ ← observeClosureSources fixture observed
  let ⟨bodies⟩ ← observeMethodBodies fixture
  let ⟨methods⟩ ← observeMethodCatalog fixture
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,40,67,149,176,258,340,403] do
    throw (IO.userError s!"method scoped stores changed: {reprStr stores}")
  IO.println "METHOD_GENERIC_SUBSTITUTION_FORWARD_PASS: seven Source calls; all seven sufficient public fuel bounds; three retained closures; scalar33/true/33/55; generic implementation substitutions and direct calls with actual Mark evidence"

end Tests.SourceCoreMethodGenericSubstitution
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodImplementationScopedFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodImplementationScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (receiver : ObservedReceiver fixture observed)
  (support : StaticSupportPackage fixture observed receiver.completion)
  (sources : ObservedClosureSources fixture observed)
  (bodies : MethodBodies fixture)
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "initialFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
local notation "functions" => support.toOrdinaryInventory.functions receiver

include receiver support bodies in
theorem StaticSupportPackage.method_supports :
    CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.MixedMethodSupports
      (compiled := fixture.recipe.compiled) (headers := headers support.toOrdinaryInventory.rows)
      (stages := actualRegistry) (semanticFaults := initialFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  exact bodies.support observed port.principal port.sourceAt ⟨port.diagnostics⟩ receiver.issued
    (headers support.toOrdinaryInventory.rows) actualRegistry

include support in
private theorem owners_physical : ∀ selected : CallableIndexedOwnedFunctionValues.OwnedKey (keys fixture.recipe.compiled),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical selected.key (headers support.toOrdinaryInventory.rows) := by
  intro selected
  have same : selected = CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled := by
    cases selected with
    | mk position =>
      have samePosition : position = (CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled).position := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < 1 at bound
        change position.val = 0
        omega
      cases samePosition
      rfl
  rw [same]
  exact CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry)

include receiver extension in
private theorem static_extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.recipe.compiled.compatible.checked).registry
    receiving.result.context.registry := by
  change SourceCoreRawMetadata.Extends fixture.recipe.compiled.compatible.checked.staticRegistry _
  rw [← receiver.registry]
  exact extension

include receiver support issued extension in
private theorem semantic_extension : ∀ reason token, initialFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
  obtain ⟨program, present, _⟩ := support.wordHeader.diagnostic.actual
  intro reason token represented
  exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
    receiver.issued issued present extension represented

include receiver support sources bodies methods issued extension in
/-- Both body families are derived at the real reached metadata registry. -/
theorem preserves_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.preserves_with_methods issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.bodies support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) header member selected budget

include receiver support sources bodies methods issued extension in
theorem reflects_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.reflects_with_methods issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.bodies support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) rfl header member selected budget

end Tests.SourceCoreMethodImplementationScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodImplementationScopedPublicExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodImplementationScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  registry : request.encodedValues.registry = before.receiving.result.context.registry
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session entries
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value scalar.source) after.heap

structure FactoryMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (resultType : TypeSystem.Ty) (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session (entries ++ [entry])
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value entry.source) after.heap

theorem RetainedState.word_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Core.Word) (flag : Bool)
    (call : ObservedFunctionCall session observed.wordRow.row.key [.word value, .word next, .bool flag])
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.wordHeader.header call .word [.word value, .word next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_inputs value next flag
  have raw : request.header.function.resultType = closureType .word := by
    rw [selected, support.wordHeader.word_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.wordHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (word_simple value next flag) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.bool_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Bool) (flag : Bool)
    (call : ObservedFunctionCall session observed.boolRow.row.key [.bool value, .bool next, .bool flag])
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.boolHeader.header call .bool [.bool value, .bool next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_inputs value next flag
  have raw : request.header.function.resultType = closureType .bool := by
    rw [selected, support.boolHeader.bool_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.boolHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (bool_simple value next flag) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useWord_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useWordRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useWordHeader.header (.word value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useWordHeader.header :=
    selected_useWord_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useWordHeader.useWord_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [selected, support.useWordHeader.useWord_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [selected, support.useWordHeader.useWord_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useWordHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.word value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useBool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .bool)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Bool) (call : ObservedCall session observed.useBoolRow.row.key [.function handle])
    (returned : call.completion.value = .bool value)
    (stages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useBoolHeader.header (.bool value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useBoolHeader.header :=
    selected_useBool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useBoolHeader.useBool_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.bool value : ScalarOutput).sourceType := by
    rw [selected, support.useBoolHeader.useBool_result_type]; rfl
  have native : request.header.output = (.bool value : ScalarOutput).nativeType := by
    rw [selected, support.useBoolHeader.useBool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useBoolHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.bool value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  firstEntry : Entry
  firstType : firstEntry.sourceType = closureType .word
  firstHandle : firstEntry.handle = sequence.first.handle
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session [firstEntry]
  firstTrace : SourceCall support.toOrdinaryInventory support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value firstEntry.source) initial.heap
  secondMeaning : FactoryMeaning initial support.boolHeader.header sequence.second .bool [.bool false, .bool true, .bool true]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  firstReadMeaning : CallMeaning secondMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.firstRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdMeaning : FactoryMeaning firstReadMeaning.after support.wordHeader.header sequence.third .word [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  secondReadMeaning : CallMeaning thirdMeaning.after support.useBoolHeader.header (.bool true) sequence.secondRead [secondMeaning.entry.source]
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  repeatedReadMeaning : CallMeaning secondReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdReadMeaning : CallMeaning repeatedReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead [thirdMeaning.entry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)

theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) :
    meaning.firstEntry.handle ≠ meaning.secondMeaning.entry.handle ∧
      meaning.firstEntry.handle ≠ meaning.thirdMeaning.entry.handle ∧
      meaning.secondMeaning.entry.handle ≠ meaning.thirdMeaning.entry.handle := by
  rw [meaning.firstHandle, meaning.secondMeaning.handleEq, meaning.thirdMeaning.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed factories methods receiver.issued
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    (support.bodies support.wordHeader.header support.toOrdinaryInventory.word_member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods receiver.issued (.refl _)
      support.wordHeader.header support.toOrdinaryInventory.word_member selected budget) wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_factory_meaning support sources bodies methods initial false true true sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.useWord_meaning support sources bodies methods second.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.firstRead sequence.firstValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_factory_meaning support sources bodies methods firstRead.after
    (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.useBool_meaning support sources bodies methods third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.useWord_meaning support sources bodies methods secondRead.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.repeatedRead sequence.repeatedValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.useWord_meaning support sources bodies methods repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55) sequence.thirdRead sequence.thirdValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages useWordStages useBoolStages factories sources bodies methods sequence receiver⟩

end Tests.SourceCoreMethodImplementationScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodImplementationScopedSequenceForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodImplementationScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (ready : session.ExportsReady) :
    ForwardAt (entries := entries) support.toOrdinaryInventory receiver scalar call meaning.after.heap := by
  apply forward_call before scalar call meaning.request meaning.inputs meaning.registry meaning.rawType meaning.nativeType ready
    (support.bodies meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

theorem FactoryMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFunctionCall session key publicArguments} {resultType : TypeSystem.Ty}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : FactoryMeaning before header call resultType arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (ready : session.ExportsReady) :
    FactoryForwardAt (entries := entries) support.toOrdinaryInventory receiver call resultType meaning.entry.source meaning.after.heap := by
  apply forward_factory before call meaning.request meaning.inputs simple meaning.rawType ready
    (support.bodies meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support.toOrdinaryInventory receiver sequence.first meaning.firstEntry.source meaning.initial.heap
  second : FactoryForwardAt (entries := [meaning.firstEntry]) meaning.support.toOrdinaryInventory receiver sequence.second .bool
    meaning.secondMeaning.entry.source meaning.secondMeaning.after.heap
  firstRead : ForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.firstRead meaning.firstReadMeaning.after.heap
  third : FactoryForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry]) meaning.support.toOrdinaryInventory receiver
    sequence.third .word meaning.thirdMeaning.entry.source meaning.thirdMeaning.after.heap
  secondRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.bool true) sequence.secondRead meaning.secondReadMeaning.after.heap
  repeatedRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead meaning.repeatedReadMeaning.after.heap
  thirdRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead meaning.thirdReadMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨forward_initial meaning.support.toOrdinaryInventory meaning.support.distinct sequence.first
      (meaning.support.bodies meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member)
      (fun budget {child} selected => preserves_bodies receiver meaning.support sources bodies methods receiver.issued (.refl _)
        meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member selected budget)
      meaning.firstTrace,
    meaning.secondMeaning.forward sources bodies methods (bool_simple false true true) firstReady,
    meaning.firstReadMeaning.forward sources bodies methods secondReady,
    meaning.thirdMeaning.forward sources bodies methods (word_simple (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false) firstReadReady,
    meaning.secondReadMeaning.forward sources bodies methods thirdReady,
    meaning.repeatedReadMeaning.forward sources bodies methods secondReadReady,
    meaning.thirdReadMeaning.forward sources bodies methods repeatedReady⟩

theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  exact ⟨receiver, meaning, meaning.forward sources bodies methods⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let factories ← observeFactories fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let ⟨sources⟩ ← observeClosureSources fixture observed
  let ⟨bodies⟩ ← observeMethodBodies fixture
  let ⟨methods⟩ ← observeMethodCatalog fixture
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [11,38,65,120,147,202,257,302] do
    throw (IO.userError s!"method scoped stores changed: {reprStr stores}")
  IO.println "METHOD_IMPLEMENTATION_SCOPED_FORWARD_PASS: seven Source calls; all seven sufficient public fuel bounds; three retained closures; scalar33/true/33/55; constrained named relay and implementation method locals with loops"

end Tests.SourceCoreMethodImplementationScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodNamedScopedFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodNamedScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (receiver : ObservedReceiver fixture observed)
  (support : StaticSupportPackage fixture observed receiver.completion)
  (sources : ObservedClosureSources fixture observed)
  (bodies : MethodBodies fixture)
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "initialFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
local notation "functions" => support.toOrdinaryInventory.functions receiver

include receiver support bodies in
theorem StaticSupportPackage.method_supports :
    CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.MethodSupports
      (compiled := fixture.recipe.compiled) (headers := headers support.toOrdinaryInventory.rows)
      (stages := actualRegistry) (semanticFaults := initialFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  exact bodies.support observed port.principal port.sourceAt ⟨port.diagnostics⟩ receiver.issued
    (headers support.toOrdinaryInventory.rows) actualRegistry

include support in
private theorem owners_physical : ∀ selected : CallableIndexedOwnedFunctionValues.OwnedKey (keys fixture.recipe.compiled),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical selected.key (headers support.toOrdinaryInventory.rows) := by
  intro selected
  have same : selected = CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled := by
    cases selected with
    | mk position =>
      have samePosition : position = (CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled).position := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < 1 at bound
        change position.val = 0
        omega
      cases samePosition
      rfl
  rw [same]
  exact CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry)

include receiver extension in
private theorem static_extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.recipe.compiled.compatible.checked).registry
    receiving.result.context.registry := by
  change SourceCoreRawMetadata.Extends fixture.recipe.compiled.compatible.checked.staticRegistry _
  rw [← receiver.registry]
  exact extension

include receiver support issued extension in
private theorem semantic_extension : ∀ reason token, initialFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
  obtain ⟨program, present, _⟩ := support.wordHeader.diagnostic.actual
  intro reason token represented
  exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
    receiver.issued issued present extension represented

include receiver support sources bodies methods issued extension in
/-- Both body families are derived at the real reached metadata registry. -/
theorem preserves_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.preserves_with_bodies issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.bodies support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) header member selected budget

include receiver support sources bodies methods issued extension in
theorem reflects_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.reflects_with_bodies issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.bodies support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) rfl header member selected budget

end Tests.SourceCoreMethodNamedScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodNamedScopedPublicExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodNamedScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  registry : request.encodedValues.registry = before.receiving.result.context.registry
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session entries
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value scalar.source) after.heap

structure FactoryMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (resultType : TypeSystem.Ty) (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session (entries ++ [entry])
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value entry.source) after.heap

theorem RetainedState.word_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Core.Word) (flag : Bool)
    (call : ObservedFunctionCall session observed.wordRow.row.key [.word value, .word next, .bool flag])
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.wordHeader.header call .word [.word value, .word next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_inputs value next flag
  have raw : request.header.function.resultType = closureType .word := by
    rw [selected, support.wordHeader.word_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.wordHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (word_simple value next flag) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.bool_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Bool) (flag : Bool)
    (call : ObservedFunctionCall session observed.boolRow.row.key [.bool value, .bool next, .bool flag])
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.boolHeader.header call .bool [.bool value, .bool next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_inputs value next flag
  have raw : request.header.function.resultType = closureType .bool := by
    rw [selected, support.boolHeader.bool_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.boolHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (bool_simple value next flag) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useWord_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useWordRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useWordHeader.header (.word value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useWordHeader.header :=
    selected_useWord_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useWordHeader.useWord_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [selected, support.useWordHeader.useWord_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [selected, support.useWordHeader.useWord_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useWordHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.word value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useBool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .bool)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Bool) (call : ObservedCall session observed.useBoolRow.row.key [.function handle])
    (returned : call.completion.value = .bool value)
    (stages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useBoolHeader.header (.bool value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useBoolHeader.header :=
    selected_useBool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useBoolHeader.useBool_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.bool value : ScalarOutput).sourceType := by
    rw [selected, support.useBoolHeader.useBool_result_type]; rfl
  have native : request.header.output = (.bool value : ScalarOutput).nativeType := by
    rw [selected, support.useBoolHeader.useBool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useBoolHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.bool value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  firstEntry : Entry
  firstType : firstEntry.sourceType = closureType .word
  firstHandle : firstEntry.handle = sequence.first.handle
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session [firstEntry]
  firstTrace : SourceCall support.toOrdinaryInventory support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value firstEntry.source) initial.heap
  secondMeaning : FactoryMeaning initial support.boolHeader.header sequence.second .bool [.bool false, .bool true, .bool true]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  firstReadMeaning : CallMeaning secondMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.firstRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdMeaning : FactoryMeaning firstReadMeaning.after support.wordHeader.header sequence.third .word [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  secondReadMeaning : CallMeaning thirdMeaning.after support.useBoolHeader.header (.bool true) sequence.secondRead [secondMeaning.entry.source]
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  repeatedReadMeaning : CallMeaning secondReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdReadMeaning : CallMeaning repeatedReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead [thirdMeaning.entry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)

theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) :
    meaning.firstEntry.handle ≠ meaning.secondMeaning.entry.handle ∧
      meaning.firstEntry.handle ≠ meaning.thirdMeaning.entry.handle ∧
      meaning.secondMeaning.entry.handle ≠ meaning.thirdMeaning.entry.handle := by
  rw [meaning.firstHandle, meaning.secondMeaning.handleEq, meaning.thirdMeaning.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed factories methods receiver.issued
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    (support.bodies support.wordHeader.header support.toOrdinaryInventory.word_member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods receiver.issued (.refl _)
      support.wordHeader.header support.toOrdinaryInventory.word_member selected budget) wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_factory_meaning support sources bodies methods initial false true true sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.useWord_meaning support sources bodies methods second.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.firstRead sequence.firstValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_factory_meaning support sources bodies methods firstRead.after
    (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.useBool_meaning support sources bodies methods third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.useWord_meaning support sources bodies methods secondRead.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.repeatedRead sequence.repeatedValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.useWord_meaning support sources bodies methods repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55) sequence.thirdRead sequence.thirdValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages useWordStages useBoolStages factories sources bodies methods sequence receiver⟩

end Tests.SourceCoreMethodNamedScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodNamedScopedSequenceForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodNamedScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (ready : session.ExportsReady) :
    ForwardAt (entries := entries) support.toOrdinaryInventory receiver scalar call meaning.after.heap := by
  apply forward_call before scalar call meaning.request meaning.inputs meaning.registry meaning.rawType meaning.nativeType ready
    (support.bodies meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

theorem FactoryMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFunctionCall session key publicArguments} {resultType : TypeSystem.Ty}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : FactoryMeaning before header call resultType arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (ready : session.ExportsReady) :
    FactoryForwardAt (entries := entries) support.toOrdinaryInventory receiver call resultType meaning.entry.source meaning.after.heap := by
  apply forward_factory before call meaning.request meaning.inputs simple meaning.rawType ready
    (support.bodies meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support.toOrdinaryInventory receiver sequence.first meaning.firstEntry.source meaning.initial.heap
  second : FactoryForwardAt (entries := [meaning.firstEntry]) meaning.support.toOrdinaryInventory receiver sequence.second .bool
    meaning.secondMeaning.entry.source meaning.secondMeaning.after.heap
  firstRead : ForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.firstRead meaning.firstReadMeaning.after.heap
  third : FactoryForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry]) meaning.support.toOrdinaryInventory receiver
    sequence.third .word meaning.thirdMeaning.entry.source meaning.thirdMeaning.after.heap
  secondRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.bool true) sequence.secondRead meaning.secondReadMeaning.after.heap
  repeatedRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead meaning.repeatedReadMeaning.after.heap
  thirdRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead meaning.thirdReadMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨forward_initial meaning.support.toOrdinaryInventory meaning.support.distinct sequence.first
      (meaning.support.bodies meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member)
      (fun budget {child} selected => preserves_bodies receiver meaning.support sources bodies methods receiver.issued (.refl _)
        meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member selected budget)
      meaning.firstTrace,
    meaning.secondMeaning.forward sources bodies methods (bool_simple false true true) firstReady,
    meaning.firstReadMeaning.forward sources bodies methods secondReady,
    meaning.thirdMeaning.forward sources bodies methods (word_simple (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false) firstReadReady,
    meaning.secondReadMeaning.forward sources bodies methods thirdReady,
    meaning.repeatedReadMeaning.forward sources bodies methods secondReadReady,
    meaning.thirdReadMeaning.forward sources bodies methods repeatedReady⟩

theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  exact ⟨receiver, meaning, meaning.forward sources bodies methods⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let factories ← observeFactories fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let ⟨sources⟩ ← observeClosureSources fixture observed
  let ⟨bodies⟩ ← observeMethodBodies fixture
  let ⟨methods⟩ ← observeMethodCatalog fixture
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [11,38,65,99,126,160,194,225] do
    throw (IO.userError s!"method scoped stores changed: {reprStr stores}")
  IO.println "METHOD_NAMED_SCOPED_FORWARD_PASS: seven Source calls; all seven sufficient public fuel bounds; three retained closures; scalar33/true/33/55; constrained named relay with local writes and true/false loops"

end Tests.SourceCoreMethodNamedScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOwnEvidenceFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOwnEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (receiver : ObservedReceiver fixture observed)
  (support : StaticSupportPackage fixture observed receiver.completion)
  (sources : ObservedClosureSources fixture observed)
  (bodies : MethodBodies fixture)
  (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog fixture.recipe.compiled)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "initialFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
local notation "functions" => support.toOrdinaryInventory.functions receiver

include receiver support bodies in
theorem StaticSupportPackage.method_supports :
    CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.MixedMethodSupports
      (compiled := fixture.recipe.compiled) (headers := headers support.toOrdinaryInventory.rows)
      (stages := actualRegistry) (semanticFaults := initialFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  exact bodies.support observed port.principal port.sourceAt port.resolved ⟨port.diagnostics⟩ receiver.issued
    support.toOrdinaryInventory actualRegistry

include support in
private theorem owners_physical : ∀ selected : CallableIndexedOwnedFunctionValues.OwnedKey (keys fixture.recipe.compiled),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical selected.key (headers support.toOrdinaryInventory.rows) := by
  intro selected
  have same : selected = CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled := by
    cases selected with
    | mk position =>
      have samePosition : position = (CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled).position := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < 1 at bound
        change position.val = 0
        omega
      cases samePosition
      rfl
  rw [same]
  exact CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry)

include receiver extension in
private theorem static_extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.recipe.compiled.compatible.checked).registry
    receiving.result.context.registry := by
  change SourceCoreRawMetadata.Extends fixture.recipe.compiled.compatible.checked.staticRegistry _
  rw [← receiver.registry]
  exact extension

include receiver support issued extension in
private theorem semantic_extension : ∀ reason token, initialFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
  obtain ⟨program, present, _⟩ := support.wordHeader.diagnostic.actual
  intro reason token represented
  exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
    receiver.issued issued present extension represented

include receiver support sources bodies methods issued extension in
/-- Both body families are derived at the real reached metadata registry. -/
theorem preserves_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.preserves_with_methods issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.bodies support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) header member selected budget

include receiver support sources bodies methods issued extension in
theorem reflects_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.reflects_with_methods issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.bodies support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) rfl header member selected budget

end Tests.SourceCoreMethodOwnEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOwnEvidencePublicExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOwnEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  registry : request.encodedValues.registry = before.receiving.result.context.registry
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session entries
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value scalar.source) after.heap

structure FactoryMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (resultType : TypeSystem.Ty) (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session (entries ++ [entry])
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value entry.source) after.heap

theorem RetainedState.word_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog fixture.recipe.compiled)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Core.Word) (flag : Bool)
    (call : ObservedFunctionCall session observed.wordRow.row.key [.word value, .word next, .bool flag])
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.wordHeader.header call .word [.word value, .word next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_inputs value next flag
  have raw : request.header.function.resultType = closureType .word := by
    rw [selected, support.wordHeader.word_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.wordHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (word_simple value next flag) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.bool_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog fixture.recipe.compiled)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Bool) (flag : Bool)
    (call : ObservedFunctionCall session observed.boolRow.row.key [.bool value, .bool next, .bool flag])
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.boolHeader.header call .bool [.bool value, .bool next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_inputs value next flag
  have raw : request.header.function.resultType = closureType .bool := by
    rw [selected, support.boolHeader.bool_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.boolHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (bool_simple value next flag) descriptor (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useWord_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog fixture.recipe.compiled)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useWordRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useWordHeader.header (.word value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useWordHeader.header :=
    selected_useWord_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useWordHeader.useWord_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [selected, support.useWordHeader.useWord_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [selected, support.useWordHeader.useWord_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useWordHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.word value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useBool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog fixture.recipe.compiled)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .bool)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Bool) (call : ObservedCall session observed.useBoolRow.row.key [.function handle])
    (returned : call.completion.value = .bool value)
    (stages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useBoolHeader.header (.bool value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.relayWordInput, support.relayBoolInput, support.useWordInput, support.useBoolInput, support.identityWordInput, support.identityBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useBoolHeader.header :=
    selected_useBool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.relayWordHeader support.relayBoolHeader support.useWordHeader support.useBoolHeader support.identityWordHeader support.identityBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useBoolHeader.useBool_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.bool value : ScalarOutput).sourceType := by
    rw [selected, support.useBoolHeader.useBool_result_type]; rfl
  have native : request.header.output = (.bool value : ScalarOutput).nativeType := by
    rw [selected, support.useBoolHeader.useBool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useBoolHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.bool value) call returned request inputs registry raw native descriptor
    (support.bodies request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  firstEntry : Entry
  firstType : firstEntry.sourceType = closureType .word
  firstHandle : firstEntry.handle = sequence.first.handle
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session [firstEntry]
  firstTrace : SourceCall support.toOrdinaryInventory support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value firstEntry.source) initial.heap
  secondMeaning : FactoryMeaning initial support.boolHeader.header sequence.second .bool [.bool false, .bool true, .bool true]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  firstReadMeaning : CallMeaning secondMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.firstRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdMeaning : FactoryMeaning firstReadMeaning.after support.wordHeader.header sequence.third .word [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  secondReadMeaning : CallMeaning thirdMeaning.after support.useBoolHeader.header (.bool true) sequence.secondRead [secondMeaning.entry.source]
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  repeatedReadMeaning : CallMeaning secondReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdReadMeaning : CallMeaning repeatedReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead [thirdMeaning.entry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)

theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) :
    meaning.firstEntry.handle ≠ meaning.secondMeaning.entry.handle ∧
      meaning.firstEntry.handle ≠ meaning.thirdMeaning.entry.handle ∧
      meaning.secondMeaning.entry.handle ≠ meaning.thirdMeaning.entry.handle := by
  rw [meaning.firstHandle, meaning.secondMeaning.handleEq, meaning.thirdMeaning.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog fixture.recipe.compiled)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed factories methods receiver.issued
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    (support.bodies support.wordHeader.header support.toOrdinaryInventory.word_member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods receiver.issued (.refl _)
      support.wordHeader.header support.toOrdinaryInventory.word_member selected budget) wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_factory_meaning support sources bodies methods initial false true true sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.useWord_meaning support sources bodies methods second.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.firstRead sequence.firstValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_factory_meaning support sources bodies methods firstRead.after
    (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.useBool_meaning support sources bodies methods third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.useWord_meaning support sources bodies methods secondRead.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.repeatedRead sequence.repeatedValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.useWord_meaning support sources bodies methods repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55) sequence.thirdRead sequence.thirdValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog fixture.recipe.compiled)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages useWordStages useBoolStages factories sources bodies methods sequence receiver⟩

end Tests.SourceCoreMethodOwnEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOwnEvidenceSequenceForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOwnEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog fixture.recipe.compiled)
    (ready : session.ExportsReady) :
    ForwardAt (entries := entries) support.toOrdinaryInventory receiver scalar call meaning.after.heap := by
  apply forward_call before scalar call meaning.request meaning.inputs meaning.registry meaning.rawType meaning.nativeType ready
    (support.bodies meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

theorem FactoryMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFunctionCall session key publicArguments} {resultType : TypeSystem.Ty}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : FactoryMeaning before header call resultType arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog fixture.recipe.compiled)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (ready : session.ExportsReady) :
    FactoryForwardAt (entries := entries) support.toOrdinaryInventory receiver call resultType meaning.entry.source meaning.after.heap := by
  apply forward_factory before call meaning.request meaning.inputs simple meaning.rawType ready
    (support.bodies meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support.toOrdinaryInventory receiver sequence.first meaning.firstEntry.source meaning.initial.heap
  second : FactoryForwardAt (entries := [meaning.firstEntry]) meaning.support.toOrdinaryInventory receiver sequence.second .bool
    meaning.secondMeaning.entry.source meaning.secondMeaning.after.heap
  firstRead : ForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.firstRead meaning.firstReadMeaning.after.heap
  third : FactoryForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry]) meaning.support.toOrdinaryInventory receiver
    sequence.third .word meaning.thirdMeaning.entry.source meaning.thirdMeaning.after.heap
  secondRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.bool true) sequence.secondRead meaning.secondReadMeaning.after.heap
  repeatedRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead meaning.repeatedReadMeaning.after.heap
  thirdRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead meaning.thirdReadMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog fixture.recipe.compiled) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨forward_initial meaning.support.toOrdinaryInventory meaning.support.distinct sequence.first
      (meaning.support.bodies meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member)
      (fun budget {child} selected => preserves_bodies receiver meaning.support sources bodies methods receiver.issued (.refl _)
        meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member selected budget)
      meaning.firstTrace,
    meaning.secondMeaning.forward sources bodies methods (bool_simple false true true) firstReady,
    meaning.firstReadMeaning.forward sources bodies methods secondReady,
    meaning.thirdMeaning.forward sources bodies methods (word_simple (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false) firstReadReady,
    meaning.secondReadMeaning.forward sources bodies methods thirdReady,
    meaning.repeatedReadMeaning.forward sources bodies methods secondReadReady,
    meaning.thirdReadMeaning.forward sources bodies methods repeatedReady⟩

theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog fixture.recipe.compiled)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  exact ⟨receiver, meaning, meaning.forward sources bodies methods⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let factories ← observeFactories fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let ⟨sources⟩ ← observeClosureSources fixture observed
  let ⟨bodies⟩ ← observeMethodBodies fixture
  let ⟨methods⟩ ← observeMethodCatalog fixture
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,40,67,149,176,258,340,403] do
    throw (IO.userError s!"method scoped stores changed: {reprStr stores}")
  IO.println "METHOD_OWN_EVIDENCE_FORWARD_PASS: seven Source calls; all seven sufficient public fuel bounds; three retained closures; scalar33/true/33/55; generic implementation substitutions, own method Mark dictionaries, and constrained direct calls"

end Tests.SourceCoreMethodOwnEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (receiver : ObservedReceiver fixture observed)
  (support : StaticSupportPackage fixture observed receiver.completion)
  (sources : ObservedClosureSources fixture observed)
  (bodies : MethodBodies fixture)
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "initialFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
local notation "functions" => support.toOrdinaryInventory.functions receiver

include receiver support bodies in
theorem StaticSupportPackage.method_supports :
    CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.MethodSupports
      (compiled := fixture.recipe.compiled) (headers := headers support.toOrdinaryInventory.rows)
      (stages := actualRegistry) (semanticFaults := initialFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  exact bodies.support observed port.principal port.sourceAt ⟨port.diagnostics⟩ receiver.issued
    (headers support.toOrdinaryInventory.rows) actualRegistry

include support in
private theorem owners_physical : ∀ selected : CallableIndexedOwnedFunctionValues.OwnedKey (keys fixture.recipe.compiled),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical selected.key (headers support.toOrdinaryInventory.rows) := by
  intro selected
  have same : selected = CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled := by
    cases selected with
    | mk position =>
      have samePosition : position = (CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled).position := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < 1 at bound
        change position.val = 0
        omega
      cases samePosition
      rfl
  rw [same]
  exact CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry)

include receiver extension in
private theorem static_extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.recipe.compiled.compatible.checked).registry
    receiving.result.context.registry := by
  change SourceCoreRawMetadata.Extends fixture.recipe.compiled.compatible.checked.staticRegistry _
  rw [← receiver.registry]
  exact extension

include receiver support issued extension in
private theorem semantic_extension : ∀ reason token, initialFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
  obtain ⟨program, present, _⟩ := support.wordHeader.diagnostic.actual
  intro reason token represented
  exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
    receiver.issued issued present extension represented

include receiver support sources bodies methods issued extension in
/-- Both body families are derived at the real reached metadata registry. -/
theorem preserves_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory.rows
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.preserves issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.terminals support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) header member selected budget

include receiver support sources bodies methods issued extension in
theorem reflects_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory.rows
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.reflects issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.terminals support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) rfl header member selected budget

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedPublicExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  registry : request.encodedValues.registry = before.receiving.result.context.registry
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session entries
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value scalar.source) after.heap

structure FactoryMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (before : RetainedState support.toOrdinaryInventory receiver session entries)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key publicArguments)
    (resultType : TypeSystem.Ty) (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.toOrdinaryInventory.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : RetainedState support.toOrdinaryInventory receiver call.completion.session (entries ++ [entry])
  trace : SourceCall support.toOrdinaryInventory header invocation before.heap arguments (.value entry.source) after.heap

theorem RetainedState.word_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Core.Word) (flag : Bool)
    (call : ObservedFunctionCall session observed.wordRow.row.key [.word value, .word next, .bool flag])
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.wordHeader.header call .word [.word value, .word next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_inputs value next flag
  have raw : request.header.function.resultType = closureType .word := by
    rw [selected, support.wordHeader.word_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.wordHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (word_simple value next flag) descriptor (support.terminals request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.bool_factory_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (value next : Bool) (flag : Bool)
    (call : ObservedFunctionCall session observed.boolRow.row.key [.bool value, .bool next, .bool flag])
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (FactoryMeaning state support.boolHeader.header call .bool [.bool value, .bool next, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_inputs value next flag
  have raw : request.header.function.resultType = closureType .bool := by
    rw [selected, support.boolHeader.bool_result_type]
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.boolHeader
  obtain ⟨entry, entryType, handleEq, _handleType, after, trace⟩ := state.make_typed_handle call request inputs
    (bool_simple value next flag) descriptor (support.terminals request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, raw, entry, entryType.trans raw, handleEq, after,
    by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useWord_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useWordRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useWordHeader.header (.word value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useWordHeader.header :=
    selected_useWord_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useWordHeader.useWord_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [selected, support.useWordHeader.useWord_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [selected, support.useWordHeader.useWord_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useWordHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.word value) call returned request inputs registry raw native descriptor
    (support.terminals request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

theorem RetainedState.useBool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (support : StaticSupportPackage fixture observed receiver.completion)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (state : RetainedState support.toOrdinaryInventory receiver session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .bool)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Bool) (call : ObservedCall session observed.useBoolRow.row.key [.function handle])
    (returned : call.completion.value = .bool value)
    (stages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.useBoolHeader.header (.bool value) call [entry.source] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_covered
    fixture.recipePrepared [support.wordInput, support.boolInput, support.makeWordInput, support.makeBoolInput, support.useWordInput, support.useBoolInput]
    support.toOrdinaryInventory.rows support.toOrdinaryInventory.public_coverage state.atRecipe
    state.history.semantic.current.1 state.atSession call.started
  have selected : request.header = support.useBoolHeader.header :=
    selected_useBool_at support.wordHeader support.boolHeader support.makeWordHeader support.makeBoolHeader support.useWordHeader support.useBoolHeader support.toOrdinaryInventory.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [selected, support.useBoolHeader.useBool_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.bool value : ScalarOutput).sourceType := by
    rw [selected, support.useBoolHeader.useBool_result_type]; rfl
  have native : request.header.output = (.bool value : ScalarOutput).nativeType := by
    rw [selected, support.useBoolHeader.useBool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]; exact stages.descriptor_at support.useBoolHeader
  have registry := request.started.function_registry state.registry
  obtain ⟨after, trace⟩ := state.finished_call (.bool value) call returned request inputs registry raw native descriptor
    (support.terminals request.header request.selected.member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods state.issued state.extension
      request.header request.selected.member selected budget) invocation
  exact ⟨⟨request, selected, inputs, registry, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : StaticSupportPackage fixture observed receiver.completion
  firstEntry : Entry
  firstType : firstEntry.sourceType = closureType .word
  firstHandle : firstEntry.handle = sequence.first.handle
  initial : RetainedState support.toOrdinaryInventory receiver sequence.first.completion.session [firstEntry]
  firstTrace : SourceCall support.toOrdinaryInventory support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value firstEntry.source) initial.heap
  secondMeaning : FactoryMeaning initial support.boolHeader.header sequence.second .bool [.bool false, .bool true, .bool true]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  firstReadMeaning : CallMeaning secondMeaning.after support.useWordHeader.header (.word seed) sequence.firstRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdMeaning : FactoryMeaning firstReadMeaning.after support.wordHeader.header sequence.third .word [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  secondReadMeaning : CallMeaning thirdMeaning.after support.useBoolHeader.header (.bool false) sequence.secondRead [secondMeaning.entry.source]
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  repeatedReadMeaning : CallMeaning secondReadMeaning.after support.useWordHeader.header (.word seed) sequence.repeatedRead [firstEntry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  thirdReadMeaning : CallMeaning repeatedReadMeaning.after support.useWordHeader.header (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead [thirdMeaning.entry.source]
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)

theorem SequenceWitness.handles_distinct {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) :
    meaning.firstEntry.handle ≠ meaning.secondMeaning.entry.handle ∧
      meaning.firstEntry.handle ≠ meaning.thirdMeaning.entry.handle ∧
      meaning.secondMeaning.entry.handle ≠ meaning.thirdMeaning.entry.handle := by
  rw [meaning.firstHandle, meaning.secondMeaning.handleEq, meaning.thirdMeaning.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed factories methods receiver.issued
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    (support.terminals support.wordHeader.header support.toOrdinaryInventory.word_member)
    (fun budget {child} selected => reflects_bodies receiver support sources bodies methods receiver.issued (.refl _)
      support.wordHeader.header support.toOrdinaryInventory.word_member selected budget) wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_factory_meaning support sources bodies methods initial false true true sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.useWord_meaning support sources bodies methods second.after firstEntry
    (by simp) firstType firstHandle seed sequence.firstRead sequence.firstValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_factory_meaning support sources bodies methods firstRead.after
    (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.useBool_meaning support sources bodies methods third.after second.entry
    (by simp) second.entryType second.handleEq false sequence.secondRead sequence.secondValue useBoolStages
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.useWord_meaning support sources bodies methods secondRead.after firstEntry
    (by simp) firstType firstHandle seed sequence.repeatedRead sequence.repeatedValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.useWord_meaning support sources bodies methods repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55) sequence.thirdRead sequence.thirdValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages useWordStages useBoolStages factories sources bodies methods sequence receiver⟩

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedSequenceForward
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (ready : session.ExportsReady) :
    ForwardAt (entries := entries) support.toOrdinaryInventory receiver scalar call meaning.after.heap := by
  apply forward_call before scalar call meaning.request meaning.inputs meaning.registry meaning.rawType meaning.nativeType ready
    (support.terminals meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

theorem FactoryMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFunctionCall session key publicArguments} {resultType : TypeSystem.Ty}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : FactoryMeaning before header call resultType arguments invocation)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (ready : session.ExportsReady) :
    FactoryForwardAt (entries := entries) support.toOrdinaryInventory receiver call resultType meaning.entry.source meaning.after.heap := by
  apply forward_factory before call meaning.request meaning.inputs simple meaning.rawType ready
    (support.terminals meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support sources bodies methods before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support.toOrdinaryInventory receiver sequence.first meaning.firstEntry.source meaning.initial.heap
  second : FactoryForwardAt (entries := [meaning.firstEntry]) meaning.support.toOrdinaryInventory receiver sequence.second .bool
    meaning.secondMeaning.entry.source meaning.secondMeaning.after.heap
  firstRead : ForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word seed) sequence.firstRead meaning.firstReadMeaning.after.heap
  third : FactoryForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry]) meaning.support.toOrdinaryInventory receiver
    sequence.third .word meaning.thirdMeaning.entry.source meaning.thirdMeaning.after.heap
  secondRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.bool false) sequence.secondRead meaning.secondReadMeaning.after.heap
  repeatedRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word seed) sequence.repeatedRead meaning.repeatedReadMeaning.after.heap
  thirdRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead meaning.thirdReadMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
    {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨forward_initial meaning.support.toOrdinaryInventory meaning.support.distinct sequence.first
      (meaning.support.terminals meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member)
      (fun budget {child} selected => preserves_bodies receiver meaning.support sources bodies methods receiver.issued (.refl _)
        meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member selected budget)
      meaning.firstTrace,
    meaning.secondMeaning.forward sources bodies methods (bool_simple false true true) firstReady,
    meaning.firstReadMeaning.forward sources bodies methods secondReady,
    meaning.thirdMeaning.forward sources bodies methods (word_simple (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false) firstReadReady,
    meaning.secondReadMeaning.forward sources bodies methods thirdReady,
    meaning.repeatedReadMeaning.forward sources bodies methods secondReadReady,
    meaning.thirdReadMeaning.forward sources bodies methods repeatedReady⟩

theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (factories : ObservedFactories fixture observed)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  exact ⟨receiver, meaning, meaning.forward sources bodies methods⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let factories ← observeFactories fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let ⟨sources⟩ ← observeClosureSources fixture observed
  let ⟨bodies⟩ ← observeMethodBodies fixture
  let ⟨methods⟩ ← observeMethodCatalog fixture
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed wordStages boolStages useWordStages useBoolStages
    factories sources bodies methods sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [9,36,63,88,115,140,165,187] do
    throw (IO.userError s!"method scoped stores changed: {reprStr stores}")
  IO.println "METHOD_SCOPED_FORWARD_PASS: seven Source calls; all seven sufficient public fuel bounds; three retained closures; scalar11/false/11/55; captured value+flag writes stay in their call, true/false loops"

end Tests.SourceCoreMethodScoped
end
