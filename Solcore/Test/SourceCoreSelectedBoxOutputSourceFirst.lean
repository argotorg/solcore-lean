import Solcore.Test.SourceCoreSelectedBoxOutputFixture

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedBoxOutput
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicPhysicalSessionState (StartedCall PlainValue SourceCall)
open SelectedCompilationStageClosedDirectForward.Output (ForwardAt ReturnedValue)

variable {fixture : Fixture}

private theorem selected_shape (fixture : Fixture)
    {header : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (same : header.named = fixture.named) : Nonempty (Shape header.function.source) := by
  have sourceEq := header.agreement.source.trans
    (congrArg (fun named => named.specialized.function.typedBody) same)
  exact ⟨sourceEq.symm ▸ fixture.shape⟩

private theorem selected_eq (fixture : Fixture)
    (row : SelectedCompilationCertifiedPublicSession.EligibleRow fixture.recipe.compiled fixture.named.signature.key) :
    row.named = fixture.named := by
  have member := List.mem_of_getElem? row.cached
  rw [fixture.functions] at member
  exact List.mem_singleton.mp member

structure LaterMeaning (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (before : issued.toIssued.State anchor session []) (word : Word)
    (call : StartedCall session fixture.named.signature.key [.word word] runOptions)
    (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session fixture.named.signature.key [.word word] runOptions.inputValidationFuel
    before.world before.store
  shape : Shape request.header.function.source
  plain : PlainValue anchor request.header invocation before.heap [.word word]
    (result shape.instantiation word) (appendWord before.heap word)
  forward :
    (SourceCall anchor request.header invocation before.heap [.word word]
      (.value (result shape.instantiation word)) (appendWord before.heap word) ∧
      ForwardAt issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe []
        request.header.function.resultType call.checkpoint (result shape.instantiation word)
        (appendWord before.heap word)) ∨
    SelectedCompilationStagePublicForward.StageStopped issued before call request.header invocation [.word word]

theorem later_from_source (fixture : Fixture) (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (before : issued.toIssued.State anchor session []) (word : Word)
    (call : StartedCall session fixture.named.signature.key [.word word] runOptions)
    (ready : session.ExportsReady) (invocation : Staging.Recursive.Scope) :
    Nonempty (LaterMeaning issued before word call invocation) := by
  obtain ⟨row⟩ := fixture.eligible
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row before call row
  obtain ⟨shape⟩ := selected_shape fixture (namedEq.trans (selected_eq fixture row))
  have certified := issued.support.certificates request.header request.selected.member
  have plain := ordinary_call request.header shape certified request.sourceAt anchor invocation before.heap word
  have bindingTypes : request.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
    have types := Dynamic.MonoBindersExtend.bodyTypes_eq request.header.extended
    rw [request.header.parameters] at types
    simpa only [input_types request.header shape, List.map_map, Function.comp_def] using types
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [bindingTypes]
    exact .cons (.data ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩) .nil
  exact ⟨⟨request, shape, plain,
    SelectedCompilationStageClosedOutputForward.later issued before call request inputs ready plain⟩⟩

structure InitialMeaning (fixture : Fixture) (started : Started fixture) where
  issued : Profiled fixture.recipe
  initial : Initial issued.toIssued started.call
  shape : Shape initial.header.function.source
  plain : ∀ invocation, PlainValue initial.header initial.header invocation ⟨[]⟩ [.word seed]
    (result shape.instantiation seed) (appendWord ⟨[]⟩ seed)
  forward : ∀ invocation,
    (SourceCall initial.header initial.header invocation ⟨[]⟩ [.word seed]
      (.value (result shape.instantiation seed)) (appendWord ⟨[]⟩ seed) ∧
      ForwardAt issued.catalog.rows initial.header issued.initial issued.support.profile fixture.recipe []
        initial.header.function.resultType started.call.checkpoint (result shape.instantiation seed)
        (appendWord ⟨[]⟩ seed)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped issued started.call initial invocation [.word seed]

theorem initial_from_source (fixture : Fixture) (started : Started fixture) :
    Nonempty (InitialMeaning fixture started) := by
  obtain ⟨row⟩ := fixture.eligible
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    fixture.checked fixture.accepted fixture.selected fixture.profile started.opened started.call
    started.bootstrap started.fresh started.authority (.single started.ready) row
  obtain ⟨shape⟩ := selected_shape fixture (namedEq.trans (selected_eq fixture row))
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts issued.catalog.rows).receipts
      initial.header initial.start.selected.member
  have certified := issued.support.certificates initial.header initial.start.selected.member
  have plain := fun invocation => ordinary_call initial.header shape certified sourceAt
    initial.header invocation ⟨[]⟩ seed
  have simple : ∀ value ∈ ([.word seed] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    cases List.mem_singleton.mp member
    exact .word seed
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [input_types initial.header shape]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have meanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  exact ⟨⟨issued, initial, shape, plain, fun invocation =>
    SelectedCompilationStageClosedOutputForward.initial issued started.call initial simple inputTypes meanings
      (plain invocation)⟩⟩

/-- Every sufficiently funded first completion carries its entire constructor
representation. A subsequent actual named start obtains a fresh independent
ordinary constructor trace and the same full-output guarantee. -/
def InitialMeaning.Followed
    {started : Started fixture} (meaning : InitialMeaning fixture started)
    (invocation : Staging.Recursive.Scope) : Prop :=
    (∃ executionBound outputBound,
      ∀ executionFuel outputFuel outcome, executionBound ≤ executionFuel → outputBound ≤ outputFuel →
      started.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion, outcome = .succeeded completion ∧
      ∃ after : meaning.issued.toIssued.State meaning.initial.header completion.session [],
        after.heap = appendWord ⟨[]⟩ seed ∧
        ReturnedValue completion after meaning.initial.header.function.resultType
          (result meaning.shape.instantiation seed) outputFuel ∧
        ∀ word (call : StartedCall completion.session fixture.named.signature.key [.word word] runOptions),
          Nonempty (LaterMeaning meaning.issued after word call invocation)) ∨
    SelectedCompilationStageClosedInitialForward.StageStopped meaning.issued started.call
      meaning.initial invocation [.word seed]

theorem InitialMeaning.followed
    {started : Started fixture} (meaning : InitialMeaning fixture started)
    (invocation : Staging.Recursive.Scope) : meaning.Followed invocation := by
  rcases meaning.forward invocation with ⟨_source, bound, outBound, forward⟩ | stopped
  · refine .inl ⟨bound, outBound, ?_⟩
    intro fuel outFuel outcome enough outputEnough resumed
    obtain ⟨completion, succeeded, ready, after, heap, represented, _selection⟩ :=
      forward fuel outFuel outcome enough outputEnough resumed
    exact ⟨completion, succeeded, after, heap, represented,
      fun word call => later_from_source fixture meaning.issued after word call ready invocation⟩
  · exact .inr stopped

/-- The initial ordinary proof and the subsequent ordinary proof share the
actual returned history and full constructor representation. -/
theorem from_source (fixture : Fixture) (started : Started fixture) :
    ∃ meaning : InitialMeaning fixture started, ∀ invocation, meaning.Followed invocation := by
  obtain ⟨meaning⟩ := initial_from_source fixture started
  exact ⟨meaning, meaning.followed⟩

end Tests.SourceCoreSelectedBoxOutput
