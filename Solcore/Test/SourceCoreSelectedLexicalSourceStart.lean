import Solcore.Test.SourceCoreSelectedLexicalOrdinaryTraces
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.Test.SourceCoreSelectedLexicalFailureProfile
import Solcore.Test.SourceCoreCertifiedLexicalFailureRuntime

/-! This observer stops at the public call checkpoint. No execution result is
stored or required to construct its automatically issued initial session. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedLexicalSourceStart
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open SelectedCompilationCertifiedPublicSession (Profiled Initial)

structure Started (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : RecursiveNamedPublicPhysicalSessionState.StartedCall session key arguments runOptions

def observeStarted (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "lexical source bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2,
        session, ready, checkpoint, started⟩

theorem initial {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (row : ObservedRow fixture signature) {arguments : List SourceCorePublicValues.Value}
    (started : Started fixture row.row.key arguments) :
    ∃ issued : Profiled fixture.recipe, ∃ first : Initial issued.toIssued started.call,
      ∃ actual : ActualHeader fixture row.row, actual.header = first.header := by
  obtain ⟨selected, sameRow⟩ := Tests.SourceCoreCertifiedLexicalFailure.eligible_row row
  obtain ⟨issued, first, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile started.opened started.call started.bootstrap started.fresh started.authority
    (show started.bootstrap.ReadyAt 100000 started.session from .single started.ready) selected
  obtain ⟨actual, actualEq⟩ := Tests.SourceCoreCertifiedLexicalFailure.header_of_member row issued.catalog.rows
    first.start.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  exact ⟨issued, first, actual, actualEq⟩


theorem failed_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) : actual.header.types = [] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  have parameters : actual.header.function.parameters = [] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.failedShape.inputs]
  simpa only [parameters, List.map_nil] using types.symm

theorem identity_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  have parameters : actual.header.function.parameters = [observed.identityShape.binder] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.identityShape.inputs]
  simpa only [parameters, List.map_cons, List.map_nil, observed.identityShape.binderScheme,
    TypeSystem.Scheme.mono] using types.symm

theorem identity_result {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.function.resultType = .word := by
  obtain ⟨facts, final, typed, roots, complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.identityShape.roots] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  have unique : NodeOccurrencesUnique observed.identityRow.row.function.typedBody := actual.source ▸ actual.header.unique
  cases typed with
  | singleton last =>
    cases last with
    | returnValue contains form expression type =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.identityShape.statementFound)
      cases same
      exact type.symm.trans observed.identityShape.statementType
    | _ =>
      have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.identityShape.statementFound)
      cases same
      simp_all [observed.identityShape.statementForm]

theorem identity_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [identity_result actual] at projected
  exact (Except.ok.inj projected).symm

end Tests.SourceCoreSelectedLexicalSourceStart
