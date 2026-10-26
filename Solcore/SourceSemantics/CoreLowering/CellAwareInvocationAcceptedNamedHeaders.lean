import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts

/-! An actual prepared named header determines its accepted-body invocation.
Checker certification, the header's result projection and the Core typing of
the compiled body discharge the static premises of the accepted-body theorems;
expression meaning, coverage and the physical entry state are not derived here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedHeaders
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
theorem record :
    SourceCompilationPlan.exactSpecialization whole.indexed.base.plan prepared.named.signature.key =
      .ok prepared.named.specialized := by
  simpa only [aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record whole header

/-- The named cache row's own accepted-body invocation. -/
def index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView :=
  .named prepared.compilation (record prepared aligned)

/-- Static inputs of `CellAwareInvocationAcceptedFlow.body_preserves` and
`body_reflects` at the actual header: fixed-control checker typing of the
compiled statements, the result projection and the native typing of the body. -/
theorem static_inputs
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    (index prepared aligned).source = header.function.source ∧
    (∃ control : ControlContext, ∃ staticFinal facts,
      control.returnType = header.function.resultType ∧ control.loopDepth = 0 ∧
      StatementsHaveType (index prepared aligned).source control header.context
        (index prepared aligned).statements staticFinal facts) ∧
    whole.compatible.checked.catalog.project header.function.resultType = .ok (index prepared aligned).result ∧
    ∃ nativeType, HasType (SourceCoreLocalCell.coreContext (index prepared aligned).scope ++
        RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
      (index prepared aligned).body nativeType whole.indexed.layouts.definitions := by
  have sourceEq : header.function.source = source prepared.named := by
    rw [header.agreement.source, aligned.named]
    rfl
  have statementsEq : header.function.body = prepared.compilation.statements := by
    rw [aligned.function]
    rfl
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [sourceEq, statementsEq] at typed
  have native := CallableIndexedOwnedPreparedNamedLexicalCollectors.body_typed prepared aligned ready member
  have projection : whole.compatible.checked.catalog.project header.function.resultType =
      .ok prepared.named.signature.resultType := by
    simpa only [← header.resultType, aligned.named] using aligned.projection
  have bodyTyped : HasType (SourceCoreLocalCell.coreContext
        (prepared.named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) ++
        RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
      prepared.compilation.body (LanguageResult.resultType header.output) whole.indexed.layouts.definitions := by
    simpa only [CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.parameterScope, aligned.bindings,
      aligned.body] using native
  exact ⟨sourceEq.symm, ⟨_, final, facts, rfl, rfl, typed⟩, projection, _, bodyTyped⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedHeaders
