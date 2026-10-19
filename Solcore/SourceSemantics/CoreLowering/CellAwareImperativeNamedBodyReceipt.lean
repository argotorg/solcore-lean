import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeBodyProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations

/-! The actual public preparation and named header produce the bounded mixed
body certificate. Source typing, parameter declarations and native body typing
are recovered from their original receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedBodyReceipt
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
theorem of_header
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareImperativeBodyProducer.Profile whole.indexed prepared.named
      prepared.compilation.statements prepared.named.specialized.function.inferredBodyType) :
    Nonempty (CellAwareImperativeBodyProducer.Body prepared.compilation
      (CellAwareImperativeBodyProducer.Certificate prepared.compilation)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
      header.context header.function.resultType) := by
  have sourceEq : header.function.source = source prepared.named := by
    rw [header.agreement.source, aligned.named]
    rfl
  have statementsEq : header.function.body = prepared.compilation.statements := by
    rw [aligned.function]
    rfl
  have resultEq : header.function.resultType = prepared.named.specialized.function.inferredBodyType := by
    rw [header.agreement.result, aligned.named]
  have record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan
      prepared.named.signature.key = .ok prepared.named.specialized := by
    simpa only [aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record whole header
  have native := CallableIndexedOwnedPreparedNamedLexicalCollectors.body_typed prepared aligned ready member
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed)
    (values := SourceCoreCompatibleValues.Context.initial whole.compatible.checked)
    (prepared := whole.indexed.ancestry) (program := Program.ofChecked whole.sourceProgram) header
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [sourceEq, statementsEq] at typed
  apply CellAwareImperativeBodyProducer.of_compilation prepared.compilation record
    (CallableIndexedOwnedIssuedAssignmentRecipes.assignments_prepared prepared.selected prepared.compilation
      (CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared prepared diagnostic))
    (by simpa only [resultEq] using profile) (sourceEq ▸ header.unique) rfl typed
  · simpa only [sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope, aligned.bindings,
      CellAwareImperativeBodyProducer.scope] using declarations
  · exact RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header)
  · simpa only [CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.parameterScope,
      aligned.bindings, aligned.body, CellAwareImperativeBodyProducer.scope] using native

include aligned in
/-- Whole-program typing is one way to supply the actual selected certificate. -/
theorem of_program
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareImperativeBodyProducer.Profile whole.indexed prepared.named
      prepared.compilation.statements prepared.named.specialized.function.inferredBodyType) :
    Nonempty (CellAwareImperativeBodyProducer.Body prepared.compilation
      (CellAwareImperativeBodyProducer.Certificate prepared.compilation)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
      header.context header.function.resultType) :=
  of_header prepared aligned ready diagnostic (RecursiveNamedHeaderSourceTyping.certificate header wellFormed) member profile

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedBodyReceipt
