import Solcore.Test.SourceCoreChosenOrdinaryAcceptedArgumentAdmission

/-! The accepted indirect parent has one physical argument occurrence. Its
original pair outcome proof fixes the actual value and unchanged heap, and
excludes a fault in that same singleton list. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedNamedGeneration
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedOuterTyping

variable (fixture : AcceptedFixture)
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap}

/-- Any actual completed singleton argument trace retains the original pair
value and the same input heap. Source size remains the trace's own grade. -/
theorem values_at {size : Nat} {values : List Dynamic.Value}
    (trace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (localContext fixture) evidence (source fixture.packet.named) environment before
      [expressionId fixture.packet 6] values after) :
    values = [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue] ∧ after = before := by
  have actual := trace.sound
  cases actual with
  | cons head tail =>
    cases tail
    obtain ⟨same, heap⟩ := SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argument_outcome fixture (.value head)
    exact ⟨congrArg (fun value => [value]) (Dynamic.ExpressionOutcome.value.inj same), heap⟩

/-- The original pair's genuine outcome excludes the head fault; the empty
remaining list has no fault constructor. -/
theorem noFault (size : Nat) (reason : Dynamic.SemanticFault)
    (after : Dynamic.Heap)
    (trace : SourceExecutionSize.ExpressionsFault (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (localContext fixture) evidence (source fixture.packet.named) environment before
      [expressionId fixture.packet 6] reason after) : False := by
  have actual := trace.sound
  cases actual with
  | head fault =>
    have impossible := (SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argument_outcome fixture (.fault fault)).1
    cases impossible
  | tail _ fault => cases fault

/-- Existing ordered pair execution supplies a real sized singleton list;
no completed child law is an input. -/
theorem evaluates : ∃ size,
    SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (localContext fixture) evidence (source fixture.packet.named) environment before
      [expressionId fixture.packet 6] [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue] before := by
  exact SourceExecutionSize.ExpressionsEvaluate.has_size (Dynamic.ExpressionsEvaluate.cons
    (SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argument_evaluates fixture) .nil)

end Tests.SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes
