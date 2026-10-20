import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementContracts
import Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceRecursion
import Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceProducer

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {source : Syntax.Statement} {expectedReturn : Ty}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}

theorem StatementBoundary.initializerOccurrence
    {inferenceContext : SourceInference.Context} {initial : State} {result : Detail.StatementResult}
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext source
      expectedReturn initial result frames target)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ occurrence : BodyInitializerOccurrence selected source,
      occurrence.childFuel = childFuel ∧ occurrence.inferenceContext = inferenceContext ∧
      occurrence.entry = initial ∧ occurrence.result = result :=
  BodyInitializerOccurrence.of_accepted checked boundary.scope form boundary.accepted boundary.invariant.ready
    boundary.operational boundary.rawSubtree boundary.extension

/-- The concrete occurrence and its selected-scope barrier feed the same
statement conclusion consumed by source-order sequencing. -/
theorem statement_initialized
    (occurrence : BodyInitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRootedSoundness selected occurrence.childFuel)
    (boundary : StatementBoundary selected (occurrence.childFuel + 1)
      occurrence.inferenceContext source expectedReturn occurrence.entry occurrence.result frames target)
    (barrier : GeneralizationBarrierTransport occurrence.receipt.ready occurrence.receipt.locals
      occurrence.entry.nextRequirement (occurrence.receipt.ready.resolve occurrence.receipt.value.type)
      selected.body.finalized.substitution target (localSchemeTemplateIds occurrence.initializerBinding.binder)) :
    StatementConclusion selected occurrence.inferenceContext expectedReturn occurrence.result frames target := by
  have idEq : occurrence.result.id = occurrence.entry.allocateStatementId.1 :=
    congrArg Detail.StatementResult.id occurrence.receipt.completed
  obtain ⟨finalContext, invariant, actual, operational, typing, agreement⟩ :=
    occurrence.statement_of_expressionSoundness checked boundary.scope boundary.interfaces boundary.invariant
      boundary.actual boundary.operational boundary.rawSubtree boundary.integerPatterns boundary.integerLiterals
      boundary.requirements (idEq ▸ boundary.covered) (idEq ▸ boundary.actualCovered) barrier recursive
  exact ⟨finalContext, _, invariant, actual, operational, typing, agreement⟩

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
