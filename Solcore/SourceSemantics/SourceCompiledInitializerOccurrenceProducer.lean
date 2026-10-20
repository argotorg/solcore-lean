import Solcore.SourceSemantics.SourceCompiledInitializerOccurrence

/-! The recursive statement boundary constructs its initializer occurrence
directly from that actual call and retained subtree, including inside an
expression or lambda. No separately indexed block continuation is required. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness

theorem of_accepted {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {source : Syntax.Statement}
    {entry : State} {result : Detail.StatementResult} {expectedReturn : Ty}
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (scope : CheckingScope selected inferenceContext)
    (form : source.value = .letDecl name annotation (some initializer))
    (accepted : Detail.inferStatementFuel (childFuel + 1) inferenceContext source expectedReturn entry = .ok result)
    (ready : entry.InferenceReady)
    (operational : GeneralizedActualStateInvariant entry (evidenceSource selected))
    (rawSubtree : RawSubtreePreserved (result.state.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.statement result.id))
    (extension : selected.body.finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    ∃ occurrence : InitializerOccurrence selected source,
      occurrence.childFuel = childFuel ∧
      occurrence.inferenceContext = inferenceContext ∧
      occurrence.entry = entry ∧ occurrence.result = result := by
  obtain ⟨receipt⟩ := LocalLetRequirementTiming.of_initialized_accepted form accepted
  have idEq : result.id = entry.allocateStatementId.1 :=
    congrArg Detail.StatementResult.id receipt.completed
  have recorded : .statement {
      id := entry.allocateStatementId.1, span := source.span, type := .unit
      form := .letDecl receipt.binding.1 (some receipt.value.id) } ∈ selected.body.returned.nodes := by
    apply rawSubtree.nodes _ receipt.recorded
    exact .inl (congrArg NodeId.statement idEq.symm)
  exact ⟨ofReceipt checked scope receipt ready operational recorded extension, rfl, rfl, rfl, rfl⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
