import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Static preparation receipts and actual raw metadata replacements. The raw
fixtures test retained occurrence/form provenance, not source typing or the
execution meaning of the edited evidence. The contract flags survive edits to
an ancestor and to the lambda's own metadata. No evaluator is imported. -/

set_option autoImplicit false
namespace Tests.SourceLambdaSourceAlignment
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open LambdaMetadataViews

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_source_alignment", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "lambda_source_alignment.solc"⟩, 0, 1⟩
private def parameter : TypedBinder := {
  id := ⟨owner, 0⟩, name := "input", scheme := .mono .word, comptime := true }
private def sourceType : TypeSystem.Ty := .function .word .unit
private def requirement (index : Nat) : RequirementId := ⟨index⟩
private def coercion (index : Nat) : CoercionStep := {
  requirement := requirement index, source := sourceType, target := sourceType }
private def lambda : ExpressionNode := {
  id := id 1, span, type := sourceType, form := .lambda [parameter] .unit []
  requirements := [requirement 1], coercions := [coercion 1] }
private def ancestor : ExpressionNode := {
  id := id 0, span, type := sourceType, form := .group (id 1)
  requirements := [requirement 0], coercions := [coercion 0] }
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression (id 0)], nodes := [.expression ancestor, .expression lambda] }
private def raw (node : ExpressionNode) : ExpressionNode := {
  node with type := node.rawType, requirements := [], coercions := [] }
private def firstView : TypedSource := SourceCoreEvidence.withNode source (raw ancestor)
private def finalView : TypedSource := SourceCoreEvidence.withNode firstView (raw lambda)

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

private theorem first_metadata : MetadataView source firstView :=
  raw_view unique rfl []

private theorem final_metadata : MetadataView source finalView :=
  first_metadata.trans (raw_view (first_metadata.unique unique) rfl [])

/-- Replacing a raw ancestor does change the full table. -/
example : source ≠ firstView := by decide

/-- The real evidence helper also changes the lambda's own metadata. -/
example : firstView ≠ finalView := by decide

/-- Original staging flags and body IDs are nevertheless unchanged. -/
example : ∃ node, source.lookupExpression? (id 1) = some node ∧
    node.form = .lambda [parameter] .unit [] := by
  obtain ⟨node, found, _, form⟩ := final_metadata.expression
    (show finalView.lookupExpression? (id 1) = some (raw lambda) from rfl)
  exact ⟨node, found, form⟩

example : NodeOccurrencesUnique finalView := final_metadata.unique unique

/-- Preparation eliminates source equality as a free premise. Both the
canonical caller and the entire active substitution are extracted from the
actual local-evidence factory, including its original-source checks. -/
example {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
    {prepared : SourceCoreLocalEvidence.Prepared}
    {id : ExpressionId} {contract : SourceCoreStageContracts.Contract}
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared)
    (original : AuthenticatedCallableLedger.LambdaSource plan candidate.origin.caller id prepared.substitution contract) :
    prepared.source = original.source :=
  LambdaSourceAlignment.source_alignment (.contextual accepted) original

/-- Distinct source tables can have the same complete expression forms;
empty active substitution retains every original metadata field exactly. -/
example : source.applySubstitution [] = source := EmptySourceSubstitution.source _

/-- Normalization's real acceptance checks suffice for another view step. -/
example {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : SourceCoreLocalPolymorphism.Binding} {parent : Option SourceCoreLocalEvidence.Prepared}
    {result : TypedSource} {expression : ExpressionId}
    (accepted : SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent finalView expression = .ok result) :
    MetadataView source result :=
  final_metadata.trans (normalized_view (final_metadata.unique unique) accepted)

end Tests.SourceLambdaSourceAlignment
