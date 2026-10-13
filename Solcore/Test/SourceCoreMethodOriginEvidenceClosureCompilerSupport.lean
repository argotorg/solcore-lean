import Solcore.Test.SourceCoreMethodOriginEvidenceMetadata
import Solcore.Test.SourceCoreMethodOriginEvidenceFactoryCompilerSupport
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedReturningExpressionAdmission

/-! Original factory closure nodes are identified without a body scanner.
Accepted inner compiler actions retain the direct call and its ordered reads. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open AcceptedNamedExpressionFlow

variable {fixture : CompiledFixture} {signature generic : ProgramFunctionSignature}
  {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
  {row : ObservedRow fixture signature}
  (shape : SelectedFactoryShape row.row.function generic parameter type trait)

/-- The declaration callee remains in Source. Only the original call and its
actual argument occurrences belong to this reached set. -/
def SelectedFactoryShape.Reached (id : ExpressionId) : Prop :=
  id = shape.call.value.node.id ∨ id = shape.firstRead.node.id ∨
    id = shape.secondRead.node.id ∨ id = shape.flagRead.node.id

theorem SelectedFactoryShape.reached_form {id : ExpressionId} {node : ExpressionNode}
    (reached : shape.Reached id)
    (found : row.row.function.typedBody.lookupExpression? id = some node) :
    (∃ name binder, node.form = .reference name (.local binder)) ∨
      node.form = .call shape.call.callee.node.id
        [shape.firstRead.node.id, shape.secondRead.node.id, shape.flagRead.node.id]
        (.declaration shape.call.instantiation) := by
  rcases reached with same | same | same | same
  · rw [same, shape.call.value.found] at found
    cases Option.some.inj found
    exact .inr shape.call.form
  · rw [same, shape.firstRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, shape.firstRead.form⟩
  · rw [same, shape.secondRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, shape.secondRead.form⟩
  · rw [same, shape.flagRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, shape.flagRead.form⟩

theorem SelectedFactoryShape.reached_forms : ReachedForms row.row.function.typedBody shape.Reached := by
  intro id node reached found
  rcases shape.reached_form reached found with ⟨name, binder, form⟩ | form
  · exact .inl (form ▸ LeafForm.read name binder)
  · exact .inr ⟨_, _, _, form⟩

theorem SelectedFactoryShape.reached_arguments : ReachedArguments row.row.function.typedBody shape.Reached := by
  intro id node reached found callee arguments instantiation form argument member
  rcases shape.reached_form reached found with ⟨name, binder, localForm⟩ | directForm
  · rw [localForm] at form
    cases form
  · have same := (ExpressionForm.call.inj (form.symm.trans directForm)).2.1
    rw [same] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second | flag
    · exact .inr (.inl first)
    · exact .inr (.inr (.inl second))
    · exact .inr (.inr (.inr flag))

theorem SelectedFactoryShape.direct_coverage
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (site : DirectSite directRows shape.call.instantiation) :
    ∀ id node, row.row.function.typedBody.lookupExpression? id = some node →
      ∀ callee arguments instantiation,
      node.form = .call callee arguments (.declaration instantiation) → DirectSite directRows instantiation := by
  intro id node found callee arguments instantiation form
  rcases shape.expressions nodes found with same | same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.flagRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · have same := CallResolution.declaration.inj
      ((ExpressionForm.call.inj (form.symm.trans shape.call.form)).2.2)
    exact same ▸ site

  · rw [shape.lambda] at form; cases form

/-- The original finite node list contains this single lambda. Its body receipt
accounts for that lambda while every remaining node is retained unchanged. -/
theorem SelectedFactoryShape.closure_source
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    {directRows : List SourceSpecialization.SpecializedFunction} {allowCoerced : Bool}
    (certificate : Nonempty (CallableIndexedOwnedPreparedClosureAdmission.OrdinaryBodyCertificate
      fixture.recipe.compiled row.named directRows [shape.statement.id])) :
    CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
      fixture.recipe.compiled row.named directRows allowCoerced := by
  obtain ⟨certificate⟩ := certificate
  constructor
  intro node member
  rw [row.same, nodes] at member
  simp only [SelectedFactoryShape.nodeList, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, shape.firstRead.form]
  · simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, shape.secondRead.form]
  · simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, shape.flagRead.form]
  · simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, shape.call.calleeForm]
  · simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, shape.call.form]
  · trivial
  · simp only [CallableIndexedOwnedPreparedClosureAdmission.NodeReady, shape.lambda]
    exact ⟨.ordinary certificate⟩
  · trivial

/-- The actual lambda compiler body supplies its return expression grammar.
Original metadata and finite source forms retain the same captured variables. -/
theorem ActualHeader.closure_compiler_source
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {directRows : List SourceSpecialization.SpecializedFunction} {allowCoerced : Bool}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed row.named row.row.function.typedBody (DirectSite directRows))
    (site : DirectSite directRows shape.call.instantiation)
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
        fixture.recipe.compiled.indexed.base.plan instantiation) :
    CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
      fixture.recipe.compiled row.named directRows allowCoerced := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named
    actual.prepared row.cached row.same
  have actualMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source (DirectSite directRows) := by
    rw [namedEq, actual.source]
    exact metadata
  have initializers : ∀ id, shape.Reached id → ¬ Nonempty
      (AcceptedContextualDirectReceipt.InitializerAt fixture.recipe.compiled.indexed
        (CallableIndexedNamedGeneration.context fixture.recipe.compiled.indexed actual.prepared.named) id) := by
    intro id _ initializer
    obtain ⟨initializer⟩ := initializer
    have found := initializer.found
    simp only [noLocals, List.find?_nil, Option.filter_none] at found
    cases found
  have issued := AcceptedNamedClosureAdmission.of_returning actual.prepared actual.aligned
    (actual.factory_compiler_roots shape)
    (by rw [actual.source]; exact shape.outerReturnFound) shape.outerReturnForm
    (by rw [actual.source]; exact shape.expression.found) shape.lambda
    shape.expression.requirements shape.expression.coercions
    (by simp only [noLocals, List.find?_nil])
    (by rw [actual.source]; exact shape.statementFound) shape.statementForm fixture.source_wellFormed
    actualMetadata supported (by rw [actual.source]; exact shape.direct_coverage nodes site)
    (by rw [actual.source]; exact shape.reached_forms) initializers
    (by rw [actual.source]; exact shape.reached_arguments)
    (show shape.Reached shape.call.value.node.id from .inl rfl)
  obtain ⟨certificate⟩ := issued
  exact shape.closure_source nodes (AcceptedNamedClosureAdmission.source_of_header
    actual.prepared row.cached row.same certificate)

end Tests.SourceCoreMethodOriginEvidence
