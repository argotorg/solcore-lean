import Solcore.Test.SourceCoreMethodOriginEvidenceMetadata
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedReturningExpressionAdmission

/-! The two original entry roots use the same accepted-body producer. Their
three argument occurrences retain their order and original evidence metadata. -/
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
  (shape : RootShape row.row.function signature generic parameter type trait)

/-- The declaration callee remains in Source. Only the original call and its
actual argument occurrences belong to this reached set. -/
def RootShape.Reached (id : ExpressionId) : Prop :=
  id = shape.call.value.node.id ∨ id = shape.firstRead.node.id ∨
    id = shape.secondRead.node.id ∨ id = shape.flagRead.node.id

theorem RootShape.reached_form {id : ExpressionId} {node : ExpressionNode}
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

theorem RootShape.reached_forms : ReachedForms row.row.function.typedBody shape.Reached := by
  intro id node reached found
  rcases shape.reached_form reached found with ⟨name, binder, form⟩ | form
  · exact .inl (form ▸ LeafForm.read name binder)
  · exact .inr ⟨_, _, _, form⟩

theorem RootShape.reached_arguments : ReachedArguments row.row.function.typedBody shape.Reached := by
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

theorem RootShape.direct_coverage
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (site : DirectSite directRows shape.call.instantiation) :
    ∀ id node, row.row.function.typedBody.lookupExpression? id = some node →
      ∀ callee arguments instantiation,
      node.form = .call callee arguments (.declaration instantiation) → DirectSite directRows instantiation := by
  intro id node found callee arguments instantiation form
  rcases shape.expressions nodes found with same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.flagRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · have same := CallResolution.declaration.inj
      ((ExpressionForm.call.inj (form.symm.trans shape.call.form)).2.2)
    exact same ▸ site

/-- Original source forms and metadata close residuals from this same accepted
Header body. The caller supplies no expression or statement grammar. -/
theorem ActualHeader.root_compiler_admission
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (site : DirectSite directRows shape.call.instantiation)
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
        fixture.recipe.compiled.indexed.base.plan instantiation) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header directRows := by
  have bodyEq : actual.header.function.body = [shape.statement.id] := by
    rw [actual.aligned.function]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, shape.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source (DirectSite directRows) := by
    rw [actual.source]
    exact shape.metadata nodes actual.prepared.named noLocals
  apply AcceptedNamedBodyExpressionAdmission.of_returning actual.prepared actual.aligned metadata
    supported (by rw [actual.source]; exact shape.direct_coverage nodes site)
    bodyEq (by rw [actual.source]; exact shape.statementFound) shape.statementForm
    (by rw [actual.source]; exact shape.reached_forms)
    (fun id _ initializer => ?_)
    (by rw [actual.source]; exact shape.reached_arguments) (show shape.Reached shape.call.value.node.id from .inl rfl) fixture.source_wellFormed
  obtain ⟨initializer⟩ := initializer
  have found := initializer.found
  simp only [noLocals, List.find?_nil, Option.filter_none] at found
  cases found

end Tests.SourceCoreMethodOriginEvidence
