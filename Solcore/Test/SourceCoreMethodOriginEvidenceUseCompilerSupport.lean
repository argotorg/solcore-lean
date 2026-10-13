import Solcore.Test.SourceCoreMethodOriginEvidenceMetadata
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedReturningExpressionAdmission

/-! The original indirect caller retains its actual callee action. Its checked
metadata and original read occurrence close the accepted compiler trace. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open AcceptedNamedExpressionFlow

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
  {type : TypeSystem.Ty} {row : ObservedRow fixture signature}
  (shape : UseShape row.row.function signature type)

def UseShape.Reached (id : ExpressionId) : Prop :=
  id = shape.value.node.id ∨ id = shape.body.read.node.id

theorem UseShape.reached_form {id : ExpressionId} {node : ExpressionNode}
    (reached : shape.Reached id)
    (found : row.row.function.typedBody.lookupExpression? id = some node) :
    (∃ name binder, node.form = .reference name (.local binder)) ∨
      node.form = .call shape.body.read.node.id [] (.indirect shape.metadata) := by
  rcases reached with same | same
  · rw [same, shape.value.found] at found
    cases Option.some.inj found
    exact .inr shape.form
  · rw [same, shape.body.read.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, shape.body.read.form⟩

theorem UseShape.reached_indirect {id : ExpressionId} {node : ExpressionNode}
    (reached : shape.Reached id)
    (found : row.row.function.typedBody.lookupExpression? id = some node)
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (form : node.form = .call callee arguments (.indirect metadata)) :
    callee = shape.body.read.node.id ∧ arguments = [] := by
  rcases shape.reached_form reached found with ⟨name, binder, localForm⟩ | indirectForm
  · rw [localForm] at form
    cases form
  · have same := ExpressionForm.call.inj (form.symm.trans indirectForm)
    exact ⟨same.1, same.2.1⟩

theorem UseShape.no_direct
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    {id : ExpressionId} {node : ExpressionNode}
    (found : row.row.function.typedBody.lookupExpression? id = some node)
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation)) : False := by
  rcases shape.expressions nodes found with same | same
  all_goals subst node
  · rw [shape.body.read.form] at form; cases form
  · rw [shape.form] at form; cases form


theorem UseShape.reached_call_forms : ReachedCallForms row.row.function.typedBody shape.Reached := by
  intro id node reached found
  rcases shape.reached_form reached found with ⟨name, binder, form⟩ | form
  · exact .inl (form ▸ LeafForm.read name binder)
  · exact .inr (.inr ⟨_, _, _, form⟩)

theorem UseShape.reached_call_arguments
    (nodes : row.row.function.typedBody.nodes = shape.nodeList) :
    ReachedCallArguments row.row.function.typedBody shape.Reached := by
  constructor
  · intro id node _reached found callee arguments instantiation form argument member
    exact False.elim (shape.no_direct nodes found form)
  · intro id node reached found callee arguments metadata form
    obtain ⟨calleeEq, argumentsEq⟩ := shape.reached_indirect reached found form
    refine ⟨.inr calleeEq, ?_⟩
    intro argument member
    rw [argumentsEq] at member
    cases member

/-- The actual metadata check is transported to the same Header and projected
at each original indirect node. Accepted compiler children supply the grammar. -/
theorem ActualHeader.use_compiler_admission
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed row.named row.row.function.typedBody (DirectSite directRows))
    (metadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      fixture.recipe.compiled.indexed row.named row.row.function.typedBody (DirectSite directRows) = some ⟨metadata⟩)
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
        fixture.recipe.compiled.indexed.base.plan instantiation) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header directRows := by
  have bodyEq : actual.header.function.body = [shape.body.statement.id] := by
    rw [actual.aligned.function]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, shape.body.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have namedEq : actual.prepared.named = row.named :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named actual.prepared row.cached row.same
  have checked : ∃ receipt : PLift
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
        fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source (DirectSite directRows)),
      CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
        fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source (DirectSite directRows) = some receipt := by
    rw [namedEq, actual.source]
    exact ⟨⟨metadata⟩, metadataAccepted⟩
  obtain ⟨⟨actualMetadata⟩, actualAccepted⟩ := checked
  apply AcceptedNamedBodyExpressionAdmission.of_returning_calls actual.prepared actual.aligned actualMetadata
    supported (by
      intro id node found callee arguments instantiation form
      rw [actual.source] at found
      exact False.elim (shape.no_direct nodes found form))
    bodyEq (by rw [actual.source]; exact shape.body.statementFound) shape.body.statementForm
    (by rw [actual.source]; exact shape.reached_call_forms)
    (fun id _ initializer => ?_)
    (by rw [actual.source]; exact shape.reached_call_arguments nodes)
    (ReachedIndirectMetadata.of_accepted actualAccepted)
    (show shape.Reached shape.value.node.id from .inl rfl) fixture.source_wellFormed
  obtain ⟨initializer⟩ := initializer
  have found := initializer.found
  simp only [noLocals, List.find?_nil, Option.filter_none] at found
  cases found

end Tests.SourceCoreMethodOriginEvidence
