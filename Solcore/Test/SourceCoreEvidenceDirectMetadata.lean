import Solcore.Test.SourceCoreEvidenceDirectFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (SupportedSyntax)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

theorem ObservedRow.record {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) :
    SourceCompilationPlan.exactSpecialization fixture.recipe.compiled.indexed.base.plan row.row.key = .ok row.row := by
  obtain ⟨input, _same, packet, actual, _⟩ := row.issue
  have record := CallableIndexedActualNamedSourceReceipts.header_record fixture.recipe.compiled actual.header
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared,
    actual.prepared.same] at record
  exact record

private theorem retained_ordered {plan : SourceCompilationPlan.Plan}
    {row : SourceSpecialization.SpecializedFunction}
    (target : SourceCompilationPlan.exactInstantiationKey plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key)
    (record : SourceCompilationPlan.exactSpecialization plan row.key = .ok row) :
    RecursiveNamedCallSelectionCertificates.Ordered plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) := by
  intro key selected selectedTarget selectedRecord
  have sameKey := Except.ok.inj (target.symm.trans selectedTarget)
  subst key
  have sameRow := Except.ok.inj (record.symm.trans selectedRecord)
  subst selected
  exact List.map_reverse

theorem ObservedProgram.word_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.wordShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.wordShape.call.exact] at member
    rcases List.mem_cons.mp member with same | member
    · rw [(Prod.mk.inj same).2]; rfl
    · have same := List.mem_singleton.mp member
      rw [(Prod.mk.inj same).2]; rfl
  · rw [observed.wordInstantiation]
    exact retained_ordered observed.relayWordRow.target observed.relayWordRow.record

theorem ObservedProgram.bool_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.boolShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.boolShape.call.exact] at member
    rcases List.mem_cons.mp member with same | member
    · rw [(Prod.mk.inj same).2]; rfl
    · have same := List.mem_singleton.mp member
      rw [(Prod.mk.inj same).2]; rfl
  · rw [observed.boolInstantiation]
    exact retained_ordered observed.relayBoolRow.target observed.relayBoolRow.record

theorem ObservedProgram.relayWord_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.relayWordShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.relayWordShape.call.exact] at member
    rcases List.mem_cons.mp member with same | member
    · rw [(Prod.mk.inj same).2]; rfl
    · have same := List.mem_singleton.mp member
      rw [(Prod.mk.inj same).2]; rfl
  · rw [observed.relayWordInstantiation]
    exact retained_ordered observed.chooseWordRow.target observed.chooseWordRow.record

theorem ObservedProgram.relayBool_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.relayBoolShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.relayBoolShape.call.exact] at member
    rcases List.mem_cons.mp member with same | member
    · rw [(Prod.mk.inj same).2]; rfl
    · have same := List.mem_singleton.mp member
      rw [(Prod.mk.inj same).2]; rfl
  · rw [observed.relayBoolInstantiation]
    exact retained_ordered observed.chooseBoolRow.target observed.chooseBoolRow.record

section Root
variable {function : CheckedFunction} {signature generic : ProgramFunctionSignature}
  {firstParameter secondParameter : TypeSystem.TypeParameterId} {firstType secondType : TypeSystem.Ty} {trait : ProgramTraitId}
  (shape : RootShape function signature generic firstParameter secondParameter firstType secondType trait)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem RootShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.firstRead.node ∨ node = shape.secondRead.node ∨
      node = shape.call.callee.node ∨ node = shape.call.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [RootShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem RootShape.metadata {fixture : CompiledFixture}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor
      fixture.recipe.compiled.indexed named function.typedBody
      (Supported fixture.recipe.compiled.indexed.base.plan) := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · exact .inl shape.firstRead.requirements
    · exact .inl shape.secondRead.requirements
    · exact .inl shape.call.callee.requirements
    · exact .inr (.inr ⟨_, _, _, shape.call.form⟩)
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · exact shape.firstRead.coercions
    · exact shape.secondRead.coercions
    · exact shape.call.callee.coercions
    · exact shape.call.value.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · rw [shape.firstRead.form] at form; cases form
    · rw [shape.secondRead.form] at form; cases form
    · rw [shape.call.calleeForm] at form; cases form
    · rw [shape.call.form] at form; cases form
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem RootShape.syntax {plan : SourceCompilationPlan.Plan}
    (ordinary : Supported plan shape.call.instantiation) :
    SupportedSyntax plan function.typedBody shape.call.value.node.id := by
  refine .direct shape.call.value.found shape.call.form ordinary ?_
  intro id member
  rcases List.mem_cons.mp member with same | member
  · subst id
    exact .leaf (.read shape.firstRead.found shape.firstRead.form)
  · have same := List.mem_singleton.mp member
    subst id
    exact .leaf (.read shape.secondRead.found shape.secondRead.form)
end Root
end Tests.SourceCoreEvidenceDirect
