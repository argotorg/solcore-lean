import Solcore.Test.SourceCoreMethodOwnEvidenceInventory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOwnEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedMethodRootStaticSupport (NoIndirectSource)

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
    cases List.mem_singleton.mp member
    rfl
  · rw [observed.wordInstantiation]
    exact retained_ordered observed.makeWordRow.target observed.makeWordRow.record

theorem ObservedProgram.bool_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.boolShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.boolShape.call.exact] at member
    cases List.mem_singleton.mp member
    rfl
  · rw [observed.boolInstantiation]
    exact retained_ordered observed.makeBoolRow.target observed.makeBoolRow.record

theorem ObservedProgram.makeWord_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.makeWordShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.makeWordShape.call.exact] at member
    cases List.mem_singleton.mp member
    rfl
  · rw [observed.makeWordRelayInstantiation]
    exact retained_ordered observed.relayWordRow.target observed.relayWordRow.record

theorem ObservedProgram.makeBool_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.makeBoolShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.makeBoolShape.call.exact] at member
    cases List.mem_singleton.mp member
    rfl
  · rw [observed.makeBoolRelayInstantiation]
    exact retained_ordered observed.relayBoolRow.target observed.relayBoolRow.record

section Root
variable {function : CheckedFunction} {signature generic : ProgramFunctionSignature}
  {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
  (shape : RootShape function signature generic parameter type trait)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem RootShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.firstRead.node ∨ node = shape.secondRead.node ∨ node = shape.flagRead.node ∨ node = shape.call.callee.node ∨ node = shape.call.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [Tests.SourceCoreMethodScoped.RootShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem RootShape.no_indirect : NoIndirectSource function.typedBody := by
  intro id node callee ids metadata found form
  rcases shape.expressions nodes found with same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.flagRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form

include nodes in
theorem RootShape.metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same
    all_goals subst node
    · exact .inl shape.firstRead.requirements
    · exact .inl shape.secondRead.requirements
    · exact .inl shape.flagRead.requirements
    · exact .inl shape.call.callee.requirements
    · exact .inr (.inr (.inl ⟨_, _, _, shape.call.form⟩))
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same
    all_goals subst node
    · exact shape.firstRead.coercions
    · exact shape.secondRead.coercions
    · exact shape.flagRead.coercions
    · exact shape.call.callee.coercions
    · exact shape.call.value.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    exact False.elim (shape.no_indirect nodes id node callee ids metadata found form)
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem RootShape.syntax :
    GeneralSyntax function.typedBody shape.call.value.node.id (fun inst => inst = shape.call.instantiation) := by
  refine .direct shape.call.value.found shape.call.form rfl ?_
  intro id member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .leaf (.read shape.firstRead.found shape.firstRead.form)
  · exact .leaf (.read shape.secondRead.found shape.secondRead.form)
  · exact .leaf (.read shape.flagRead.found shape.flagRead.form)
end Root

section Factory
variable {function : CheckedFunction} {generic : ProgramFunctionSignature}
  {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
  (shape : SelectedFactoryShape function generic parameter type trait)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem SelectedFactoryShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.firstRead.node ∨ node = shape.secondRead.node ∨ node = shape.flagRead.node ∨ node = shape.call.callee.node ∨ node = shape.call.value.node ∨ node = shape.expression.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [SelectedFactoryShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem SelectedFactoryShape.no_indirect : NoIndirectSource function.typedBody := by
  intro id node callee ids metadata found form
  rcases shape.expressions nodes found with same | same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.flagRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form
  · rw [shape.lambda] at form; cases form

include nodes in
theorem SelectedFactoryShape.metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same | same
    all_goals subst node
    · exact .inl shape.firstRead.requirements
    · exact .inl shape.secondRead.requirements
    · exact .inl shape.flagRead.requirements
    · exact .inl shape.call.callee.requirements
    · exact .inr (.inr (.inl ⟨_, _, _, shape.call.form⟩))
    · exact .inl shape.expression.requirements
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same | same
    all_goals subst node
    · exact shape.firstRead.coercions
    · exact shape.secondRead.coercions
    · exact shape.flagRead.coercions
    · exact shape.call.callee.coercions
    · exact shape.call.value.coercions
    · exact shape.expression.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    exact False.elim (shape.no_indirect nodes id node callee ids metadata found form)
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem SelectedFactoryShape.inner_syntax :
    GeneralSyntax function.typedBody shape.call.value.node.id (fun inst => inst = shape.call.instantiation) := by
  refine .direct shape.call.value.found shape.call.form rfl ?_
  intro id member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .leaf (.read shape.firstRead.found shape.firstRead.form)
  · exact .leaf (.read shape.secondRead.found shape.secondRead.form)
  · exact .leaf (.read shape.flagRead.found shape.flagRead.form)
end Factory

section Use
variable {function : CheckedFunction} {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
  (shape : UseShape function signature type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem UseShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.body.read.node ∨ node = shape.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [Tests.SourceCoreMethodClosure.UseShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem UseShape.policy_metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same
    all_goals subst node
    · exact .inl shape.body.read.requirements
    · exact .inl shape.value.requirements
  · intro id _ node found
    rcases shape.expressions nodes found with same | same
    all_goals subst node
    · exact shape.body.read.coercions
    · exact shape.value.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases shape.expressions nodes found with same | same
    all_goals subst node
    · rw [shape.body.read.form] at form; cases form
    · rw [shape.form] at form
      have same : shape.metadata = metadata := CallResolution.indirect.inj (ExpressionForm.call.inj form).2.2
      rw [← same, shape.application]
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem UseShape.syntax : GeneralSyntax function.typedBody shape.value.node.id (fun _ => False) := by
  refine .call shape.value.found shape.form (.leaf (.read shape.body.read.found shape.body.read.form)) ?_
  intro id member
  cases member
end Use
section Identity
variable {function : CheckedFunction} {type : TypeSystem.Ty}
  (shape : SelectedIdentityShape function type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem SelectedIdentityShape.expression {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) : node = shape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [SelectedIdentityShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem SelectedIdentityShape.metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rw [shape.expression nodes found]
    exact .inl shape.read.requirements
  · intro id _ node found
    rw [shape.expression nodes found]
    exact shape.read.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [shape.expression nodes found, shape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem SelectedIdentityShape.syntax : GeneralSyntax function.typedBody shape.read.node.id (fun _ => False) :=
  .leaf (.read shape.read.found shape.read.form)
end Identity
end Tests.SourceCoreMethodOwnEvidence
