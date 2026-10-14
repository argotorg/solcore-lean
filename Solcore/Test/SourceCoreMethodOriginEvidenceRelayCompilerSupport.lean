import Solcore.Test.SourceCoreMethodOriginEvidenceRelaySyntax
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedRefinedBodyAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionBoundaryExclusion

/-! Original relay observations identify every source expression. The eventual
body admission follows the actual compiler tree and its ordered child actions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open AcceptedNamedExpressionFlow AcceptedNamedBodyFlow

variable {function : CheckedFunction} {type : TypeSystem.Ty}
  (shape : SelectedRelayShape function type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes

/-- Every original stored expression is a leaf or one of the three method
operator occurrences, with its original nonempty requirement list. -/
theorem SelectedRelayShape.compiler_form {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    LeafForm node.form ∨
      (∃ operand, node.form = .unary .bitNot operand ∧ node.requirements ≠ []) := by
  rcases shape.expressions nodes found with same | same | same | same | same | same | same | same
  all_goals subst node
  · exact .inl (shape.firstRead.form ▸ LeafForm.read _ _)
  · exact .inr ⟨_, shape.call.form, by rw [shape.call.requirements]; simp⟩
  · exact .inl (shape.conditionRead.form ▸ LeafForm.read _ _)
  · exact .inl (shape.loopSecondRead.form ▸ LeafForm.read _ _)
  · exact .inr ⟨_, shape.loopCall.form, by rw [shape.loopCall.requirements]; simp⟩
  · exact .inl (shape.stopForm ▸ LeafForm.literal (.bool "false" false))
  · exact .inl (shape.finalRead.form ▸ LeafForm.read _ _)
  · exact .inr ⟨_, shape.finalCall.form, by rw [shape.finalCall.requirements]; simp⟩

theorem SelectedRelayShape.no_direct {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node)
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation)) : False := by
  rcases shape.compiler_form nodes found with leaf | ⟨operand, unary, _⟩
  · rw [form] at leaf
    cases leaf with
    | literal atomic => cases atomic
  · rw [unary] at form
    cases form


theorem SelectedRelayShape.compiler_forms :
    ReachedMethodForms function.typedBody (fun _ => True) := by
  intro id node _ found
  rcases shape.compiler_form nodes found with leaf | ⟨operand, form, _⟩
  · exact .inl leaf
  · exact .inr (.inr (.inr (.inl ⟨_, _, form⟩)))

theorem SelectedRelayShape.compiler_requirements :
    ReachedMethodRequirements function.typedBody (fun _ => True) := by
  intro id node _ found method
  rcases shape.compiler_form nodes found with leaf | ⟨_, _, requirements⟩
  · rcases method with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
    all_goals
      rw [form] at leaf
      cases leaf with
      | literal atomic => cases atomic
  · exact requirements

theorem SelectedRelayShape.local_assignable :
    Assignable function.typedBody shape.resolution .equal := by
  refine ⟨rfl, shape.targetBare, ?_⟩
  intro binder found
  rw [shape.targetRoot, shape.local_declaration nodes] at found
  cases Except.ok.inj found
  rw [shape.localScheme, shape.targetType]
  rfl

theorem SelectedRelayShape.flag_assignable :
    Assignable function.typedBody shape.flagResolution .equal := by
  refine ⟨rfl, shape.flagTargetBare, ?_⟩
  intro binder found
  rw [shape.flagTargetRoot, shape.flag_declaration nodes] at found
  cases Except.ok.inj found
  rw [shape.flagScheme, shape.flagTargetType]
  rfl

omit nodes in
private theorem assignment_details {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    {statement : StatementNode} {assignment : AssignmentResolution} {expression : ExpressionId}
    {rest : List StatementId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope (statement.id :: rest) code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? statement.id = some statement)
    (form : statement.form = .assignValue assignment .equal expression)
    (assignable : Assignable source assignment .equal)
    (tail : ∀ {fuel scope code},
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest code) →
      remaining.Ready → remaining.closed = true ∧ remaining.bindings = []) :
    tree.closed = true ∧ tree.bindings = [] := by
  cases tree with
  | assigning read original _ remaining assigned =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at original
      cases original
      exact False.elim (ready.1 assignable)
  | assigned read original _ remaining receipt targetType =>
      exact tail remaining ready
  | initialized read original | absent read original | returning read original
  | returnUnit read original | whileLoop read original
  | discard read original | block read original | conditional read original
  | forLoop read original | forBoundary read original | breaking read original | continuing read original =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp_all
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp only [form, expanded] at outside
      cases outside


private theorem loop_details {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    (tree : Tree policy function.typedBody result reasonAt mode escaped fuel scope
      [shape.loop.id, shape.statement.id] code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked) :
    tree.closed = true ∧ tree.bindings = [] := by
  cases tree with
  | whileLoop read form _ child generated conditionType inner remaining =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.loopFound)
      cases same
      rw [shape.loopForm] at form
      cases form
      have inside : inner.closed = true ∧ inner.bindings = [] :=
        assignment_details inner ready.1 reader shape.assignmentFound shape.assignmentForm
          (shape.local_assignable nodes) (fun remaining ready =>
            assignment_details remaining ready reader shape.flagAssignmentFound shape.flagAssignmentForm
              (shape.flag_assignable nodes) (fun remaining _ => by cases remaining; exact ⟨rfl, rfl⟩))
      have tail := remaining.at_return reader shape.statementFound shape.statementForm
      simp only [Tree.closed, inside.1, tail.1, Bool.and_self, Tree.bindings,
        inside.2, tail.2.1, List.nil_append, and_self]
  | initialized read form | absent read form | returning read form | returnUnit read form
  | assigning read form | assigned read form
  | discard read form | block read form | conditional read form
  | forLoop read form | forBoundary read form | breaking read form | continuing read form =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.loopFound)
      cases same
      rw [shape.loopForm] at form
      cases form
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.loopFound)
      cases same
      simp only [shape.loopForm, expanded] at outside
      cases outside

/-- Inverting the original accepted let, loop, two writes and return closes
this exact compiler tree and identifies its only declaration. -/
theorem SelectedRelayShape.compiler_details {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    (tree : Tree policy function.typedBody result reasonAt mode escaped fuel scope shape.body code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked) :
    tree.closed = true ∧ tree.bindings.map (·.binder) = [shape.localBinder] := by
  cases tree with
  | initialized read form _ projected child generated childType remaining allocated =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.initializedFound)
      cases same
      rw [shape.initializedForm] at form
      cases form
      have tail := loop_details shape nodes remaining ready reader
      simp only [Tree.closed, Tree.bindings, List.map_cons, tail.1, tail.2,
        List.map_nil, and_self]
  | absent read form | returning read form | returnUnit read form
  | assigning read form | assigned read form | whileLoop read form
  | discard read form | block read form | conditional read form
  | forLoop read form | forBoundary read form | breaking read form | continuing read form =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.initializedFound)
      cases same
      rw [shape.initializedForm] at form
      cases form
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.initializedFound)
      cases same
      simp only [shape.initializedForm, expanded] at outside
      cases outside


omit nodes in
private theorem details_transport {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    {source : TypedSource} {statements : List StatementId}
    (sourceEq : source = function.typedBody) (roots : statements = shape.body)
    (nodes : function.typedBody.nodes = shape.nodeList)
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked) :
    tree.closed = true ∧ tree.bindings.map (·.binder) = [shape.localBinder] := by
  subst source statements
  exact shape.compiler_details nodes tree ready reader


omit nodes

section Header
variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
  {row : ObservedRow fixture signature}

/-- The original metadata check and the accepted compiler tree together issue
this Header's scoped source certificate. -/
theorem ActualHeader.relay_compiler_admission
    (shape : SelectedRelayShape row.row.function type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed row.named row.row.function.typedBody
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows))
    (metadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      fixture.recipe.compiled.indexed row.named row.row.function.typedBody
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows) = some ⟨metadata⟩)
    (supported : ∀ instantiation, CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
        fixture.recipe.compiled.indexed.base.plan instantiation) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header directRows := by
  have bodyEq : actual.header.function.body = shape.body := by
    rw [actual.aligned.function]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, shape.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have namedEq : actual.prepared.named = row.named :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named actual.prepared row.cached row.same
  have checked : ∃ receipt : PLift
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
        fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source
        (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows)),
      CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
        fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source
        (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows) = some receipt := by
    rw [namedEq, actual.source]
    exact ⟨⟨metadata⟩, metadataAccepted⟩
  obtain ⟨⟨actualMetadata⟩, actualAccepted⟩ := checked
  obtain ⟨receipt, ready⟩ := AcceptedNamedBodyRefinement.of_header actual.prepared actual.aligned
  have details := details_transport shape actual.source bodyEq nodes receipt.tree ready
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read actual.prepared actual.aligned)
  refine AcceptedNamedRefinedBodyAdmission.of_receipt actual.prepared actual.aligned receipt actualMetadata
    supported ?_ details.1 ?_ ?_ fixture.source_wellFormed
  · intro id node found callee arguments instantiation form
    rw [actual.source] at found
    exact False.elim (shape.no_direct nodes found form)
  · intro binding member
    have present := List.mem_map.mpr
      (show ∃ actual ∈ receipt.tree.bindings, actual.binder = binding.binder from ⟨binding, member, rfl⟩)
    rw [details.2] at present
    have same := List.mem_singleton.mp present
    rw [same, shape.localScheme]
    rfl
  · intro child _member ⟨residual⟩
    exact residual.impossible_methods actualMetadata
      (reached := fun _ => True)
      (by rw [actual.source]; exact shape.compiler_forms nodes)
      (fun id _ initializer => by
        obtain ⟨initializer⟩ := initializer
        have found := initializer.found
        simp only [noLocals, List.find?_nil, Option.filter_none] at found
        cases found)
      ⟨⟨fun _ _ _ _ _ _ _ _ _ _ => True.intro,
        fun _ _ _ _ _ _ _ _ => ⟨True.intro, fun _ _ => True.intro⟩⟩,
        fun _ _ _ _ _ _ _ => True.intro,
        fun _ _ _ _ _ _ _ _ => ⟨True.intro, True.intro⟩⟩
      (ReachedMethodMetadata.of_accepted actualAccepted)
      (by rw [actual.source]; exact shape.compiler_requirements nodes)
      True.intro
end Header

end Tests.SourceCoreMethodOriginEvidence
