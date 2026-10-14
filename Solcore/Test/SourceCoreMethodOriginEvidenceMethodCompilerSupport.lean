import Solcore.Test.SourceCoreMethodOriginEvidenceMethodSyntax
import Solcore.Test.SourceCoreMethodOriginEvidenceCatalog
import Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyAdmission

/-! Original finite method shapes identify the accepted compiler tree and its
children. Source typing and expression grammar are supplied by the genuine
method compilation producer, with the complete selected substitution retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open AcceptedNamedExpressionFlow AcceptedNamedBodyFlow
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)

variable {function : CheckedFunction} {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
  (shape : MethodShape function signature type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes

theorem MethodShape.local_assignable :
    Assignable function.typedBody shape.resolution .equal := by
  refine ⟨rfl, shape.targetBare, ?_⟩
  intro binder found
  rw [shape.targetRoot, shape.saved_declaration nodes] at found
  cases Except.ok.inj found
  rw [shape.savedScheme, shape.targetType]
  rfl

theorem MethodShape.flag_assignable :
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
    {rest : List StatementId} {childIds : List ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope (statement.id :: rest) code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? statement.id = some statement)
    (form : statement.form = .assignValue assignment .equal expression)
    (assignable : Assignable source assignment .equal)
    (tail : ∀ {fuel scope code},
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest code) →
      remaining.Ready → remaining.closed = true ∧ remaining.bindings = [] ∧
        remaining.children.map (·.expression) = childIds) :
    tree.closed = true ∧ tree.bindings = [] ∧
      tree.children.map (·.expression) = expression :: childIds := by
  cases tree with
  | assigning read original _ remaining assigned =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at original
      cases original
      exact False.elim (ready.1 assignable)
  | assigned read original _ remaining receipt targetType =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at original
      cases original
      obtain ⟨closed, bindings, children⟩ := tail remaining ready
      exact ⟨closed, bindings, by simpa only [Tree.children, List.map_cons] using congrArg (List.cons expression) children⟩
  | initialized read original | absent read original | returning read original
  | returnUnit read original | whileLoop read original
  | discard read original | block read original | conditional read original =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp_all
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp only [form, expanded] at outside
      cases outside


omit nodes in
private theorem returning_children {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    {statement : StatementNode} {expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope [statement.id] code)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? statement.id = some statement)
    (form : statement.form = .returnStmt (some expression)) :
    tree.children.map (·.expression) = [expression] := by
  cases tree with
  | returning read original =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at original
      cases original
      rfl
  | initialized read original | absent read original | returnUnit read original
  | whileLoop read original | assigning read original | assigned read original
  | discard read original | block read original | conditional read original =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at original
      cases original
  | boundary read outside =>
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
    tree.closed = true ∧ tree.bindings = [] ∧
      tree.children.map (·.expression) =
        [shape.conditionRead.node.id, shape.loopCall.value.node.id, shape.stop.node.id, shape.finalCall.value.node.id] := by
  cases tree with
  | whileLoop read form _ child generated conditionType inner remaining =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.loopFound)
      cases same
      rw [shape.loopForm] at form
      cases form
      have inside : inner.closed = true ∧ inner.bindings = [] ∧
          inner.children.map (·.expression) = [shape.loopCall.value.node.id, shape.stop.node.id] :=
        assignment_details inner ready.1 reader shape.assignmentFound shape.assignmentForm
          (shape.local_assignable nodes) (fun remaining ready =>
            assignment_details remaining ready reader shape.flagAssignmentFound shape.flagAssignmentForm
              (shape.flag_assignable nodes) (fun remaining _ => by cases remaining; exact ⟨rfl, rfl, rfl⟩))
      have tail := remaining.at_return reader shape.statementFound shape.statementForm
      have tailChildren := returning_children remaining reader shape.statementFound shape.statementForm
      simp only [Tree.closed, inside.1, tail.1, Bool.and_self, Tree.bindings,
        inside.2.1, tail.2.1, List.nil_append, Tree.children, List.map_cons, List.map_append,
        inside.2.2, tailChildren, List.cons_append, List.nil_append, and_self]
  | initialized read form | absent read form | returning read form | returnUnit read form
  | assigning read form | assigned read form
  | discard read form | block read form | conditional read form =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.loopFound)
      cases same
      rw [shape.loopForm] at form
      cases form
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.loopFound)
      cases same
      simp only [shape.loopForm, expanded] at outside
      cases outside

/-- The exact accepted two declarations, loop writes and return retain their
ordered expression occurrences and both original lexical binders. -/
theorem MethodShape.compiler_details {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    (tree : Tree policy function.typedBody result reasonAt mode escaped fuel scope shape.body code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked) :
    tree.closed = true ∧ tree.bindings.map (·.binder) = [shape.saved, shape.flag] ∧
      tree.children.map (·.expression) = shape.childIds := by
  cases tree with
  | initialized read form _ projected child generated childType remaining allocated =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.initializedFound)
      cases same
      rw [shape.initializedForm] at form
      cases form
      cases remaining with
      | initialized read form _ projected child generated childType remaining allocated =>
          have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.flagInitializedFound)
          cases same
          rw [shape.flagInitializedForm] at form
          cases form
          have tail := loop_details shape nodes remaining ready reader
          simp only [Tree.closed, Tree.bindings, List.map_cons, tail.1, tail.2.1,
            List.map_nil, Tree.children, tail.2.2, MethodShape.childIds, and_self]
      | absent read form | returning read form | returnUnit read form
      | assigning read form | assigned read form | whileLoop read form
      | discard read form | block read form | conditional read form =>
          have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.flagInitializedFound)
          cases same
          rw [shape.flagInitializedForm] at form
          cases form
      | boundary read outside accepted =>
          have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.flagInitializedFound)
          cases same
          simp only [shape.flagInitializedForm, expanded] at outside
          cases outside
  | absent read form | returning read form | returnUnit read form
  | assigning read form | assigned read form | whileLoop read form
  | discard read form | block read form | conditional read form =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.initializedFound)
      cases same
      rw [shape.initializedForm] at form
      cases form
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.initializedFound)
      cases same
      simp only [shape.initializedForm, expanded] at outside
      cases outside


omit nodes

def MethodShape.Reached (id : ExpressionId) : Prop :=
  id ∈ [shape.initialRead.node.id, shape.call.value.node.id, shape.initialFlag.node.id,
    shape.conditionRead.node.id, shape.loopRead.node.id, shape.loopCall.value.node.id,
    shape.stop.node.id, shape.finalRead.node.id, shape.finalCall.value.node.id]

theorem MethodShape.reached_forms : ReachedForms function.typedBody shape.Reached := by
  intro id node reached found
  simp only [Reached, List.mem_cons, List.not_mem_nil, or_false] at reached
  rcases reached with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [shape.initialRead.found] at found
    cases Option.some.inj found
    exact .inl (shape.initialRead.form ▸ LeafForm.read _ _)
  · rw [shape.call.value.found] at found
    cases Option.some.inj found
    exact .inr ⟨_, _, _, shape.call.form⟩
  · rw [shape.initialFlag.found] at found
    cases Option.some.inj found
    exact .inl (shape.initialFlagForm ▸ LeafForm.literal (.bool "true" true))
  · rw [shape.conditionRead.found] at found
    cases Option.some.inj found
    exact .inl (shape.conditionRead.form ▸ LeafForm.read _ _)
  · rw [shape.loopRead.found] at found
    cases Option.some.inj found
    exact .inl (shape.loopRead.form ▸ LeafForm.read _ _)
  · rw [shape.loopCall.value.found] at found
    cases Option.some.inj found
    exact .inr ⟨_, _, _, shape.loopCall.form⟩
  · rw [shape.stop.found] at found
    cases Option.some.inj found
    exact .inl (shape.stopForm ▸ LeafForm.literal (.bool "false" false))
  · rw [shape.finalRead.found] at found
    cases Option.some.inj found
    exact .inl (shape.finalRead.form ▸ LeafForm.read _ _)
  · rw [shape.finalCall.value.found] at found
    cases Option.some.inj found
    exact .inr ⟨_, _, _, shape.finalCall.form⟩

include nodes in
theorem MethodShape.reached_arguments : ReachedArguments function.typedBody shape.Reached := by
  intro id node _ found callee arguments instantiation form argument member
  rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [shape.initialRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · have same := (ExpressionForm.call.inj (form.symm.trans shape.call.form)).2.1
    rw [same] at member
    cases List.mem_singleton.mp member
    simp [Reached]
  · rw [shape.initialFlagForm] at form; cases form
  · rw [shape.conditionRead.form] at form; cases form
  · rw [shape.loopRead.form] at form; cases form
  · rw [shape.loopCall.calleeForm] at form; cases form
  · have same := (ExpressionForm.call.inj (form.symm.trans shape.loopCall.form)).2.1
    rw [same] at member
    cases List.mem_singleton.mp member
    simp [Reached]
  · rw [shape.stopForm] at form; cases form
  · rw [shape.finalRead.form] at form; cases form
  · rw [shape.finalCall.calleeForm] at form; cases form
  · have same := (ExpressionForm.call.inj (form.symm.trans shape.finalCall.form)).2.1
    rw [same] at member
    cases List.mem_singleton.mp member
    simp [Reached]

include nodes in
theorem MethodShape.direct_coverage {directRows : List SourceSpecialization.SpecializedFunction}
    (first : DirectSite directRows shape.call.instantiation)
    (loop : DirectSite directRows shape.loopCall.instantiation)
    (last : DirectSite directRows shape.finalCall.instantiation) :
    ∀ id node, function.typedBody.lookupExpression? id = some node →
      ∀ callee arguments instantiation,
      node.form = .call callee arguments (.declaration instantiation) → DirectSite directRows instantiation := by
  intro id node found callee arguments instantiation form
  rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [shape.initialRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · have same := CallResolution.declaration.inj ((ExpressionForm.call.inj (form.symm.trans shape.call.form)).2.2)
    exact same ▸ first
  · rw [shape.initialFlagForm] at form; cases form
  · rw [shape.conditionRead.form] at form; cases form
  · rw [shape.loopRead.form] at form; cases form
  · rw [shape.loopCall.calleeForm] at form; cases form
  · have same := CallResolution.declaration.inj ((ExpressionForm.call.inj (form.symm.trans shape.loopCall.form)).2.2)
    exact same ▸ loop
  · rw [shape.stopForm] at form; cases form
  · rw [shape.finalRead.form] at form; cases form
  · rw [shape.finalCall.calleeForm] at form; cases form
  · have same := CallResolution.declaration.inj ((ExpressionForm.call.inj (form.symm.trans shape.finalCall.form)).2.2)
    exact same ▸ last

include nodes in
private theorem method_details_transport {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    {statements : List StatementId}
    (roots : statements = shape.body)
    (tree : Tree policy function.typedBody result reasonAt mode escaped fuel scope statements code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked) :
    tree.closed = true ∧ tree.bindings.map (·.binder) = [shape.saved, shape.flag] ∧
      tree.children.map (·.expression) = shape.childIds := by
  subst statements
  exact shape.compiler_details nodes tree ready reader

/-- The complete method Source certificate comes from the same cached body and
final-plan selector. The finite shape only identifies original source nodes. -/
theorem method_compiler_admission
    {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
    (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (selected : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method)
    (parameters : selected.implementation.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) method.specialized.parameterSubstitution)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    {signature : ProgramFunctionSignature}
    (shape : MethodShape cached.named.specialized.function signature cached.named.specialized.function.inferredBodyType)
    (nodes : cached.named.specialized.function.typedBody.nodes = shape.nodeList)
    (noLocals : compiled.indexed.base.locals.bindings = [])
    (first : DirectSite table.rows shape.call.instantiation)
    (loop : DirectSite table.rows shape.loopCall.instantiation)
    (last : DirectSite table.rows shape.finalCall.instantiation) :
    Nonempty (CallableIndexedOwnedPreparedScopedMethodAdmission.SourceCertificate compiled cached.named table.rows) := by
  obtain ⟨receipt, ready⟩ := AcceptedMethodBodyReceipts.of_cached cached
  have bodyEq : cached.compilation.statements = shape.body := by
    rw [← AcceptedMethodBodyAdmission.roots cached]
    simp only [AcceptedMethodBodyReceipts.source, CallableIndexedNamedGeneration.source,
      CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements, shape.roots,
      List.filterMap_cons, List.filterMap_nil, MethodShape.body]
  have details := method_details_transport shape nodes bodyEq receipt.tree ready (AcceptedMethodBodyReceipts.read cached)
  apply AcceptedMethodBodyAdmission.of_selection cached checked selected parameters range wellFormed table receipt
    (shape.direct_source nodes) (shape.metadata nodes cached.named noLocals)
    (shape.direct_coverage nodes first loop last) shape.reached_forms (shape.reached_arguments nodes)
  · intro id _ ⟨initializer⟩
    have found := initializer.found
    simp only [noLocals, List.find?_nil, Option.filter_none] at found
    cases found
  · intro child member
    have present := (congrArg (fun ids => child.expression ∈ ids) details.2.2).mp
      (List.mem_map_of_mem member)
    simp only [MethodShape.childIds, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with same | same | same | same | same | same
    all_goals simp [MethodShape.Reached, same]
  · exact details.1
  · intro binding member
    have present := (congrArg (fun binders => binding.binder ∈ binders) details.2.1).mp
      (List.mem_map_of_mem member)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with same | same
    · rw [same, shape.savedScheme]; rfl
    · rw [same, shape.flagScheme]; rfl

end Tests.SourceCoreMethodOriginEvidence
