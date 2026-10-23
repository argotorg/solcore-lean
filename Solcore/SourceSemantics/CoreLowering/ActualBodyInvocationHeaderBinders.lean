import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationInitializerReceipt

/-! The actual native catalog is built from statement declarations. A header
binder accepted by the same policy is therefore monomorphic: source ownership
prevents a header and a catalog statement from defining the same local ID. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference SourceCoreLocalPolymorphism

private theorem same_node_of_defined {nodes : List Node}
    (unique : (nodes.flatMap Node.definedLocalIds).Nodup)
    {left right : Node} (lm : left ∈ nodes) (rm : right ∈ nodes)
    {id : Resolved.LocalId} (ld : id ∈ left.definedLocalIds) (rd : id ∈ right.definedLocalIds) :
    left = right := by
  induction nodes with
  | nil => cases lm
  | cons head rest ih =>
    obtain ⟨_, tailUnique, disjoint⟩ := List.nodup_append.mp unique
    rcases List.mem_cons.mp lm with leftHead | leftTail
    · rcases List.mem_cons.mp rm with rightHead | rightTail
      · exact leftHead.trans rightHead.symm
      · exact False.elim (disjoint id (leftHead ▸ ld) id
          (List.mem_flatMap.mpr ⟨right, rightTail, rd⟩) rfl)
    · rcases List.mem_cons.mp rm with rightHead | rightTail
      · exact False.elim (disjoint id (rightHead ▸ rd) id
          (List.mem_flatMap.mpr ⟨left, leftTail, ld⟩) rfl)
      · exact ih tailUnique leftTail rightTail


private theorem binding_member {catalog : Catalog} {caller : Key} {binder : Resolved.LocalId}
    {binding : Binding} (located : catalog.binding caller binder = .ok binding) :
    binding ∈ catalog.bindings := by
  unfold Catalog.binding at located
  split at located
  · cases located
  · next actual only =>
    cases located
    have member : binding ∈ [binding] := List.mem_singleton_self _
    rw [← only] at member
    exact (List.mem_filter.mp member).1
  · cases located

/-- The concrete accepted header policy cannot select a generalized native
statement binding at a distinct source definition. No header restriction is
assumed: the result follows from that policy's success and checked ownership. -/
theorem Index.header_binder_monomorphic
    {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}
    (index : Index compiled bodyRelation)
    {workspace : Workspace.RawWorkspace} {fuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some compiled)
    (checked : checkProgram workspace fuel = .ok sourceCompiled.program)
    {id : StatementId} {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initial condition post body)
    {binder : TypedBinder} {initializer : Option ExpressionId}
    (present : ForItemForm.letDecl binder initializer ∈ initial ++ post)
    {scope : Scope} {type : Ty}
    (accepted : index.policy.lowerBinder index.compilerSource scope binder = .ok type) :
    binder.scheme.quantified = [] := by
  by_cases generalized : binder.scheme.quantified = []
  · exact generalized
  exfalso
  obtain ⟨binding, located, _metadata, _type⟩ := lowerBinder_success (index.generalized_binder generalized accepted)
  obtain ⟨origin, owner, sameId⟩ := SelectedCompilationBindingOrigins.at_binding compiled located
  have sameSource := index.native_binding_source (binding_member located) owner
  obtain ⟨recorded, recordedMember, recordedForm⟩ := origin.statement
  rw [sameSource] at recordedMember
  have ownership : LocalIdentityOwnership index.compilerSource := by
    rw [index.compiler_original]
    exact FlexibleSubstitution.LocalIdentityOwnership.applySubstitution index.active
      (index.original_source_resources artifact checked).2
  have unique : (index.compilerSource.nodes.flatMap Node.definedLocalIds).Nodup :=
    (List.nodup_append.mp (show (index.compilerSource.inputs.map (·.id) ++
        index.compilerSource.nodes.flatMap Node.definedLocalIds).Nodup from by
      simpa only [definedLocalIds, ← flatMapNodeDefinedLocalIds_eq_carrier] using ownership.unique)).2.1
  have recordedApplied : Node.statement (recorded.applySubstitution index.active) ∈ index.compilerSource.nodes := by
    rw [index.compiler_original]
    exact List.mem_map.mpr ⟨.statement recorded, recordedMember, rfl⟩
  have recordedId : binder.id ∈ (Node.statement (recorded.applySubstitution index.active)).definedLocalIds := by
    simp only [Node.definedLocalIds, StatementForm.definedLocalIds,
      StatementNode.applySubstitution, recordedForm, StatementForm.applySubstitution,
      TypedBinder.applySubstitution, sameId]
    exact List.mem_singleton_self _
  have actualId : binder.id ∈ (Node.statement statement).definedLocalIds := by
    change binder.id ∈ statement.form.definedLocalIds
    rw [form]
    change binder.id ∈ initial.flatMap ForItemForm.definedLocalIds ++ post.flatMap ForItemForm.definedLocalIds
    rw [← List.flatMap_append]
    exact List.mem_flatMap.mpr ⟨.letDecl binder initializer, present, List.mem_singleton_self _⟩
  have same := same_node_of_defined unique recordedApplied (lookupStatement?_sound found).1 recordedId actualId
  have sameStatement := Node.statement.inj same
  have incompatible := congrArg StatementNode.form sameStatement
  simp only [StatementNode.applySubstitution, recordedForm, StatementForm.applySubstitution, form] at incompatible
  cases incompatible

private theorem item_binding_form
    {policy : SourceCoreLoops.Policy} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {result : Ty} {reasonAt : ExpressionId → Word}
    {next : Scope → Except SourceCoreBasic.Error Expr} {finalScope : Scope} {finish : Expr}
    {fuel : Nat} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : AcceptedNamedBodyFlow.Items policy source site result reasonAt next finalScope finish fuel scope items code) :
    ∀ selected ∈ tree.bindings, ∃ initializer, ForItemForm.letDecl selected.binder initializer ∈ items := by
  induction tree with
  | nil same accepted => intro selected member; cases member
  | absent projected remaining allocated ih =>
    intro selected member
    rcases List.mem_cons.mp member with head | tail
    · subst selected
      exact ⟨none, List.mem_cons_self⟩
    · obtain ⟨initializer, present⟩ := ih selected tail
      exact ⟨initializer, List.mem_cons_of_mem _ present⟩
  | initialized projected child generated childType remaining allocated ih =>
    intro selected member
    rcases List.mem_cons.mp member with head | tail
    · subst selected
      exact ⟨some _, List.mem_cons_self⟩
    · obtain ⟨initializer, present⟩ := ih selected tail
      exact ⟨initializer, List.mem_cons_of_mem _ present⟩
  | discard child generated remaining ih
  | assigning remaining accepted ih
  | assigned remaining receipt targetType ih
  | projectedAssigned remaining receipt route ih
  | bitNotting remaining accepted ih
  | bitNotted remaining receipt targetType ih
  | projectedBitNotted remaining receipt route ih =>
    intro selected member
    obtain ⟨initializer, present⟩ := ih selected member
    exact ⟨initializer, List.mem_cons_of_mem _ present⟩

/-- Every actual header binding receipt, including a suffix of either list,
inherits the result from its successful policy action and enclosing for node. -/
theorem Index.header_bindings_monomorphic
    {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}
    (index : Index compiled bodyRelation)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some compiled)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    {id : StatementId} {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initial condition post body)
    {site : SourceCoreElaboration.ErrorSite} {result : Ty} {reasonAt : ExpressionId → Word}
    {next : Scope → Except SourceCoreBasic.Error Expr} {finalScope : Scope} {finish : Expr}
    {fuel : Nat} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : AcceptedNamedBodyFlow.Items index.policy index.compilerSource site result reasonAt
      next finalScope finish fuel scope items code)
    (included : ∀ item ∈ items, item ∈ initial ++ post) :
    ∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = [] := by
  intro binding member
  obtain ⟨initializer, present⟩ := item_binding_form tree binding member
  exact index.header_binder_monomorphic artifact checked found form (included _ present) binding.projected

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
