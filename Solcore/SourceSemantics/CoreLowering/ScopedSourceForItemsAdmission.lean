import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree

/-! Original for-item certificates thread the exact lexical context recovered
from genuine Source typing. The accepted compiler supplies these finite receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceForItemsAdmission
open Core Frontend SourceInference

inductive Scan (source : TypedSource) (approved : ExpressionId → Prop) : List ForItemForm → Prop where
  | nil : Scan source approved []
  | absent {binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Scan source approved rest) : Scan source approved (.letDecl binder none :: rest)
  | initialized {binder expression expressionNode rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (found : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = binder.scheme.body) (value : approved expression)
      (remaining : Scan source approved rest) : Scan source approved (.letDecl binder (some expression) :: rest)
  | discard {expression expressionNode rest}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : approved expression) (remaining : Scan source approved rest) :
      Scan source approved (.expression expression :: rest)
  | assign {assignment operator rhs rhsNode binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (targetType : binder.scheme.body = assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type) (value : approved rhs)
      (remaining : Scan source approved rest) : Scan source approved (.assignValue assignment operator rhs :: rest)

theorem Scan.map {source : TypedSource} {approved other : ExpressionId → Prop} {items : List ForItemForm}
    (scan : Scan source approved items) (mapped : ∀ id, approved id → other id) : Scan source other items := by
  induction scan with
  | nil => exact .nil
  | absent declaration mono ordinary _ ih => exact .absent declaration mono ordinary ih
  | initialized declaration mono ordinary found type value _ ih => exact .initialized declaration mono ordinary found type (mapped _ value) ih
  | discard found value _ ih => exact .discard found (mapped _ value) ih
  | assign declaration target profile bare found type value _ ih => exact .assign declaration target profile bare found type (mapped _ value) ih

theorem Scan.shape {source approved items} (scan : Scan source approved items) :
    CallableIndexedOwnedPreparedStagedBranchingTree.ItemShape items := by
  induction scan with
  | nil => exact .nil
  | absent _ _ _ _ ih => exact .absent ih
  | initialized _ _ _ _ _ _ _ ih => exact .initialized ih
  | discard _ _ _ ih => exact .discard ih
  | assign _ _ profile bare _ _ _ _ ih => exact .assign profile bare ih

private theorem expression_at {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) : ExpressionHasType source context id node.type := by
  obtain ⟨original, contains, same⟩ := typed.stored_type
  cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact same ▸ typed

/-- Original assignment typing supplies the actual writable root and raw RHS type.
The bare path keeps this fact on the declared binder used by the compiler. -/
theorem assignment_facts {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp}
    {rhs : ExpressionId} {binder : TypedBinder}
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (targetType : binder.scheme.body = assignment.target.type)
    (bare : assignment.target.projections = [])
    (typed : SourceAssignmentHasType source context assignment operator rhs) :
    (∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
      SourceProjectionsHaveType source context actual.scheme.body assignment.target.projections assignment.target.type) ∧
    (∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
      WritableLocal context assignment.target.root actual.scheme.body) ∧
    ExpressionHasType source context rhs assignment.target.type ∧
    (operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer) := by
  have original : ∃ type, SourcePlaceHasType source context assignment.target type ∧
      ExpressionHasType source context rhs type ∧ (operator = .equal ∨ type = .word) := by
    cases typed with
    | equal place value _ => exact ⟨_, place, value, .inl rfl⟩
    | wordCompound _ place value _ => exact ⟨_, place, value, .inr rfl⟩
  obtain ⟨type, place, value, profile⟩ := original
  cases place with
  | intro writable projections target =>
      refine ⟨?_, ?_, target.symm ▸ value, ?_⟩
      · intro actual actualFound
        cases Except.ok.inj (declaration.symm.trans actualFound)
        rw [targetType, bare]
        exact .nil _
      · intro actual actualFound
        cases Except.ok.inj (declaration.symm.trans actualFound)
        rw [bare] at projections
        cases projections
        exact targetType.symm ▸ target.symm ▸ writable
      · rcases profile with equal | word
        · exact .inl equal
        · exact .inr (.inl (by rw [target, word]; rfl))

theorem Scan.syntax {source approved items} (scan : Scan source approved items)
    (unique : NodeOccurrencesUnique source) {control : ControlContext}
    {context final : SourceSemantics.Context}
    (typed : ForItemsHaveType source control context items final) :
    GenericForHeader.Syntax source approved context items := by
  induction scan generalizing context final with
  | nil => exact .nil
  | absent declaration monomorphic ordinary remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | letUninitialized _ _ extended => exact .uninitialized declaration monomorphic extended ordinary (ih tail)
  | initialized declaration monomorphic ordinary found valueType value remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | letInitialized actual _ _ extended =>
          exact .initialized declaration monomorphic extended ordinary found valueType
            (expression_at unique found actual) value (ih tail)
        | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly monomorphic)
  | discard found value remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | expression actual => exact .discard found (expression_at unique found actual) value (ih tail)
  | assign declaration targetType profile bare rhsFound rhsType value remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | assignValue assignment =>
          obtain ⟨sourceTyped, writable, rightTyped, numeric⟩ :=
            assignment_facts declaration targetType bare assignment
          apply GenericForHeader.Syntax.assign sourceTyped writable rightTyped numeric
          · intro child member
            simp only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
            subst child
            exact ⟨value, _, rhsFound, expression_at unique rhsFound rightTyped⟩
          · exact ih tail


private theorem binder_final {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binder : TypedBinder} (first : BinderExtends owner context binder left)
    (second : BinderExtends owner context binder right) : left = right := by
  cases first
  cases second
  rfl

/-- A header's actual typing fixes the context at its continuation. -/
theorem initializers {source : TypedSource} {approved : ExpressionId → Prop}
    {context final : SourceSemantics.Context} {control : ControlContext}
    {items : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
    {body : List StatementId} {expected : TypeSystem.Ty}
    (tree : GenericForHeader.Syntax source approved context items)
    (typed : ForItemsHaveType source control context items final)
    (next : GenericImperativeMatch.Syntax source approved final (.initializers [] condition post body) expected) :
    GenericImperativeMatch.Syntax source approved context (.initializers items condition post body) expected := by
  induction tree generalizing final with
  | nil => cases typed; exact next
  | uninitialized declaration monomorphic extended ordinary remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | letUninitialized _ _ other =>
          have same := binder_final extended other
          subst_vars
          exact .initializerUninitialized declaration monomorphic extended ordinary (ih tail next)
  | initialized declaration monomorphic extended ordinary found sourceType child value remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | letInitialized _ _ _ other =>
          have same := binder_final extended other
          subst_vars
          exact .initializerInitialized declaration monomorphic extended ordinary found sourceType child value (ih tail next)
        | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly monomorphic)
  | discard found child value remaining ih =>
      cases typed with
      | cons head tail =>
        cases head
        exact .initializerDiscard found child value (ih tail next)
  | assign sourceTyped writable rightTyped profile children remaining ih =>
      cases typed with
      | cons head tail =>
        cases head
        exact .initializerAssign sourceTyped writable rightTyped profile children (ih tail next)
  | bitNot writable bare profile remaining ih =>
      cases typed with
      | cons head tail =>
        cases head
        exact .initializerBitNot writable bare profile (ih tail next)

end Solcore.SourceSemantics.CoreLowering.ScopedSourceForItemsAdmission
