import Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchRequests
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyShape
import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyCompletionTyping
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedForItemsSyntax
import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSyntaxFacts

/-! The compiler-issued tree supplies statement shape. Independent original
Source typing supplies annotations and lexical context changes. The remaining
inputs concern actual expression children and allocated binder declarations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

/-- The real compatible reader returns the original stored node. -/
theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
        simp only [found] at accepted
        obtain ⟨projected, _, same⟩ := bind_ok accepted
        cases same
        rfl

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

private theorem returned_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : Option ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt expression)
    (typed : StatementHasType source control context id final facts) : node.type = control.returnType := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

private theorem discard_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression true)
    (typed : StatementHasType source control context id final facts) : node.type = .unit := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

private theorem value_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression false)
    (typed : StatementHasType source control context id final facts) :
    ExpressionHasType source context expression node.type := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

private theorem conditional_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {condition : ExpressionId}
    {left : List StatementId} {right : Option (List StatementId)}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition left right)
    (typed : StatementHasType source control context id final facts) :
    node.type = .unit ∨ node.type = control.returnType := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all
  all_goals
    split at * <;> simp_all

private theorem for_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {initializer post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initializer condition post body)
    (typed : StatementHasType source control context id final facts) : node.type = .unit := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

/-- The support boundary is tested on the issued compiler tree. No separate
statement recognizer result or preconstructed body shape occurs here. -/
theorem Tree.scan_complete {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    {control : ControlContext}
    (closed : tree.complete control.returnType = true) (unique : NodeOccurrencesUnique source)
    (ownership : LocalIdentityOwnership source)
    {approved : ExpressionId → Prop}
    (children : ∀ child ∈ tree.children, approved child.expression)
    (bindings : ∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    ScopedSourceBodyAdmission.Scan source approved control.returnType mode statements := by
  induction tree generalizing control context final facts with
  | @nil actualMode _ _ _ =>
      cases actualMode with
      | false => exact .nil (.inl rfl)
      | true => exact .nil (.inr (by simpa [Tree.complete] using closed))
  | breaking read form _ => exact .breaking _ (read_found (readPolicy ▸ read)) form
  | continuing read form _ => exact .continuing _ (read_found (readPolicy ▸ read)) form
  | boundary | assigning | bitNotting | forBoundary | matching => cases closed
  | returning read form statementType child generated childType =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have annotation := returned_annotation unique found form head
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | returnValue value =>
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .returning _ found form annotation (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
  | returnUnit read form statementType unitType =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have annotation := returned_annotation unique found form head
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | returnUnit result => exact .returnUnit _ found form (annotation.trans result) result
  | initialized read form statementType projected child generated childType remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      have binder := bindings ⟨_, _, _, projected⟩ (by simp [Tree.bindings])
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letInitialized value _ _ =>
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .initialized found form binder.1 binder.2.1 binder.2.2
            (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
            (ih closed (fun child member => children child (by simp [Tree.children, member]))
              (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly binder.2.1)
  | absent read form statementType projected remaining allocated ih =>
      have found := read_found (readPolicy ▸ read)
      have binder := bindings ⟨_, _, _, projected⟩ (by simp [Tree.bindings])
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letUninitialized _ _ =>
          exact .absent found form binder.1 binder.2.1 binder.2.2
            (ih closed (fun child member => children child (by simpa [Tree.children] using member))
              (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)

  | assigned read form statementType remaining receipt targetType ih =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | assignValue assignment =>
        obtain ⟨_, _, value, _⟩ :=
          ScopedSourceForItemsAdmission.assignment_facts receipt.declaration targetType receipt.bare assignment
        obtain ⟨node, contains, same⟩ := value.stored_type
        exact .assign found form receipt.declaration targetType receipt.sourceProfile receipt.bare
          (lookupExpression?_complete unique contains) same
          (children ⟨_, _, _, receipt.child, receipt.generated⟩ (by simp [Tree.children]))
          (ih closed (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simpa only [Tree.bindings] using member)) tail)
  | bitNotted read form statementType remaining receipt targetType ih =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | assignBitNot assignment =>
        exact .bitNot found form receipt.declaration targetType receipt.sourceProfile receipt.bare
          (ih closed (fun child member => children child (by simpa only [Tree.children] using member))
            (fun binding member => bindings binding (by simpa only [Tree.bindings] using member)) tail)
  | discard read form child generated statementType remaining ih =>
      have found := read_found (readPolicy ▸ read)
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have annotation := discard_annotation unique found form head
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | expressionDiscard value =>
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .discard found form (.inl rfl) (by simpa only [Bool.true_eq, ↓reduceIte] using annotation)
            (lookupExpression?_complete unique contains)
            (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
            (ih closed (fun child member => children child (by simp [Tree.children, member]))
              (fun binding member => bindings binding (by simpa only [Tree.bindings] using member)) tail)
  | tailValue read form child generated statementType childType =>
      have found := read_found (readPolicy ▸ read)
      have raw : _ = control.returnType := of_decide_eq_true closed
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have value := value_annotation unique found form head
      obtain ⟨node, contains, same⟩ := value.stored_type
      exact .tail found form raw (lookupExpression?_complete unique contains) (same.trans raw)
        (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
  | valueDiscard read form notTail child generated statementType remaining ih =>
      have found := read_found (readPolicy ▸ read)
      have both := closed
      simp only [Tree.complete, Bool.and_eq_true] at both
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have value := value_annotation unique found form head
      obtain ⟨node, contains, same⟩ := value.stored_type
      exact .discard found form (.inr (by simpa using both.1)) (by simpa using same.symm)
        (lookupExpression?_complete unique contains)
        (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
        (ih both.2 (fun child member => children child (by simp [Tree.children, member]))
          (fun binding member => bindings binding (by simpa only [Tree.bindings] using member)) tail)
  | block read form inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have both := closed
      simp only [Tree.complete, Bool.and_eq_true, Bool.or_eq_true] at both
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | block body =>
          have innerScan := innerIH both.1.1
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) body
          rcases both.2 with tailComplete | stopped
          · exact .block found form innerScan
              (tailIH tailComplete
                (fun child member => children child (by simp [Tree.children, member]))
                (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)
          · have stop := AcceptedCompilerBodyCompletion.Stops.original stopped
            exact .terminalBlock found form
              (ScopedSourceBodyAdmission.stopped_statement_result unique found (.block found form stop) head)
              innerScan stop (remaining.formed_shape readPolicy both.1.2)
  | conditional read form child generated conditionType left right remaining leftIH rightIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have allComplete := closed
      simp only [Tree.complete, Bool.and_eq_true, Bool.or_eq_true] at allComplete
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have annotation := conditional_annotation unique found form head
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | ifWithoutElse condition body =>
          obtain ⟨node, contains, same⟩ := condition.stored_type
          have tailComplete := allComplete.2.resolve_right (by
            intro stopped
            have impossible := (AcceptedCompilerBodyCompletion.Stops.original stopped.2).nonempty
            exact impossible rfl)
          exact .conditional found form annotation (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
            (leftIH allComplete.1.1.1
              (fun child member => children child (by simp [Tree.children, member]))
              (fun binding member => bindings binding (by simp [Tree.bindings, member])) body)
            (rightIH allComplete.1.1.2
              (fun child member => children child (by simp [Tree.children, member]))
              (fun binding member => bindings binding (by simp [Tree.bindings, member])) (.nil control context))
            (tailIH tailComplete
              (fun child member => children child (by simp [Tree.children, member]))
              (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)
      | ifWithElse condition first second =>
          obtain ⟨node, contains, same⟩ := condition.stored_type
          have firstScan := leftIH allComplete.1.1.1
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) first
          have secondScan := rightIH allComplete.1.1.2
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) second
          rcases allComplete.2 with tailComplete | stopped
          · exact .conditional found form annotation (lookupExpression?_complete unique contains) same
              (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children])) firstScan secondScan
              (tailIH tailComplete
                (fun child member => children child (by simp [Tree.children, member]))
                (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)
          · have firstStop := AcceptedCompilerBodyCompletion.Stops.original stopped.1
            have secondStop := AcceptedCompilerBodyCompletion.Stops.original stopped.2
            exact .terminalConditional found form
              (ScopedSourceBodyAdmission.stopped_statement_result unique found
                (.conditional found form firstStop secondStop) head)
              (lookupExpression?_complete unique contains) same
              (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children])) firstScan secondScan
              firstStop secondStop (remaining.formed_shape readPolicy allComplete.1.2)
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have both : inner.complete control.returnType = true ∧ remaining.complete control.returnType = true := by simpa only [Tree.complete, Bool.and_eq_true_iff] using closed
      obtain ⟨innerClosed, tailClosed⟩ := both
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | whileLoop condition body =>
        obtain ⟨node, contains, same⟩ := condition.stored_type
        exact .whileLoop found form (lookupExpression?_complete unique contains) same
          (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
          (innerIH (control := control.enterLoop) innerClosed
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) body)
          (tailIH tailClosed
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)

  | matched read form receipt branches remaining branchIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have allComplete := closed
      simp only [Tree.complete, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at allComplete
      obtain ⟨scrutinee, scrutineeFound⟩ := ScopedSourceMatchAdmission.scrutinee_found receipt.certificate
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      obtain ⟨same, caseFacts, _, caseTyped, defaultTyped⟩ :=
        ScopedSourceMatchAdmission.statement_sites unique found form scrutineeFound head
      subst_vars
      have childScans : ∀ request ∈ receipt.requests,
          ScopedSourceBodyAdmission.Scan source approved control.returnType false request.statements := by
        intro request member
        obtain ⟨child, last, bodyFacts, _, body⟩ := ScopedSourceMatchAdmission.original_context
          caseTyped defaultTyped (receipt.original request member)
        exact branchIH request member (allComplete.1.1 ⟨request, member⟩ (List.mem_attach _ _))
          (fun entry present => children entry (by
            simp only [Tree.children, List.mem_cons, List.mem_append]
            exact .inr (.inl (List.mem_flatMap.mpr ⟨⟨request, member⟩, List.mem_attach _ _, present⟩))))
          (fun entry present => bindings entry (by
            simp only [Tree.bindings, List.mem_append]
            exact .inl (List.mem_flatMap.mpr ⟨⟨request, member⟩, List.mem_attach _ _, present⟩))) body
      rcases allComplete.2 with tailComplete | stopped
      · exact ScopedSourceMatchAdmission.matching_scan receipt.certificate ownership found form scrutineeFound
          (children ⟨_, _, _, receipt.child, receipt.generated⟩ (by simp [Tree.children])) childScans
          (tailIH tailComplete
            (fun entry present => children entry (by simp [Tree.children, present]))
            (fun entry present => bindings entry (by simp [Tree.bindings, present])) tail)
      · simp only [AcceptedCompilerBodyCompletion.matchStops, Bool.and_eq_true] at stopped
        obtain ⟨defaultBody, present, defaultStops⟩ := (Option.any_eq_true _ _).mp stopped.2
        have stoppedArms := fun arm member => AcceptedCompilerBodyCompletion.Stops.original
          (List.all_eq_true.mp stopped.1 arm member)
        have stoppedDefault := AcceptedCompilerBodyCompletion.Stops.original defaultStops
        obtain ⟨hiddenOrdinary, armsOrdinary⟩ := ScopedSourceMatchAdmission.ordinary_bindings ownership found form
        apply ScopedSourceBodyAdmission.Scan.terminalMatch found form
          (ScopedSourceBodyAdmission.stopped_statement_result unique found
            (.matching found form present stoppedArms stoppedDefault) head)
          scrutineeFound (children ⟨_, _, _, receipt.child, receipt.generated⟩ (by simp [Tree.children]))
          hiddenOrdinary armsOrdinary
        · intro arm member
          obtain ⟨request, member, same⟩ := ScopedSourceMatchAdmission.arm_request receipt.certificate member
          exact same ▸ childScans request member
        · intro statements present
          obtain ⟨request, member, same⟩ := ScopedSourceMatchAdmission.default_request receipt.certificate present
          exact same ▸ childScans request member
        · exact present
        · exact stoppedArms
        · exact stoppedDefault
        · exact remaining.formed_shape readPolicy allComplete.1.2

  | forLoop read form statementType child generated conditionType initial inner after remaining innerIH tailIH =>
      have found := read_found (readPolicy ▸ read)
      have allClosed := closed
      simp only [Tree.complete, Bool.and_eq_true_iff] at allClosed
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have nodeUnit := for_annotation unique found form head
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | forLoop initTyped condition body postTyped =>
        obtain ⟨node, contains, same⟩ := condition.stored_type
        exact .forLoop found form nodeUnit
          (initial.scan allClosed.1.1.1 unique
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) initTyped)
          (lookupExpression?_complete unique contains) same
          (children ⟨_, _, _, child, generated⟩ (by simp [Tree.children]))
          (innerIH (control := control.enterLoop) allClosed.1.1.2
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) body)
          (after.scan allClosed.1.2 unique
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) postTyped)
          (tailIH allClosed.2
            (fun child member => children child (by simp [Tree.children, member]))
            (fun binding member => bindings binding (by simp [Tree.bindings, member])) tail)

theorem Tree.scan {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (closed : tree.closed = true) (unique : NodeOccurrencesUnique source)
    (ownership : LocalIdentityOwnership source)
    {approved : ExpressionId → Prop}
    (children : ∀ child ∈ tree.children, approved child.expression)
    (bindings : ∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    ScopedSourceBodyAdmission.Scan source approved control.returnType mode statements := by
  exact tree.scan_complete readPolicy (tree.closed_complete closed control.returnType)
    unique ownership children bindings typed

/-- A returned compiler branch has exactly its original expression child and
no executed suffix, even if the source root list retains dead statements. -/
theorem Tree.at_return {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : StatementId} {rest : List StatementId}
    {code : Expr} {node : StatementNode} {expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope (id :: rest) code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression)) :
    tree.closed = true ∧ tree.bindings = [] ∧
      ∀ child ∈ tree.children, child.expression = expression := by
  cases tree with
  | returning read original statementType child generated childType =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all [Tree.closed, Tree.bindings, Tree.children]
  | returnUnit read original statementType unitType =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | initialized read original statementType projected child generated childType tail allocated =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | absent read original statementType projected tail allocated =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | assigning read original _ _ _ | assigned read original _ _ _ _ | bitNotting read original _ _ _ | bitNotted read original _ _ _ _ | whileLoop read original _ _ _ _ _ _
      | discard read original _ _ _ _ | valueDiscard read original _ _ _ _ _ | tailValue read original _ _ _ _ | block read original _ _ | conditional read original _ _ _ _ _ _ =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | forLoop read original _ _ _ _ _ _ _ _ | forBoundary read original _ _
      | matching read original _ _ _ | matched read original _ _ _ =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | breaking read original _ | continuing read original _ =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp_all
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      cases same
      simp only [form, expanded] at outside
      cases outside


theorem Tree.at_return_list {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {id : StatementId} {rest : List StatementId} {code : Expr} {node : StatementNode} {expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (same : statements = id :: rest)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression)) :
    tree.closed = true ∧ tree.bindings = [] ∧
      ∀ child ∈ tree.children, child.expression = expression := by
  subst statements
  exact tree.at_return readPolicy found form

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
