import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveMeaning

/-! Successful ordinary Functions lowering extracts the complete primitive
syntax tree. Operator admission follows empty retained evidence and independent
source typing; actual native operand checks select Word versus Integer. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference

private theorem bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked


private def selectedUnary (operator : Syntax.UnaryOp) (operand : Ty) : UnaryOp :=
  if operator = .bitNot && operand = .integer then .integerNot else SourceCorePrimitive.unaryOperator operator
private def selectedMode (operand : Ty) : Mode := if operand = .integer then .integer else .word

private theorem UnaryProfile.selected {catalog : SourceCoreCompatibleCatalog.Catalog}
    {operator : Syntax.UnaryOp} {operand result : TypeSystem.Ty} {core : UnaryOp} {type : Ty}
    (profile : UnaryProfile operator operand result core) (projected : catalog.project operand = .ok type) :
    selectedUnary operator type = core := by
  cases profile <;> cases projected <;> rfl
private theorem BinaryProfile.selected {catalog : SourceCoreCompatibleCatalog.Catalog}
    {operator : Syntax.BinaryOp} {operand result : TypeSystem.Ty} {mode : Mode} {type : Ty}
    (profile : BinaryProfile operator operand result mode) (projected : catalog.project operand = .ok type) :
    selectedMode type = mode := by
  cases profile <;> cases projected <;> rfl

private inductive Compound : ExpressionForm → Prop where
  | unary (operator : Syntax.UnaryOp) (operand : ExpressionId) : Compound (.unary operator operand)
  | binary (operator : Syntax.BinaryOp) (left right : ExpressionId) : Compound (.binary left operator right)
  | group (inner : ExpressionId) : Compound (.group inner)
  | pair (left right : ExpressionId) : Compound (.tuple [left, right])

private inductive Step (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (context : SourceCoreFunctions.Context) (values : ValuesContext)
    (source : TypedSource) (scope : Scope) (reasonAt : ExpressionId → Word)
    (id : ExpressionId) (node : ExpressionNode) : SourceCoreBasic.LoweredExpr → Prop where
  | unary {operator operand child}
      (form : node.form = .unary operator operand)
      (metadata : Metadata values.checked source id node (selectedUnary operator child.type).resultType)
      (generated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope operand reasonAt = .ok child)
      (operandType : (selectedUnary operator child.type).operandType = child.type) :
      Step policy body fuel context values source scope reasonAt id node
        ⟨(selectedUnary operator child.type).resultType, LocalPrimitiveResults.unary (selectedUnary operator child.type) child.expression⟩
  | binary {operator left right first second}
      (form : node.form = .binary left operator right)
      (metadata : Metadata values.checked source id node ((selectedMode first.type).resultType operator))
      (firstGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope left reasonAt = .ok first)
      (secondGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope right reasonAt = .ok second)
      (leftType : (selectedMode first.type).operandType operator = first.type)
      (rightType : (selectedMode first.type).operandType operator = second.type) :
      Step policy body fuel context values source scope reasonAt id node
        ⟨(selectedMode first.type).resultType operator, (selectedMode first.type).binary operator first.expression second.expression⟩
  | group {inner lowered}
      (form : node.form = .group inner) (metadata : Metadata values.checked source id node lowered.type)
      (generated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope inner reasonAt = .ok lowered) :
      Step policy body fuel context values source scope reasonAt id node lowered
  | pair {left right first second}
      (form : node.form = .tuple [left, right])
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (firstGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope left reasonAt = .ok first)
      (secondGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope right reasonAt = .ok second) :
      Step policy body fuel context values source scope reasonAt id node
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩

private theorem step_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (compound : Compound node.form)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) context source scope id reasonAt = .ok lowered) :
    Step policy body fuel context values source scope reasonAt id node lowered := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
      bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) context childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      generalize form : node.form = shape at compound
      cases compound <;> simp only [form, readPolicy, bind, Except.bind, pure, Except.pure] at accepted
    all_goals
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error error => simp [read] at accepted
      | ok pair =>
        obtain ⟨other, type⟩ := pair
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        simp only [read, form] at accepted
        first
        | obtain ⟨child, generated, afterChild⟩ := bind_accepted accepted
          obtain ⟨output, operandChecked, afterOperand⟩ := bind_accepted afterChild
          cases output
          obtain ⟨output, resultChecked, outputEq⟩ := bind_accepted afterOperand
          cases output
          have operandType := ensureType_ok operandChecked
          have resultType := ensureType_ok resultChecked
          subst type
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .unary form metadata generated operandType
        | obtain ⟨first, generated, afterFirst⟩ := bind_accepted accepted
          obtain ⟨second, secondGenerated, afterSecond⟩ := bind_accepted afterFirst
          split at afterSecond <;>
            obtain ⟨output, firstChecked, afterChecked⟩ := bind_accepted afterSecond <;> cases output <;>
            obtain ⟨output, secondChecked, afterSecondChecked⟩ := bind_accepted afterChecked <;> cases output <;>
            obtain ⟨output, resultChecked, outputEq⟩ := bind_accepted afterSecondChecked <;> cases output
          all_goals
            rename_i branch
            have firstType := ensureType_ok firstChecked
            have secondType := ensureType_ok secondChecked
            have resultType := ensureType_ok resultChecked
            subst type
            simp only [pure, Except.pure, Except.ok.injEq] at outputEq
            subst lowered
            simpa only [selectedMode, branch, ↓reduceIte, Mode.binary, Mode.resultType] using (Step.binary form (by simpa only [selectedMode, branch, ↓reduceIte, Mode.resultType] using metadata)
              generated secondGenerated (by simpa only [selectedMode, branch, ↓reduceIte, Mode.operandType] using firstType)
              (by simpa only [selectedMode, branch, ↓reduceIte, Mode.operandType] using secondType))
        | obtain ⟨child, generated, afterChild⟩ := bind_accepted accepted
          obtain ⟨output, checked, outputEq⟩ := bind_accepted afterChild
          cases output
          have same := ensureType_ok checked
          subst type
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .group form metadata generated
        | obtain ⟨first, generated, afterFirst⟩ := bind_accepted accepted
          obtain ⟨second, secondGenerated, afterSecond⟩ := bind_accepted afterFirst
          obtain ⟨output, checked, outputEq⟩ := bind_accepted afterSecond
          cases output
          have same := ensureType_ok checked
          subst type
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .pair form metadata generated secondGenerated
  · simp [owner, bind, Except.bind] at accepted

structure PolicyFor (policy : SourceCoreFunctions.Policy) (context : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource) (scope : Scope)
    (reasonAt : ExpressionId → Word) : Prop where
  special : ∀ id, Syntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower context child budget source scope id reasonAt) = .ok none
  read : ∀ id, Syntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values



/-- Actual successful lowering and independent source typing supply every
child certificate. No semantic child assumption is part of this extraction. -/
theorem tree_of_functions_with_literals
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (literals : GenericExpressionMeaning.Certificate)
    (literalFactory : CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt literals)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree.WithLiterals (fuel := readFuel) (values := values) (source := source)
      (context := sourceContext) (solved := context.solvedRequirements) (reasonAt := reasonAt) literals scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
  | product syntaxTree =>
    refine (fun ⟨tree, sites⟩ => ⟨_, Tree.LiteralSites.product tree sites⟩) (CompatibleExpressionProducts.tree_of_functions_with_literals literals literalFactory unique declarations ?_ ?_ syntaxTree found typed accepted)
    · exact ⟨fun id child => policyFor.special id (.product child),
        fun id child => policyFor.read id (.product child), policyFor.lower, policyFor.leaf⟩
    · exact fun id node child => coercions id node (.product child)
  | unary originalFound form child ih =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ (.unary originalFound form child)) (policyFor.read _ (.unary originalFound form child)) accepted
      cases step with
      | @unary operator operand compiled otherForm metadata generated inputChecked =>
        obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (form.symm.trans otherForm)
        obtain ⟨childNode, core, childFound, childTyped, profile⟩ :=
          unary_source_types unique originalFound form metadata.coercions metadata.requirements typed
        obtain ⟨childTree, childTreeSites⟩ := ih childFound childTyped generated
        have chosen := profile.selected (childTree.projected childFound)
        rw [chosen] at metadata inputChecked ⊢
        obtain ⟨childType, childCode⟩ := compiled
        dsimp only at inputChecked childTree ⊢
        subst childType
        exact ⟨_, .unary metadata form childFound rfl rfl profile childTree childTreeSites⟩
      | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ => simp [form] at otherForm
  | binary originalFound form leftSyntax rightSyntax leftIH rightIH =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ (.binary originalFound form leftSyntax rightSyntax))
        (policyFor.read _ (.binary originalFound form leftSyntax rightSyntax)) accepted
      cases step with
      | @binary operator left right first second otherForm metadata firstGenerated secondGenerated leftChecked rightChecked =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, mode, leftFound, rightFound, sameType, leftTyped, rightTyped, profile⟩ :=
          binary_source_types unique originalFound form metadata.coercions metadata.requirements typed
        obtain ⟨firstTree, firstTreeSites⟩ := leftIH leftFound leftTyped firstGenerated
        obtain ⟨secondTree, secondTreeSites⟩ := rightIH rightFound rightTyped secondGenerated
        have chosen := profile.selected (firstTree.projected leftFound)
        rw [chosen] at metadata leftChecked rightChecked ⊢
        obtain ⟨firstType, leftCode⟩ := first
        obtain ⟨secondType, rightCode⟩ := second
        dsimp only at leftChecked rightChecked firstTree secondTree ⊢
        subst firstType secondType
        exact ⟨_, .binary metadata form leftFound rightFound rfl sameType.symm rfl profile firstTree secondTree firstTreeSites secondTreeSites⟩
      | unary otherForm _ _ _ | group otherForm _ _ | pair otherForm _ _ _ => simp [form] at otherForm
  | group originalFound form child ih =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ (.group originalFound form child)) (policyFor.read _ (.group originalFound form child)) accepted
      cases step with
      | group otherForm metadata generated =>
        have same := ExpressionForm.group.inj (form.symm.trans otherForm)
        subst_vars
        obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ :=
          CompatibleExpressionProducts.group_source_types unique originalFound form metadata.coercions typed
        obtain ⟨acceptedChild1, acceptedChild1Sites⟩ := ih innerFound childTyped generated
        exact ⟨_, .group metadata form innerFound sourceType acceptedChild1 acceptedChild1Sites⟩
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | pair otherForm _ _ _ => simp [form] at otherForm
  | pair originalFound form leftSyntax rightSyntax leftIH rightIH =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ (.pair originalFound form leftSyntax rightSyntax))
        (policyFor.read _ (.pair originalFound form leftSyntax rightSyntax)) accepted
      cases step with
      | pair otherForm metadata firstGenerated secondGenerated =>
        have same := ExpressionForm.tuple.inj (form.symm.trans otherForm)
        simp only [List.cons.injEq, and_true] at same
        obtain ⟨rfl, rfl⟩ := same
        obtain ⟨leftNode, rightNode, leftFound, rightFound, sourceType, leftTyped, rightTyped⟩ :=
          CompatibleExpressionProducts.pair_source_types unique originalFound form metadata.coercions typed
        obtain ⟨acceptedChild2, acceptedChild2Sites⟩ := leftIH leftFound leftTyped firstGenerated
        obtain ⟨acceptedChild3, acceptedChild3Sites⟩ := rightIH rightFound rightTyped secondGenerated
        exact ⟨_, .pair metadata form leftFound rightFound sourceType
          acceptedChild2 acceptedChild3 acceptedChild2Sites acceptedChild3Sites⟩
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ => simp [form] at otherForm

/-- Original tree-only API, projected from the single supported extraction. -/
theorem tree_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  exact (tree_of_functions_with_literals
    (fun _ id lowered => CompatibleExpressionLiterals.Certificate context.solvedRequirements source id lowered)
    CompatibleExpressionProducts.LiteralFactory.ordinary unique declarations policyFor coercions syntaxTree found typed accepted).choose

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
