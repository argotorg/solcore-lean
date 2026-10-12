import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductMeaning

/-! Actual shared compiler receipts for the finite product fragment. Source
product and group types come from independent typing. Successful child compiler
results are eliminated by the structural extraction induction. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
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

private inductive Compound : ExpressionForm → Prop where
  | read (name : String) (binder : Resolved.LocalId) : Compound (.reference name (.local binder))
  | group (inner : ExpressionId) : Compound (.group inner)
  | pair (left right : ExpressionId) : Compound (.tuple [left, right])

private inductive Step (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel readFuel : Nat) (context : SourceCoreFunctions.Context) (values : ValuesContext)
    (source : TypedSource) (scope : Scope) (reasonAt : ExpressionId → Word)
    (id : ExpressionId) (node : ExpressionNode) : SourceCoreBasic.LoweredExpr → Prop where
  | read {name binder lowered}
      (form : node.form = .reference name (.local binder))
      (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
      (generated : SourceCoreCompatibleDataExpressions.lowerRead readFuel values source scope id (reasonAt id) = .ok lowered.expression) :
      Step policy body fuel readFuel context values source scope reasonAt id node lowered
  | group {inner lowered}
      (form : node.form = .group inner) (metadata : Metadata values.checked source id node lowered.type)
      (generated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope inner reasonAt = .ok lowered) :
      Step policy body fuel readFuel context values source scope reasonAt id node lowered
  | pair {left right first second}
      (form : node.form = .tuple [left, right])
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (firstGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope left reasonAt = .ok first)
      (secondGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope right reasonAt = .ok second) :
      Step policy body fuel readFuel context values source scope reasonAt id node
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩

private theorem step_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (compound : Compound node.form)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (lowerPolicy : policy.lowerRead source scope id (reasonAt id) =
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values source scope id (reasonAt id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) context source scope id reasonAt = .ok lowered) :
    Step policy body fuel readFuel context values source scope reasonAt id node lowered := by
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
        simp only [read, form, lowerPolicy] at accepted
        first
        | obtain ⟨code, generated, outputEq⟩ := bind_accepted accepted
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .read form read generated
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

/-- The only extra literal raw-type fact follows from the independent empty
source tuple typing rule, including the empty output coercion path. -/
private theorem unit_source_type {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (coercions : node.coercions = []) (typed : ExpressionHasType source context id node.type)
    (form : node.form = .tuple []) : node.type = .unit := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := requirements.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize rawTypeEq : node.type = rawType at raw
    cases raw with
    | tuple elements => cases elements; rfl

/-- The metadata conditions are about syntax and actual policy results. They
contain no source evaluation, Core evaluation, or desired semantic tree. -/
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

/-- Policy facts are needed only at occurrences admitted by the enclosing
body. The closed set is supplied independently of compiler execution. -/
structure PolicyOn (policy : SourceCoreFunctions.Policy) (context : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource) (scope : Scope)
    (reasonAt : ExpressionId → Word) (allowed : ExpressionId → Prop) : Prop where
  special : ∀ id, allowed id → Syntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower context child budget source scope id reasonAt) = .ok none
  read : ∀ id, allowed id → Syntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

/-- Existing global profiles supply every restricted profile. -/
theorem PolicyFor.on {policy : SourceCoreFunctions.Policy} {context : SourceCoreFunctions.Context}
    {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {reasonAt : ExpressionId → Word}
    (profile : PolicyFor policy context readFuel values source scope reasonAt)
    (allowed : ExpressionId → Prop) : PolicyOn policy context readFuel values source scope reasonAt allowed :=
  ⟨fun id _ tree => profile.special id tree, fun id _ tree => profile.read id tree, profile.lower, profile.leaf⟩

/- Actual successful compilation extracts the complete finite tree. The
source typing proof supplies raw group/product shape and ordinary local scheme
agreement; successful native projection is not used as a substitute. -/
/-- Static extraction at the exact accepted atomic compiler action. No runtime
law or assumption about unrelated source occurrences is a field. -/
def LiteralFactory (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (context : SourceCoreFunctions.Context) (values : ValuesContext) (source : TypedSource)
    (scope : Scope) (reasonAt : ExpressionId → Word)
    (literals : GenericExpressionMeaning.Certificate) : Prop :=
  ∀ {id node fuel lowered}, source.lookupExpression? id = some node →
    CompatibleExpressionLiterals.Atomic node.form → (node.form = .tuple [] → node.type = .unit) →
    (∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none) →
    policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id →
    policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values →
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered →
    CompatibleExpressionLiterals.Certificate context.solvedRequirements source id lowered ∧ literals scope id lowered

/-- The former ordinary extractor supplies both copies of the same leaf receipt. -/
theorem LiteralFactory.ordinary {policy body context values source scope reasonAt} :
    LiteralFactory policy body context values source scope reasonAt
      (fun _ id lowered => CompatibleExpressionLiterals.Certificate context.solvedRequirements source id lowered) := by
  intro id node fuel lowered found atomic unitType special readPolicy leafPolicy accepted
  have receipt := CompatibleExpressionLiterals.of_functions found atomic unitType special readPolicy leafPolicy accepted
  exact ⟨receipt, receipt⟩

theorem tree_of_functions_with_literals_on
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (literals : GenericExpressionMeaning.Certificate)
    (literalFactory : CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt literals)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    {allowed : ExpressionId → Prop}
    (policyFor : PolicyOn policy context readFuel values source scope reasonAt allowed)
    (closed : ∀ {parent node child}, allowed parent → source.lookupExpression? parent = some node →
      (.expression child : NodeId) ∈ node.form.references → allowed child)
    (coercions : ∀ id node, allowed id → Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) (admitted : allowed id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree.WithLiterals (fuel := readFuel) (values := values) (source := source)
      (context := sourceContext) (solved := context.solvedRequirements) (reasonAt := reasonAt) literals scope id lowered := by
  revert admitted
  induction syntaxTree generalizing node fuel lowered with
  | literal originalFound atomic =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    obtain ⟨receipt, leaf⟩ := literalFactory originalFound atomic
      (unit_source_type unique originalFound (coercions _ _ admitted (.literal originalFound atomic) originalFound) typed)
      (policyFor.special _ admitted (.literal originalFound atomic)) (policyFor.read _ admitted (.literal originalFound atomic)) policyFor.leaf accepted
    exact ⟨_, .literal receipt leaf⟩
  | read originalFound form =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ admitted (.read originalFound form)) (policyFor.read _ admitted (.read originalFound form))
        (congrFun (congrFun (congrFun (congrFun policyFor.lower source) scope) _) _) accepted
      cases step with
      | read otherForm read generated =>
        exact ⟨_, .read (CompatibleExpressionReads.loweredRead_of_accepted generated read unique declarations typed)⟩
      | group otherForm _ _ => simp [form] at otherForm
      | pair otherForm _ _ _ => simp [form] at otherForm
  | group originalFound form child ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ admitted (.group originalFound form child)) (policyFor.read _ admitted (.group originalFound form child))
        (congrFun (congrFun (congrFun (congrFun policyFor.lower source) scope) _) _) accepted
      cases step with
      | read otherForm _ _ => simp [form] at otherForm
      | group otherForm metadata generated =>
        have same := ExpressionForm.group.inj (form.symm.trans otherForm)
        subst_vars
        obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ := group_source_types unique originalFound form metadata.coercions typed
        obtain ⟨acceptedChild1, acceptedChild1Sites⟩ := ih innerFound childTyped generated (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        exact ⟨_, .group metadata form innerFound sourceType acceptedChild1 acceptedChild1Sites⟩
      | pair otherForm _ _ _ => simp [form] at otherForm
  | pair originalFound form first second leftIH rightIH =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ admitted (.pair originalFound form first second)) (policyFor.read _ admitted (.pair originalFound form first second))
        (congrFun (congrFun (congrFun (congrFun policyFor.lower source) scope) _) _) accepted
      cases step with
      | read otherForm _ _ => simp [form] at otherForm
      | group otherForm _ _ => simp [form] at otherForm
      | pair otherForm metadata generated secondGenerated =>
        have same := ExpressionForm.tuple.inj (form.symm.trans otherForm)
        simp only [List.cons.injEq, and_true] at same
        obtain ⟨rfl, rfl⟩ := same
        obtain ⟨leftNode, rightNode, leftFound, rightFound, sourceType, leftTyped, rightTyped⟩ :=
          pair_source_types unique originalFound form metadata.coercions typed
        obtain ⟨acceptedChild2, acceptedChild2Sites⟩ := leftIH leftFound leftTyped generated (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        obtain ⟨acceptedChild3, acceptedChild3Sites⟩ := rightIH rightFound rightTyped secondGenerated (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        exact ⟨_, .pair metadata form leftFound rightFound sourceType
          acceptedChild2 acceptedChild3 acceptedChild2Sites acceptedChild3Sites⟩

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
  exact tree_of_functions_with_literals_on literals literalFactory unique declarations
    (policyFor.on (fun _ => True)) (fun _ _ _ => trivial)
    (fun id node _ tree found => coercions id node tree found) syntaxTree trivial found typed accepted

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

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
