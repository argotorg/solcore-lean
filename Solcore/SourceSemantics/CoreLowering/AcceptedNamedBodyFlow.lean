import Solcore.SourceSemantics.CoreLowering.AcceptedBareAssignmentReceipt
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts

/-! Structural inversion of the actual accepted flow action. Each retained
child is the action run by the compiler at its original source and scope.
The boundary alternative records the actual first unexpanded compiler form. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

/-- These are compiler branches expanded by this receipt, not a source checker. -/
def expanded : StatementForm → Bool
  | .returnStmt _ | .letDecl _ _ | .assignValue _ _ _ | .whileLoop _ _
    | .expression _ true | .block _ | .ifThen _ _ _ => true
  | _ => false

inductive Tree (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (result : Ty) (reasonAt : ExpressionId → Word) :
    Bool → Word → Nat → SourceCoreLocalCell.Scope → List StatementId → Expr → Type where
  | nil {mode escaped fuel scope} : Tree policy source result reasonAt mode escaped fuel scope []
      (LocalLoop.fallthrough result)
  | returning {mode escaped fuel scope id rest node stored expression}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .returnStmt (some expression))
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result stored = .ok ())
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (childType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result child.type = .ok ()) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.returnValue result child.expression)
  | returnUnit {mode escaped fuel scope id rest node stored}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .returnStmt none)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result stored = .ok ())
      (unitType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ()) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.returned .unit)
  | initialized {mode escaped fuel scope id rest node stored binder expression payload tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .letDecl binder (some expression))
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (projected : policy.lowerBinder source scope binder = .ok payload)
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (childType : SourceCoreBasic.ensureType (.binder binder.id) payload child.type = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel ((binder.id, payload) :: scope) rest tail)
      (allocated : SourceCoreSourceCells.letInitialized policy.sourceCells source scope Renaming.id binder
        (LocalLoop.controlType result) payload child.expression tail = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | absent {mode escaped fuel scope id rest node stored binder payload tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .letDecl binder none)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (projected : policy.lowerBinder source scope binder = .ok payload)
      (remaining : Tree policy source result reasonAt mode escaped fuel ((binder.id, payload) :: scope) rest tail)
      (allocated : SourceCoreSourceCells.letUninitialized policy.sourceCells source scope Renaming.id binder
        payload tail = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | assigning {mode escaped fuel scope id rest node stored assignment operator expression tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .assignValue assignment operator expression)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail)
      (assigned : SourceCoreLoops.assignValue policy fuel source scope (.occurrence id.occurrence)
        assignment operator expression (LocalLoop.controlType result) tail reasonAt = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | assigned {mode escaped fuel scope id rest node stored assignment expression tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .assignValue assignment .equal expression)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail)
      (receipt : AcceptedBareAssignmentReceipt.Receipt policy fuel source scope (.occurrence id.occurrence)
        assignment expression (LocalLoop.controlType result) tail reasonAt code)
      (targetType : receipt.binder.scheme.body = assignment.target.type) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | discard {mode escaped fuel scope id rest node stored expression tail}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .expression expression true)
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalSequence.discard (LocalLoop.controlType result) child.expression tail)
  | block {mode escaped fuel scope id rest node stored statements innerCode tail}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .block statements)
      (inner : Tree policy source result reasonAt false escaped fuel scope statements innerCode)
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.sequence result innerCode tail)
  | conditional {mode escaped fuel scope id rest node stored condition thenBody elseBody thenCode elseCode tail}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .ifThen condition thenBody elseBody)
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope condition reasonAt = .ok child)
      (conditionType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool child.type = .ok ())
      (left : Tree policy source result reasonAt false escaped fuel scope thenBody thenCode)
      (right : Tree policy source result reasonAt false escaped fuel scope (elseBody.getD []) elseCode)
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.sequence result (LocalLoop.conditional result child.expression thenCode elseCode) tail)
  | whileLoop {mode escaped fuel scope id rest node stored condition body loopCode tail}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .whileLoop condition body)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope condition reasonAt = .ok child)
      (conditionType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool child.type = .ok ())
      (inner : Tree policy source result reasonAt false escaped fuel scope body loopCode)
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.sequence result (LocalLoop.whileLoop result child.expression loopCode escaped) tail)
  | boundary {mode escaped fuel scope id rest node stored code}
      (read : policy.readStatement source id = .ok (node, stored))
      (outside : expanded node.form = false)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code

/-- Inversion follows the compiler branch and its actual decreasing fuel. It
requires no independently recognized statement shape. -/
theorem of_accepted {policy : SourceCoreLoops.Policy} {source : TypedSource}
    {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      statements result reasonAt mode escaped = .ok code) :
    Nonempty (Tree policy source result reasonAt mode escaped fuel scope statements code) := by
  induction fuel generalizing mode scope statements code with
  | zero =>
      cases statements with
      | nil => cases accepted; exact ⟨.nil⟩
      | cons id rest => cases accepted
  | succ fuel ih =>
      cases statements with
      | nil => cases accepted; exact ⟨.nil⟩
      | cons id rest =>
        have whole := accepted
        simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
        obtain ⟨⟨node, stored⟩, read, accepted⟩ := bind_ok accepted
        cases form : node.form with
        | returnStmt value =>
            simp only [form] at accepted
            cases value with
            | none =>
                obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
                cases checked
                obtain ⟨checked, unitType, accepted⟩ := bind_ok accepted
                cases checked
                cases accepted
                exact ⟨.returnUnit read form statementType unitType⟩
            | some expression =>
                obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
                cases checked
                obtain ⟨child, generated, accepted⟩ := bind_ok accepted
                obtain ⟨checked, childType, accepted⟩ := bind_ok accepted
                cases checked
                cases accepted
                exact ⟨.returning read form statementType child generated childType⟩
        | letDecl binder initializer =>
            simp only [form] at accepted
            obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
            cases checked
            obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
            cases initializer with
            | none =>
                obtain ⟨tail, generated, allocated⟩ := bind_ok accepted
                obtain ⟨remaining⟩ := ih generated
                exact ⟨.absent read form statementType projected remaining allocated⟩
            | some expression =>
                obtain ⟨child, generated, accepted⟩ := bind_ok accepted
                obtain ⟨checked, childType, accepted⟩ := bind_ok accepted
                cases checked
                obtain ⟨tail, tailGenerated, allocated⟩ := bind_ok accepted
                obtain ⟨remaining⟩ := ih tailGenerated
                exact ⟨.initialized read form statementType projected child generated childType remaining allocated⟩
        | assignValue assignment operator expression =>
            simp only [form] at accepted
            obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
            cases checked
            obtain ⟨tail, tailGenerated, assigned⟩ := bind_ok accepted
            obtain ⟨remaining⟩ := ih tailGenerated
            exact ⟨.assigning read form statementType remaining assigned⟩
        | expression value semicolon =>
            cases semicolon with
            | false => exact ⟨.boundary read (by simp only [form, expanded]) whole⟩
            | true =>
                simp only [form, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at accepted
                obtain ⟨child, generated, accepted⟩ := bind_ok accepted
                obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
                cases checked
                obtain ⟨tail, tailGenerated, accepted⟩ := bind_ok accepted
                cases accepted
                obtain ⟨remaining⟩ := ih tailGenerated
                exact ⟨.discard read form child generated statementType remaining⟩
        | block statements =>
            simp only [form] at accepted
            obtain ⟨innerCode, innerGenerated, accepted⟩ := bind_ok accepted
            obtain ⟨tail, tailGenerated, accepted⟩ := bind_ok accepted
            cases accepted
            obtain ⟨inner⟩ := ih innerGenerated
            obtain ⟨remaining⟩ := ih tailGenerated
            exact ⟨.block read form inner remaining⟩
        | ifThen condition thenBody elseBody =>
            simp only [form] at accepted
            obtain ⟨child, generated, accepted⟩ := bind_ok accepted
            obtain ⟨checked, conditionType, accepted⟩ := bind_ok accepted
            cases checked
            obtain ⟨thenCode, thenGenerated, accepted⟩ := bind_ok accepted
            obtain ⟨left⟩ := ih thenGenerated
            cases elseBody with
            | none =>
                simp only [pure, Except.pure, bind, Except.bind] at accepted
                obtain ⟨tail, tailGenerated, accepted⟩ := bind_ok accepted
                cases accepted
                obtain ⟨remaining⟩ := ih tailGenerated
                exact ⟨.conditional read form child generated conditionType left .nil remaining⟩
            | some statements =>
                obtain ⟨elseCode, elseGenerated, accepted⟩ := bind_ok accepted
                obtain ⟨tail, tailGenerated, accepted⟩ := bind_ok accepted
                cases accepted
                obtain ⟨right⟩ := ih elseGenerated
                obtain ⟨remaining⟩ := ih tailGenerated
                exact ⟨.conditional read form child generated conditionType left right remaining⟩
        | whileLoop condition body =>
            simp only [form] at accepted
            obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
            cases checked
            obtain ⟨child, generated, accepted⟩ := bind_ok accepted
            obtain ⟨checked, conditionType, accepted⟩ := bind_ok accepted
            cases checked
            obtain ⟨loopCode, loopGenerated, accepted⟩ := bind_ok accepted
            obtain ⟨tail, tailGenerated, accepted⟩ := bind_ok accepted
            cases accepted
            obtain ⟨inner⟩ := ih loopGenerated
            obtain ⟨remaining⟩ := ih tailGenerated
            exact ⟨.whileLoop read form statementType child generated conditionType inner remaining⟩
        | assignBitNot | forLoop | matchWith | breakStmt | continueStmt =>
            exact ⟨.boundary read (by simp only [form, expanded]) whole⟩

/-- The footer is retained once, around the exact recursively issued flow. -/
structure Body (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (statements : List StatementId) (result : Ty)
    (reasonAt : ExpressionId → Word) (fellThrough escaped : Word) (code : Expr) where
  flow : Expr
  tree : Tree policy source result reasonAt true escaped fuel scope statements flow
  emitted : code = CompatibleStatements.finish result flow fellThrough escaped

theorem body_of_accepted {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
      result reasonAt fellThrough escaped = .ok code) :
    Nonempty (Body policy fuel source scope statements result reasonAt fellThrough escaped code) := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  obtain ⟨tree⟩ := of_accepted generated
  exact ⟨⟨flow, tree, (Except.ok.inj returned).symm⟩⟩


/-- Ordered expanded expression actions, including repeated source occurrences. -/
structure Child (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (reasonAt : ExpressionId → Word) where
  fuel : Nat
  scope : SourceCoreLocalCell.Scope
  expression : ExpressionId
  lowered : SourceCoreBasic.LoweredExpr
  accepted : policy.lowerExpression fuel source scope expression reasonAt = .ok lowered

structure Binding (policy : SourceCoreLoops.Policy) (source : TypedSource) where
  scope : SourceCoreLocalCell.Scope
  binder : TypedBinder
  payload : Ty
  projected : policy.lowerBinder source scope binder = .ok payload

variable {policy : SourceCoreLoops.Policy} {source : TypedSource} {result : Ty}
  {reasonAt : ExpressionId → Word} {mode : Bool}

-- Empty fallthrough remains a separate boundary: accepted native code alone
-- does not prove the original source body's return obligation.
def Tree.closed {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) : Bool :=
  match tree with
  | .nil => !mode
  | .boundary .. | .assigning .. => false
  | .returning .. | .returnUnit .. => true
  | .initialized _ _ _ _ _ _ _ tail _ | .absent _ _ _ _ tail _ => tail.closed
  | .assigned _ _ _ tail _ _ | .discard _ _ _ _ _ tail => tail.closed
  | .block _ _ inner tail => inner.closed && tail.closed
  | @Tree.conditional _ _ _ _ _ _ _ _ _ _ node _ _ _ _ _ _ _ _ _ _ _ _ left right tail =>
      decide (node.type = .unit) && left.closed && right.closed && tail.closed
  | .whileLoop _ _ _ _ _ _ inner tail => inner.closed && tail.closed

def Tree.children {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    List (Child policy source reasonAt) :=
  match tree with
  | .nil | .returnUnit .. | .boundary .. => []
  | @Tree.returning _ _ _ _ _ _ fuel scope _ _ _ _ expression _ _ _ child generated _ =>
      [⟨fuel, scope, expression, child, generated⟩]
  | @Tree.initialized _ _ _ _ _ _ fuel scope _ _ _ _ _ expression _ _ _ _ _ _ _ child generated _ tail _ =>
      ⟨fuel, scope, expression, child, generated⟩ :: tail.children
  | .absent _ _ _ _ tail _ | .assigning _ _ _ tail _ => tail.children
  | @Tree.assigned _ _ _ _ _ _ fuel scope _ _ _ _ _ expression _ _ _ _ _ tail receipt _ =>
      ⟨fuel, scope, expression, receipt.child, receipt.generated⟩ :: tail.children
  | @Tree.discard _ _ _ _ _ _ fuel scope _ _ _ _ expression _ _ _ child generated _ tail =>
      ⟨fuel, scope, expression, child, generated⟩ :: tail.children
  | .block _ _ inner tail => inner.children ++ tail.children
  | @Tree.conditional _ _ _ _ _ _ fuel scope _ _ _ _ condition _ _ _ _ _ _ _ child generated _ left right tail =>
      ⟨fuel, scope, condition, child, generated⟩ :: (left.children ++ right.children ++ tail.children)
  | @Tree.whileLoop _ _ _ _ _ _ fuel scope _ _ _ _ condition _ _ _ _ _ _ child generated _ inner tail =>
      ⟨fuel, scope, condition, child, generated⟩ :: (inner.children ++ tail.children)

def Tree.bindings {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    List (Binding policy source) :=
  match tree with
  | .nil | .returning .. | .returnUnit .. | .boundary .. => []
  | @Tree.initialized _ _ _ _ _ _ _ scope _ _ _ _ binder _ payload _ _ _ _ _ projected _ _ _ tail _ =>
      ⟨scope, binder, payload, projected⟩ :: tail.bindings
  | @Tree.absent _ _ _ _ _ _ _ scope _ _ _ _ binder payload _ _ _ _ _ projected tail _ =>
      ⟨scope, binder, payload, projected⟩ :: tail.bindings
  | .assigning _ _ _ tail _ | .assigned _ _ _ tail _ _ | .discard _ _ _ _ _ tail => tail.bindings
  | .block _ _ inner tail => inner.bindings ++ tail.bindings
  | .conditional _ _ _ _ _ left right tail => left.bindings ++ right.bindings ++ tail.bindings
  | .whileLoop _ _ _ _ _ _ inner tail => inner.bindings ++ tail.bindings

/-- Bare equal writes retain the original declaration type as well as native layout. -/
def Assignable (source : TypedSource) (assignment : AssignmentResolution)
    (operator : Solcore.Syntax.ValueAssignOp) : Prop :=
  operator = .equal ∧ assignment.target.projections = [] ∧
    ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      binder.scheme.body = assignment.target.type

/-- A refined tree exposes every supported assignment RHS from its actual callback. -/
def Tree.Ready {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) : Prop :=
  match tree with
  | .nil | .returning .. | .returnUnit .. | .boundary .. => True
  | .initialized _ _ _ _ _ _ _ tail _ | .absent _ _ _ _ tail _ | .assigned _ _ _ tail _ _ => tail.Ready
  | @Tree.assigning _ _ _ _ _ _ _ _ _ _ _ _ assignment operator _ _ _ _ _ _ tail _ =>
      ¬ Assignable source assignment operator ∧ tail.Ready
  | .discard _ _ _ _ _ tail => tail.Ready
  | .block _ _ inner tail => inner.Ready ∧ tail.Ready
  | .conditional _ _ _ _ _ left right tail => left.Ready ∧ right.Ready ∧ tail.Ready
  | .whileLoop _ _ _ _ _ _ inner tail => inner.Ready ∧ tail.Ready

/-- The profile identifies the actual callback. Unsupported original writes
keep their complete action and suffix in the returned tree. -/
theorem Tree.refine {values : SourceCoreCompatibleValues.Context}
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    (matched : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missing)
    {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    ∃ refined : Tree policy source result reasonAt mode escaped fuel scope statements code, refined.Ready := by
  classical
  induction tree with
  | nil => exact ⟨.nil, True.intro⟩
  | returning read form statementType child generated childType =>
      exact ⟨.returning read form statementType child generated childType, True.intro⟩
  | returnUnit read form statementType unitType =>
      exact ⟨.returnUnit read form statementType unitType, True.intro⟩
  | initialized read form statementType projected child generated childType remaining allocated ih =>
      obtain ⟨tail, ready⟩ := ih
      exact ⟨.initialized read form statementType projected child generated childType tail allocated, ready⟩
  | absent read form statementType projected remaining allocated ih =>
      obtain ⟨tail, ready⟩ := ih
      exact ⟨.absent read form statementType projected tail allocated, ready⟩
  | @assigning mode escaped fuel scope id rest node stored assignment operator expression tail code
      read form statementType remaining assigned ih =>
      obtain ⟨tail, ready⟩ := ih
      by_cases supported : Assignable source assignment operator
      · obtain ⟨rfl, bare, target⟩ := supported
        obtain ⟨receipt⟩ := AcceptedBareAssignmentReceipt.of_accepted matched bare assigned
        exact ⟨.assigned read form statementType tail receipt (target receipt.binder receipt.declaration), ready⟩
      · exact ⟨.assigning read form statementType tail assigned, supported, ready⟩
  | assigned read form statementType remaining receipt targetType ih =>
      obtain ⟨tail, ready⟩ := ih
      exact ⟨.assigned read form statementType tail receipt targetType, ready⟩
  | discard read form child generated statementType remaining ih =>
      obtain ⟨tail, ready⟩ := ih
      exact ⟨.discard read form child generated statementType tail, ready⟩
  | block read form inner remaining innerIH tailIH =>
      obtain ⟨inner, innerReady⟩ := innerIH
      obtain ⟨tail, tailReady⟩ := tailIH
      exact ⟨.block read form inner tail, innerReady, tailReady⟩
  | conditional read form child generated conditionType left right remaining leftIH rightIH tailIH =>
      obtain ⟨left, leftReady⟩ := leftIH
      obtain ⟨right, rightReady⟩ := rightIH
      obtain ⟨tail, tailReady⟩ := tailIH
      exact ⟨.conditional read form child generated conditionType left right tail, leftReady, rightReady, tailReady⟩
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
      obtain ⟨inner, innerReady⟩ := innerIH
      obtain ⟨tail, tailReady⟩ := tailIH
      exact ⟨.whileLoop read form statementType child generated conditionType inner tail, innerReady, tailReady⟩
  | boundary read outside accepted => exact ⟨.boundary read outside accepted, True.intro⟩

theorem Tree.accepted {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements
      result reasonAt mode escaped = .ok code := by
  induction tree with
  | nil => simp [SourceCoreLoops.lowerFlowStatementsWithPolicy]
  | returning read form statementType child generated childType =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        generated, childType, bind, Except.bind, pure, Except.pure]
  | returnUnit read form statementType unitType =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        unitType, bind, Except.bind, pure, Except.pure]
  | initialized read form statementType projected child generated childType _ allocated ih =>
      simpa [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        projected, generated, childType, ih, bind, Except.bind, pure, Except.pure] using allocated
  | absent read form statementType projected _ allocated ih =>
      simpa [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        projected, ih, bind, Except.bind, pure, Except.pure] using allocated
  | assigning read form statementType _ assigned ih =>
      simpa [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        ih, bind, Except.bind, pure, Except.pure] using assigned
  | assigned read form statementType _ receipt _ ih =>
      simpa [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        ih, bind, Except.bind, pure, Except.pure] using receipt.accepted
  | discard read form child generated statementType _ ih =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, generated, statementType,
        ih, bind, Except.bind, pure, Except.pure]
  | block read form _ _ innerIH tailIH =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, innerIH, tailIH,
        bind, Except.bind, pure, Except.pure]
  | @conditional _ _ _ _ _ _ _ _ _ _ elseBody _ _ _ read form child generated conditionType _ _ _ leftIH rightIH tailIH =>
      cases elseBody with
      | none =>
          simp only [Option.getD_none, SourceCoreLoops.lowerFlowStatementsWithPolicy, Except.ok.injEq] at rightIH
          cases rightIH
          simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, generated, conditionType,
            leftIH, tailIH, bind, Except.bind, pure, Except.pure]
      | some statements =>
          simp only [Option.getD_some] at rightIH
          simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, generated, conditionType,
            leftIH, rightIH, tailIH, bind, Except.bind, pure, Except.pure]
  | whileLoop read form statementType child generated conditionType _ _ innerIH tailIH =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        generated, conditionType, innerIH, tailIH, bind, Except.bind, pure, Except.pure]
  | boundary _ _ accepted => exact accepted

/-- A remaining compiler branch, retaining its exact action and local scope. -/
inductive Boundary (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (result : Ty) (reasonAt : ExpressionId → Word) : Bool → Word → Type where
  | fallthrough {mode escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope []
        result reasonAt mode escaped = .ok (LocalLoop.fallthrough result)) :
      Boundary policy source result reasonAt mode escaped
  | statement {mode escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (node : StatementNode) (stored : Ty) (code : Expr)
      (read : policy.readStatement source id = .ok (node, stored))
      (outside : expanded node.form = false)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Boundary policy source result reasonAt mode escaped

  | assignment {mode escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (code : Expr)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Boundary policy source result reasonAt mode escaped
  | conditionalType {mode escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (node : StatementNode) (stored : Ty) (code : Expr)
      (read : policy.readStatement source id = .ok (node, stored))
      (notUnit : node.type ≠ .unit)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Boundary policy source result reasonAt mode escaped
  | nested {mode escaped} (boundary : Boundary policy source result reasonAt false escaped) :
      Boundary policy source result reasonAt mode escaped

theorem Tree.frontier {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (openBranch : tree.closed = false) : Nonempty (Boundary policy source result reasonAt mode escaped) := by
  induction tree with
  | @nil _ _ actualFuel actualScope => exact ⟨.fallthrough actualFuel actualScope (by simp [SourceCoreLoops.lowerFlowStatementsWithPolicy])⟩
  | returning | returnUnit => cases openBranch
  | initialized _ _ _ _ _ _ _ _ _ ih | absent _ _ _ _ _ _ ih => exact ih openBranch
  | assigning read form statementType remaining assigned ih =>
      exact ⟨.assignment _ _ _ _ _ (Tree.assigning read form statementType remaining assigned).accepted⟩
  | assigned _ _ _ _ _ _ ih => exact ih openBranch
  | discard _ _ _ _ _ _ ih => exact ih openBranch
  | block read form inner remaining innerIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with innerOpen | tailOpen
      · obtain ⟨boundary⟩ := innerIH innerOpen
        exact ⟨.nested boundary⟩
      · exact tailIH tailOpen
  | conditional read form child generated conditionType left right remaining leftIH rightIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with ((notUnit | leftOpen) | rightOpen) | tailOpen
      · exact ⟨.conditionalType _ _ _ _ _ _ _ read (of_decide_eq_false notUnit)
          (Tree.conditional read form child generated conditionType left right remaining).accepted⟩
      · obtain ⟨boundary⟩ := leftIH leftOpen
        exact ⟨.nested boundary⟩
      · obtain ⟨boundary⟩ := rightIH rightOpen
        exact ⟨.nested boundary⟩
      · exact tailIH tailOpen
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with innerOpen | tailOpen
      · obtain ⟨boundary⟩ := innerIH innerOpen
        exact ⟨.nested boundary⟩
      · exact tailIH tailOpen
  | boundary read outside accepted => exact ⟨.statement _ _ _ _ _ _ _ read outside accepted⟩

theorem Body.accepted {escaped fellThrough : Word} {fuel scope statements code}
    (body : Body policy fuel source scope statements result reasonAt fellThrough escaped code) :
    SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements result
      reasonAt fellThrough escaped = .ok code := by
  rw [body.emitted]
  unfold SourceCoreLoops.lowerStatementsWithPolicy
  rw [body.tree.accepted]
  rfl

/-- The residual is indexed by the complete accepted body, so a frontier
from an unrelated source position cannot satisfy this alternative. -/
structure Incomplete (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (statements : List StatementId) (result : Ty)
    (reasonAt : ExpressionId → Word) (fellThrough escaped : Word) (code : Expr) where
  body : Body policy fuel source scope statements result reasonAt fellThrough escaped code
  openBranch : body.tree.closed = false

theorem Incomplete.frontier {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (receipt : Incomplete policy fuel source scope statements result reasonAt fellThrough escaped code) :
    Nonempty (Boundary policy source result reasonAt true escaped) :=
  receipt.body.tree.frontier receipt.openBranch

/-- The exact named policy keeps the original full ledger, parents, local
specializations, diagnostics and callable context of the accepted action. -/
def namedPolicy {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : CallableIndexedNamedGeneration.Named)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (parents : List SourceCoreLocalEvidence.Prepared)
    (own : SourceCoreProgramFaultSites.Function) : SourceCoreLoops.Policy :=
  let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
  { actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
      own.assignments diagnostics named.signature.key
      (SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
        prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
        (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none) with
    sourceCells := actual.expressions.sourceCells
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }

/-- This endpoint starts at the actual sealed named compilation receipt. -/
theorem of_compilation {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked}
    {named : CallableIndexedNamedGeneration.Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    Nonempty (Body (namedPolicy prepared named diagnostics compilation.parents compilation.own)
      prepared.fuel (CallableIndexedNamedGeneration.source named)
      (named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) compilation.statements
      named.signature.resultType (diagnostics.reasonAt named.signature.key)
      compilation.own.fellThroughReason compilation.own.table.escapedReason compilation.body) :=
  body_of_accepted compilation.bodyCompiled

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
