import Solcore.SourceSemantics.CoreLowering.AcceptedNamedForItemsFlow
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedMatchFlow
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
  | .returnStmt _ | .letDecl _ _ | .assignValue _ _ _ | .assignBitNot _ | .whileLoop _ _
    | .expression _ _ | .matchWith _ | .block _ | .ifThen _ _ _ | .forLoop _ _ _ _ | .breakStmt | .continueStmt => true

/-- Exact compiler continuation after all initializer declarations are in scope. -/
def forNext (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (site : SourceCoreElaboration.ErrorSite) (result : Ty) (reasonAt : ExpressionId → Word)
    (escaped : Word) (fuel : Nat) (condition : ExpressionId) (body : List StatementId)
    (post : List ForItemForm) (scope : SourceCoreLocalCell.Scope) : Except SourceCoreBasic.Error Expr := do
  let child ← policy.lowerExpression fuel source scope condition reasonAt
  SourceCoreBasic.ensureType site .bool child.type
  let loopBody ← SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope body result reasonAt false escaped
  let postCode ← SourceCoreLoops.lowerForItems policy site fuel source scope post result reasonAt
    (fun _ => pure (LocalLoop.fallthrough result))
  pure (LocalLoop.iterate result child.expression loopBody postCode escaped)

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
  | assigned {mode escaped fuel scope id rest node stored assignment operator expression tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .assignValue assignment operator expression)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail)
      (receipt : AcceptedBareAssignmentReceipt.Receipt policy fuel source scope (.occurrence id.occurrence)
        assignment operator expression (LocalLoop.controlType result) tail reasonAt code)
      (targetType : receipt.binder.scheme.body = assignment.target.type) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | projectedAssigned {mode escaped fuel scope id rest node stored assignment operator expression tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .assignValue assignment operator expression)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail)
      (receipt : AcceptedProjectedAssignmentReceipt.Receipt policy fuel source scope (.occurrence id.occurrence)
        assignment operator expression (LocalLoop.controlType result) tail reasonAt code)
      (route : AcceptedProjectedAssignmentRoute.Route source receipt.binder.scheme.body
        assignment.target.projections assignment.target.type) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | bitNotting {mode escaped fuel scope id rest node stored assignment tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .assignBitNot assignment)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | bitNotted {mode escaped fuel scope id rest node stored assignment tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .assignBitNot assignment)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail)
      (receipt : AcceptedBareBitNotReceipt.Receipt policy fuel source scope (.occurrence id.occurrence)
        assignment (LocalLoop.controlType result) tail reasonAt code)
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
  | tailValue {escaped fuel scope id node stored expression}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .expression expression false)
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result stored = .ok ())
      (childType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result child.type = .ok ()) :
      Tree policy source result reasonAt true escaped (fuel + 1) scope [id]
        (LocalLoop.returnValue result child.expression)
  | valueDiscard {mode escaped fuel scope id rest node stored expression tail}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .expression expression false)
      (notTail : (mode && rest.isEmpty) = false)
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) stored child.type = .ok ())
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
  | matching {mode escaped fuel scope id rest node stored resolution matchedCode tail callback}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .matchWith resolution)
      (selected : policy.lowerMatch = some callback)
      (accepted : callback policy.lowerExpression (AcceptedNamedMatchFlow.bodyCallback policy fuel)
        fuel source scope id resolution result reasonAt escaped = .ok matchedCode)
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.sequence result matchedCode tail)
  | matched {mode escaped fuel scope id rest node stored resolution matchedCode tail compilation}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .matchWith resolution)
      (receipt : AcceptedNamedMatchFlow.Receipt policy compilation source scope id resolution
        result reasonAt escaped fuel matchedCode)
      (branches : ∀ request ∈ receipt.requests,
        Tree policy source result reasonAt false escaped fuel request.scope request.statements request.code)
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.sequence result matchedCode tail)
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
  | breaking {mode escaped fuel scope id rest node stored}
      (read : policy.readStatement source id = .ok (node, stored)) (form : node.form = .breakStmt)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ()) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) (LocalLoop.breaking result)
  | continuing {mode escaped fuel scope id rest node stored}
      (read : policy.readStatement source id = .ok (node, stored)) (form : node.form = .continueStmt)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ()) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) (LocalLoop.continuing result)
  | forLoop {mode escaped fuel scope id rest node stored initializer condition post body
      loopScope postScope loopCode postCode initialCode tail}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .forLoop initializer condition post body)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source loopScope condition reasonAt = .ok child)
      (conditionType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool child.type = .ok ())
      (initial : Items policy source (.occurrence id.occurrence) result reasonAt
        (forNext policy source (.occurrence id.occurrence) result reasonAt escaped fuel condition body post)
        loopScope (LocalLoop.iterate result child.expression loopCode postCode escaped) fuel scope initializer initialCode)
      (inner : Tree policy source result reasonAt false escaped fuel loopScope body loopCode)
      (after : Items policy source (.occurrence id.occurrence) result reasonAt
        (fun _ => pure (LocalLoop.fallthrough result)) postScope (LocalLoop.fallthrough result) fuel loopScope post postCode)
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest tail) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.sequence result initialCode tail)
  | forBoundary {mode escaped fuel scope id rest node stored initializer condition post body code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .forLoop initializer condition post body)
      (outside : ¬ (HeaderForms initializer ∧ HeaderForms post))
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
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
  classical
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
            | false =>
                simp only [form] at accepted
                obtain ⟨child, generated, accepted⟩ := bind_ok accepted
                by_cases tail : (mode && rest.isEmpty) = true
                · have both : mode = true ∧ rest.isEmpty = true := by simpa only [Bool.and_eq_true] using tail
                  cases both.1
                  have empty : rest = [] := List.isEmpty_iff.mp both.2
                  subst rest
                  simp only [Bool.not_false, Bool.true_and, List.isEmpty_nil, ↓reduceIte] at accepted
                  obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
                  cases checked
                  obtain ⟨checked, childType, accepted⟩ := bind_ok accepted
                  cases checked
                  cases accepted
                  exact ⟨.tailValue read form child generated statementType childType⟩
                · have notTail : (mode && rest.isEmpty) = false := Bool.eq_false_iff.mpr tail
                  simp only [Bool.not_false, Bool.true_and, notTail, Bool.false_eq_true, ↓reduceIte] at accepted
                  obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
                  cases checked
                  obtain ⟨tail, tailGenerated, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨remaining⟩ := ih tailGenerated
                  exact ⟨.valueDiscard read form notTail child generated statementType remaining⟩
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
        | forLoop initializer condition post body =>
            by_cases headers : HeaderForms initializer ∧ HeaderForms post
            · simp only [form] at accepted
              obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
              cases checked
              obtain ⟨initialCode, initialAccepted, accepted⟩ := bind_ok accepted
              obtain ⟨tail, tailGenerated, emitted⟩ := bind_ok accepted
              cases emitted
              change SourceCoreLoops.lowerForItems policy (.occurrence id.occurrence) fuel source scope initializer
                result reasonAt (forNext policy source (.occurrence id.occurrence) result reasonAt escaped fuel condition body post) = .ok initialCode at initialAccepted
              obtain ⟨loopScope, finish, ⟨initial⟩⟩ := Items.of_accepted headers.1 initialAccepted
              have continuation := initial.finish_accepted
              unfold forNext at continuation
              obtain ⟨child, generated, continuation⟩ := bind_ok continuation
              obtain ⟨checked, conditionType, continuation⟩ := bind_ok continuation
              cases checked
              obtain ⟨loopCode, loopGenerated, continuation⟩ := bind_ok continuation
              obtain ⟨postCode, postGenerated, emitted⟩ := bind_ok continuation
              cases emitted
              obtain ⟨postScope, finish, ⟨after⟩⟩ := Items.of_accepted headers.2 postGenerated
              have final := after.finish_accepted
              cases final
              obtain ⟨inner⟩ := ih loopGenerated
              obtain ⟨remaining⟩ := ih tailGenerated
              exact ⟨.forLoop read form statementType child generated conditionType initial inner after remaining⟩
            · exact ⟨.forBoundary read form headers whole⟩
        | breakStmt =>
            simp only [form] at accepted
            obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
            cases checked
            cases accepted
            exact ⟨.breaking read form statementType⟩
        | continueStmt =>
            simp only [form] at accepted
            obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
            cases checked
            cases accepted
            exact ⟨.continuing read form statementType⟩
        | matchWith resolution =>
            simp only [form] at accepted
            cases selected : policy.lowerMatch with
            | none => simp only [selected] at accepted; cases accepted
            | some callback =>
                simp only [selected] at accepted
                obtain ⟨matchedCode, matchedAccepted, accepted⟩ := bind_ok accepted
                obtain ⟨tail, tailGenerated, emitted⟩ := bind_ok accepted
                cases emitted
                obtain ⟨remaining⟩ := ih tailGenerated
                exact ⟨.matching read form selected matchedAccepted remaining⟩
        | assignBitNot assignment =>
            simp only [form] at accepted
            obtain ⟨checked, statementType, accepted⟩ := bind_ok accepted
            cases checked
            cases selected : policy.assignBitNotWithExpression with
            | some callback =>
                simp only [selected] at accepted
                obtain ⟨tail, tailGenerated, _assigned⟩ := bind_ok accepted
                obtain ⟨remaining⟩ := ih tailGenerated
                exact ⟨.bitNotting read form statementType remaining whole⟩
            | none =>
                simp only [selected] at accepted
                cases legacy : policy.assignBitNot with
                | none => simp only [legacy] at accepted; cases accepted
                | some callback =>
                    simp only [legacy] at accepted
                    obtain ⟨tail, tailGenerated, _assigned⟩ := bind_ok accepted
                    obtain ⟨remaining⟩ := ih tailGenerated
                    exact ⟨.bitNotting read form statementType remaining whole⟩

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


variable {policy : SourceCoreLoops.Policy} {source : TypedSource} {result : Ty}
  {reasonAt : ExpressionId → Word} {mode : Bool}

-- Empty fallthrough remains a separate boundary: accepted native code alone
-- does not prove the original source body's return obligation.
def Tree.closed {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) : Bool :=
  match tree with
  | .nil => !mode
  | .boundary .. | .assigning .. | .bitNotting .. | .forBoundary .. | .matching .. | .tailValue .. => false
  | .returning .. | .returnUnit .. | .breaking .. | .continuing .. => true
  | .initialized _ _ _ _ _ _ _ tail _ | .absent _ _ _ _ tail _ => tail.closed
  | .assigned _ _ _ tail _ _ | .projectedAssigned _ _ _ tail _ _ | .bitNotted _ _ _ tail _ _ | .discard _ _ _ _ _ tail => tail.closed
  | .valueDiscard _ _ _ _ _ _ tail => !mode && tail.closed
  | .block _ _ inner tail => inner.closed && tail.closed
  | .conditional _ _ _ _ _ left right tail =>
      left.closed && right.closed && tail.closed
  | .matched _ _ receipt branches tail =>
      receipt.requests.attach.all (fun request => (branches request.val request.property).closed) && tail.closed
  | .whileLoop _ _ _ _ _ _ inner tail => inner.closed && tail.closed
  | .forLoop _ _ _ _ _ _ initial inner after tail => initial.closed && inner.closed && after.closed && tail.closed

def Tree.children {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    List (Child policy source reasonAt) :=
  match tree with
  | .nil | .returnUnit .. | .boundary .. | .forBoundary .. | .breaking .. | .continuing .. => []
  | @Tree.returning _ _ _ _ _ _ fuel scope _ _ _ _ expression _ _ _ child generated _ =>
      [⟨fuel, scope, expression, child, generated⟩]
  | @Tree.tailValue _ _ _ _ _ fuel scope _ _ _ expression _ _ child generated _ _ =>
      [⟨fuel, scope, expression, child, generated⟩]
  | @Tree.valueDiscard _ _ _ _ _ _ fuel scope _ _ _ _ expression _ _ _ _ child generated _ tail =>
      ⟨fuel, scope, expression, child, generated⟩ :: tail.children
  | @Tree.initialized _ _ _ _ _ _ fuel scope _ _ _ _ _ expression _ _ _ _ _ _ _ child generated _ tail _ =>
      ⟨fuel, scope, expression, child, generated⟩ :: tail.children
  | .absent _ _ _ _ tail _ | .assigning _ _ _ tail _ | .bitNotting _ _ _ tail _ | .bitNotted _ _ _ tail _ _ | .matching _ _ _ _ tail => tail.children
  | @Tree.assigned _ _ _ _ _ _ fuel scope _ _ _ _ _ _ expression _ _ _ _ _ tail receipt _ =>
      ⟨fuel, scope, expression, receipt.child, receipt.generated⟩ :: tail.children
  | @Tree.projectedAssigned _ _ _ _ _ _ fuel scope _ _ _ _ _ _ expression _ _ _ _ _ tail receipt _route =>
      keyChildren fuel scope receipt.place.keys receipt.keys receipt.keysGenerated ++
        (⟨fuel, scope, expression, receipt.child, receipt.generated⟩ :: tail.children)
  | @Tree.discard _ _ _ _ _ _ fuel scope _ _ _ _ expression _ _ _ child generated _ tail =>
      ⟨fuel, scope, expression, child, generated⟩ :: tail.children
  | .block _ _ inner tail => inner.children ++ tail.children
  | @Tree.conditional _ _ _ _ _ _ fuel scope _ _ _ _ condition _ _ _ _ _ _ _ child generated _ left right tail =>
      ⟨fuel, scope, condition, child, generated⟩ :: (left.children ++ right.children ++ tail.children)
  | .matched _ _ receipt branches tail =>
      ⟨receipt.childFuel, _, _, receipt.child, receipt.generated⟩ ::
        (receipt.requests.attach.flatMap (fun request => (branches request.val request.property).children) ++ tail.children)
  | @Tree.whileLoop _ _ _ _ _ _ fuel scope _ _ _ _ condition _ _ _ _ _ _ child generated _ inner tail =>
      ⟨fuel, scope, condition, child, generated⟩ :: (inner.children ++ tail.children)

  | @Tree.forLoop _ _ _ _ _ _ fuel _ _ _ _ _ _ condition _ _ loopScope _ _ _ _ _ _ _ _ child generated _ initial inner after tail =>
      initial.children ++ (⟨fuel, loopScope, condition, child, generated⟩ :: (inner.children ++ after.children ++ tail.children))

def Tree.bindings {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    List (Binding policy source) :=
  match tree with
  | .nil | .returning .. | .returnUnit .. | .boundary .. | .forBoundary .. | .breaking .. | .continuing .. | .tailValue .. => []
  | @Tree.initialized _ _ _ _ _ _ _ scope _ _ _ _ binder _ payload _ _ _ _ _ projected _ _ _ tail _ =>
      ⟨scope, binder, payload, projected⟩ :: tail.bindings
  | @Tree.absent _ _ _ _ _ _ _ scope _ _ _ _ binder payload _ _ _ _ _ projected tail _ =>
      ⟨scope, binder, payload, projected⟩ :: tail.bindings
  | .assigning _ _ _ tail _ | .assigned _ _ _ tail _ _ | .projectedAssigned _ _ _ tail _ _ | .bitNotting _ _ _ tail _ | .bitNotted _ _ _ tail _ _ | .discard _ _ _ _ _ tail | .valueDiscard _ _ _ _ _ _ tail | .matching _ _ _ _ tail => tail.bindings
  | .block _ _ inner tail => inner.bindings ++ tail.bindings
  | .conditional _ _ _ _ _ left right tail => left.bindings ++ right.bindings ++ tail.bindings
  | .matched _ _ receipt branches tail =>
      receipt.requests.attach.flatMap (fun request => (branches request.val request.property).bindings) ++ tail.bindings
  | .whileLoop _ _ _ _ _ _ inner tail => inner.bindings ++ tail.bindings
  | .forLoop _ _ _ _ _ _ initial inner after tail => initial.bindings ++ inner.bindings ++ after.bindings ++ tail.bindings

/-- A refined tree exposes every supported assignment RHS from its actual callback. -/
def Tree.Ready {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) : Prop :=
  match tree with
  | .nil | .returning .. | .returnUnit .. | .boundary .. | .forBoundary .. | .breaking .. | .continuing .. | .tailValue .. => True
  | .initialized _ _ _ _ _ _ _ tail _ | .absent _ _ _ _ tail _ | .assigned _ _ _ tail _ _ | .projectedAssigned _ _ _ tail _ _ | .bitNotted _ _ _ tail _ _ => tail.Ready
  | @Tree.assigning _ _ _ _ _ _ _ _ _ _ _ _ assignment operator _ _ _ _ _ _ tail _ =>
      ¬ ValueAssignable source assignment operator ∧ tail.Ready
  | @Tree.bitNotting _ _ _ _ _ _ _ _ _ _ _ _ assignment _ _ _ _ _ tail _ =>
      ¬ BitNotAssignable source assignment ∧ tail.Ready
  | .discard _ _ _ _ _ tail | .valueDiscard _ _ _ _ _ _ tail => tail.Ready
  | .block _ _ inner tail => inner.Ready ∧ tail.Ready
  | .conditional _ _ _ _ _ left right tail => left.Ready ∧ right.Ready ∧ tail.Ready
  | .matching .. => False
  | .matched _ _ receipt branches tail => (∀ request member, (branches request member).Ready) ∧ tail.Ready
  | .whileLoop _ _ _ _ _ _ inner tail => inner.Ready ∧ tail.Ready
  | .forLoop _ _ _ _ _ _ initial inner after tail => initial.Ready ∧ inner.Ready ∧ after.Ready ∧ tail.Ready

/-- The profile identifies the actual callback. Unsupported original writes
keep their complete action and suffix in the returned tree. -/
theorem Tree.accepted {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements
      result reasonAt mode escaped = .ok code := by
  induction tree with
  | nil => simp [SourceCoreLoops.lowerFlowStatementsWithPolicy]
  | breaking read form statementType | continuing read form statementType =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        bind, Except.bind, pure, Except.pure]
  | returning read form statementType child generated childType =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        generated, childType, bind, Except.bind, pure, Except.pure]
  | returnUnit read form statementType unitType =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        unitType, bind, Except.bind, pure, Except.pure]
  | tailValue read form child generated statementType childType =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        generated, childType, bind, Except.bind, pure, Except.pure]
  | valueDiscard read form notTail child generated statementType _ ih =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, notTail,
        generated, statementType, ih, bind, Except.bind, pure, Except.pure]
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
  | projectedAssigned read form statementType _ receipt route ih =>
      simpa [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        ih, bind, Except.bind, pure, Except.pure] using receipt.accepted
  | bitNotting _ _ _ _ accepted _ => exact accepted
  | bitNotted read form statementType _ receipt _ ih =>
      simpa only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        receipt.selected, ih, bind, Except.bind] using receipt.accepted
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
  | matching read form selected accepted _ tailIH =>
      unfold AcceptedNamedMatchFlow.bodyCallback at accepted
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, selected,
        accepted, tailIH, bind, Except.bind, pure, Except.pure]
  | matched read form receipt branches remaining branchIH tailIH =>
      have accepted := receipt.accepted
      unfold AcceptedNamedMatchFlow.bodyCallback at accepted
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, receipt.selected,
        accepted, tailIH, bind, Except.bind, pure, Except.pure]
  | whileLoop read form statementType child generated conditionType _ _ innerIH tailIH =>
      simp [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
        generated, conditionType, innerIH, tailIH, bind, Except.bind, pure, Except.pure]
  | @forLoop mode escaped fuel scope id rest node stored initializer condition post body loopScope postScope
      loopCode postCode initialCode tail read form statementType child generated conditionType initial inner after remaining innerIH tailIH =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType, bind, Except.bind]
      change (do
        let loop ← SourceCoreLoops.lowerForItems policy (.occurrence id.occurrence) fuel source scope initializer result reasonAt
          (forNext policy source (.occurrence id.occurrence) result reasonAt escaped fuel condition body post)
        let next ← SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope rest result reasonAt mode escaped
        pure (LocalLoop.sequence result loop next)) = .ok (LocalLoop.sequence result initialCode tail)
      rw [initial.accepted]
      simp only [bind, Except.bind]
      rw [tailIH]
      rfl
  | forBoundary _ _ _ accepted => exact accepted
  | boundary _ _ accepted => exact accepted

theorem Tree.refine {values : SourceCoreCompatibleValues.Context}
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    (matched : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missing)
    {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    (unary : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missing)
    {compilation : SourceCoreCompatibleDataMatches.Context}
    (matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy compilation)
    {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    ∃ refined : Tree policy source result reasonAt mode escaped fuel scope statements code, refined.Ready := by
  classical
  induction fuel using Nat.strongRecOn generalizing mode scope statements code with
  | ind fuel ih =>
    cases tree with
    | nil => exact ⟨.nil, True.intro⟩
    | breaking read form statementType => exact ⟨.breaking read form statementType, True.intro⟩
    | continuing read form statementType => exact ⟨.continuing read form statementType, True.intro⟩
    | returning read form statementType child generated childType =>
        exact ⟨.returning read form statementType child generated childType, True.intro⟩
    | returnUnit read form statementType unitType =>
        exact ⟨.returnUnit read form statementType unitType, True.intro⟩
    | tailValue read form child generated statementType childType =>
        exact ⟨.tailValue read form child generated statementType childType, True.intro⟩
    | valueDiscard read form notTail child generated statementType remaining =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.valueDiscard read form notTail child generated statementType tail, ready⟩
    | initialized read form statementType projected child generated childType remaining allocated =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.initialized read form statementType projected child generated childType tail allocated, ready⟩
    | absent read form statementType projected remaining allocated =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.absent read form statementType projected tail allocated, ready⟩
    | @assigning mode escaped fuel scope id rest node stored assignment operator expression tail code
        read form statementType remaining assigned =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        by_cases supported : Assignable source assignment operator
        · obtain ⟨profile, bare, target⟩ := supported
          obtain ⟨receipt⟩ := AcceptedBareAssignmentReceipt.of_accepted matched profile bare assigned
          exact ⟨.assigned read form statementType tail receipt (target receipt.binder receipt.declaration), ready⟩
        · by_cases projected : ProjectedAssignable source assignment operator
          · obtain ⟨receipt⟩ := AcceptedProjectedAssignmentReceipt.of_accepted matched projected.1 projected.2.1 assigned
            exact ⟨.projectedAssigned read form statementType tail receipt (projected.2.2 receipt.binder receipt.description.binding), ready⟩
          · exact ⟨.assigning read form statementType tail assigned,
              (fun eligible => eligible.elim supported projected), ready⟩
    | assigned read form statementType remaining receipt targetType =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.assigned read form statementType tail receipt targetType, ready⟩
    | projectedAssigned read form statementType remaining receipt route =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.projectedAssigned read form statementType tail receipt route, ready⟩
    | @bitNotting mode escaped fuel scope id rest node stored assignment body code
        read form statementType remaining assigned =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        by_cases supported : BitNotAssignable source assignment
        · obtain ⟨profile, bare, target⟩ := supported
          have lowered := assigned
          simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, form, statementType,
            unary, remaining.accepted, bind, Except.bind] at lowered
          obtain ⟨receipt⟩ := AcceptedBareBitNotReceipt.of_accepted unary profile bare unary lowered
          exact ⟨.bitNotted read form statementType tail receipt (target receipt.binder receipt.declaration), ready⟩
        · exact ⟨.bitNotting read form statementType tail assigned, supported, ready⟩
    | bitNotted read form statementType remaining receipt targetType =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.bitNotted read form statementType tail receipt targetType, ready⟩
    | discard read form child generated statementType remaining =>
        obtain ⟨tail, ready⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.discard read form child generated statementType tail, ready⟩
    | block read form inner remaining =>
        obtain ⟨inner, innerReady⟩ := ih _ (Nat.lt_succ_self _) inner
        obtain ⟨tail, tailReady⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.block read form inner tail, innerReady, tailReady⟩
    | conditional read form child generated conditionType left right remaining =>
        obtain ⟨left, leftReady⟩ := ih _ (Nat.lt_succ_self _) left
        obtain ⟨right, rightReady⟩ := ih _ (Nat.lt_succ_self _) right
        obtain ⟨tail, tailReady⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.conditional read form child generated conditionType left right tail, leftReady, rightReady, tailReady⟩
    | @matching _ _ childFuel _ _ _ _ _ _ _ _ _ read form selected accepted remaining =>
        obtain ⟨receipt⟩ := AcceptedNamedMatchFlow.of_accepted matchPolicy selected accepted
        have each : ∀ request ∈ receipt.requests, ∃ refined :
            Tree policy source result reasonAt false escaped childFuel request.scope request.statements request.code,
            refined.Ready := by
          intro request member
          obtain ⟨raw⟩ := of_accepted (receipt.bodies request member)
          exact ih _ (Nat.lt_succ_self _) raw
        let branches := fun request member => Classical.choose (each request member)
        have branchesReady := fun request member => Classical.choose_spec (each request member)
        obtain ⟨tail, tailReady⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.matched read form receipt branches tail, branchesReady, tailReady⟩
    | matched read form receipt branches remaining =>
        have each := fun request member => ih _ (Nat.lt_succ_self _) (branches request member)
        let refined := fun request member => Classical.choose (each request member)
        have branchesReady := fun request member => Classical.choose_spec (each request member)
        obtain ⟨tail, tailReady⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.matched read form receipt refined tail, branchesReady, tailReady⟩
    | whileLoop read form statementType child generated conditionType inner remaining =>
        obtain ⟨inner, innerReady⟩ := ih _ (Nat.lt_succ_self _) inner
        obtain ⟨tail, tailReady⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.whileLoop read form statementType child generated conditionType inner tail, innerReady, tailReady⟩
    | forLoop read form statementType child generated conditionType initial inner after remaining =>
        obtain ⟨initial, initialReady⟩ := initial.refine matched unary
        obtain ⟨inner, innerReady⟩ := ih _ (Nat.lt_succ_self _) inner
        obtain ⟨after, afterReady⟩ := after.refine matched unary
        obtain ⟨tail, tailReady⟩ := ih _ (Nat.lt_succ_self _) remaining
        exact ⟨.forLoop read form statementType child generated conditionType initial inner after tail,
          initialReady, innerReady, afterReady, tailReady⟩
    | forBoundary read form outside accepted => exact ⟨.forBoundary read form outside accepted, True.intro⟩
    | boundary read outside accepted => exact ⟨.boundary read outside accepted, True.intro⟩

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

  | tailExpression {escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (code : Expr)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        [id] result reasonAt true escaped = .ok code) :
      Boundary policy source result reasonAt true escaped

  | valueExpression {escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (code : Expr)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt true escaped = .ok code) :
      Boundary policy source result reasonAt true escaped
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
  | header {mode escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (code : Expr)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Boundary policy source result reasonAt mode escaped
  | matchCallback {mode escaped} (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (code : Expr)
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
  | returning | returnUnit | breaking | continuing => cases openBranch
  | initialized _ _ _ _ _ _ _ _ _ ih | absent _ _ _ _ _ _ ih => exact ih openBranch
  | assigning read form statementType remaining assigned ih =>
      exact ⟨.assignment _ _ _ _ _ (Tree.assigning read form statementType remaining assigned).accepted⟩
  | assigned _ _ _ _ _ _ ih | projectedAssigned _ _ _ _ _ _ ih | bitNotted _ _ _ _ _ _ ih => exact ih openBranch
  | bitNotting read form statementType remaining accepted ih =>
      exact ⟨.assignment _ _ _ _ _ accepted⟩
  | discard _ _ _ _ _ _ ih => exact ih openBranch
  | @valueDiscard actualMode _ _ _ _ _ _ _ _ _ read form notTail child generated statementType remaining ih =>
    cases actualMode with
    | false => exact ih openBranch
    | true => exact ⟨.valueExpression _ _ _ _ _
        (Tree.valueDiscard read form notTail child generated statementType remaining).accepted⟩
  | tailValue read form child generated statementType childType =>
      exact ⟨.tailExpression _ _ _ _ (Tree.tailValue read form child generated statementType childType).accepted⟩
  | block read form inner remaining innerIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with innerOpen | tailOpen
      · obtain ⟨boundary⟩ := innerIH innerOpen
        exact ⟨.nested boundary⟩
      · exact tailIH tailOpen
  | conditional read form child generated conditionType left right remaining leftIH rightIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with (leftOpen | rightOpen) | tailOpen
      · obtain ⟨boundary⟩ := leftIH leftOpen
        exact ⟨.nested boundary⟩
      · obtain ⟨boundary⟩ := rightIH rightOpen
        exact ⟨.nested boundary⟩
      · exact tailIH tailOpen
  | matching read form selected accepted remaining tailIH =>
      exact ⟨.matchCallback _ _ _ _ _ (Tree.matching read form selected accepted remaining).accepted⟩
  | matched read form receipt branches remaining branchIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with branchOpen | tailOpen
      · have existsOpen : ∃ request : { request // request ∈ receipt.requests },
            (branches request.val request.property).closed = false := by
          classical
          apply Classical.byContradiction
          intro missing
          have allClosed : ∀ request : { request // request ∈ receipt.requests },
              (branches request.val request.property).closed = true := by
            intro request
            cases same : (branches request.val request.property).closed with
            | false => exact False.elim (missing ⟨request, same⟩)
            | true => rfl
          have accepted : receipt.requests.attach.all (fun request => (branches request.val request.property).closed) = true :=
            List.all_eq_true.mpr (fun request _ => allClosed request)
          rw [accepted] at branchOpen
          cases branchOpen
        obtain ⟨request, failed⟩ := existsOpen
        obtain ⟨boundary⟩ := branchIH request.val request.property failed
        exact ⟨.nested boundary⟩
      · exact tailIH tailOpen
  | whileLoop read form statementType child generated conditionType inner remaining innerIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with innerOpen | tailOpen
      · obtain ⟨boundary⟩ := innerIH innerOpen
        exact ⟨.nested boundary⟩
      · exact tailIH tailOpen
  | forLoop read form statementType child generated conditionType initial inner after remaining innerIH tailIH =>
      simp only [Tree.closed, Bool.and_eq_false_iff] at openBranch
      rcases openBranch with ((initialOpen | innerOpen) | afterOpen) | tailOpen
      · exact ⟨.header _ _ _ _ _ (Tree.forLoop read form statementType child generated conditionType initial inner after remaining).accepted⟩
      · obtain ⟨boundary⟩ := innerIH innerOpen
        exact ⟨.nested boundary⟩
      · exact ⟨.header _ _ _ _ _ (Tree.forLoop read form statementType child generated conditionType initial inner after remaining).accepted⟩
      · exact tailIH tailOpen
  | forBoundary read form outside accepted => exact ⟨.header _ _ _ _ _ accepted⟩
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
