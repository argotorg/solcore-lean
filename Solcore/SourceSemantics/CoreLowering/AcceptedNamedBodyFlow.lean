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
  | .returnStmt _ | .letDecl _ _ => true
  | _ => false

inductive Tree (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (result : Ty) (reasonAt : ExpressionId → Word) (mode : Bool) (escaped : Word) :
    Nat → SourceCoreLocalCell.Scope → List StatementId → Expr → Type where
  | nil {fuel scope} : Tree policy source result reasonAt mode escaped fuel scope []
      (LocalLoop.fallthrough result)
  | returning {fuel scope id rest node stored expression}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .returnStmt (some expression))
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result stored = .ok ())
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (childType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result child.type = .ok ()) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.returnValue result child.expression)
  | returnUnit {fuel scope id rest node stored}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .returnStmt none)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) result stored = .ok ())
      (unitType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ()) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest)
        (LocalLoop.returned .unit)
  | initialized {fuel scope id rest node stored binder expression payload tail code}
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
  | absent {fuel scope id rest node stored binder payload tail code}
      (read : policy.readStatement source id = .ok (node, stored))
      (form : node.form = .letDecl binder none)
      (statementType : SourceCoreBasic.ensureType (.occurrence id.occurrence) .unit stored = .ok ())
      (projected : policy.lowerBinder source scope binder = .ok payload)
      (remaining : Tree policy source result reasonAt mode escaped fuel ((binder.id, payload) :: scope) rest tail)
      (allocated : SourceCoreSourceCells.letUninitialized policy.sourceCells source scope Renaming.id binder
        payload tail = .ok code) :
      Tree policy source result reasonAt mode escaped (fuel + 1) scope (id :: rest) code
  | boundary {fuel scope id rest node stored code}
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
  induction fuel generalizing scope statements code with
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
        | expression | assignValue | assignBitNot | block | ifThen | whileLoop | forLoop | matchWith | breakStmt | continueStmt =>
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
def Tree.closed {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) : Bool :=
  match tree with
  | .nil | .boundary .. => false
  | .returning .. | .returnUnit .. => true
  | .initialized _ _ _ _ _ _ _ tail _ | .absent _ _ _ _ tail _ => tail.closed

def Tree.children {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    List (Child policy source reasonAt) :=
  match tree with
  | .nil | .returnUnit .. | .boundary .. => []
  | @Tree.returning _ _ _ _ _ _ fuel scope _ _ _ _ expression _ _ _ child generated _ =>
      [⟨fuel, scope, expression, child, generated⟩]
  | @Tree.initialized _ _ _ _ _ _ fuel scope _ _ _ _ _ expression _ _ _ _ _ _ _ child generated _ tail _ =>
      ⟨fuel, scope, expression, child, generated⟩ :: tail.children
  | .absent _ _ _ _ tail _ => tail.children

def Tree.bindings {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) :
    List (Binding policy source) :=
  match tree with
  | .nil | .returning .. | .returnUnit .. | .boundary .. => []
  | @Tree.initialized _ _ _ _ _ _ _ scope _ _ _ _ binder _ payload _ _ _ _ _ projected _ _ _ tail _ =>
      ⟨scope, binder, payload, projected⟩ :: tail.bindings
  | @Tree.absent _ _ _ _ _ _ _ scope _ _ _ _ binder payload _ _ _ _ _ projected tail _ =>
      ⟨scope, binder, payload, projected⟩ :: tail.bindings

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
  | boundary _ _ accepted => exact accepted

/-- A remaining compiler branch, retaining its exact action and local scope. -/
inductive Boundary (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (result : Ty) (reasonAt : ExpressionId → Word) (mode : Bool) (escaped : Word) : Type where
  | fallthrough (fuel : Nat) (scope : SourceCoreLocalCell.Scope)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope []
        result reasonAt mode escaped = .ok (LocalLoop.fallthrough result)) :
      Boundary policy source result reasonAt mode escaped
  | statement (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : StatementId)
      (rest : List StatementId) (node : StatementNode) (stored : Ty) (code : Expr)
      (read : policy.readStatement source id = .ok (node, stored))
      (outside : expanded node.form = false)
      (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt mode escaped = .ok code) :
      Boundary policy source result reasonAt mode escaped

theorem Tree.frontier {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (openBranch : tree.closed = false) : Nonempty (Boundary policy source result reasonAt mode escaped) := by
  induction tree with
  | @nil actualFuel actualScope => exact ⟨.fallthrough actualFuel actualScope (by simp [SourceCoreLoops.lowerFlowStatementsWithPolicy])⟩
  | returning | returnUnit => cases openBranch
  | initialized _ _ _ _ _ _ _ _ _ ih | absent _ _ _ _ _ _ ih => exact ih openBranch
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
