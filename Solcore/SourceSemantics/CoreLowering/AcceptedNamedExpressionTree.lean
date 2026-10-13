import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
import Solcore.SourceSemantics.CoreLowering.AcceptedContextualDirectReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionPolicy

/-! Original expression trees follow accepted child actions. Unexpanded compiler
branches retain the actual selected action and its original source occurrence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child Supported Receipt)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

inductive LeafForm : ExpressionForm → Prop where
  | literal {form} (atomic : CompatibleExpressionLiterals.Atomic form) : LeafForm form
  | read (name : String) (binder : Resolved.LocalId) : LeafForm (.reference name (.local binder))

theorem LeafForm.view {form : ExpressionForm} (leaf : LeafForm form) :
    CompatibleExpressionLiterals.Atomic form ∨ ∃ name binder, form = .reference name (.local binder) := by
  cases leaf with
  | literal atomic => exact .inl atomic
  | read name binder => exact .inr ⟨name, binder, rfl⟩

def DirectForm (form : ExpressionForm) : Prop :=
  ∃ callee arguments instantiation, form = .call callee arguments (.declaration instantiation)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

local notation "policy" => root.selected.policy
local notation "body" => root.selected.lowerBody
local notation "current" => context compiled.indexed named
local notation "valueContext" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked

inductive Cause {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Head policy body fuel current source scope id reasonAt lowered) where
  | special (selected : head.special = some lowered) (outside : ¬ DirectForm head.node.form)
  | initializer (selected : head.special = some lowered)
      (actual : AcceptedContextualDirectReceipt.InitializerAt compiled.indexed current id)
  | form (selected : head.special = none)
      (notLeaf : ¬ LeafForm head.node.form) (notDirect : ¬ DirectForm head.node.form)

inductive Step (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) (fuel : Nat) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) where
  | leaf (head : Head policy body fuel current source scope id reasonAt lowered)
      (plain : head.special = none) (form : LeafForm head.node.form)
  | ordinary (head : Head policy body fuel current source scope id reasonAt lowered)
      (plain : head.special = none) {callee : ExpressionId} {arguments : List ExpressionId}
      {instantiation : DeclarationInstantiation}
      (receipt : Receipt policy body fuel current valueContext source scope id callee arguments instantiation reasonAt lowered)
  | evidence (head : Head policy body fuel current source scope id reasonAt lowered)
      (selected : head.special = some lowered) {callee : ExpressionId} {arguments : List ExpressionId}
      {instantiation : DeclarationInstantiation}
      (receipt : CallableCoercionExpressionCertificates.Direct compiled.indexed.base.sourceProgram
        ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
        named.specialized current (Child policy body fuel current) (fuel + 1)
        source scope id callee arguments instantiation reasonAt
        (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext []) head.node lowered)
  | boundary (head : Head policy body fuel current source scope id reasonAt lowered)
      (cause : Cause root head)

variable {root} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {reasonAt : ExpressionId → Word} {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

def ordinaryChildren {callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation}
    (receipt : Receipt policy body fuel current valueContext source scope id callee arguments instantiation reasonAt lowered) :=
  arguments.zip receipt.codes

def evidenceChildren {callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} {node : ExpressionNode}
    (receipt : CallableCoercionExpressionCertificates.Direct compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized current (Child policy body fuel current) (fuel + 1)
      source scope id callee arguments instantiation reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext []) node lowered) :=
  arguments.zip receipt.loweredArguments

def Step.children : Step root source scope reasonAt fuel id lowered →
    List (ExpressionId × SourceCoreBasic.LoweredExpr)
  | .leaf .. | .boundary .. => []
  | .ordinary _ _ receipt => ordinaryChildren receipt
  | .evidence _ _ receipt => evidenceChildren receipt

inductive Trace (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    Nat → ExpressionId → SourceCoreBasic.LoweredExpr → Type where
  | step {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} (actual : Step root source scope reasonAt fuel id lowered)
      (children : ∀ entry ∈ actual.children,
        Trace root source scope reasonAt fuel entry.1 entry.2) :
      Trace root source scope reasonAt (fuel + 1) id lowered

inductive Boundary : {fuel : Nat} → {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Trace root source scope reasonAt fuel id lowered → Type where
  | here {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
      (head : Head policy body fuel current source scope id reasonAt lowered)
      (cause : Cause root head)
      (children : ∀ entry ∈ (Step.boundary head cause).children,
        Trace root source scope reasonAt fuel entry.1 entry.2) :
      Boundary (.step (.boundary head cause) children)
  | child {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} (actual : Step root source scope reasonAt fuel id lowered)
      (children : ∀ entry ∈ actual.children, Trace root source scope reasonAt fuel entry.1 entry.2)
      (entry : ExpressionId × SourceCoreBasic.LoweredExpr) (member : entry ∈ actual.children)
      (next : Boundary (children entry member)) : Boundary (.step actual children)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Successful traversal keeps all positions, including repeated occurrences. -/
theorem mapM_receipt {α β ε : Type} {action : α → Except ε β} {ids : List α} {codes : List β}
    (accepted : ids.mapM action = .ok codes) :
    ids.length = codes.length ∧
      (∀ entry ∈ ids.zip codes, action entry.1 = .ok entry.2) ∧
      (∀ id ∈ ids, ∃ code, (id, code) ∈ ids.zip codes) := by
  induction ids generalizing codes with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst codes
    exact ⟨rfl, by simp, by simp⟩
  | cons id ids ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨code, first, accepted⟩ := bind_ok accepted
    obtain ⟨rest, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    obtain ⟨count, actions, complete⟩ := ih remaining
    refine ⟨congrArg Nat.succ count, ?_, ?_⟩
    · intro entry member
      rcases List.mem_cons.mp member with same | member
      · subst entry
        exact first
      · exact actions entry member
    · intro other member
      rcases List.mem_cons.mp member with same | member
      · subst other
        exact ⟨code, by simp⟩
      · obtain ⟨otherCode, member⟩ := complete other member
        exact ⟨otherCode, List.mem_cons_of_mem _ member⟩

/-- Each edge is an action that the selected compiler actually accepted. -/
theorem Step.child_accepted (actual : Step root source scope reasonAt fuel id lowered)
    (entry : ExpressionId × SourceCoreBasic.LoweredExpr) (member : entry ∈ actual.children) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel current source scope entry.1 reasonAt = .ok entry.2 := by
  cases actual with
  | leaf => cases member
  | boundary => cases member
  | ordinary head plain receipt => exact (mapM_receipt receipt.generated).2.1 entry member
  | evidence head selected receipt =>
    have accepted := (mapM_receipt receipt.argumentsAccepted).2.1 entry member
    simpa only [Child, Nat.min_eq_right (Nat.le_succ fuel)] using accepted

variable {directSites : DeclarationInstantiation → Prop}

theorem Step.of_head
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed named source directSites)
    (supported : ∀ instantiation, directSites instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) → directSites instantiation)
    (head : Head policy body fuel current source scope id reasonAt lowered) :
    Nonempty (Step root source scope reasonAt fuel id lowered) := by
  classical
  by_cases leaf : LeafForm head.node.form
  · have form : CompatibleExpressionLiterals.Atomic head.node.form ∨
        ∃ name binder, head.node.form = .reference name (.local binder) := leaf.view
    have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata head.found form
      (Child policy body fuel current) (fuel + 1) scope reasonAt
    have plain : head.special = none := Except.ok.inj (head.selected.symm.trans profile.2.2)
    exact ⟨.leaf head plain leaf⟩
  · by_cases direct : DirectForm head.node.form
    · obtain ⟨callee, arguments, instantiation, form⟩ := direct
      cases selected : head.special with
      | none =>
        have actual : specialAction policy body fuel current source scope id reasonAt = .ok none :=
          head.selected.trans (congrArg Except.ok selected)
        obtain ⟨receipt⟩ := AcceptedDirectExpressionReceipt.of_supported (values := valueContext) head.found form
          (supported instantiation (covered id head.node head.found callee arguments instantiation form)) actual
          (AcceptedNamedExpressionPolicy.direct_read root.compilerPolicy head.found form) head.accepted
        exact ⟨.ordinary head selected receipt⟩
      | some output =>
        have same := head.result output selected
        have selected' : head.special = some lowered := selected.trans (congrArg some same.symm)
        have actual : specialAction policy body fuel current source scope id reasonAt = .ok (some lowered) :=
          head.selected.trans (congrArg Except.ok selected')
        have extracted := AcceptedContextualDirectReceipt.of_special compilation root.compilerPolicy head.found form actual
        cases extracted with
        | inl receipts =>
          obtain ⟨receipt⟩ := receipts
          exact ⟨.evidence head selected' receipt⟩
        | inr initializers =>
          obtain ⟨initializer⟩ := initializers
          exact ⟨.boundary head (.initializer selected' initializer)⟩
    · cases selected : head.special with
      | none => exact ⟨.boundary head (.form selected leaf direct)⟩
      | some output =>
        have same := head.result output selected
        have selected' : head.special = some lowered := selected.trans (congrArg some same.symm)
        exact ⟨.boundary head (.special selected' direct)⟩

/-- Recursion follows successful child actions and their strictly smaller fuel. -/
theorem Trace.of_accepted
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed named source directSites)
    (supported : ∀ instantiation, directSites instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) → directSites instantiation)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel current source scope id reasonAt = .ok lowered) :
    Nonempty (Trace root source scope reasonAt fuel id lowered) := by
  induction fuel generalizing id lowered with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel ih =>
    obtain ⟨head⟩ := Head.of_accepted accepted
    obtain ⟨actual⟩ := Step.of_head metadata supported covered head
    exact ⟨.step actual (fun entry member => Classical.choice (ih (actual.child_accepted entry member)))⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
