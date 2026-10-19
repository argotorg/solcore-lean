import Solcore.SourceSemantics.CoreLowering.AcceptedProxyExpressionReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
import Solcore.SourceSemantics.CoreLowering.AcceptedCompositeExpressionReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedOrdinaryExpressionReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedContextualDirectReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionPolicy
import Solcore.SourceSemantics.CoreLowering.AcceptedIndirectExpressionReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedIndexExpressionReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedConstructorExpressionReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedContextualOperatorReceipt

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

def ProxyForm (form : ExpressionForm) : Prop := ∃ inner, form = .proxy inner

def IndexForm (form : ExpressionForm) : Prop := ∃ base key, form = .index base key

def ConstructorForm (form : ExpressionForm) : Prop :=
  ∃ instantiation ids, form = .constructor instantiation ids

abbrev CompositeForm := AcceptedCompositeExpressionReceipt.Form

abbrev BuiltinForm := AcceptedOrdinaryExpressionReceipt.BuiltinForm

abbrev MethodForm := AcceptedContextualOperatorReceipt.Form

def IndirectForm (form : ExpressionForm) : Prop :=
  ∃ callee arguments metadata, form = .call callee arguments (.indirect metadata)

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
      (outsideMethod : ¬ MethodForm head.node.form)
  | initializer (selected : head.special = some lowered)
      (actual : AcceptedContextualDirectReceipt.InitializerAt compiled.indexed current id)
  | form (selected : head.special = none)
      (notLeaf : ¬ LeafForm head.node.form) (notDirect : ¬ DirectForm head.node.form)
      (notIndirect : ¬ IndirectForm head.node.form) (notMethod : ¬ MethodForm head.node.form)
      (notIndex : ¬ IndexForm head.node.form) (notConstructor : ¬ ConstructorForm head.node.form)
      (notComposite : ¬ CompositeForm head.node.form) (notBuiltin : ¬ BuiltinForm head.node.form)
      (notProxy : ¬ ProxyForm head.node.form)
  | constructorRange (selected : head.special = none) {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
      (form : head.node.form = .constructor instantiation ids)
      (missing : ¬ CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution)
  | indexOperands (selected : head.special = none) {base key : ExpressionId}
      (form : head.node.form = .index base key)
      (missing : ¬ AcceptedIndexExpressionReceipt.Operands source base key)
  | operatorCoercions (selected : head.special = some lowered) (form : MethodForm head.node.form)
      (coercions : head.node.coercions ≠ [])

inductive Step (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) (fuel : Nat) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) where
  | leaf (head : Head policy body fuel current source scope id reasonAt lowered)
      (plain : head.special = none) (form : LeafForm head.node.form)
  | proxy (head : Head policy body fuel current source scope id reasonAt lowered)
      (plain : head.special = none)
      (receipt : CompatibleExpressionProxies.Certificate valueContext source scope id lowered)
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
  | indirect (head : Head policy body fuel current source scope id reasonAt lowered)
      (plain : head.special = none) {callee : ExpressionId} {arguments : List ExpressionId}
      {metadata : IndirectCallResolution}
      (receipt : CallableIndirectCallCertificates.Receipt policy body fuel current source scope
        id callee arguments metadata reasonAt lowered)
  | method (head : Head policy body fuel current source scope id reasonAt lowered)
      (selected : head.special = some lowered)
      (receipt : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
        policy body fuel current valueContext source scope id reasonAt lowered)
  | index (head : Head policy body fuel current source scope id reasonAt lowered)
      (plain : head.special = none) {base key : ExpressionId}
      (receipt : AcceptedIndexExpressionReceipt.Receipt root source scope reasonAt fuel id base key lowered)
  | constructor (head : Head policy body fuel current source scope id reasonAt lowered)
      (plain : head.special = none) {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
      (receipt : AcceptedConstructorExpressionReceipt.Receipt root source scope reasonAt fuel id instantiation ids lowered)
  | composite (head : Head policy body fuel current source scope id reasonAt lowered)
      (plain : head.special = none)
      (receipt : AcceptedCompositeExpressionReceipt.Receipt root source scope reasonAt fuel id lowered)
  | primitive (head : Head policy body fuel current source scope id reasonAt lowered)
      (plain : head.special = none)
      (receipt : AcceptedOrdinaryExpressionReceipt.OperatorReceipt root source scope reasonAt fuel id lowered)
  | builtin (head : Head policy body fuel current source scope id reasonAt lowered)
      (plain : head.special = none) {callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
      (receipt : CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.Receipt policy body fuel current valueContext
        source scope id callee ids function reasonAt lowered)
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
  | .leaf .. | .proxy .. | .boundary .. => []
  | .ordinary _ _ receipt => ordinaryChildren receipt
  | .evidence _ _ receipt => evidenceChildren receipt
  | .indirect _ _ receipt => receipt.entries
  | .method _ _ receipt => receipt.arguments.zip receipt.codes
  | .index (base := base) (key := key) _ _ receipt => [(base, receipt.first), (key, receipt.second)]
  | .constructor (ids := ids) _ _ receipt => ids.zip receipt.codes
  | .composite _ _ receipt => (AcceptedCompositeExpressionReceipt.operands receipt.node.form).zip receipt.codes
  | .primitive _ _ receipt => (AcceptedOrdinaryExpressionReceipt.operands receipt.node.form).zip receipt.codes
  | .builtin (ids := ids) _ _ receipt => ids.zip receipt.codes

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
  | leaf | proxy => cases member
  | boundary => cases member
  | ordinary head plain receipt => exact (mapM_receipt receipt.generated).2.1 entry member
  | evidence head selected receipt =>
    have accepted := (mapM_receipt receipt.argumentsAccepted).2.1 entry member
    simpa only [Child, Nat.min_eq_right (Nat.le_succ fuel)] using accepted

  | indirect head plain receipt => exact receipt.ordered_children.2 entry.1 entry.2 member
  | method head selected receipt => exact (mapM_receipt receipt.generated).2.1 entry member
  | constructor head plain receipt => exact (mapM_receipt (receipt.generated root)).2.1 entry member
  | composite head plain receipt => exact (mapM_receipt receipt.generated).2.1 entry member
  | primitive head plain receipt => exact (mapM_receipt receipt.generated).2.1 entry member
  | builtin head plain receipt => exact (mapM_receipt receipt.generated).2.1 entry member
  | index head plain receipt =>
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ receipt.firstAccepted
    · have same := List.mem_singleton.mp member
      exact same ▸ receipt.secondAccepted

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
    · by_cases method : MethodForm head.node.form
      · cases selected : head.special with
        | none =>
          obtain ⟨receipt⟩ := AcceptedOrdinaryExpressionReceipt.operator_of_head root head selected method
          exact ⟨.primitive head selected receipt⟩
        | some output =>
          have same := head.result output selected
          have selected' : head.special = some lowered := selected.trans (congrArg some same.symm)
          by_cases coercions : head.node.coercions = []
          · cases AcceptedContextualOperatorReceipt.of_head root head selected' method coercions with
            | inl methods =>
              obtain ⟨receipt⟩ := methods
              exact ⟨.method head selected' receipt⟩
            | inr initializers =>
              obtain ⟨initializer⟩ := initializers
              exact ⟨.boundary head (.initializer selected' initializer)⟩
          · exact ⟨.boundary head (.operatorCoercions selected' method coercions)⟩
      · cases selected : head.special with
        | none =>
          by_cases indirect : IndirectForm head.node.form
          · obtain ⟨callee, arguments, metadata, form⟩ := indirect
            obtain ⟨receipt⟩ := AcceptedIndirectExpressionReceipt.of_head root head selected form
            exact ⟨.indirect head selected receipt⟩
          · by_cases index : IndexForm head.node.form
            · obtain ⟨base, key, form⟩ := index
              by_cases operands : AcceptedIndexExpressionReceipt.Operands source base key
              · obtain ⟨baseNode, keyNode, baseFound, keyFound⟩ := operands
                obtain ⟨receipt⟩ := AcceptedIndexExpressionReceipt.of_head root head selected form baseFound keyFound
                exact ⟨.index head selected receipt⟩
              · exact ⟨.boundary head (.indexOperands selected form operands)⟩
            · by_cases constructor : ConstructorForm head.node.form
              · obtain ⟨instantiation, ids, form⟩ := constructor
                by_cases range : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution
                · obtain ⟨receipt⟩ := AcceptedConstructorExpressionReceipt.of_head root head selected form range
                  exact ⟨.constructor head selected receipt⟩
                · exact ⟨.boundary head (.constructorRange selected form range)⟩
              · by_cases composite : CompositeForm head.node.form
                · obtain ⟨receipt⟩ := AcceptedCompositeExpressionReceipt.of_head root head selected composite
                  exact ⟨.composite head selected receipt⟩
                · by_cases builtin : BuiltinForm head.node.form
                  · obtain ⟨callee, ids, function, form⟩ := builtin
                    obtain ⟨receipt⟩ := AcceptedOrdinaryExpressionReceipt.builtin_of_head root head selected form
                    exact ⟨.builtin head selected receipt⟩
                  · by_cases proxy : ProxyForm head.node.form
                    · obtain ⟨inner, form⟩ := proxy
                      exact ⟨.proxy head selected (AcceptedProxyExpressionReceipt.of_head root head selected form)⟩
                    · exact ⟨.boundary head (.form selected leaf direct indirect method index constructor composite builtin proxy)⟩
        | some output =>
          have same := head.result output selected
          have selected' : head.special = some lowered := selected.trans (congrArg some same.symm)
          exact ⟨.boundary head (.special selected' direct method)⟩

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
