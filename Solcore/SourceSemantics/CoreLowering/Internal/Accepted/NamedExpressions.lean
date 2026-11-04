import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ExpressionReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedMethodAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySyntaxTable

/-!
# Accepted named expressions

The accepted expression tree of named bodies: syntax, residuals, metadata, boundary exclusion and admission, with method body receipts.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionTree
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedCoercedDirectExpressionReceipt
/-! A nonempty original coercion suffix forces the genuine evidence branch.
The resulting receipt retains its complete selected call and ordered children. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCoercedDirectExpressionReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open AcceptedNamedExpressionFlow
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child Supported)

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

theorem of_head {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (head : Head policy body fuel current source scope id reasonAt lowered)
    (form : head.node.form = .call callee arguments (.declaration instantiation))
    (supported : Supported (current).plan instantiation)
    (coercions : head.node.coercions ≠ [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (current).owner ∧ binding.initializer = id)) = none) :
    Nonempty (CallableCoercionExpressionCertificates.Direct compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized current (Child policy body fuel current) (fuel + 1)
      source scope id callee arguments instantiation reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext []) head.node lowered) := by
  cases selected : head.special with
  | none =>
    have actual : specialAction policy body fuel current source scope id reasonAt = .ok none :=
      head.selected.trans (congrArg Except.ok selected)
    obtain ⟨receipt⟩ := AcceptedDirectExpressionReceipt.of_supported
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      head.found form supported actual
      (AcceptedNamedExpressionPolicy.direct_read root.compilerPolicy head.found form) head.accepted
    have same := Option.some.inj (receipt.metadata.found.symm.trans head.found)
    exact False.elim (coercions (same ▸ receipt.metadata.coercions))
  | some output =>
    have same := head.result output selected
    have selected' : head.special = some lowered := selected.trans (congrArg some same.symm)
    have actual : specialAction policy body fuel current source scope id reasonAt = .ok (some lowered) :=
      head.selected.trans (congrArg Except.ok selected')
    have extracted := AcceptedContextualDirectReceipt.of_special compilation root.compilerPolicy
      head.found form actual
    cases extracted with
    | inl receipt => exact receipt
    | inr initializers =>
      obtain ⟨initializer⟩ := initializers
      have found := initializer.found
      rw [ordinary] at found
      cases found

/-- Each leaf is matched to its own successful action in the full ordered
argument list, at the actual predecessor budget. -/
theorem children {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CallableCoercionExpressionCertificates.Direct compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized current (Child policy body fuel current) (fuel + 1)
      source scope id callee arguments instantiation reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext []) node lowered)
    (forms : ∀ argument ∈ arguments, ∃ node,
      source.lookupExpression? argument = some node ∧ LeafForm node.form) :
    ∀ argument ∈ arguments,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        source argument (fun _ => False) := by
  intro argument member
  obtain ⟨code, present⟩ := (mapM_receipt receipt.argumentsAccepted).2.2 argument member
  have generated := (mapM_receipt receipt.argumentsAccepted).2.1 (argument, code) present
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel current
      source scope argument reasonAt = .ok code := by
    simpa only [Child, Nat.min_eq_right (Nat.le_succ fuel)] using generated
  cases fuel with
  | zero => simp only [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted; cases accepted
  | succ predecessor =>
    obtain ⟨head⟩ := Head.of_accepted accepted
    obtain ⟨original, found, form⟩ := forms argument member
    have same := Option.some.inj (head.found.symm.trans found)
    have leaf : LeafForm head.node.form := same ▸ form
    rcases leaf.view with literal | ⟨name, binder, read⟩
    · exact .leaf (.literal head.found literal)
    · exact .leaf (.read head.found read)

end Solcore.SourceSemantics.CoreLowering.AcceptedCoercedDirectExpressionReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionResidual
/-! A residual retains the exact accepted Header expression and a boundary
reached through its own original, ordered compiler child actions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
open Core Frontend SourceInference
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)

structure Residual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (_directSites : DeclarationInstantiation → Prop)
    (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  accepted : header.policy.lowerExpression fuel source scope id header.reasonAt = .ok lowered
  predecessor : Nat
  sameFuel : fuel = predecessor + 1
  root : RootPolicyReceipt (compiled := compiled) prepared.named prepared.diagnostics prepared.code
    prepared.compilation predecessor source scope id header.reasonAt lowered
  tree : Trace root source scope header.reasonAt (predecessor + 1) id lowered
  boundary : Boundary tree

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionTraceSyntax
/-! The compiler trace supplies original expression grammar or an exact path to
an unexpanded action. Successful traversal covers every ordered argument. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  {root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {directSites : DeclarationInstantiation → Prop}

/-- The residual names the same trace and follows its actual child positions.
Argument coverage uses accepted map traversal, including repeated occurrences. -/
theorem Trace.syntax_or_boundary
    (trace : Trace root source scope reasonAt fuel id lowered)
    (covered : ∀ child node, source.lookupExpression? child = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        directSites instantiation) :
    GeneralSyntax source id directSites ∨ Nonempty (Boundary trace) := by
  classical
  induction trace with
  | @step fuel id lowered actual children ih =>
    by_cases all : ∀ entry ∈ actual.children, GeneralSyntax source entry.1 directSites
    · cases actual with
      | leaf head plain form =>
        rcases form.view with atomic | ⟨name, binder, localForm⟩
        · exact .inl (.leaf (.literal head.found atomic))
        · exact .inl (.leaf (.read head.found localForm))
      | proxy head plain receipt =>
        cases receipt with
        | proxy header => exact .inl (.proxy header.metadata.found header.form)
      | boundary head cause => exact .inr ⟨.here head cause children⟩
      | ordinary head plain receipt =>
        refine .inl (.direct receipt.metadata.found receipt.form
          (covered id receipt.node receipt.metadata.found _ _ _ receipt.form) ?_)
        intro argument member
        obtain ⟨code, present⟩ := (mapM_receipt receipt.generated).2.2 argument member
        exact all (argument, code) present
      | evidence head selected receipt =>
        refine .inl (.direct receipt.found receipt.form
          (covered id head.node receipt.found _ _ _ receipt.form) ?_)
        intro argument member
        obtain ⟨code, present⟩ := (mapM_receipt receipt.argumentsAccepted).2.2 argument member
        exact all (argument, code) present
      | indirect head plain receipt =>
        refine .inl (.call receipt.found receipt.originalForm ?_ ?_)
        · exact all (_, receipt.calleeCode) (by
            simp only [Step.children, CallableIndirectCallCertificates.Receipt.entries, List.mem_cons_self])
        · intro argument member
          obtain ⟨code, present⟩ := (mapM_receipt receipt.argumentsAccepted).2.2 argument member
          exact all (argument, code) (List.mem_cons_of_mem _ present)
      | constructor head plain receipt =>
        refine .inl (.constructor receipt.found receipt.form receipt.range ?_)
        intro argument member
        obtain ⟨code, present⟩ := (mapM_receipt (receipt.generated root)).2.2 argument member
        exact all (argument, code) present
      | index head plain receipt =>
        exact .inl (.index receipt.found receipt.form receipt.keyFound
          (all (_, receipt.first) (by simp only [Step.children, List.mem_cons_self]))
          (all (_, receipt.second) (by simp [Step.children])))
      | primitive head plain receipt =>
        have grammar : ∀ child ∈ AcceptedOrdinaryExpressionReceipt.operands receipt.node.form,
            GeneralSyntax source child directSites := by
          intro child member
          obtain ⟨code, present⟩ := (mapM_receipt receipt.generated).2.2 child member
          exact all (child, code) present
        rcases receipt.form with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
        · exact .inl (.unary receipt.found form
            (grammar operand (by simp [form, AcceptedOrdinaryExpressionReceipt.operands])))
        · exact .inl (.binary receipt.found form
            (grammar left (by simp [form, AcceptedOrdinaryExpressionReceipt.operands]))
            (grammar right (by simp [form, AcceptedOrdinaryExpressionReceipt.operands])))
      | builtin head plain receipt =>
        refine .inl (.builtin receipt.metadata.found receipt.form ?_)
        intro child member
        obtain ⟨code, present⟩ := (mapM_receipt receipt.generated).2.2 child member
        exact all (child, code) present
      | composite head plain receipt =>
        have grammar : ∀ child ∈ AcceptedCompositeExpressionReceipt.operands receipt.node.form,
            GeneralSyntax source child directSites := by
          intro child member
          obtain ⟨code, present⟩ := (mapM_receipt receipt.generated).2.2 child member
          exact all (child, code) present
        have form := receipt.form
        generalize same : receipt.node.form = shape at form
        cases form with
        | group inner =>
          exact .inl (.group receipt.found same (grammar inner (by simp [same, AcceptedCompositeExpressionReceipt.operands])))
        | tuple first rest =>
          exact .inl (.tuple receipt.found same (by simpa only [same, AcceptedCompositeExpressionReceipt.operands] using grammar))
        | conditional test yes no =>
          exact .inl (.conditional receipt.found same
            (grammar test (by simp [same, AcceptedCompositeExpressionReceipt.operands]))
            (grammar yes (by simp [same, AcceptedCompositeExpressionReceipt.operands]))
            (grammar no (by simp [same, AcceptedCompositeExpressionReceipt.operands])))
      | method head selected receipt =>
        have childrenSyntax : ∀ child ∈ receipt.arguments, GeneralSyntax source child directSites := by
          intro child member
          obtain ⟨code, present⟩ := (mapM_receipt receipt.generated).2.2 child member
          exact all (child, code) present
        rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ |
          ⟨operator, left, right, form, arguments⟩
        · refine .inl (.unary receipt.metadata.found form (childrenSyntax operand ?_))
          simp only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
            arguments, List.mem_singleton]
        · refine .inl (.binary receipt.metadata.found form (childrenSyntax left ?_) (childrenSyntax right ?_))
          all_goals simp only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
            arguments, List.mem_cons, true_or, or_true]
    · obtain ⟨entry, absent⟩ := Classical.not_forall.mp all
      have member : entry ∈ actual.children := Classical.byContradiction fun missing =>
        absent (fun present => False.elim (missing present))
      have missing : ¬ GeneralSyntax source entry.1 directSites :=
        fun grammar => absent (fun _ => grammar)
      cases ih entry member with
      | inl grammar => exact False.elim (missing grammar)
      | inr boundary => exact .inr ⟨.child actual children entry member (Classical.choice boundary)⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionSyntax
/-! Genuine Header acceptance supplies the entire recursive action trace. Its
original expression grammar is derived only after those actions are recovered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

/-- The result uses the genuine selected policy and actual ordered child calls.
Metadata and supported target rows stay explicit static premises. -/
theorem syntax_of_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {directSites : DeclarationInstantiation → Prop}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named source directSites)
    (supported : ∀ instantiation, directSites instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) → directSites instantiation)
    (accepted : header.policy.lowerExpression fuel source scope id header.reasonAt = .ok lowered) :
    GeneralSyntax source id directSites ∨ Nonempty (Residual prepared header directSites fuel source scope id lowered) := by
  obtain ⟨predecessor, sameFuel, root, _head⟩ := of_header prepared aligned accepted
  obtain ⟨tree⟩ := Trace.of_accepted (root := root) metadata supported covered root.selected.accepted
  cases Trace.syntax_or_boundary tree covered with
  | inl grammar => exact .inl grammar
  | inr boundaries =>
    obtain ⟨boundary⟩ := boundaries
    exact .inr ⟨⟨accepted, predecessor, sameFuel, root, tree, boundary⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionMetadata
/-! Successful finite metadata checking retains facts for each original supported
node before any recursive expression grammar has been constructed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionMetadata
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedNamedSyntaxAdmission
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

theorem at_of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {source : TypedSource}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : metadata? prepared named source directSites = some receipt)
    {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (supported : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.SupportedForm node.form) :
    MetadataTest prepared named node := by
  unfold metadata? at accepted
  simp only [bind, Option.bind] at accepted
  split at accepted
  next => contradiction
  next facts selected =>
    exact facts.down _ (lookupExpression?_sound found).1 node rfl (by
      generalize shape : node.form = original at supported ⊢
      cases supported with
      | literal atomic => cases atomic <;> rfl
      | proxy | read | unary | binary | index | conditional | group | tuple | constructor | builtin | direct | call => rfl)


theorem indirect_of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {source : TypedSource}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : metadata? prepared named source directSites = some receipt)
    {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (form : node.form = .call callee arguments (.indirect metadata)) :
    MetadataTest prepared named node := by
  exact at_of_accepted accepted found (form ▸ .call callee arguments metadata)

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionMetadata
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionBoundaryExclusion
/-! A finite set of reached original occurrences excludes expression boundaries.
Closure follows actual ordered call children. Declaration names stay static;
indirect callees are retained as the leading child. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  {root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {directSites : DeclarationInstantiation → Prop} {reached : ExpressionId → Prop}

/-- Only original occurrences that are actually reached need these form facts. -/
def ReachedForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    LeafForm node.form ∨ DirectForm node.form

/-- Every argument occurrence is retained, including duplicate positions. -/
def ReachedArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
      ∀ argument ∈ arguments, reached argument

private theorem leaf_not_method {form : ExpressionForm} (leaf : LeafForm form) : ¬ MethodForm form := by
  rcases leaf.view with atomic | ⟨name, binder, rfl⟩
  · cases atomic <;> simp [MethodForm, AcceptedContextualOperatorReceipt.Form]
  · simp [MethodForm, AcceptedContextualOperatorReceipt.Form]

private theorem direct_not_method {form : ExpressionForm} (direct : DirectForm form) : ¬ MethodForm form := by
  obtain ⟨callee, arguments, instantiation, rfl⟩ := direct
  simp [MethodForm, AcceptedContextualOperatorReceipt.Form]

private theorem indirect_not_method {form : ExpressionForm} (indirect : IndirectForm form) : ¬ MethodForm form := by
  obtain ⟨callee, arguments, metadata, rfl⟩ := indirect
  simp [MethodForm, AcceptedContextualOperatorReceipt.Form]

private theorem not_index {form : ExpressionForm}
    (allowed : LeafForm form ∨ DirectForm form ∨ IndirectForm form ∨ MethodForm form) : ¬ IndexForm form := by
  rcases allowed with leaf | ⟨callee, args, inst, rfl⟩ | ⟨callee, args, metadata, rfl⟩ | method
  · rcases leaf.view with atomic | ⟨name, binder, rfl⟩
    · cases atomic <;> simp [IndexForm]
    · simp [IndexForm]
  · simp [IndexForm]
  · simp [IndexForm]
  · rcases method with ⟨operator, operand, rfl⟩ | ⟨operator, left, right, rfl⟩ <;> simp [IndexForm]

private theorem not_constructor {form : ExpressionForm}
    (allowed : (LeafForm form ∨ DirectForm form ∨ IndirectForm form ∨ MethodForm form) ∨ IndexForm form) :
    ¬ ConstructorForm form := by
  rcases allowed with (leaf | ⟨callee, args, inst, rfl⟩ | ⟨callee, args, metadata, rfl⟩ | method) | ⟨base, key, rfl⟩
  · rcases leaf.view with atomic | ⟨name, binder, rfl⟩
    · cases atomic <;> simp [ConstructorForm]
    · simp [ConstructorForm]
  · simp [ConstructorForm]
  · simp [ConstructorForm]
  · rcases method with ⟨operator, operand, rfl⟩ | ⟨operator, left, right, rfl⟩ <;> simp [ConstructorForm]
  · simp [ConstructorForm]

private theorem not_composite {form : ExpressionForm}
    (allowed : ((LeafForm form ∨ DirectForm form ∨ IndirectForm form ∨ MethodForm form) ∨ IndexForm form) ∨ ConstructorForm form) :
    ¬ CompositeForm form := by
  intro composite
  rcases allowed with ((leaf | ⟨callee, args, inst, rfl⟩ | ⟨callee, args, metadata, rfl⟩ | method) | ⟨base, key, rfl⟩) | ⟨inst, ids, rfl⟩
  · rcases leaf.view with atomic | ⟨name, binder, rfl⟩
    · cases atomic <;> cases composite
    · cases composite
  · cases composite
  · cases composite
  · rcases method with ⟨operator, operand, rfl⟩ | ⟨operator, left, right, rfl⟩ <;> cases composite
  · cases composite
  · cases composite

private theorem not_builtin {form : ExpressionForm}
    (allowed : (((LeafForm form ∨ DirectForm form ∨ IndirectForm form ∨ MethodForm form) ∨ IndexForm form) ∨ ConstructorForm form) ∨ CompositeForm form) :
    ¬ BuiltinForm form := by
  intro ⟨callee, ids, function, same⟩
  rcases allowed with (((leaf | ⟨callee, args, inst, rfl⟩ | ⟨callee, args, metadata, rfl⟩ | method) | ⟨base, key, rfl⟩) | ⟨inst, ids, rfl⟩) | composite
  · rcases leaf.view with atomic | ⟨name, binder, rfl⟩
    · cases atomic <;> cases same
    · cases same
  · cases same
  · cases same
  · rcases method with ⟨operator, operand, rfl⟩ | ⟨operator, left, right, rfl⟩ <;> cases same
  · cases same
  · cases same
  · cases composite <;> cases same

private theorem receipt_method_form
    (receipt : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
      root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      (.initial compiled.compatible.checked) source scope id reasonAt lowered) : MethodForm receipt.node.form := by
  rcases receipt.operator.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
  · exact .inl ⟨operator, operand, form⟩
  · exact .inr ⟨operator, left, right, form⟩

private theorem forms_not_method (forms : ReachedForms source reached)
    {id : ExpressionId} {node : ExpressionNode} (present : reached id)
    (found : source.lookupExpression? id = some node) : ¬ MethodForm node.form := by
  rcases forms id node present found with leaf | direct
  · exact leaf_not_method leaf
  · exact direct_not_method direct

theorem Cause.impossible
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False := by
  have form := forms id head.node present head.found
  cases cause with
  | form _ notLeaf notDirect _ _ _ _ _ _ _ =>
    rcases form with leaf | direct
    · exact notLeaf leaf
    · exact notDirect direct
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | special selected outside _ =>
    rcases form with leaf | direct
    · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata
        head.found leaf.view (Child root.selected.policy root.selected.lowerBody fuel
          (context compiled.indexed named)) (fuel + 1) scope reasonAt
      have same := head.selected.symm.trans profile.2.2
      rw [selected] at same
      cases same
    · exact outside direct

  | operatorCoercions _ operator _ =>
    exact forms_not_method forms present head.found operator

  | indexOperands _ indexForm _ => exact not_index (by rcases form with leaf | direct; exact .inl leaf; exact .inr (.inl direct)) ⟨_, _, indexForm⟩

  | constructorRange _ constructorForm _ => exact not_constructor (by rcases form with leaf | direct; exact .inl (.inl leaf); exact .inl (.inr (.inl direct))) ⟨_, _, constructorForm⟩

theorem Step.child_reached
    (forms : ReachedForms source reached)
    (arguments : ReachedArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf | proxy => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have original := forms id receipt.original present receipt.found
    rcases original with leaf | ⟨callee, args, instantiation, direct⟩
    · rw [receipt.originalForm] at leaf
      cases leaf with
      | literal atomic => cases atomic
    · rw [receipt.originalForm] at direct
      cases direct

  | method head selected receipt =>
    exact False.elim (forms_not_method forms present receipt.metadata.found (receipt_method_form receipt))

  | index head plain receipt =>
    exact False.elim (not_index (by rcases forms id receipt.node present receipt.found with leaf | direct; exact .inl leaf; exact .inr (.inl direct)) ⟨_, _, receipt.form⟩)

  | constructor head plain receipt =>
    exact False.elim (not_constructor (by rcases forms id receipt.node present receipt.found with leaf | direct; exact .inl (.inl leaf); exact .inl (.inr (.inl direct))) ⟨_, _, receipt.form⟩)

  | composite head plain receipt =>
    exact False.elim (not_composite (by rcases forms id receipt.node present receipt.found with leaf | direct; exact .inl (.inl (.inl leaf)); exact .inl (.inl (.inr (.inl direct)))) receipt.form)

  | primitive head plain receipt =>
    exact False.elim (forms_not_method forms present receipt.found receipt.form)
  | builtin head plain receipt =>
    exact False.elim (not_builtin (by rcases forms id receipt.node present receipt.metadata.found with leaf | direct; exact .inl (.inl (.inl (.inl leaf))); exact .inl (.inl (.inl (.inr (.inl direct))))) ⟨_, _, _, receipt.form⟩)

/-- The excluded endpoint belongs to this same trace and its actual child path. -/
theorem Boundary.impossible
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedArguments source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible metadata forms initializers present
  | child step children entry member next ih => exact ih (step.child_reached forms arguments present member)

/-- The Header residual is excluded by forms and actual argument reachability.
No recursive expression grammar is a premise. -/
theorem Residual.impossible {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedArguments source reached)
    (present : reached id) : False :=
  residual.boundary.impossible metadata forms initializers arguments present

/-- Indirect calls include the original callee occurrence as well as arguments. -/
def ReachedCallForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    LeafForm node.form ∨ DirectForm node.form ∨ IndirectForm node.form

/-- Reachability follows original argument order, with an indirect callee first. -/
def ReachedCallArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedArguments source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ callee arguments metadata, node.form = .call callee arguments (.indirect metadata) →
      reached callee ∧ ∀ argument ∈ arguments, reached argument

/-- These are raw original-node checks, independent of recursive grammar. -/
def ReachedIndirectMetadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ callee arguments metadata, node.form = .call callee arguments (.indirect metadata) →
      CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest prepared named node

theorem ReachedIndirectMetadata.of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {source : TypedSource} {reached : ExpressionId → Prop}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      prepared named source directSites = some receipt) :
    ReachedIndirectMetadata prepared named source reached := by
  intro id node _ found callee arguments metadata form
  exact AcceptedNamedExpressionMetadata.indirect_of_accepted accepted found form

private theorem callForms_not_method (forms : ReachedCallForms source reached)
    {id : ExpressionId} {node : ExpressionNode} (present : reached id)
    (found : source.lookupExpression? id = some node) : ¬ MethodForm node.form := by
  rcases forms id node present found with leaf | direct | indirect
  · exact leaf_not_method leaf
  · exact direct_not_method direct
  · exact indirect_not_method indirect

theorem Cause.impossible_calls
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedCallForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedIndirectMetadata compiled.indexed named source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False := by
  have original := forms id head.node present head.found
  cases cause with
  | form _ notLeaf notDirect notIndirect _ _ _ _ _ _ =>
    rcases original with leaf | direct | indirect
    · exact notLeaf leaf
    · exact notDirect direct
    · exact notIndirect indirect
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | special selected outside _ =>
    rcases original with leaf | direct | ⟨callee, arguments, callMetadata, form⟩
    · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata
        head.found leaf.view (Child root.selected.policy root.selected.lowerBody fuel
          (context compiled.indexed named)) (fuel + 1) scope reasonAt
      have same := head.selected.symm.trans profile.2.2
      rw [selected] at same
      cases same
    · exact outside direct
    · have clean := rawMetadata id head.node present head.found callee arguments callMetadata form
      have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root (scope := scope) (reasonAt := reasonAt) head.found form
        (by simpa only [form] using clean.2.2.1) clean.1
        (by simpa only [form] using clean.2.2.2.1)
        (by simpa only [(lookupExpression?_sound head.found).2] using clean.2.1)
      have noneSelected := profile.special
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same

  | operatorCoercions _ operator _ =>
    exact callForms_not_method forms present head.found operator

  | indexOperands _ indexForm _ => exact not_index (by rcases original with leaf | direct | indirect; exact .inl leaf; exact .inr (.inl direct); exact .inr (.inr (.inl indirect))) ⟨_, _, indexForm⟩

  | constructorRange _ constructorForm _ => exact not_constructor (by rcases original with leaf | direct | indirect; exact .inl (.inl leaf); exact .inl (.inr (.inl direct)); exact .inl (.inr (.inr (.inl indirect)))) ⟨_, _, constructorForm⟩

theorem Step.child_reached_calls
    (forms : ReachedCallForms source reached)
    (arguments : ReachedCallArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf | proxy => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments.1 id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments.1 id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have children := arguments.2 id receipt.original present receipt.found _ _ _ receipt.originalForm
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact children.2 entry.1 (List.of_mem_zip member).1

  | method head selected receipt =>
    exact False.elim (callForms_not_method forms present receipt.metadata.found (receipt_method_form receipt))

  | index head plain receipt =>
    exact False.elim (not_index (by rcases forms id receipt.node present receipt.found with leaf | direct | indirect; exact .inl leaf; exact .inr (.inl direct); exact .inr (.inr (.inl indirect))) ⟨_, _, receipt.form⟩)

  | constructor head plain receipt =>
    exact False.elim (not_constructor (by rcases forms id receipt.node present receipt.found with leaf | direct | indirect; exact .inl (.inl leaf); exact .inl (.inr (.inl direct)); exact .inl (.inr (.inr (.inl indirect)))) ⟨_, _, receipt.form⟩)

  | composite head plain receipt =>
    exact False.elim (not_composite (by rcases forms id receipt.node present receipt.found with leaf | direct | indirect; exact .inl (.inl (.inl leaf)); exact .inl (.inl (.inr (.inl direct))); exact .inl (.inl (.inr (.inr (.inl indirect))))) receipt.form)

  | primitive head plain receipt =>
    exact False.elim (callForms_not_method forms present receipt.found receipt.form)
  | builtin head plain receipt =>
    exact False.elim (not_builtin (by rcases forms id receipt.node present receipt.metadata.found with leaf | direct | indirect; exact .inl (.inl (.inl (.inl leaf))); exact .inl (.inl (.inl (.inr (.inl direct)))); exact .inl (.inl (.inl (.inr (.inr (.inl indirect)))))) ⟨_, _, _, receipt.form⟩)

theorem Boundary.impossible_calls
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedCallForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedCallArguments source reached)
    (rawMetadata : ReachedIndirectMetadata compiled.indexed named source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible_calls metadata forms initializers rawMetadata present
  | child step children entry member next ih => exact ih (step.child_reached_calls forms arguments present member)

theorem Residual.impossible_calls {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedCallForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedCallArguments source reached)
    (rawMetadata : ReachedIndirectMetadata compiled.indexed prepared.named source reached)
    (present : reached id) : False :=
  residual.boundary.impossible_calls metadata forms initializers arguments rawMetadata present

/-- Method occurrences are original unary or binary nodes. -/
def ReachedMethodForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    LeafForm node.form ∨ DirectForm node.form ∨ IndirectForm node.form ∨ MethodForm node.form

/-- Method operands retain unary or left-to-right binary order. -/
def ReachedMethodArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedCallArguments source reached ∧
  (∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ operator operand, node.form = .unary operator operand → reached operand) ∧
  (∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ operator left right, node.form = .binary left operator right → reached left ∧ reached right)

/-- The bounded method lane requires the genuine nonempty requirement list. -/
def ReachedMethodRequirements (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    MethodForm node.form → node.requirements ≠ []

def ReachedMethodMetadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedIndirectMetadata prepared named source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    MethodForm node.form → CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest prepared named node

theorem ReachedMethodMetadata.of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {source : TypedSource} {reached : ExpressionId → Prop}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      prepared named source directSites = some receipt) :
    ReachedMethodMetadata prepared named source reached := by
  refine ⟨ReachedIndirectMetadata.of_accepted accepted, ?_⟩
  intro id node _ found form
  apply AcceptedNamedExpressionMetadata.at_of_accepted accepted found
  rcases form with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
  · exact form ▸ .unary operator operand
  · exact form ▸ .binary left operator right

theorem Cause.impossible_methods
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedMethodForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedMethodMetadata compiled.indexed named source reached)
    (_requirements : ReachedMethodRequirements source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False := by
  have original := forms id head.node present head.found
  cases cause with
  | form _ notLeaf notDirect notIndirect notMethod _ _ _ _ _ =>
    rcases original with leaf | direct | indirect | method
    · exact notLeaf leaf
    · exact notDirect direct
    · exact notIndirect indirect
    · exact notMethod method
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | operatorCoercions _ form nonempty => exact nonempty (rawMetadata.2 id head.node present head.found form).1
  | special selected outside outsideMethod =>
    rcases original with leaf | direct | ⟨callee, arguments, callMetadata, form⟩ | method
    · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata
        head.found leaf.view (Child root.selected.policy root.selected.lowerBody fuel
          (context compiled.indexed named)) (fuel + 1) scope reasonAt
      have same := head.selected.symm.trans profile.2.2
      rw [selected] at same
      cases same
    · exact outside direct
    · have clean := rawMetadata.1 id head.node present head.found callee arguments callMetadata form
      have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root
        (scope := scope) (reasonAt := reasonAt) head.found form
        (by simpa only [form] using clean.2.2.1) clean.1
        (by simpa only [form] using clean.2.2.2.1)
        (by simpa only [(lookupExpression?_sound head.found).2] using clean.2.1)
      have noneSelected := profile.special
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same
    · exact outsideMethod method

  | indexOperands _ indexForm _ => exact not_index (original) ⟨_, _, indexForm⟩

  | constructorRange _ constructorForm _ => exact not_constructor (.inl (original)) ⟨_, _, constructorForm⟩

theorem Step.child_reached_methods
    (forms : ReachedMethodForms source reached)
    (arguments : ReachedMethodArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf | proxy => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments.1.1 id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments.1.1 id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have children := arguments.1.2 id receipt.original present receipt.found _ _ _ receipt.originalForm
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact children.2 entry.1 (List.of_mem_zip member).1
  | method head _ receipt =>
    have child := (List.of_mem_zip member).1
    rcases receipt.operator.form with ⟨operator, operand, form, actual⟩ |
      ⟨operator, left, right, form, actual⟩
    · have same : entry.1 = operand := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_singleton] using child
      exact same ▸ arguments.2.1 id receipt.node present receipt.metadata.found operator operand form
    · have cases : entry.1 = left ∨ entry.1 = right := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_cons, List.not_mem_nil, or_false] using child
      have children := arguments.2.2 id receipt.node present receipt.metadata.found operator left right form
      rcases cases with same | same
      · exact same ▸ children.1
      · exact same ▸ children.2

  | index head plain receipt =>
    exact False.elim (not_index (forms id receipt.node present receipt.found) ⟨_, _, receipt.form⟩)

  | constructor head plain receipt =>
    exact False.elim (not_constructor (.inl (forms id receipt.node present receipt.found)) ⟨_, _, receipt.form⟩)

  | composite head plain receipt =>
    exact False.elim (not_composite (.inl (.inl (forms id receipt.node present receipt.found))) receipt.form)

  | primitive head plain receipt =>
    have member := (List.of_mem_zip member).1
    rcases receipt.form with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
    · have same : entry.1 = operand := by simpa only [form, AcceptedOrdinaryExpressionReceipt.operands, List.mem_singleton] using member
      exact same ▸ arguments.2.1 id receipt.node present receipt.found operator operand form
    · have choices : entry.1 = left ∨ entry.1 = right := by
        simpa only [form, AcceptedOrdinaryExpressionReceipt.operands, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using member
      rcases choices with same | same
      · exact same ▸ (arguments.2.2 id receipt.node present receipt.found operator left right form).1
      · exact same ▸ (arguments.2.2 id receipt.node present receipt.found operator left right form).2
  | builtin head plain receipt =>
    exact False.elim (not_builtin (.inl (.inl (.inl (forms id receipt.node present receipt.metadata.found)))) ⟨_, _, _, receipt.form⟩)

theorem Boundary.impossible_methods
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedMethodForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedMethodArguments source reached)
    (rawMetadata : ReachedMethodMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible_methods metadata forms initializers rawMetadata requirements present
  | child step children entry member next ih => exact ih (step.child_reached_methods forms arguments present member)

theorem Residual.impossible_methods {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedMethodForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedMethodArguments source reached)
    (rawMetadata : ReachedMethodMetadata compiled.indexed prepared.named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (present : reached id) : False :=
  residual.boundary.impossible_methods metadata forms initializers arguments rawMetadata requirements present

/-- The expanded lane retains indices without changing the method-only predicates. -/
def ReachedIndexForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    (LeafForm node.form ∨ DirectForm node.form ∨ IndirectForm node.form ∨ MethodForm node.form) ∨ IndexForm node.form

def ReachedIndexArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedMethodArguments source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ base key, node.form = .index base key → reached base ∧ reached key

def ReachedIndexOperands (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ base key, node.form = .index base key → AcceptedIndexExpressionReceipt.Operands source base key

def ReachedIndexMetadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedMethodMetadata prepared named source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ base key, node.form = .index base key →
      CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest prepared named node

theorem ReachedIndexMetadata.of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {source : TypedSource} {reached : ExpressionId → Prop}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      prepared named source directSites = some receipt) :
    ReachedIndexMetadata prepared named source reached := by
  refine ⟨ReachedMethodMetadata.of_accepted accepted, ?_⟩
  intro id node _ found base key form
  exact AcceptedNamedExpressionMetadata.at_of_accepted accepted found (form ▸ .index base key)

theorem Cause.impossible_indices
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedIndexForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedIndexMetadata compiled.indexed named source reached)
    (_requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False := by
  have original := forms id head.node present head.found
  cases cause with
  | form _ notLeaf notDirect notIndirect notMethod notIndex _ _ _ _ =>
    rcases original with (leaf | direct | indirect | method) | index
    · exact notLeaf leaf
    · exact notDirect direct
    · exact notIndirect indirect
    · exact notMethod method
    · exact notIndex index
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | operatorCoercions _ form nonempty => exact nonempty (rawMetadata.1.2 id head.node present head.found form).1
  | special selected outside outsideMethod =>
    rcases original with (leaf | direct | ⟨callee, arguments, callMetadata, form⟩ | method) | ⟨base, key, form⟩
    · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata
        head.found leaf.view (Child root.selected.policy root.selected.lowerBody fuel
          (context compiled.indexed named)) (fuel + 1) scope reasonAt
      have same := head.selected.symm.trans profile.2.2
      rw [selected] at same
      cases same
    · exact outside direct
    · have clean := rawMetadata.1.1 id head.node present head.found callee arguments callMetadata form
      have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root
        (scope := scope) (reasonAt := reasonAt) head.found form
        (by simpa only [form] using clean.2.2.1) clean.1
        (by simpa only [form] using clean.2.2.2.1)
        (by simpa only [(lookupExpression?_sound head.found).2] using clean.2.1)
      have noneSelected := profile.special
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same
    · exact outsideMethod method
    · have clean := rawMetadata.2 id head.node present head.found base key form
      have noneSelected := AcceptedIndexExpressionReceipt.special_none root (scope := scope) (reasonAt := reasonAt) head.found form clean
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same

  | indexOperands _ indexForm missing => exact missing (operands id head.node present head.found _ _ indexForm)

  | constructorRange _ constructorForm _ => exact not_constructor (original) ⟨_, _, constructorForm⟩

theorem Step.child_reached_indices
    (forms : ReachedIndexForms source reached)
    (arguments : ReachedIndexArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf | proxy => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments.1.1.1 id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments.1.1.1 id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have children := arguments.1.1.2 id receipt.original present receipt.found _ _ _ receipt.originalForm
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact children.2 entry.1 (List.of_mem_zip member).1
  | method head _ receipt =>
    have child := (List.of_mem_zip member).1
    rcases receipt.operator.form with ⟨operator, operand, form, actual⟩ |
      ⟨operator, left, right, form, actual⟩
    · have same : entry.1 = operand := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_singleton] using child
      exact same ▸ arguments.1.2.1 id receipt.node present receipt.metadata.found operator operand form
    · have cases : entry.1 = left ∨ entry.1 = right := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_cons, List.not_mem_nil, or_false] using child
      have children := arguments.1.2.2 id receipt.node present receipt.metadata.found operator left right form
      rcases cases with same | same
      · exact same ▸ children.1
      · exact same ▸ children.2

  | index head plain receipt =>
    have children := arguments.2 id receipt.node present receipt.found _ _ receipt.form
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact (List.mem_singleton.mp member) ▸ children.2

  | constructor head plain receipt =>
    exact False.elim (not_constructor (forms id receipt.node present receipt.found) ⟨_, _, receipt.form⟩)

  | composite head plain receipt =>
    exact False.elim (not_composite (.inl (forms id receipt.node present receipt.found)) receipt.form)

  | primitive head plain receipt =>
    have member := (List.of_mem_zip member).1
    rcases receipt.form with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
    · have same : entry.1 = operand := by simpa only [form, AcceptedOrdinaryExpressionReceipt.operands, List.mem_singleton] using member
      exact same ▸ arguments.1.2.1 id receipt.node present receipt.found operator operand form
    · have choices : entry.1 = left ∨ entry.1 = right := by
        simpa only [form, AcceptedOrdinaryExpressionReceipt.operands, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using member
      rcases choices with same | same
      · exact same ▸ (arguments.1.2.2 id receipt.node present receipt.found operator left right form).1
      · exact same ▸ (arguments.1.2.2 id receipt.node present receipt.found operator left right form).2
  | builtin head plain receipt =>
    exact False.elim (not_builtin (.inl (.inl (forms id receipt.node present receipt.metadata.found))) ⟨_, _, _, receipt.form⟩)

theorem Boundary.impossible_indices
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedIndexForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedIndexArguments source reached)
    (rawMetadata : ReachedIndexMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible_indices metadata forms initializers rawMetadata requirements operands present
  | child step children entry member next ih => exact ih (step.child_reached_indices forms arguments present member)

theorem Residual.impossible_indices {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedIndexForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedIndexArguments source reached)
    (rawMetadata : ReachedIndexMetadata compiled.indexed prepared.named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (present : reached id) : False :=
  residual.boundary.impossible_indices metadata forms initializers arguments rawMetadata requirements operands present

/-- Constructors add their complete ordered payload list to the existing lane. -/
def ReachedConstructorForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ((LeafForm node.form ∨ DirectForm node.form ∨ IndirectForm node.form ∨ MethodForm node.form) ∨ IndexForm node.form) ∨ ConstructorForm node.form

def ReachedConstructorArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedIndexArguments source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ instantiation ids, node.form = .constructor instantiation ids → ∀ child ∈ ids, reached child

def ReachedConstructorRanges (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ instantiation ids, node.form = .constructor instantiation ids →
      CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution

def ReachedConstructorMetadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedIndexMetadata prepared named source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ instantiation ids, node.form = .constructor instantiation ids →
      CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest prepared named node

theorem ReachedConstructorMetadata.of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {source : TypedSource} {reached : ExpressionId → Prop}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      prepared named source directSites = some receipt) :
    ReachedConstructorMetadata prepared named source reached := by
  refine ⟨ReachedIndexMetadata.of_accepted accepted, ?_⟩
  intro id node _ found instantiation ids form
  exact AcceptedNamedExpressionMetadata.at_of_accepted accepted found (form ▸ .constructor instantiation ids)

private theorem Cause.impossible_constructor_at
    (metadata : MetadataFor compiled.indexed named source directSites)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedConstructorMetadata compiled.indexed named source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head)
    (original : ((LeafForm head.node.form ∨ DirectForm head.node.form ∨ IndirectForm head.node.form ∨ MethodForm head.node.form) ∨ IndexForm head.node.form) ∨ ConstructorForm head.node.form)
    (present : reached id) : False := by
  cases cause with
  | form _ notLeaf notDirect notIndirect notMethod notIndex notConstructor _ _ _ =>
    rcases original with ((leaf | direct | indirect | method) | index) | constructor
    · exact notLeaf leaf
    · exact notDirect direct
    · exact notIndirect indirect
    · exact notMethod method
    · exact notIndex index
    · exact notConstructor constructor
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | operatorCoercions _ form nonempty => exact nonempty (rawMetadata.1.1.2 id head.node present head.found form).1
  | special selected outside outsideMethod =>
    rcases original with ((leaf | direct | ⟨callee, arguments, callMetadata, form⟩ | method) | ⟨base, key, form⟩) | ⟨instantiation, ids, form⟩
    · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata
        head.found leaf.view (Child root.selected.policy root.selected.lowerBody fuel
          (context compiled.indexed named)) (fuel + 1) scope reasonAt
      have same := head.selected.symm.trans profile.2.2
      rw [selected] at same
      cases same
    · exact outside direct
    · have clean := rawMetadata.1.1.1 id head.node present head.found callee arguments callMetadata form
      have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root
        (scope := scope) (reasonAt := reasonAt) head.found form
        (by simpa only [form] using clean.2.2.1) clean.1
        (by simpa only [form] using clean.2.2.2.1)
        (by simpa only [(lookupExpression?_sound head.found).2] using clean.2.1)
      have noneSelected := profile.special
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same
    · exact outsideMethod method
    · have clean := rawMetadata.1.2 id head.node present head.found base key form
      have noneSelected := AcceptedIndexExpressionReceipt.special_none root (scope := scope) (reasonAt := reasonAt) head.found form clean
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same

    · have clean := rawMetadata.2 id head.node present head.found instantiation ids form
      have noneSelected := AcceptedConstructorExpressionReceipt.special_none root (scope := scope) (reasonAt := reasonAt)
        head.found form clean
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same
  | indexOperands _ indexForm missing => exact missing (operands id head.node present head.found _ _ indexForm)

  | constructorRange _ constructorForm missing => exact missing (ranges id head.node present head.found _ _ constructorForm)

theorem Cause.impossible_constructors
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedConstructorForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedConstructorMetadata compiled.indexed named source reached)
    (_requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False :=
  cause.impossible_constructor_at metadata initializers rawMetadata operands ranges
    (forms id head.node present head.found) present

theorem Step.child_reached_constructors
    (forms : ReachedConstructorForms source reached)
    (arguments : ReachedConstructorArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf | proxy => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments.1.1.1.1 id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments.1.1.1.1 id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have children := arguments.1.1.1.2 id receipt.original present receipt.found _ _ _ receipt.originalForm
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact children.2 entry.1 (List.of_mem_zip member).1
  | method head _ receipt =>
    have child := (List.of_mem_zip member).1
    rcases receipt.operator.form with ⟨operator, operand, form, actual⟩ |
      ⟨operator, left, right, form, actual⟩
    · have same : entry.1 = operand := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_singleton] using child
      exact same ▸ arguments.1.1.2.1 id receipt.node present receipt.metadata.found operator operand form
    · have cases : entry.1 = left ∨ entry.1 = right := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_cons, List.not_mem_nil, or_false] using child
      have children := arguments.1.1.2.2 id receipt.node present receipt.metadata.found operator left right form
      rcases cases with same | same
      · exact same ▸ children.1
      · exact same ▸ children.2

  | index head plain receipt =>
    have children := arguments.1.2 id receipt.node present receipt.found _ _ receipt.form
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact (List.mem_singleton.mp member) ▸ children.2

  | constructor head plain receipt =>
    exact arguments.2 id receipt.node present receipt.found _ _ receipt.form
      entry.1 (List.of_mem_zip member).1

  | composite head plain receipt =>
    exact False.elim (not_composite (forms id receipt.node present receipt.found) receipt.form)

  | primitive head plain receipt =>
    have member := (List.of_mem_zip member).1
    rcases receipt.form with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
    · have same : entry.1 = operand := by simpa only [form, AcceptedOrdinaryExpressionReceipt.operands, List.mem_singleton] using member
      exact same ▸ arguments.1.1.2.1 id receipt.node present receipt.found operator operand form
    · have choices : entry.1 = left ∨ entry.1 = right := by
        simpa only [form, AcceptedOrdinaryExpressionReceipt.operands, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using member
      rcases choices with same | same
      · exact same ▸ (arguments.1.1.2.2 id receipt.node present receipt.found operator left right form).1
      · exact same ▸ (arguments.1.1.2.2 id receipt.node present receipt.found operator left right form).2
  | builtin head plain receipt =>
    exact False.elim (not_builtin (.inl (forms id receipt.node present receipt.metadata.found)) ⟨_, _, _, receipt.form⟩)

theorem Boundary.impossible_constructors
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedConstructorForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedConstructorArguments source reached)
    (rawMetadata : ReachedConstructorMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible_constructors metadata forms initializers rawMetadata requirements operands ranges present
  | child step children entry member next ih => exact ih (step.child_reached_constructors forms arguments present member)

theorem Residual.impossible_constructors {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedConstructorForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedConstructorArguments source reached)
    (rawMetadata : ReachedConstructorMetadata compiled.indexed prepared.named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    (present : reached id) : False :=
  residual.boundary.impossible_constructors metadata forms initializers arguments rawMetadata requirements operands ranges present


/-- General composites retain their actual ordered source children. -/
def ReachedCompositeForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    (((LeafForm node.form ∨ DirectForm node.form ∨ IndirectForm node.form ∨ MethodForm node.form) ∨ IndexForm node.form) ∨ ConstructorForm node.form) ∨ CompositeForm node.form

def ReachedCompositeArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedConstructorArguments source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node → CompositeForm node.form →
    ∀ child ∈ AcceptedCompositeExpressionReceipt.operands node.form, reached child

def ReachedCompositeMetadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedConstructorMetadata prepared named source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node → CompositeForm node.form →
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest prepared named node

theorem ReachedCompositeMetadata.of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {source : TypedSource} {reached : ExpressionId → Prop}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      prepared named source directSites = some receipt) :
    ReachedCompositeMetadata prepared named source reached := by
  refine ⟨ReachedConstructorMetadata.of_accepted accepted, ?_⟩
  intro id node _ found form
  apply AcceptedNamedExpressionMetadata.at_of_accepted accepted found
  generalize eq : node.form = shape at form
  cases form
  · exact .group _
  · exact .tuple _
  · exact .conditional _ _ _

theorem Cause.impossible_composite_at
    (metadata : MetadataFor compiled.indexed named source directSites)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedCompositeMetadata compiled.indexed named source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head)
    (original : (((LeafForm head.node.form ∨ DirectForm head.node.form ∨ IndirectForm head.node.form ∨ MethodForm head.node.form) ∨ IndexForm head.node.form) ∨ ConstructorForm head.node.form) ∨ CompositeForm head.node.form)
    (present : reached id) : False := by
  rcases original with old | composite
  · exact cause.impossible_constructor_at metadata initializers rawMetadata.1 operands ranges old present
  · cases cause with
    | form _ _ _ _ _ _ _ outside _ _ => exact outside composite
    | initializer _ selected => exact initializers id present ⟨selected⟩
    | special selected _ _ =>
      have noneSelected := AcceptedCompositeExpressionReceipt.special_none root (scope := scope) (reasonAt := reasonAt)
        head.found composite (rawMetadata.2 id head.node present head.found composite)
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same
    | operatorCoercions _ method _ =>
      exact not_composite (.inl (.inl (.inr (.inr (.inr method))))) composite
    | indexOperands _ form _ => exact not_composite (.inl (.inr ⟨_, _, form⟩)) composite
    | constructorRange _ form _ => exact not_composite (.inr ⟨_, _, form⟩) composite

theorem Cause.impossible_composites
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedCompositeForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedCompositeMetadata compiled.indexed named source reached)
    (_requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False :=
  cause.impossible_composite_at metadata initializers rawMetadata operands ranges (forms id head.node present head.found) present

theorem Step.child_reached_composites
    (forms : ReachedCompositeForms source reached)
    (arguments : ReachedCompositeArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf | proxy => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments.1.1.1.1.1 id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments.1.1.1.1.1 id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have children := arguments.1.1.1.1.2 id receipt.original present receipt.found _ _ _ receipt.originalForm
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact children.2 entry.1 (List.of_mem_zip member).1
  | method head _ receipt =>
    have child := (List.of_mem_zip member).1
    rcases receipt.operator.form with ⟨operator, operand, form, actual⟩ |
      ⟨operator, left, right, form, actual⟩
    · have same : entry.1 = operand := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_singleton] using child
      exact same ▸ arguments.1.1.1.2.1 id receipt.node present receipt.metadata.found operator operand form
    · have cases : entry.1 = left ∨ entry.1 = right := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_cons, List.not_mem_nil, or_false] using child
      have children := arguments.1.1.1.2.2 id receipt.node present receipt.metadata.found operator left right form
      rcases cases with same | same
      · exact same ▸ children.1
      · exact same ▸ children.2

  | index head plain receipt =>
    have children := arguments.1.1.2 id receipt.node present receipt.found _ _ receipt.form
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact (List.mem_singleton.mp member) ▸ children.2

  | constructor head plain receipt =>
    exact arguments.1.2 id receipt.node present receipt.found _ _ receipt.form
      entry.1 (List.of_mem_zip member).1

  | composite head plain receipt =>
    exact arguments.2 id receipt.node present receipt.found receipt.form entry.1 (List.of_mem_zip member).1

  | primitive head plain receipt =>
    have member := (List.of_mem_zip member).1
    rcases receipt.form with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
    · have same : entry.1 = operand := by simpa only [form, AcceptedOrdinaryExpressionReceipt.operands, List.mem_singleton] using member
      exact same ▸ arguments.1.1.1.2.1 id receipt.node present receipt.found operator operand form
    · have choices : entry.1 = left ∨ entry.1 = right := by
        simpa only [form, AcceptedOrdinaryExpressionReceipt.operands, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using member
      rcases choices with same | same
      · exact same ▸ (arguments.1.1.1.2.2 id receipt.node present receipt.found operator left right form).1
      · exact same ▸ (arguments.1.1.1.2.2 id receipt.node present receipt.found operator left right form).2
  | builtin head plain receipt =>
    exact False.elim (not_builtin (forms id receipt.node present receipt.metadata.found) ⟨_, _, _, receipt.form⟩)

theorem Boundary.impossible_composites
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedCompositeForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedCompositeArguments source reached)
    (rawMetadata : ReachedCompositeMetadata compiled.indexed named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible_composites metadata forms initializers rawMetadata requirements operands ranges present
  | child step children entry member next ih => exact ih (step.child_reached_composites forms arguments present member)

theorem Residual.impossible_composites {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedCompositeForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedCompositeArguments source reached)
    (rawMetadata : ReachedCompositeMetadata compiled.indexed prepared.named source reached)
    (requirements : ReachedMethodRequirements source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    (present : reached id) : False :=
  residual.boundary.impossible_composites metadata forms initializers arguments rawMetadata requirements operands ranges present



/-- The broad lane includes accepted builtin calls, proxy leaves and both operator routes. -/
def ReachedOrdinaryForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ((((LeafForm node.form ∨ DirectForm node.form ∨ IndirectForm node.form ∨ MethodForm node.form) ∨ IndexForm node.form) ∨ ConstructorForm node.form) ∨ CompositeForm node.form) ∨ (BuiltinForm node.form ∨ ProxyForm node.form)

def ReachedOrdinaryArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedCompositeArguments source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ callee ids function, node.form = .call callee ids (.builtinFunction function) → ∀ child ∈ ids, reached child

def ReachedOrdinaryMetadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ReachedCompositeMetadata prepared named source reached ∧
  ∀ id node, reached id → source.lookupExpression? id = some node → (BuiltinForm node.form ∨ ProxyForm node.form) →
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest prepared named node

theorem ReachedOrdinaryMetadata.of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {source : TypedSource} {reached : ExpressionId → Prop}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      prepared named source directSites = some receipt) :
    ReachedOrdinaryMetadata prepared named source reached := by
  refine ⟨ReachedCompositeMetadata.of_accepted accepted, ?_⟩
  intro id node _ found form
  rcases form with ⟨callee, ids, function, form⟩ | ⟨inner, form⟩
  · exact AcceptedNamedExpressionMetadata.at_of_accepted accepted found (form ▸ .builtin callee ids function)
  · exact AcceptedNamedExpressionMetadata.at_of_accepted accepted found (form ▸ .proxy inner)

theorem Cause.impossible_ordinary
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedOrdinaryForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (rawMetadata : ReachedOrdinaryMetadata compiled.indexed named source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False := by
  rcases forms id head.node present head.found with old | builtin | proxy
  · exact cause.impossible_composite_at metadata initializers rawMetadata.1 operands ranges old present
  · cases cause with
    | form _ _ _ _ _ _ _ _ outside _ => exact outside builtin
    | initializer _ selected => exact initializers id present ⟨selected⟩
    | special selected _ _ =>
      have noneSelected := AcceptedOrdinaryExpressionReceipt.builtin_special_none root (scope := scope) (reasonAt := reasonAt)
        head.found builtin (rawMetadata.2 id head.node present head.found (.inl builtin))
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same
    | operatorCoercions _ method _ =>
      exact not_builtin (.inl (.inl (.inl (.inr (.inr (.inr method)))))) builtin
    | indexOperands _ form _ => exact not_builtin (.inl (.inl (.inr ⟨_, _, form⟩))) builtin
    | constructorRange _ form _ => exact not_builtin (.inl (.inr ⟨_, _, form⟩)) builtin

  · obtain ⟨inner, proxy⟩ := proxy
    cases cause with
    | form _ _ _ _ _ _ _ _ _ outside => exact outside ⟨inner, proxy⟩
    | initializer _ selected => exact initializers id present ⟨selected⟩
    | special selected _ _ =>
      have noneSelected := AcceptedProxyExpressionReceipt.special_none root (scope := scope) (reasonAt := reasonAt)
        head.found proxy (rawMetadata.2 id head.node present head.found (.inr ⟨inner, proxy⟩))
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)) (fuel + 1)
      have same := head.selected.symm.trans noneSelected
      rw [selected] at same
      cases same
    | operatorCoercions _ method _ =>
      rcases method with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩ <;> simp [proxy] at form
    | indexOperands _ form _ => simp [proxy] at form
    | constructorRange _ form _ => simp [proxy] at form

theorem Step.child_reached_ordinary
    (arguments : ReachedOrdinaryArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf | proxy => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments.1.1.1.1.1.1 id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments.1.1.1.1.1.1 id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | indirect head _ receipt =>
    have children := arguments.1.1.1.1.1.2 id receipt.original present receipt.found _ _ _ receipt.originalForm
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact children.2 entry.1 (List.of_mem_zip member).1
  | method head _ receipt =>
    have child := (List.of_mem_zip member).1
    rcases receipt.operator.form with ⟨operator, operand, form, actual⟩ |
      ⟨operator, left, right, form, actual⟩
    · have same : entry.1 = operand := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_singleton] using child
      exact same ▸ arguments.1.1.1.1.2.1 id receipt.node present receipt.metadata.found operator operand form
    · have cases : entry.1 = left ∨ entry.1 = right := by
        simpa only [CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt.arguments,
          actual, List.mem_cons, List.not_mem_nil, or_false] using child
      have children := arguments.1.1.1.1.2.2 id receipt.node present receipt.metadata.found operator left right form
      rcases cases with same | same
      · exact same ▸ children.1
      · exact same ▸ children.2

  | index head plain receipt =>
    have children := arguments.1.1.1.2 id receipt.node present receipt.found _ _ receipt.form
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ children.1
    · exact (List.mem_singleton.mp member) ▸ children.2

  | constructor head plain receipt =>
    exact arguments.1.1.2 id receipt.node present receipt.found _ _ receipt.form
      entry.1 (List.of_mem_zip member).1

  | composite head plain receipt =>
    exact arguments.1.2 id receipt.node present receipt.found receipt.form entry.1 (List.of_mem_zip member).1

  | primitive head plain receipt =>
    have member := (List.of_mem_zip member).1
    rcases receipt.form with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
    · have same : entry.1 = operand := by simpa only [form, AcceptedOrdinaryExpressionReceipt.operands, List.mem_singleton] using member
      exact same ▸ arguments.1.1.1.1.2.1 id receipt.node present receipt.found operator operand form
    · have choices : entry.1 = left ∨ entry.1 = right := by
        simpa only [form, AcceptedOrdinaryExpressionReceipt.operands, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using member
      rcases choices with same | same
      · exact same ▸ (arguments.1.1.1.1.2.2 id receipt.node present receipt.found operator left right form).1
      · exact same ▸ (arguments.1.1.1.1.2.2 id receipt.node present receipt.found operator left right form).2
  | builtin head plain receipt =>
    exact arguments.2 id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1

theorem Boundary.impossible_ordinary
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedOrdinaryForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedOrdinaryArguments source reached)
    (rawMetadata : ReachedOrdinaryMetadata compiled.indexed named source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible_ordinary metadata forms initializers rawMetadata operands ranges present
  | child step children entry member next ih => exact ih (step.child_reached_ordinary arguments present member)

theorem Residual.impossible_ordinary {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedOrdinaryForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedOrdinaryArguments source reached)
    (rawMetadata : ReachedOrdinaryMetadata compiled.indexed prepared.named source reached)
    (operands : ReachedIndexOperands source reached)
    (ranges : ReachedConstructorRanges source reached)
    (present : reached id) : False :=
  residual.boundary.impossible_ordinary metadata forms initializers arguments rawMetadata operands ranges present

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyReceipts
/-! Selected method cache entries retain the same complete compiler action as
ordinary entries. These receipts use that action without an ordinary origin or
Header. Original method instantiation supplies Source typing separately. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyReceipts
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open AcceptedNamedExpressionFlow
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallablePreparedMethodSelection (Cached)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (cached : Cached compiled method.specialized)

abbrev source := CallableIndexedNamedGeneration.source cached.named
abbrev policy := CallablePreparedMethodRuntimeProfileFactory.policy cached.compilation
abbrev reasonAt := cached.diagnostics.reasonAt cached.named.signature.key
abbrev parameterScope := CallablePreparedMethodRuntimeProfileFactory.scope (named := cached.named)

abbrev BodyAt := Body (policy cached) compiled.indexed.fuel (source cached)
  (parameterScope cached) cached.compilation.statements cached.named.signature.resultType
  (reasonAt cached) cached.compilation.own.fellThroughReason
  cached.compilation.own.table.escapedReason cached.compilation.body

def invalidProjection (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  cached.diagnostics.placeReason cached.named.signature.key site root none

def invalidOperand (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (operator : Solcore.Syntax.ValueAssignOp) : Word :=
  if operator = .equal then Word.zero else cached.compilation.own.assignments.reasonAt site root (.value operator)

def invalidUnary (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  cached.compilation.own.assignments.reasonAt site root .bitNot

def missingDefault (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (type : TypeSystem.Ty) : Word :=
  cached.diagnostics.placeReason cached.named.signature.key site root (some type)

/-- These are the callbacks in the retained method compilation itself. -/
theorem assignments : CompatibleAssignmentStatements.AssignmentPolicy
    (policy cached) (.initial compiled.compatible.checked)
    (invalidProjection cached) (invalidOperand cached) (missingDefault cached) := by
  refine ⟨rfl, rfl, ?_⟩
  change some _ = some _
  apply congrArg some
  funext expression fuel source scope site assignment operator rhs output next reasonAt
  cases operator <;> rfl

/-- The unary callback uses the same retained method assignment table. -/
theorem unary : CompatibleBitNotStatements.Policy
    (policy cached) (.initial compiled.compatible.checked)
    (invalidProjection cached) (invalidUnary cached) (missingDefault cached) := rfl

theorem read : (policy cached).readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := rfl

/-- The selected method keeps its actual matcher and final native table. -/
def matchContext : SourceCoreCompatibleDataMatches.Context :=
  CompatibleMatchAmbientLowering.withDefinitions
    ⟨.initial compiled.compatible.checked, cached.named.specialized.function.solvedRequirements,
      some (CallableIndexedNamedGeneration.allocator compiled.indexed cached.named), none⟩
    compiled.indexed.layouts.definitions

theorem match_policy : CompatibleMatchAmbientLowering.PolicySuccess
    (policy cached) (matchContext cached) := by
  apply CompatibleMatchAmbientLowering.PolicySuccess.extend (by rfl)
  exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

/-- The exact accepted body is refined only through its actual assignment
callbacks. The result preserves code, source, roots, scopes and child budgets. -/
theorem of_cached : ∃ receipt : BodyAt cached, receipt.tree.Ready := by
  obtain ⟨body⟩ := body_of_accepted cached.compilation.bodyCompiled
  obtain ⟨tree, ready⟩ := body.tree.refine (assignments cached) (unary cached) (match_policy cached)
  exact ⟨⟨body.flow, tree, body.emitted⟩, ready⟩

/-- Full cached specialization authenticates the method policy at this child. -/
theorem policy_receipt {scope : SourceCoreLocalCell.Scope} {fuel : Nat}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (policy cached).lowerExpression fuel (source cached) scope id
      (reasonAt cached) = .ok lowered) :
    ∃ predecessor, fuel = predecessor + 1 ∧
      Nonempty (CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
        (compiled := compiled) cached.named cached.diagnostics cached.code cached.compilation
        predecessor (source cached) scope id (reasonAt cached) lowered) := by
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext cached.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    cached.compilation.parents cached.compilation.own.assignments cached.diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed cached.named)
    compiled.indexed.base.callableContext none none fuel (source cached) scope id
    (reasonAt cached) = .ok lowered at accepted
  cases fuel with
  | zero => rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted; cases accepted
  | succ predecessor =>
    exact ⟨predecessor, rfl,
      CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
        cached.compilation
        (CallableIndexedActualNamedSourceReceipts.cached_record compiled cached.selected cached.compilation.hook)
        accepted⟩

/-- Original finite form and reachability facts exclude boundaries of the
actual recursive child trace. No expression grammar or execution law is an input. -/
theorem child_syntax
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (forms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    {scope : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (policy cached).lowerExpression fuel (source cached) scope id
      (reasonAt cached) = .ok lowered) (present : reached id) :
    GeneralSyntax (source cached) id (DirectSite table.rows) := by
  obtain ⟨catalog⟩ := CallableIndexedOwnedPreparedOrdinaryCatalog.of_compiled compiled wellFormed
  obtain ⟨predecessor, _same, ⟨root⟩⟩ := policy_receipt cached accepted
  obtain ⟨trace⟩ := Trace.of_accepted (root := root) metadata
    (fun _ site => site.supported (table.aligned catalog)) covered root.selected.accepted
  cases trace.syntax_or_boundary covered with
  | inl grammar => exact grammar
  | inr residual =>
    obtain ⟨boundary⟩ := residual
    exact False.elim (boundary.impossible metadata forms initializers arguments present)

end Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyAdmission
/-! A genuine method instantiation supplies original Source typing for the
actual cached body. Its accepted statement and expression actions construct
the existing method certificate, preserving its full synthetic specialization. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyAdmission
open Core Frontend SourceInference
open AcceptedMethodBodyReceipts
open AcceptedNamedBodyFlow AcceptedNamedExpressionFlow
open CallablePreparedMethodSelection (Cached)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots (DirectSource)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedScopedMethodAdmission (SourceCertificate)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (cached : Cached compiled method.specialized)

/-- Final-plan provenance already retains the full successful method recheck
and specialization. Head matching is not needed to recover its typed body;
formation of every actual raw replacement remains a separate premise. -/
theorem instantiates_of_selection
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (selected : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method)
    (parameters : selected.implementation.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
      method.specialized.parameterSubstitution) :
    ∃ definition, definition ∈ (Program.ofChecked compiled.sourceProgram).methods ∧
      definition.id = selected.declaration.id ∧
      Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
        selected.implementation selected.declaration selected.trait definition
        method.specialized.parameterSubstitution
        (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method) := by
  obtain ⟨retained, member, idEq, completeEq⟩ := selected.retained checked
  let receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method :=
    ⟨selected, retained, member, idEq, completeEq⟩
  have owner : retained.checked.declaration = selected.implementation.id := by
    rw [← completeEq]
    exact checkFunctionBody_success_declaration selected.bodyChecked
  have traitLookup := selected.traitLookup
  unfold ProgramSignatures.trait? at traitLookup
  have traitMember := List.mem_of_find?_eq_some traitLookup
  have traitOwner : selected.declaration.traitMethod.trait = selected.trait.id := by
    exact (of_decide_eq_true (List.find?_some
      (p := fun trait : ProgramTraitSignature => decide (trait.id = selected.declaration.traitMethod.trait))
      traitLookup)).symm
  have domain : method.specialized.parameterSubstitution.map Prod.fst = selected.implementation.parameters :=
    SourceSpecialization.specializeFunction_parameterDomain selected.specialized
  have exactSubstitution : SourceSemantics.ParameterSubstitution.Exact
      method.specialized.parameterSubstitution selected.implementation.parameters :=
    ⟨parameters, by rw [SourceSemantics.ParameterSubstitution.domain, domain]⟩
  refine ⟨MethodDefinition.ofChecked retained, List.mem_map.mpr ⟨retained, member, rfl⟩,
    idEq.trans selected.methodId, ?_⟩
  apply Dynamic.TraitMethodInstantiates.intro selected.implementationMember selected.methodMember
    traitMember traitOwner (List.mem_map.mpr ⟨retained, member, rfl⟩)
    (idEq.trans selected.methodId) owner exactSubstitution range
  · exact receipt.body
  · exact receipt.result.1
  · change declarationContext compiled.sourceProgram.signatures method.specialized.function.typedBody.owner []
      method.specialized.assumptions method.specialized.function.solvedRequirements = _
    rw [receipt.owner, receipt.assumptions, receipt.ledger]
    change declarationContext compiled.sourceProgram.signatures selected.implementation.id [] _ _ =
      declarationContext compiled.sourceProgram.signatures retained.checked.declaration [] _ _
    rw [owner]
    rfl

theorem roots : statements (source cached) = cached.compilation.statements := by
  unfold statements source CallableIndexedNamedGeneration.source
  rw [RecursiveNamedPreparedSourceFrames.compiled_roots_eq cached.compilation]
  simp only [List.filterMap_map]
  induction cached.compilation.statements with
  | nil => rfl
  | cons first rest ih =>
    simpa only [List.filterMap_cons, Function.comp_apply] using congrArg (List.cons first) ih

/-- Source typing follows the full original trait-method substitution. Neither
cache membership nor equality of native result types supplies these facts. -/
theorem source_typing
    {implementation : ProgramImplementationSignature} {declaration : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : TypeSystem.ParameterSubstitution}
    (instantiated : Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
      implementation declaration trait definition substitution
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ context final facts,
      StatementsHaveType (source cached) {returnType := cached.named.specialized.function.inferredBodyType}
        context cached.compilation.statements final facts ∧
      NodeOccurrencesUnique (source cached) ∧ LocalIdentityOwnership (source cached) := by
  obtain ⟨types, context, facts, typed⟩ := instantiated.certificate wellFormed
  have sameSource : (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method).source =
      source cached := by
    simp only [source, CallableIndexedNamedGeneration.source, cached.same,
      CallableCoercionMethodInstantiation.bodyInstance]
  have sameResult : (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method).resultType =
      cached.named.specialized.function.inferredBodyType := by
    rw [cached.same]
    rfl
  have body := typed.typing.body_typed
  rw [sameSource, sameResult] at body
  obtain ⟨final, body, _roots, _complete⟩ := body
  change StatementsHaveType (source cached)
    {returnType := cached.named.specialized.function.inferredBodyType}
    context (statements (source cached)) final facts at body
  rw [roots cached] at body
  exact ⟨context, final, facts, body,
    sameSource ▸ typed.graph_closed.wellFormed.nodeOccurrencesUnique,
    sameSource ▸ typed.local_identity_ownership⟩

/-- Open structure and generalized locals remain attached to the same emitted
method body. They are static boundaries, not assumed execution behavior. -/
inductive Unsupported (receipt : BodyAt cached) where
  | structure (openBranch : receipt.tree.closed = false)
  | generalized (binding : Binding (policy cached) (source cached))
      (member : binding ∈ receipt.tree.bindings) (quantified : binding.binder.scheme.quantified ≠ [])

/-- Every reached expression grammar is derived from the actual compiler trace.
Finite original forms and child membership only exclude its retained boundaries. -/
theorem of_instantiated
    {implementation : ProgramImplementationSignature} {declaration : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : TypeSystem.ParameterSubstitution}
    (instantiated : Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
      implementation declaration trait definition substitution
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (receipt : BodyAt cached)
    (forms : DirectSource (source cached))
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (reachedForms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    (children : ∀ child ∈ receipt.tree.children, reached child.expression)
    (closed : receipt.tree.closed = true)
    (monomorphic : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = []) :
    Nonempty (SourceCertificate compiled cached.named table.rows) := by
  obtain ⟨context, final, facts, typed, unique, ownership⟩ := source_typing cached instantiated wellFormed
  have binders := AcceptedNamedBodyBindings.of_monomorphic receipt.tree (read cached)
    unique ownership typed monomorphic
  have grammar : ∀ child ∈ receipt.tree.children,
      GeneralSyntax (source cached) child.expression (DirectSite table.rows) := by
    intro child member
    exact child_syntax cached table wellFormed metadata covered reachedForms arguments initializers
      child.accepted (children child member)
  have body := receipt.tree.scan (read cached) closed unique ownership grammar binders typed
  rw [← roots cached] at body
  exact ⟨⟨forms, ⟨metadata, body⟩⟩⟩

/-- The source certificate or remaining structural boundary belongs to the
same actual method body. No successful shape check is assumed globally. -/
theorem of_receipt
    {implementation : ProgramImplementationSignature} {declaration : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : TypeSystem.ParameterSubstitution}
    (instantiated : Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
      implementation declaration trait definition substitution
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (receipt : BodyAt cached)
    (forms : DirectSource (source cached))
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (reachedForms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    (children : ∀ child ∈ receipt.tree.children, reached child.expression) :
    Nonempty (SourceCertificate compiled cached.named table.rows) ∨ Nonempty (Unsupported cached receipt) := by
  classical
  cases closed : receipt.tree.closed with
  | false => exact .inr ⟨.structure closed⟩
  | true =>
    by_cases mono : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = []
    · exact .inl (of_instantiated cached instantiated wellFormed table receipt forms metadata covered
        reachedForms arguments initializers children closed mono)
    · have generalized : ∃ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified ≠ [] := by
        apply Classical.byContradiction
        intro absent
        apply mono
        intro binding member
        apply Classical.byContradiction
        intro different
        exact absent ⟨binding, member, different⟩
      obtain ⟨binding, member, different⟩ := generalized
      exact .inr ⟨.generalized binding member different⟩

/-- The genuine selector retained by final preparation feeds the same existing
method certificate without inventing an ordinary declaration or Source call. -/
theorem of_selection
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (selected : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method)
    (parameters : selected.implementation.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
      method.specialized.parameterSubstitution)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (receipt : BodyAt cached)
    (forms : DirectSource (source cached))
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (reachedForms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    (children : ∀ child ∈ receipt.tree.children, reached child.expression)
    (closed : receipt.tree.closed = true)
    (monomorphic : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = []) :
    Nonempty (SourceCertificate compiled cached.named table.rows) := by
  obtain ⟨definition, _member, _id, instantiated⟩ := instantiates_of_selection checked selected parameters range
  exact of_instantiated cached instantiated wellFormed table receipt forms metadata covered
    reachedForms arguments initializers children closed monomorphic

end Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyExpressionAdmission
/-! Each child of one actual accepted body is admitted from its own compiler
action. Original Header typing supplies lexical binding facts. Unsupported
branches retain that same whole body and, when relevant, the actual child. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyExpressionAdmission
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open AcceptedNamedBodyAdmission (BodyAt)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedScopedAdmission (Admission)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

/-- The original body and ordered child membership remain part of the residual.
No failure from a different body or detached source occurrence is substituted. -/
inductive Unsupported (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (directRows : List SourceSpecialization.SpecializedFunction) where
  | structure (receipt : BodyAt header) (openBranch : receipt.tree.closed = false)
  | generalized (receipt : BodyAt header) (binding : Binding header.policy header.function.source)
      (member : binding ∈ receipt.tree.bindings) (quantified : binding.binder.scheme.quantified ≠ [])
  | expression (receipt : BodyAt header)
      (child : Child header.policy header.function.source header.reasonAt)
      (member : child ∈ receipt.tree.children)
      (residual : AcceptedNamedExpressionFlow.Residual prepared header (DirectSite directRows)
        child.fuel header.function.source child.scope child.expression child.lowered)

include aligned

/-- This producer consumes a single actual body receipt. Every child is handled
by accepted-expression inversion; no child syntax callback or body scan runs. -/
theorem of_receipt {directRows : List SourceSpecialization.SpecializedFunction}
    (receipt : BodyAt header)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows ∨ Nonempty (Unsupported prepared header directRows) := by
  classical
  cases closed : receipt.tree.closed with
  | false => exact .inr ⟨.structure receipt closed⟩
  | true =>
    rcases AcceptedNamedBodyBindings.of_header prepared aligned wellFormed receipt.tree with binders | generalized
    · by_cases children : ∀ child ∈ receipt.tree.children,
        GeneralSyntax header.function.source child.expression (DirectSite directRows)
      · obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
        exact .inl ⟨metadata, receipt.tree.scan
          (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
          closed header.unique (by
        obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
        rw [header.frame.source]
        exact certificate.local_identity_ownership) children binders typed⟩
      · obtain ⟨child, absent⟩ := Classical.not_forall.mp children
        have member : child ∈ receipt.tree.children := Classical.byContradiction fun missing =>
          absent (fun present => False.elim (missing present))
        have missing : ¬ GeneralSyntax header.function.source child.expression (DirectSite directRows) :=
          fun grammar => absent (fun _ => grammar)
        cases AcceptedNamedExpressionFlow.syntax_of_header prepared aligned metadata
            supported covered child.accepted with
        | inl grammar => exact False.elim (missing grammar)
        | inr residual => exact .inr ⟨.expression receipt child member (Classical.choice residual)⟩
    · obtain ⟨binding, member, quantified⟩ := generalized
      exact .inr ⟨.generalized receipt binding member quantified⟩

/-- The body receipt itself is recovered from the genuine aligned Header action. -/
theorem of_actual {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows ∨ Nonempty (Unsupported prepared header directRows) := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  exact of_receipt prepared aligned receipt metadata supported covered wellFormed

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyExpressionAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedReturningExpressionAdmission
/-! A genuine returning Header body supplies its own expression actions.
Original reached forms discharge every residual and yield the existing admission. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyExpressionAdmission
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open AcceptedNamedExpressionFlow
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedScopedAdmission (Admission)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

/-- The accepted body and its children are recovered before expression syntax.
The original return head closes the actual body and excludes local bindings. -/
theorem of_returning {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation)
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {expression : ExpressionId}
    (roots : header.function.body = id :: rest)
    (found : header.function.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    {reached : ExpressionId → Prop}
    (forms : ReachedForms header.function.source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed prepared.named) id))
    (arguments : ReachedArguments header.function.source reached)
    (present : reached expression)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  cases of_receipt prepared aligned receipt metadata supported covered wellFormed with
  | inl admission => exact admission
  | inr failures =>
    obtain ⟨failure⟩ := failures
    cases failure with
    | «structure» actual openBranch =>
      have details := actual.tree.at_return_list
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
      rw [details.1] at openBranch
      cases openBranch
    | generalized actual binding member quantified =>
      have details := actual.tree.at_return_list
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
      rw [details.2.1] at member
      cases member
    | expression actual child member residual =>
      have details := actual.tree.at_return_list
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
      have childReached : reached child.expression := (details.2.2 child member).symm ▸ present
      exact False.elim (residual.impossible metadata forms initializers arguments childReached)

/-- The accepted body and its children are recovered before expression syntax.
The original return head closes the actual body and excludes local bindings. -/
theorem of_returning_calls {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation)
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {expression : ExpressionId}
    (roots : header.function.body = id :: rest)
    (found : header.function.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    {reached : ExpressionId → Prop}
    (forms : ReachedCallForms header.function.source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed prepared.named) id))
    (arguments : ReachedCallArguments header.function.source reached)
    (rawMetadata : ReachedIndirectMetadata compiled.indexed prepared.named header.function.source reached)
    (present : reached expression)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  cases of_receipt prepared aligned receipt metadata supported covered wellFormed with
  | inl admission => exact admission
  | inr failures =>
    obtain ⟨failure⟩ := failures
    cases failure with
    | «structure» actual openBranch =>
      have details := actual.tree.at_return_list
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
      rw [details.1] at openBranch
      cases openBranch
    | generalized actual binding member quantified =>
      have details := actual.tree.at_return_list
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
      rw [details.2.1] at member
      cases member
    | expression actual child member residual =>
      have details := actual.tree.at_return_list
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
      have childReached : reached child.expression := (details.2.2 child member).symm ▸ present
      exact False.elim (residual.impossible_calls metadata forms initializers arguments rawMetadata childReached)

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyExpressionAdmission
end
