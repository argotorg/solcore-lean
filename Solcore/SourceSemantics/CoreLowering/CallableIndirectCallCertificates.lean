import Solcore.Frontend.SourceCoreGeneralFunctions

/-! Actual indirect lowering receipts. Parent special-hook delegation and both
source lookups remain explicit: an arbitrary policy can observe a different
source node. The actual callee and ordered argument compiler vector share the
same remaining fuel. No source or called-body execution law is stored here. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndirectCallCertificates
open Core Frontend SourceInference
abbrev Scope := SourceCoreBasic.Scope
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr

structure Receipt (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (compilation : SourceCoreFunctions.Context) (source : TypedSource) (scope : Scope)
    (id callee : ExpressionId) (arguments : List ExpressionId) (metadata : IndirectCallResolution)
    (reasonAt : ExpressionId → Word) (lowered : LoweredExpr) where
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id reasonAt = .ok lowered
  specialDelegation : ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none
  original : ExpressionNode
  found : source.lookupExpression? id = some original
  originalForm : original.form = .call callee arguments (.indirect metadata)
  owned : id.occurrence.owner = source.owner
  node : ExpressionNode
  type : Ty
  read : policy.readExpression source id = .ok (node, type)
  form : node.form = .call callee arguments (.indirect metadata)
  argumentCoercions : metadata.argumentCoercions = []
  validated : SourceCompilationPlan.validateIndirectCallMetadata source node callee arguments metadata = .ok ()
  calleeNode : ExpressionNode
  calleeReadType : Ty
  calleeRead : policy.readExpression source callee = .ok (calleeNode, calleeReadType)
  parameter : TypeSystem.Ty
  result : TypeSystem.Ty
  calleeType : calleeNode.type = .function parameter result
  parameterType : Ty
  resultType : Ty
  parameterProject : policy.projectType (.occurrence id.occurrence) parameter = .ok parameterType
  resultProject : policy.projectType (.occurrence id.occurrence) result = .ok resultType
  resultTypeEq : resultType = type
  calleeCode : LoweredExpr
  codes : List LoweredExpr
  calleeAccepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope callee reasonAt = .ok calleeCode
  argumentsAccepted : arguments.mapM (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt) = .ok codes
  packedType : parameterType = (SourceCoreCalls.packArguments codes).type
  callableType : policy.callables.functionType parameterType resultType = calleeCode.type
  expression : Expr
  hook : policy.callables.callCallable compilation source node resultType calleeCode.expression (SourceCoreCalls.packArguments codes).expression = .ok expression
  output : lowered = ⟨type, expression⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensure_type {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

/-- The receipt comes from the actual successful branch. It retains both
original and policy-read nodes without claiming their full metadata equality. -/
theorem of_functions {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : LoweredExpr} {original node : ExpressionNode} {type : Ty}
    (found : source.lookupExpression? id = some original)
    (originalForm : original.form = .call callee arguments (.indirect metadata))
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee arguments (.indirect metadata))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered) := by
  have originalAccepted := accepted
  have originalSpecial := special
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owned : id.occurrence.owner = source.owner
  · simp only [owned, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [originalForm, read, form, bind, Except.bind, pure, Except.pure] at accepted
      by_cases empty : metadata.argumentCoercions.isEmpty = true
      · simp only [empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
        obtain ⟨checked, validated, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨pair, calleeRead, accepted⟩ := bind_ok accepted
        obtain ⟨calleeNode, calleeReadType⟩ := pair
        cases calleeType : calleeNode.type <;> simp only [calleeType] at accepted
        all_goals try cases accepted
        rename_i parameter result
        obtain ⟨parameterType, parameterProject, accepted⟩ := bind_ok accepted
        obtain ⟨resultType, resultProject, accepted⟩ := bind_ok accepted
        obtain ⟨checked, resultChecked, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨calleeCode, calleeAccepted, accepted⟩ := bind_ok accepted
        obtain ⟨codes, argumentsAccepted, accepted⟩ := bind_ok accepted
        obtain ⟨checked, packedChecked, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨checked, callableChecked, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨expression, callAccepted, accepted⟩ := bind_ok accepted
        cases accepted
        have actualValidated : SourceCompilationPlan.validateIndirectCallMetadata source node callee arguments metadata = .ok () := by
          cases h : SourceCompilationPlan.validateIndirectCallMetadata source node callee arguments metadata <;> simp_all [Except.mapError]
        exact ⟨{ accepted := originalAccepted, specialDelegation := originalSpecial
                 original, found, originalForm, owned, node, type, read, form
                 argumentCoercions := List.isEmpty_iff.mp empty
                 validated := actualValidated, calleeNode, calleeReadType, calleeRead
                 parameter, result, calleeType, parameterType, resultType, parameterProject, resultProject
                 resultTypeEq := ensure_type resultChecked, calleeCode, codes, calleeAccepted, argumentsAccepted
                 packedType := ensure_type packedChecked, callableType := ensure_type callableChecked
                 expression, hook := callAccepted, output := rfl }⟩
      · simp [empty] at accepted
  · simp [owned, bind, Except.bind] at accepted

private theorem mapM_ordered {α β ε : Type} {ids : List α} {codes : List β}
    {compile : α → Except ε β} (accepted : ids.mapM compile = .ok codes) :
    ids.length = codes.length ∧ ∀ id code, (id, code) ∈ ids.zip codes → compile id = .ok code := by
  induction ids generalizing codes with
  | nil =>
      simp only [List.mapM_nil, pure, Except.pure] at accepted
      cases accepted
      exact ⟨rfl, by simp⟩
  | cons head tail ih =>
      simp only [List.mapM_cons] at accepted
      obtain ⟨headCode, headAccepted, accepted⟩ := bind_ok accepted
      obtain ⟨tailCodes, tailAccepted, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨length, children⟩ := ih tailAccepted
      refine ⟨by simp only [List.length_cons, length], ?_⟩
      intro id code member
      rcases List.mem_cons.mp member with same | remaining
      · cases same; exact headAccepted
      · exact children id code remaining

/-- The vector retains physical order and duplicates. Each pair refers to the
same compiler invocation and same fuel, including the leading callee. -/
def Receipt.entries {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : LoweredExpr}
    (receipt : Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered) :
    List (ExpressionId × LoweredExpr) := (callee, receipt.calleeCode) :: arguments.zip receipt.codes

theorem Receipt.ordered_children {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : LoweredExpr}
    (receipt : Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered) :
    arguments.length = receipt.codes.length ∧ ∀ child code, (child, code) ∈ receipt.entries →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt = .ok code := by
  obtain ⟨length, children⟩ := mapM_ordered receipt.argumentsAccepted
  refine ⟨length, ?_⟩
  intro child code member
  rcases List.mem_cons.mp member with same | remaining
  · cases same; exact receipt.calleeAccepted
  · exact children child code remaining

/-- The actual general callable policy recovers its prepared table row, rather
than replacing an arbitrary hook with a contract expression. -/
theorem Receipt.prepared_site {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : LoweredExpr}
    (receipt : Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (actualPolicy : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active) :
    ∃ site, SourceCoreCallableContracts.prepareCallsite native.table compilation.owner receipt.node.id native.diagnostics.reasonAt = .ok site ∧
      site.table = native.table ∧ site.caller = compilation.owner ∧ site.call = receipt.node.id ∧
      receipt.expression = site.lower native.diagnostics.unknown receipt.resultType receipt.calleeCode.expression (SourceCoreCalls.packArguments receipt.codes).expression := by
  have accepted := receipt.hook
  rw [actualPolicy] at accepted
  simp only [SourceCoreGeneralFunctions.callablePolicy, receipt.form, bind, Except.bind, pure, Except.pure] at accepted
  cases prepared : SourceCoreCallableContracts.prepareCallsite native.table compilation.owner receipt.node.id native.diagnostics.reasonAt with
  | error => simp [prepared, Except.mapError] at accepted
  | ok site =>
      simp only [prepared, Except.mapError, bind, Except.bind, pure, Except.pure] at accepted
      have expressionEq := (Except.ok.inj accepted).symm
      refine ⟨site, rfl, ?_, ?_, ?_, expressionEq⟩
      all_goals unfold SourceCoreCallableContracts.prepareCallsite at prepared
      all_goals split at prepared
      all_goals first | cases prepared; rfl | cases prepared

end Solcore.SourceSemantics.CoreLowering.CallableIndirectCallCertificates
