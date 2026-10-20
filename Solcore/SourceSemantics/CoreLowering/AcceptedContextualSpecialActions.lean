import Solcore.SourceSemantics.CoreLowering.AcceptedContextualGeneralizedInitializerReceipt
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts

/-! The original special callback selects one of four actual actions. In
particular, generalized reads retain their contextual source and native view
without assuming an empty metadata list or equality with an unnormalized node. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedContextualSpecialActions
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaPolicyRecipes (special)
open GeneralizedLocalInitializerCompilation (namedInputs)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compilation : Compilation prepared named diagnostics code)

abbrev initializer (current : SourceCoreFunctions.Context) (id : ExpressionId) :=
  prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = current.owner ∧ binding.initializer = id))

abbrev evidence (current : SourceCoreFunctions.Context) (child : SourceCoreFunctions.ExpressionLowerer)
    (budget : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) :=
  SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
    ((representation prepared).atContext named.signature.key []).expressions.projectType
    named.specialized current child budget source scope id reasonAt
    (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [])

def LocalAbsent (current : SourceCoreFunctions.Context) (node : ExpressionNode) : Prop :=
  match node.form with
  | .reference _ (.local binder) =>
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = current.owner ∧ binding.binder.id = binder)) = false
  | _ => True

/-- Every alternative retains the exact action and its output. Initializer rows
are ordered; local reads retain the complete selected substitution and slot. -/
inductive Receipt (compilation : Compilation prepared named diagnostics code)
    (rootFuel : Nat) (current : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Word) : Option SourceCoreBasic.LoweredExpr → Prop where
  | initialized {initial binding lowered}
      (selected : initializer (prepared := prepared) current id = some initial)
      (located : prepared.base.locals.binding current.owner initial.binder.id = .ok binding)
      (bundle : Nonempty (GeneralizedLocalInitializerCompilation.Receipt
        (namedInputs compilation rootFuel budget current scope id reasonAt) binding [] lowered)) :
      Receipt compilation rootFuel current child budget source scope id reasonAt (some lowered)
  | evidenced {viewed node lowered}
      (contextual : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
        current.plan prepared.base.locals current.owner none source id = .ok viewed)
      (found : viewed.lookupExpression? id = some node)
      (notInitializer : initializer (prepared := prepared) current id = none)
      (generated : evidence (prepared := prepared) (named := named) current child budget
        viewed scope id reasonAt = .ok (some lowered)) :
      Receipt compilation rootFuel current child budget source scope id reasonAt (some lowered)
  | generalizedRead {viewed node name binder raw lowered}
      (contextual : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
        current.plan prepared.base.locals current.owner none source id = .ok viewed)
      (found : viewed.lookupExpression? id = some node)
      (form : node.form = .reference name (.local binder))
      (notInitializer : initializer (prepared := prepared) current id = none)
      (noEvidence : evidence (prepared := prepared) (named := named) current child budget
        viewed scope id reasonAt = .ok none)
      (registered : prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = current.owner ∧ binding.binder.id = binder)) = true)
      (readAccepted : SourceCoreLocalPolymorphism.lowerRead prepared.base.locals
        current.owner [] viewed scope id (reasonAt id) = .ok raw)
      (read : Nonempty (GeneralizedLocalReadReceipts.Certificate prepared.base.locals
        current.owner [] viewed scope id (reasonAt id) raw))
      (viewAccepted : ((representation prepared).atContext named.signature.key []).localReadView
        current.owner [] viewed scope id raw = .ok lowered)
      (type : raw.type = lowered.type) :
      Receipt compilation rootFuel current child budget source scope id reasonAt (some lowered)
  | plain {viewed node}
      (contextual : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
        current.plan prepared.base.locals current.owner none source id = .ok viewed)
      (found : viewed.lookupExpression? id = some node)
      (notInitializer : initializer (prepared := prepared) current id = none)
      (noEvidence : evidence (prepared := prepared) (named := named) current child budget
        viewed scope id reasonAt = .ok none)
      (noLocal : LocalAbsent (prepared := prepared) current node) :
      Receipt compilation rootFuel current child budget source scope id reasonAt none

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ}
    {result : α} (accepted : action.mapError change = .ok result) : action = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

private theorem ensure_type {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

/-- Invert the real callback, including normalized source selection, evidence,
generalized bundle selection and the final indexed view. No syntax scan is used. -/
theorem of_special {rootFuel budget : Nat} {current : SourceCoreFunctions.Context}
    {child : SourceCoreFunctions.ExpressionLowerer} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {output : Option SourceCoreBasic.LoweredExpr}
    (accepted : special compilation rootFuel current child budget source scope id reasonAt = .ok output) :
    Receipt compilation rootFuel current child budget source scope id reasonAt output := by
  cases selected : initializer (prepared := prepared) current id with
  | some initial =>
    obtain ⟨binding, lowered, same, located, bundle⟩ :=
      AcceptedContextualGeneralizedInitializerReceipt.of_special_output compilation selected accepted
    subst output
    exact .initialized selected located bundle
  | none =>
    unfold special at accepted
    obtain ⟨viewed, contextual, accepted⟩ := bind_ok accepted
    cases found : viewed.lookupExpression? id with
    | none => simp [found, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
    | some node =>
      simp only [found, bind, Except.bind, pure, Except.pure, selected, Option.filter_none] at accepted
      obtain ⟨optional, generated, accepted⟩ := bind_ok accepted
      cases optional with
      | some lowered =>
        cases accepted
        exact .evidenced contextual found selected generated
      | none =>
        simp only at accepted
        cases form : node.form <;> simp only [form] at accepted
        all_goals
          first
          | (cases accepted; exact .plain contextual found selected generated (by simp [LocalAbsent, form]))
          | skip
        next name resolution =>
          cases resolution <;> simp only at accepted
          all_goals
            first
            | (cases accepted; exact .plain contextual found selected generated (by simp [LocalAbsent, form]))
            | skip
          next binder =>
            cases registered : prepared.base.locals.bindings.any (fun binding =>
                decide (binding.caller = current.owner ∧ binding.binder.id = binder)) with
            | false =>
              simp only [registered, Bool.false_eq_true, ↓reduceIte] at accepted
              cases accepted
              exact .plain contextual found selected generated (by simpa [LocalAbsent, form] using registered)
            | true =>
              simp only [registered, ↓reduceIte] at accepted
              obtain ⟨raw, readAccepted, accepted⟩ := bind_ok accepted
              have readAccepted := mapError_ok readAccepted
              obtain ⟨lowered, viewAccepted, accepted⟩ := bind_ok accepted
              obtain ⟨checkedType, type, accepted⟩ := bind_ok accepted
              cases checkedType
              cases accepted
              exact .generalizedRead contextual found form selected generated registered readAccepted
                (GeneralizedLocalReadReceipts.of_accepted readAccepted) viewAccepted (ensure_type type)

/-- Every reached head observes the same root callback at its actual child
budget; this classifier introduces no separate initializer or local-read law. -/
theorem of_head {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    {compilation : Compilation compiled.indexed named diagnostics code}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word}
    {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := compiled) named diagnostics code compilation rootFuel rootSource rootScope
      rootId rootReasonAt rootLowered)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (head : AcceptedNamedExpressionFlow.Head root.selected.policy root.selected.lowerBody fuel
      (context compiled.indexed named) source scope id reasonAt lowered) :
    Receipt compilation rootFuel (context compiled.indexed named)
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child root.selected.policy
        root.selected.lowerBody fuel (context compiled.indexed named))
      (fuel + 1) source scope id reasonAt head.special := by
  have accepted := head.selected
  rw [AcceptedNamedExpressionFlow.specialAction, root.compilerPolicy.lowerSpecial] at accepted
  exact of_special compilation accepted

end Solcore.SourceSemantics.CoreLowering.AcceptedContextualSpecialActions
