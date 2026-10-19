import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerCompilation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts

/-! A generalized read retains the actual contextual normalization and indexed
view wrapper. The original raw occurrence is kept beside the normalized row;
no equality between their complete requirement lists is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadCompilation
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CompatibleEncoding (bind_ok)

structure Observations {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) where
  original : ExpressionNode
  originalFound : source.lookupExpression? id = some original
  name : String
  binder : Resolved.LocalId
  originalForm : original.form = .reference name (.local binder)
  originalCoercions : original.coercions = []
  normalized : TypedSource
  contextual : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
    (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok normalized
  normalizedOwner : normalized.owner = source.owner
  node : ExpressionNode
  found : normalized.lookupExpression? id = some node
  form : node.form = original.form
  rawType : node.rawType = original.rawType
  type : node.type = original.type
  requirements : node.requirements = []
  coercions : node.coercions = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  localPresent : prepared.base.locals.bindings.any (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.binder.id = binder)) = true

def observations? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) : Option (Observations prepared named source id) :=
  match originalFound : source.lookupExpression? id with
  | none => none
  | some original =>
    match originalForm : original.form with
    | .reference name (.local binder) =>
      if originalCoercions : original.coercions = [] then
        match contextual : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
            (context prepared named).plan prepared.base.locals named.signature.key none source id with
        | .error _ => none
        | .ok normalized =>
          if normalizedOwner : normalized.owner = source.owner then
            match found : normalized.lookupExpression? id with
            | none => none
            | some node =>
              if form : node.form = original.form then
                if rawType : node.rawType = original.rawType then
                  if type : node.type = original.type then
                    if requirements : node.requirements = [] then
                      if coercions : node.coercions = [] then
                        if notInitializer : prepared.base.locals.bindings.find? (fun binding =>
                            decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none then
                          if localPresent : prepared.base.locals.bindings.any (fun binding =>
                              decide (binding.caller = named.signature.key ∧ binding.binder.id = binder)) = true then
                            some ⟨original, originalFound, name, binder, originalForm, originalCoercions, normalized, contextual,
                              normalizedOwner, node, found, form, rawType, type, requirements, coercions,
                              notInitializer, localPresent⟩
                          else none
                        else none
                      else none
                    else none
                  else none
                else none
              else none
          else none
      else none
    | _ => none

structure Certificate {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  observations : Observations prepared named source id
  raw : SourceCoreBasic.LoweredExpr
  read : GeneralizedLocalReadReceipts.Certificate prepared.base.locals named.signature.key []
    observations.normalized scope id (reasonAt id) raw
  readAccepted : SourceCoreLocalPolymorphism.lowerRead prepared.base.locals named.signature.key []
    observations.normalized scope id (reasonAt id) = .ok raw
  viewAccepted : SourceCoreCallableIndexedAncestry.lowerView prepared.ancestry named.signature.key []
    observations.normalized scope id raw = .ok lowered
  type : raw.type = lowered.type

private theorem evidence_none {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {source : TypedSource} {id : ExpressionId} (observed : Observations prepared named source id)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget observed.normalized scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? observed.node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [observed.requirements, observed.coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, observed.found, observed.form, observed.originalForm,
    ordinary, observed.requirements, observed.coercions]

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ} {result : α}
    (accepted : action.mapError change = .ok result) : action = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

private theorem ensure_type {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- The reached special callback produces the exact raw read and actual
indexed wrapper. Its child evaluator is never called by this branch. -/
theorem of_special {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {rootFuel budget : Nat} {child : SourceCoreFunctions.ExpressionLowerer}
    {output : Option SourceCoreBasic.LoweredExpr}
    (observed : Observations prepared named source id)
    (accepted : CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok output) :
    ∃ lowered, output = some lowered ∧ Nonempty (Certificate prepared named source scope id reasonAt lowered) := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special at accepted
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq] at accepted
  rw [observed.contextual] at accepted
  simp only [bind, Except.bind, pure, Except.pure, observed.found, observed.notInitializer,
    Option.filter_none] at accepted
  rw [evidence_none observed child budget scope reasonAt] at accepted
  simp only [observed.form, observed.originalForm,
    observed.localPresent, ↓reduceIte] at accepted
  obtain ⟨raw, readAccepted, accepted⟩ := bind_ok accepted
  have readAccepted := mapError_ok readAccepted
  obtain ⟨viewed, viewAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
  cases checkedType
  have type := ensure_type sameType
  have outputEq : output = some viewed := (Except.ok.inj accepted).symm
  obtain ⟨read⟩ := GeneralizedLocalReadReceipts.of_accepted readAccepted
  exact ⟨viewed, outputEq, ⟨⟨observed, raw, read, readAccepted, viewAccepted, type⟩⟩⟩

/-- This receipt follows the same root policy at every recursive child budget. -/
theorem of_policy {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {rootFuel fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (observed : Observations prepared named source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) (fuel + 1) (context prepared named) source scope id reasonAt = .ok lowered) :
    Nonempty (Certificate prepared named source scope id reasonAt lowered) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, observed.originalFound,
      bind, Except.bind, pure, Except.pure] at accepted
    change (do
      let output ← CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
        (context prepared named) _ (fuel + 1) source scope id reasonAt
      _) = .ok lowered at accepted
    obtain ⟨output, special, accepted⟩ := bind_ok accepted
    obtain ⟨actual, rfl, receipt⟩ := of_special compiled observed special
    have same : actual = lowered := Except.ok.inj accepted
    exact same ▸ receipt
  · simp [owner, throw, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadCompilation
