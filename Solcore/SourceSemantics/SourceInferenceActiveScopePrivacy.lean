import Solcore.SourceSemantics.SourceInferenceActiveQuantifierPrivacy
import Solcore.SourceSemantics.SourceInferencePrivacyScopeRetention

/-! Scope-preserving inference and actual saved-scope restoration carry the
privacy established for each active generalized binder. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem LiveBindersSafe.restrict {protectedVars : List TypeVarId} {before after : State}
    (live : LiveBindersSafe protectedVars before)
    (subset : after.localBinders ⊆ before.localBinders)
    (same : after.inference.substitution = before.inference.substitution) :
    LiveBindersSafe protectedVars after := by
  intro binder member
  exact (live binder (subset member)).transport (.of_substitution_eq same)

theorem ActiveQuantifiersPrivate.congr {before after : State}
    (privateVars : ActiveQuantifiersPrivate before)
    (binders : after.localBinders = before.localBinders)
    (same : after.inference.substitution = before.inference.substitution) :
    ActiveQuantifiersPrivate after := by
  intro binder member
  exact (privateVars binder (binders ▸ member)).transport binders (.of_substitution_eq same)

theorem ActiveQuantifiersPrivate.restrict {before after : State}
    (privateVars : ActiveQuantifiersPrivate before)
    (subset : after.localBinders ⊆ before.localBinders)
    (same : after.inference.substitution = before.inference.substitution) :
    ActiveQuantifiersPrivate after := by
  intro binder member
  exact (privateVars binder (subset member)).restrict subset same

theorem ActiveQuantifiersPrivate.inferExprFuel
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial : State} {result : InferredExpression × State}
    (privateVars : ActiveQuantifiersPrivate initial)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (bound : ActiveQuantifiersBelowNext initial)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedClosed : ∀ type ∈ expected, type.VariablesBelow 0)
    (accepted : inferExprFuel fuel context source expected initial = .ok result) :
    ActiveQuantifiersPrivate result.2 := by
  have same : result.2.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq accepted)
  intro binder member
  have original : binder ∈ initial.localBinders := same ▸ member
  exact (inferExprFuel_private binder.scheme.quantified fuel context source expected initial
    ready wellFormed (bound binder original) (privateVars binder original) catalog formation canonical
    (fun type present => (expectedClosed type present).weaken (Nat.zero_le _))
    (fun type present => safe_closed _ _ (expectedClosed type present)) result accepted).2.2.1

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
