import Solcore.SourceSemantics.SourceInferenceActiveHeaderSequence
import Solcore.SourceSemantics.SourceInferenceActiveScopePrivacy
import Solcore.Frontend.SourceInference.ForStatementInferenceContinuation

/-! Both header return points have actual privacy continuations through the
remaining for computation, including its two real saved-scope restorations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace ForStatementInferenceContinuation.Receipt
variable {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expected : Ty} {initial : State} {result : StatementResult}

/-- The final scope is a subset of the real post state, and recording the for
node leaves both substitution and requirement ledger unchanged. -/
theorem privacy_after_post
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result)
    {protectedVars : List TypeVarId}
    (live : LiveBindersSafe protectedVars receipt.postResult.state) :
    SafeTransport protectedVars receipt.postResult.state result.state ∧
      LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ receipt.postResult.state.requirements →
        PredicateSafe protectedVars result.state row.predicate := by
  have same := congrArg InferState.substitution receipt.inference_eq
  have binders : result.state.localBinders ⊆ receipt.postResult.state.localBinders := by
    rw [congrArg (fun result : StatementResult => result.state.localBinders) receipt.completed]
    exact (inferForItemsFuel_binders_subset receipt.initialization).trans
      (inferForItemsFuel_binders_subset (initial := receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope) receipt.postAccepted)
  refine ⟨.of_substitution_eq same,live.restrict binders same,?_⟩
  intro row member fresh
  have requirements := congrArg (fun result : StatementResult => result.state.requirements) receipt.completed
  exact False.elim (fresh (requirements ▸ member))

/-- A generalized initializer's returned state reaches the post header and
final saved scope through the actual condition and body calls. -/
theorem privacy_after_initialization
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedClosed : expected.VariablesBelow 0)
    {protectedVars : List TypeVarId}
    (bound : ∀ v ∈ protectedVars, v.index < receipt.initialized.state.inference.next)
    (live : LiveBindersSafe protectedVars receipt.initialized.state) :
    SafeTransport protectedVars receipt.initialized.state result.state ∧
      LiveBindersSafe protectedVars result.state ∧
      ∀ row ∈ result.state.requirements, row ∉ receipt.initialized.state.requirements →
        PredicateSafe protectedVars result.state row.predicate := by
  have initProperties := inferForItemsFuel_inferenceProperties ready.allocateStatementId formation canonical receipt.initialization
  have initWellFormed := (inferForItemsFuel_direct_progress receipt.initialization).wellFormed wellFormed
  have boolBelow : ∀ type ∈ some Ty.bool, type.VariablesBelow receipt.initialized.state.inference.next := by
    intro type member
    cases Option.mem_def.mp member
    exact Ty.variablesBelow_constructor _ _
  have boolSafe : ∀ type ∈ some Ty.bool, Safe protectedVars receipt.initialized.state type := by
    intro type member
    cases Option.mem_def.mp member
    exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  have testProperties := inferExprFuel_inferenceProperties initProperties.2 formation canonical boolBelow receipt.tested
  have testPrivacy := inferExprFuel_private protectedVars fuel context condition (some .bool) receipt.initialized.state
    initProperties.2 initWellFormed bound live catalog formation canonical boolBelow boolSafe _ receipt.tested
  have testWellFormed := (inferExprFuel_direct_progress receipt.tested).wellFormed initWellFormed
  have bodyProperties := inferStatementsFuel_inferenceProperties (context := SourceInference.ForStatementInferenceContinuation.loopContext context)
    testProperties.2.1 formation canonical (expectedClosed.weaken (Nat.zero_le _)) receipt.bodyAccepted
  have bodyPrivacy := inferStatementsFuel_private protectedVars fuel
    (SourceInference.ForStatementInferenceContinuation.loopContext context) body.value expected receipt.testState
    testProperties.2.1 testWellFormed
    (fun v member => Nat.lt_of_lt_of_le (bound v member) testProperties.1.next_le)
    testPrivacy.2.2.1 catalog formation canonical (expectedClosed.weaken (Nat.zero_le _))
    (safe_closed _ _ expectedClosed) _ receipt.bodyAccepted
  let afterBody := receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope
  have restoredProperties := State.restoreLexicalScope_inferenceProperties initProperties.2
    (testProperties.1.trans bodyProperties.1)
  have restoredPrivacy : SafeTransport protectedVars receipt.bodyResult.state afterBody := .of_substitution_eq rfl
  have afterBodyLive : LiveBindersSafe protectedVars afterBody := live.restore (testPrivacy.1.trans bodyPrivacy.1)
  have afterBodyWellFormed : afterBody.RequirementsWellFormed :=
    State.restoreLexicalScope_preserves_requirementsWellFormed _ _
      ((inferStatementsFuel_direct_progress receipt.bodyAccepted).wellFormed testWellFormed)
  have postPrivacy := inferForItemsFuel_private protectedVars fuel
    (SourceInference.ForStatementInferenceContinuation.loopContext context) post afterBody
    restoredProperties.2 afterBodyWellFormed
    (fun v member => Nat.lt_of_lt_of_le (bound v member) restoredProperties.1.next_le)
    afterBodyLive catalog formation canonical _ receipt.postAccepted
  have finalPrivacy := privacy_after_post receipt postPrivacy.2.1
  refine ⟨testPrivacy.1.trans (bodyPrivacy.1.trans (restoredPrivacy.trans (postPrivacy.1.trans finalPrivacy.1))),
    finalPrivacy.2.1,?_⟩
  have bodyRows := new_requirements_trans testPrivacy.2.2.2 bodyPrivacy.2.2.2 bodyPrivacy.1
  have restoredRows : ∀ row ∈ afterBody.requirements, row ∉ receipt.initialized.state.requirements →
      PredicateSafe protectedVars afterBody row.predicate := by
    intro row member fresh type typeMember
    exact restoredPrivacy _ (bodyRows row member fresh type typeMember)
  have postRows := new_requirements_trans restoredRows postPrivacy.2.2 postPrivacy.1
  exact new_requirements_trans postRows finalPrivacy.2.2 finalPrivacy.1

end ForStatementInferenceContinuation.Receipt
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
