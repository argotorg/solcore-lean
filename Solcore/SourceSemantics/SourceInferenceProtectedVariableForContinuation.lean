import Solcore.SourceSemantics.SourceInferenceProtectedVariableFrameContracts
import Solcore.SourceSemantics.SourceInferenceProtectedVariablePatterns

/-! The real for initializer, condition, body and post sequence preserves
private scheme variables, including both lexical-scope restorations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem inferStatementFuel_for_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .forLoop headerSpan initializer condition post body)
    (initializerIH : InferForItemsFuelFixedness protectedVars fuel context initializer initial.allocateStatementId.2)
    (conditionIH : ∀ initialized : InferredForItems,
      InferExprFuelFixedness protectedVars fuel context condition (some .bool) initialized.state)
    (bodyIH : ∀ state, InferStatementsFuelFixedness protectedVars fuel
      {context with loopDepth := context.loopDepth + 1} body.value expectedReturn state)
    (postIH : ∀ (initialized : InferredForItems) (checkedBody : BlockResult),
      InferForItemsFuelFixedness protectedVars fuel {context with loopDepth := context.loopDepth + 1} post
        (checkedBody.state.restoreLexicalScope initialized.state.lexicalScope)) :
    InferStatementFuelFixedness protectedVars (fuel+1) context statement expectedReturn initial := by
  intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
  let id := initial.allocateStatementId.1
  let allocated := initial.allocateStatementId.2
  let loopContext := {context with loopDepth := context.loopDepth + 1}
  have allocationEq : initial.allocateStatementId = (id,allocated) := rfl
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  have allocatedLive : LiveBindersSafe protectedVars allocated := live.transport rfl allocatedPrivacy
  unfold inferStatementFuel at success
  simp only [allocationEq, form, bind, Except.bind] at success
  cases initializerRun : inferForItemsFuel fuel context initializer allocated with
  | error error => simp [initializerRun] at success
  | ok initialized =>
    simp only [initializerRun] at success
    have initProperties := inferForItemsFuel_inferenceProperties allocatedReady validated canonical initializerRun
    have initPrivacy := inferForItemsFuel_private protectedVars fuel context initializer allocated allocatedReady wellFormed bound allocatedLive catalog validated canonical initialized initializerRun
    have initFixed := initializerIH allocatedReady wellFormed bound allocatedLive (fixed.of_substitution_eq rfl) catalog validated canonical initialized initializerRun
    have initWellFormed := (inferForItemsFuel_direct_progress initializerRun).wellFormed wellFormed
    cases conditionRun : inferExprFuel fuel context condition (some .bool) initialized.state with
    | error error => simp [conditionRun] at success
    | ok conditionPair =>
      rcases conditionPair with ⟨checkedCondition, conditionState⟩
      simp only [conditionRun] at success
      have boolBelow : ∀ type ∈ some Ty.bool, type.VariablesBelow initialized.state.inference.next := by
        intro type member
        cases Option.mem_def.mp member
        exact Ty.variablesBelow_constructor _ _
      have boolSafe : ∀ type ∈ some Ty.bool, Safe protectedVars initialized.state type := by
        intro type member
        cases Option.mem_def.mp member
        exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)
      have conditionProperties := inferExprFuel_inferenceProperties initProperties.2 validated canonical boolBelow conditionRun
      have conditionPrivacy := inferExprFuel_private protectedVars fuel context condition (some .bool) initialized.state initProperties.2 initWellFormed
        (fun v member => Nat.lt_of_lt_of_le (bound v member) initProperties.1.next_le)
        initPrivacy.2.1 catalog validated canonical boolBelow boolSafe (checkedCondition,conditionState) conditionRun
      have conditionFixed := conditionIH initialized initProperties.2 initWellFormed
        (fun v member => Nat.lt_of_lt_of_le (bound v member) initProperties.1.next_le)
        initPrivacy.2.1 initFixed catalog validated canonical boolBelow boolSafe (checkedCondition,conditionState) conditionRun
      have conditionWellFormed := (inferExprFuel_direct_progress conditionRun).wellFormed initWellFormed
      have throughCondition := initProperties.1.trans conditionProperties.1
      have privacyThroughCondition := initPrivacy.1.trans conditionPrivacy.1
      cases bodyRun : inferStatementsFuel fuel loopContext body.value expectedReturn conditionState with
      | error error => simp [loopContext,bodyRun] at success
      | ok checkedBody =>
        simp only [loopContext,bodyRun] at success
        have bodyProperties := inferStatementsFuel_inferenceProperties (context := loopContext)
          conditionProperties.2.1 validated (fun signature member => canonical signature member)
          (returnBelow.weaken throughCondition.next_le) bodyRun
        have bodyPrivacy := inferStatementsFuel_private protectedVars fuel loopContext body.value expectedReturn conditionState conditionProperties.2.1 conditionWellFormed
          (fun v member => Nat.lt_of_lt_of_le (bound v member) throughCondition.next_le)
          conditionPrivacy.2.2.1 catalog validated (fun signature member => canonical signature member)
          (returnBelow.weaken throughCondition.next_le)
          (privacyThroughCondition _ returnSafe) checkedBody bodyRun
        have bodyFixed := bodyIH conditionState conditionProperties.2.1 conditionWellFormed
          (fun v member => Nat.lt_of_lt_of_le (bound v member) throughCondition.next_le)
          conditionPrivacy.2.2.1 conditionFixed catalog validated (fun signature member => canonical signature member)
          (returnBelow.weaken throughCondition.next_le)
          (privacyThroughCondition _ returnSafe) checkedBody bodyRun
        let afterBody := checkedBody.state.restoreLexicalScope initialized.state.lexicalScope
        have restoredProperties := State.restoreLexicalScope_inferenceProperties initProperties.2
          (conditionProperties.1.trans bodyProperties.1)
        have restoredPrivacy : SafeTransport protectedVars checkedBody.state afterBody := .of_substitution_eq rfl
        have conditionBodyPrivacy := conditionPrivacy.1.trans bodyPrivacy.1
        have afterBodyLive : LiveBindersSafe protectedVars afterBody := initPrivacy.2.1.restore conditionBodyPrivacy
        have afterBodyWellFormed : afterBody.RequirementsWellFormed :=
          State.restoreLexicalScope_preserves_requirementsWellFormed _ _
            ((inferStatementsFuel_direct_progress bodyRun).wellFormed conditionWellFormed)
        have throughBody := initProperties.1.trans restoredProperties.1
        cases postRun : inferForItemsFuel fuel loopContext post afterBody with
        | error error => simp [loopContext,afterBody,postRun] at success
        | ok checkedPost =>
          simp only [loopContext,afterBody,postRun,pure,Pure.pure,Except.pure,Except.ok.injEq] at success
          subst result
          have postFixed := postIH initialized checkedBody restoredProperties.2 afterBodyWellFormed
            (fun v member => Nat.lt_of_lt_of_le (bound v member) throughBody.next_le)
            afterBodyLive (bodyFixed.of_substitution_eq rfl) catalog validated (fun signature member => canonical signature member) checkedPost postRun
          exact postFixed.of_substitution_eq rfl

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
