import Solcore.SourceSemantics.Internal.Privacy.SelectedReferences
import Solcore.SourceSemantics.Internal.Privacy.SelectedInference

/-!
# Protected variables through inference steps

Each inference branch leaves protected, initially fixed variables unchanged.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableFixedness
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

/-- The current substitution leaves the protected variables themselves fixed.
This is stronger than preservation of types which avoid those variables. -/
def FixesProtected (protectedVars : List TypeVarId) (state : State) : Prop :=
  ∀ q ∈ protectedVars, state.resolve (.variable q) = .variable q

theorem FixesProtected.of_substitution_eq
    {protectedVars : List TypeVarId} {before after : State}
    (fixed : FixesProtected protectedVars before)
    (same : after.inference.substitution = before.inference.substitution) :
    FixesProtected protectedVars after := by
  simpa only [FixesProtected, State.resolve, InferState.resolve, same] using fixed

theorem unify_fixes_protected {protectedVars : List TypeVarId}
    {before after : State} {left right : Ty}
    (fixed : FixesProtected protectedVars before)
    (leftSafe : Safe protectedVars before left)
    (rightSafe : Safe protectedVars before right)
    (accepted : Detail.unify before left right = .ok after) :
    FixesProtected protectedVars after := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    unfold InferState.unify at unified
    cases update : Unification.unifyTypes (before.inference.resolve left)
        (before.inference.resolve right) with
    | error error => simp [update, bind, Except.bind] at unified
    | ok substitution =>
      simp only [update, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at unified
      cases unified
      intro q member
      have outside : q ∉ substitution.domain := by
        intro present
        obtain ⟨constraint, origin, occurs⟩ := Unification.unify_domain_origin update present
        have same : constraint = { left := before.inference.resolve left, right := before.inference.resolve right } :=
          List.mem_singleton.mp origin
        subst constraint
        rcases occurs with inLeft | inRight
        · exact leftSafe q inLeft member
        · exact rightSafe q inRight member
      have beforeFixed := fixed q member
      change (substitution.compose before.inference.substitution).apply (.variable q) = .variable q
      rw [Substitution.compose_apply]
      change substitution.apply (before.resolve (.variable q)) = .variable q
      rw [beforeFixed]
      simp only [Substitution.apply, (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside,
        Option.getD_none]

theorem withExpected_fixes_protected
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult}
    (fixed : FixesProtected protectedVars state)
    (actualSafe : Safe protectedVars state actual.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    FixesProtected protectedVars result.state := by
  cases expected with
  | none =>
    simp only [Detail.withExpected, Except.ok.injEq] at accepted
    cases accepted
    exact fixed
  | some expected =>
    have expectedSafe := expectedSafe expected (by simp)
    cases unified : state.inference.unify actual.type expected with
    | ok inference =>
      simp only [Detail.withExpected, unified, Except.ok.injEq] at accepted
      cases accepted
      exact unify_fixes_protected fixed actualSafe expectedSafe (by
        simp [Detail.unify, unified, Detail.liftUnification, bind, Except.bind])
    | error error =>
      cases error with
      | occursCheck _ _ => simp [Detail.withExpected, unified] at accepted
      | exhausted => simp [Detail.withExpected, unified] at accepted
      | mismatch left right =>
        simp only [Detail.withExpected, unified] at accepted
        cases planned : Detail.coercionPlan? context state
            (state.resolve actual.type) (state.resolve expected) with
        | error error => simp [planned, bind, Except.bind] at accepted
        | ok option =>
          cases option with
          | none => simp [planned, bind, Except.bind] at accepted
          | some plan =>
            simp only [planned, bind, Except.bind] at accepted
            change Except.ok _ = Except.ok result at accepted
            cases Except.ok.inj accepted
            intro q member
            simpa only [Detail.commitCoercionPlan_resolve] using fixed q member

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableFrameContracts
/-! Actual inference leaves protected, initially fixed variables unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

def InferExprFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (expression : Syntax.Expr)
    (expected : Option Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expected, Safe protectedVars state expectedType) →
    ∀ result,
      inferExprFuel fuel context expression expected state = .ok result →
      FixesProtected protectedVars result.2

def InferConstructorApplicationFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (source : Syntax.Expr)
    (id : ExpressionId) (instantiation : DataConstructorInstantiation)
    (arguments : List Syntax.Expr) (expected : Option Ty)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    (∀ payload ∈ instantiation.payloadTypes,
      payload.VariablesBelow state.inference.next) →
    (∀ payload ∈ instantiation.payloadTypes, Safe protectedVars state payload) →
    instantiation.resultType.VariablesBelow state.inference.next →
    Safe protectedVars state instantiation.resultType →
    (∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expected, Safe protectedVars state expectedType) →
    ∀ result,
      inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state = .ok result →
      FixesProtected protectedVars result.2

def InferConstructorArgumentsFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (sources : List Syntax.Expr)
    (expectedTypes : List Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    (∀ expectedType ∈ expectedTypes,
      expectedType.VariablesBelow state.inference.next) →
    (∀ expectedType ∈ expectedTypes, Safe protectedVars state expectedType) →
    ∀ result,
      inferConstructorArgumentsFuel fuel context sources expectedTypes state =
          .ok result →
      FixesProtected protectedVars result.2

def InferStatementsFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (statements : List Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    expectedReturn.VariablesBelow state.inference.next →
    Safe protectedVars state expectedReturn →
    ∀ result,
      inferStatementsFuel fuel context statements expectedReturn state =
          .ok result →
      FixesProtected protectedVars result.state

def InferStatementFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (statement : Syntax.Statement)
    (expectedReturn : Ty) (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    expectedReturn.VariablesBelow state.inference.next →
    Safe protectedVars state expectedReturn →
    ∀ result,
      inferStatementFuel fuel context statement expectedReturn state =
          .ok result →
      FixesProtected protectedVars result.state

def InferForItemsFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (items : List Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferForItemsFuel fuel context items state = .ok result →
      FixesProtected protectedVars result.state

def InferForItemFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (item : Syntax.ForItem)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferForItemFuel fuel context item state = .ok result →
      FixesProtected protectedVars result.2

def InferPlaceFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferPlaceFuel fuel context target state = .ok result →
      FixesProtected protectedVars result.2

def InferAssignedValueFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (target : Syntax.Expr)
    (operator : Syntax.ValueAssignOp) (value : Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferAssignedValueFuel fuel context target operator value state =
          .ok result →
      FixesProtected protectedVars result.2.2

def InferExprsFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (expressions : List Syntax.Expr)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    ∀ result,
      inferExprsFuel fuel context expressions state = .ok result →
      FixesProtected protectedVars result.2

def InferMatchCasesFuelFixedness
    (protectedVars : List TypeVarId) (fuel : Nat) (context : SourceInference.Context) (scrutineeType expectedReturn : Ty)
    (outerScope : LexicalScope) (cases : List Syntax.MatchCase)
    (state : State) : Prop :=
  state.InferenceReady →
    state.RequirementsWellFormed →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    SignatureCatalogWellFormed context.signatures →
    ProgramSignatureFormationValidated context.signatures →
    (∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes)) →
    scrutineeType.VariablesBelow state.inference.next →
    Safe protectedVars state scrutineeType →
    expectedReturn.VariablesBelow state.inference.next →
    Safe protectedVars state expectedReturn →
    state.lexicalScope = outerScope →
    ∀ result,
      inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state = .ok result →
      FixesProtected protectedVars result.state

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableArguments
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem recordExpressionWithExpected_fixes_protected
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId} {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State}
    (fixed : FixesProtected protectedVars state)
    (typeSafe : Safe protectedVars state type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements
      expected state start = .ok result) :
    FixesProtected protectedVars result.2 := by
  unfold Detail.recordExpressionWithExpected at accepted
  cases fitted : Detail.withExpected context state {id, type} expected with
  | error error => simp [fitted, bind, Except.bind] at accepted
  | ok fit =>
    simp only [fitted, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact (withExpected_fixes_protected fixed typeSafe expectedSafe fitted).of_substitution_eq rfl

private theorem candidate_fit {context : SourceInference.Context} {state : State}
    {actual : InferredExpression} {expected : Option Ty} {result : Detail.ExpectationResult}
    (accepted : Detail.candidateWithExpected context state actual expected = .ok (some result)) :
    Detail.withExpected context state actual expected = .ok result := by
  unfold Detail.candidateWithExpected at accepted
  cases fitted : Detail.withExpected context state actual expected with
  | ok value =>
    simp only [fitted, Except.ok.injEq, Option.some.injEq] at accepted
    cases accepted
    rfl
  | error error =>
    cases error <;> simp [fitted] at accepted
    all_goals cases ‹Unification.Error› <;> simp_all

private theorem fitTrace_fixes_protected
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {state : State} {arguments : List InferredExpression} {parameters : List Ty}
    {result : Detail.ArgumentFitResult}
    (trace : Detail.ArgumentFitTrace context state arguments parameters result) :
    state.InferenceReady →
    (∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next) →
    (∀ parameter ∈ parameters, parameter.VariablesBelow state.inference.next) →
    (∀ argument ∈ arguments, Safe protectedVars state argument.type) →
    (∀ parameter ∈ parameters, Safe protectedVars state parameter) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    FixesProtected protectedVars result.state := by
  induction trace with
  | nil state =>
    intro _ _ _ _ _ _ fixed
    exact fixed
  | @cons state argument arguments parameter parameters fitted tail head rest ih =>
    intro ready argumentsBelow parametersBelow argumentsSafe parametersSafe live fixed
    have accepted := candidate_fit head
    have argumentBelow := argumentsBelow argument (by simp)
    have parameterBelow := parametersBelow parameter (by simp)
    have expectedBelow : ∀ type ∈ some parameter, type.VariablesBelow state.inference.next := by
      intro type member
      cases Option.mem_def.mp member
      exact parameterBelow
    have expectedSafe : ∀ type ∈ some parameter, Safe protectedVars state type := by
      intro type member
      cases Option.mem_def.mp member
      exact parametersSafe parameter (by simp)
    have fitProgress := Detail.withExpected_inferenceProperties ready argumentBelow expectedBelow accepted
    have fitting := withExpected_private ready argumentBelow expectedBelow
      (argumentsSafe argument (by simp)) expectedSafe live accepted
    have fittedFixed := withExpected_fixes_protected fixed (argumentsSafe argument (by simp)) expectedSafe accepted
    exact ih fitProgress.2.1
      (fun arg member => (argumentsBelow arg (List.mem_cons_of_mem _ member)).weaken fitProgress.1.next_le)
      (fun param member => (parametersBelow param (List.mem_cons_of_mem _ member)).weaken fitProgress.1.next_le)
      (fun arg member => fitting.1 _ (argumentsSafe arg (List.mem_cons_of_mem _ member)))
      (fun param member => fitting.1 _ (parametersSafe param (List.mem_cons_of_mem _ member)))
      fitting.2.2 fittedFixed

theorem fitArguments_fixes_protected
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {state : State} {arguments : List InferredExpression} {parameters : List Ty}
    {result : Detail.ArgumentFitResult}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (parametersBelow : ∀ parameter ∈ parameters, parameter.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (parametersSafe : ∀ parameter ∈ parameters, Safe protectedVars state parameter)
    (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.fitArguments context state arguments parameters = .ok (some result)) :
    FixesProtected protectedVars result.state :=
  fitTrace_fixes_protected (Detail.fitArguments_some_trace accepted) ready
    argumentsBelow parametersBelow argumentsSafe parametersSafe live fixed

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableApplications
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem functionParts_eq {type parameter result : Ty}
    (found : Detail.functionParts? type = some (parameter,result)) :
    type = .function parameter result := by
  cases type <;> simp [Detail.functionParts?] at found
  case function left right => rcases found with ⟨rfl,rfl⟩; rfl

theorem applyFunctionType_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {call : ExpressionId} {callee : Ty}
    {arguments : List InferredExpression} {expected : Option Ty} {state : State}
    {result : Detail.IndirectApplicationResult}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (calleeBelow : callee.VariablesBelow state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (calleeSafe : Safe protectedVars state callee)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.applyFunctionType context call callee arguments expected state = .ok result) :
    FixesProtected protectedVars result.state := by
  have argumentsBelow : ∀ type ∈ arguments.map InferredExpression.type,
      type.VariablesBelow state.inference.next := by
    intro type member
    obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp member
    exact argumentsBelow arg argMember
  have argumentsSafe : ∀ type ∈ arguments.map InferredExpression.type,
      Safe protectedVars state type := by
    intro type member
    obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp member
    exact argumentsSafe arg argMember
  have productBelow := Ty.variablesBelow_productMany argumentsBelow
  have productSafe := safe_productMany protectedVars state _ argumentsSafe
  rcases Detail.applyFunctionType_success_facts accepted with existing | inferred
  · obtain ⟨parameter, returnType, fittedArgument, fittedResult, parts, argumentFit, resultFit, resultEq⟩ := existing
    subst result
    have partsBelow := Detail.functionParts?_success_variablesBelow
      (ready.solved.variablesBelow_apply calleeBelow) parts
    have partsSafe : Safe protectedVars state parameter ∧ Safe protectedVars state returnType := by
      have safe := safe_resolved ready calleeSafe
      rw [functionParts_eq parts] at safe
      exact (safe_function_iff _ _ _ _).mp safe
    have parameterBelow : ∀ type ∈ some parameter, type.VariablesBelow state.inference.next := by
      intro type member
      cases Option.mem_def.mp member
      exact partsBelow.1
    have parameterSafe : ∀ type ∈ some parameter, Safe protectedVars state type := by
      intro type member
      cases Option.mem_def.mp member
      exact partsSafe.1
    have argumentPrivacy := withExpected_private ready productBelow parameterBelow productSafe parameterSafe live argumentFit
    have argumentFixed := withExpected_fixes_protected fixed productSafe parameterSafe argumentFit
    exact withExpected_fixes_protected argumentFixed
      (argumentPrivacy.1 _ partsSafe.2)
      (fun type member => argumentPrivacy.1 _ (expectedSafe type member)) resultFit
  · obtain ⟨returnType, freshState, unifiedState, fittedResult, _, allocated, unified, resultFit, resultEq⟩ := inferred
    subst result
    have freshSafe := fresh_type ready bound
    have freshTransport : SafeTransport protectedVars state state.fresh.2 := fresh
    have freshFixed : FixesProtected protectedVars state.fresh.2 := fixed.of_substitution_eq rfl
    rw [allocated] at freshSafe freshTransport freshFixed
    have functionSafe := (safe_function_iff protectedVars freshState _ _).mpr
      ⟨freshTransport _ productSafe, freshSafe⟩
    have unifyPrivacy := ProtectedVariables.unify (freshTransport _ calleeSafe) functionSafe unified
    have unifiedFixed := unify_fixes_protected freshFixed (freshTransport _ calleeSafe) functionSafe unified
    exact withExpected_fixes_protected unifiedFixed
      (unifyPrivacy _ freshSafe)
      (fun type member => unifyPrivacy _ (freshTransport _ (expectedSafe type member))) resultFit

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableBuiltins
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem equal_arguments_fixed {protectedVars : List TypeVarId}
    {arguments : List InferredExpression} {parameters : List Ty} {state result : State}
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (parametersSafe : ∀ parameter ∈ parameters, Safe protectedVars state parameter)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.unifyBuiltinFunctionArgumentsEqual arguments parameters state = .ok result) :
    SafeTransport protectedVars state result ∧ FixesProtected protectedVars result := by
  induction arguments generalizing parameters state result with
  | nil =>
    simp only [Detail.unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
    subst result
    exact ⟨.refl _ _, fixed⟩
  | cons argument arguments ih =>
    cases parameters with
    | nil =>
      simp only [Detail.unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
      subst result
      exact ⟨.refl _ _, fixed⟩
    | cons parameter parameters =>
      cases unified : Detail.unify state argument.type parameter with
      | error error => simp [Detail.unifyBuiltinFunctionArgumentsEqual, unified, bind, Except.bind] at accepted
      | ok middle =>
        simp only [Detail.unifyBuiltinFunctionArgumentsEqual, unified, bind, Except.bind] at accepted
        have argumentSafe := argumentsSafe argument List.mem_cons_self
        have parameterSafe := parametersSafe parameter List.mem_cons_self
        have transport := ProtectedVariables.unify argumentSafe parameterSafe unified
        have child := ih
          (fun arg member => transport _ (argumentsSafe arg (List.mem_cons_of_mem _ member)))
          (fun param member => transport _ (parametersSafe param (List.mem_cons_of_mem _ member)))
          (unify_fixes_protected fixed argumentSafe parameterSafe unified) accepted
        exact ⟨transport.trans child.1, child.2⟩

private theorem builtin_parameters_closed (function : BuiltinFunctionId) :
    ∀ type ∈ function.parameterTypes, type.VariablesBelow 0 := by
  cases function <;> simp [BuiltinFunctionId.parameterTypes, Ty.integer, Ty.word]

private theorem builtin_return_closed (function : BuiltinFunctionId) :
    function.returnType.VariablesBelow 0 := by
  cases function <;> simp [BuiltinFunctionId.returnType, Ty.integer, Ty.word, Ty.bool]

private def builtin_finish (source callee : Syntax.Expr) (name : String)
    (function : BuiltinFunctionId) (arguments : List InferredExpression) (call : ExpressionId)
    (state : State) : InferredExpression × State :=
  let (calleeId, state) := state.allocateExpressionId
  let calleeExpression : InferredExpression := {id := calleeId, type := function.type}
  let (_, state) := Detail.recordExpression callee calleeExpression
    (.reference name (.builtinFunction function)) [] [] state
  let result : InferredExpression := {id := call, type := state.resolve function.returnType}
  Detail.recordExpression source result
    (.call calleeId (arguments.map (·.id)) (.builtinFunction function)) [] [] state

theorem recordBuiltinFunctionCall_fixes_protected {protectedVars : List TypeVarId}
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    FixesProtected protectedVars result.2 := by
  unfold Detail.recordBuiltinFunctionCall at accepted
  by_cases arity : arguments.length = function.parameterTypes.length
  · simp only [if_pos arity, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases argumentsRun : Detail.unifyBuiltinFunctionArgumentsEqual arguments function.parameterTypes state with
    | error error => simp [argumentsRun] at accepted
    | ok argumentState =>
      simp only [argumentsRun] at accepted
      have argumentFrame := equal_arguments_fixed argumentsSafe
        (fun type member => safe_closed _ _ (builtin_parameters_closed function type member)) fixed argumentsRun
      cases expected with
      | none =>
        have same : builtin_finish source callee name function arguments call argumentState = result := by
          simpa only [builtin_finish, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
        subst result
        exact argumentFrame.2.of_substitution_eq rfl
      | some expected =>
        cases resultRun : Detail.unify argumentState function.returnType expected with
        | error error => simp [resultRun] at accepted
        | ok finalState =>
          have same : builtin_finish source callee name function arguments call finalState = result := by
            simpa only [resultRun, builtin_finish, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
          subst result
          have finalFixed := unify_fixes_protected argumentFrame.2
            (safe_closed _ _ (builtin_return_closed function))
            (argumentFrame.1 _ (expectedSafe expected rfl)) resultRun
          exact finalFixed.of_substitution_eq rfl
  · simp [arity, bind, Except.bind] at accepted

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableCandidates
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem formed_below {context : SourceSemantics.Context} {type : Ty}
    (formed : TypeWellFormed context type) (next : Nat) : type.VariablesBelow next := by
  intro metavariable occurs
  have closed := StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed
  simp [closed] at occurs

/-- Actual candidate instantiation, argument fitting and result fitting preserve
initially fixed variables excluded by the real operand types. -/
theorem tryFunctionCandidate_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {arguments : List InferredExpression}
    {integerOrigins : List IntegerLiteralOrigin} {call : ExpressionId} {expected : Option Ty}
    {signature : ProgramFunctionSignature} {result : Detail.CandidateAttemptResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (member : signature ∈ context.signatures.functions)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.tryFunctionCandidate context arguments integerOrigins call expected state signature = .ok (some result)) :
    FixesProtected protectedVars result.state := by
  let instantiated := signature.scheme.instantiate state.inference.next
  let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
  have signatureFormed := catalog.functions_semantic signature member
  have nextLe := ConstrainedDeclarationScheme.instantiate_next_le signature.scheme state.inference.next
  have advanceProgress : state.InferenceProgress advanced :=
    State.InferenceProgress.of_substitution_eq ready.solved nextLe rfl
  have advancedReady := State.InferenceReady.of_progress_of_binderEnvironment_eq ready advanceProgress rfl
  have advancePrivacy : SafeTransport protectedVars state advanced := .of_substitution_eq rfl
  have rangeSafe := declaration_instantiation_private signature.scheme ready bound
  have rangeBelow : ∀ {parameter replacement}, (parameter, replacement) ∈ instantiated.parameterSubstitution →
      replacement.VariablesBelow advanced.inference.next :=
    ConstrainedDeclarationScheme.instantiate_parameterSubstitution_range_variablesBelow
      signature.scheme state.inference.next
  have parametersSafe : ∀ type ∈ signature.parameterTypes.map instantiated.parameterSubstitution.apply,
      Safe protectedVars advanced type := by
    intro type typeMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp typeMember
    exact safe_parameterApply rangeSafe
      (safe_closed _ _ (formed_below (signatureFormed.parameter_types _ originalMember) 0))
  have parametersBelow : ∀ type ∈ signature.parameterTypes.map instantiated.parameterSubstitution.apply,
      type.VariablesBelow advanced.inference.next := by
    intro type typeMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp typeMember
    exact ParameterSubstitution.apply_variables_below rangeBelow
      (formed_below (signatureFormed.parameter_types _ originalMember) _)
  have returnsClosed : (Ty.productMany signature.returnTypes).VariablesBelow 0 :=
    Ty.variablesBelow_productMany (fun type member => formed_below (signatureFormed.return_types type member) 0)
  have resultSafe : Safe protectedVars advanced
      (instantiated.parameterSubstitution.apply (Ty.productMany signature.returnTypes)) :=
    safe_parameterApply rangeSafe (safe_closed _ _ returnsClosed)
  obtain ⟨fittedArguments, fittedResult, trace, fitResult, _, _, _, _, _, stateEq⟩ :=
    Detail.tryFunctionCandidate_some_resultFitAllocationWitness signatureFormed.scheme_body accepted
  have argumentAccepted := trace.fitArguments_eq
  have argumentPrivacy := fitArguments_private catalog advancedReady
    (fun arg member => (argumentsBelow arg member).weaken advanceProgress.next_le) parametersBelow
    (fun arg member => advancePrivacy _ (argumentsSafe arg member)) parametersSafe
    (live.transport rfl advancePrivacy) argumentAccepted
  have argumentFixed := fitArguments_fixes_protected advancedReady
    (fun arg member => (argumentsBelow arg member).weaken advanceProgress.next_le) parametersBelow
    (fun arg member => advancePrivacy _ (argumentsSafe arg member)) parametersSafe
    (live.transport rfl advancePrivacy) (fixed.of_substitution_eq rfl) argumentAccepted
  have fittedFixed := withExpected_fixes_protected argumentFixed
    (argumentPrivacy.1 _ resultSafe)
    (fun type member => argumentPrivacy.1 _ (advancePrivacy _ (expectedSafe type member)))
    (candidate_fit fitResult)
  have sameInference : result.state.inference = fittedResult.state.inference := by
    rw [stateEq]
    exact requirementBatch_inference _ _
  exact fittedFixed.of_substitution_eq (congrArg InferState.substitution sameInference)

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableReferences
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem formed_closed {context : SourceSemantics.Context} {type : Ty}
    (formed : TypeWellFormed context type) : type.VariablesBelow 0 := by
  intro metavariable member
  simp [StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil formed] at member

theorem declaration_reference_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {signature : ProgramFunctionSignature}
    {source : Syntax.Expr} {id : ExpressionId} {name : String} {expected : Option Ty}
    {result : InferredExpression × State}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (member : signature ∈ context.signatures.functions)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (fixed : FixesProtected protectedVars state)
    (accepted :
      let instantiated := signature.scheme.instantiate state.inference.next
      let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
      let batch := advanced.addRequirementsWithIds instantiated.predicates
      Detail.recordExpressionWithExpected context source id instantiated.body
        (.reference name (.declaration (DeclarationInstantiation.ofInstantiated signature instantiated)))
        batch.1 expected batch.2 = .ok result) :
    FixesProtected protectedVars result.2 := by
  let instantiated := signature.scheme.instantiate state.inference.next
  let advanced : State := {state with inference := {state.inference with next := instantiated.next}}
  let batch := advanced.addRequirementsWithIds instantiated.predicates
  have formed := catalog.functions_semantic signature member
  have batchInference : batch.2.inference = advanced.inference := requirementBatch_inference _ _
  have sameSubstitution : batch.2.inference.substitution = state.inference.substitution := by
    simpa only [advanced] using congrArg InferState.substitution batchInference
  have initialTransport : SafeTransport protectedVars state batch.2 := .of_substitution_eq sameSubstitution
  have bodyClosed : signature.scheme.body.VariablesBelow 0 := by
    rw [formed.scheme_body]
    intro metavariable occurs
    rcases (Ty.mem_freeVariables_function_iff _ _ _).mp occurs with occurs | occurs
    · exact Ty.variablesBelow_productMany (fun type member => formed_closed (formed.parameter_types type member)) metavariable occurs
    · exact Ty.variablesBelow_productMany (fun type member => formed_closed (formed.return_types type member)) metavariable occurs
  have bodySafe : Safe protectedVars advanced instantiated.body :=
    safe_parameterApply (declaration_instantiation_private signature.scheme ready bound)
      (safe_closed _ _ bodyClosed)
  have completion : SafeTransport protectedVars advanced batch.2 :=
    .of_substitution_eq (congrArg InferState.substitution batchInference)
  exact recordExpressionWithExpected_fixes_protected (fixed.of_substitution_eq sameSubstitution)
    (completion _ bodySafe) (fun type member => initialTransport _ (expectedSafe type member)) accepted

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableCallRecording
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem selectFunctionCandidateFrom_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state : State} {name : String}
    {candidates : List ProgramFunctionSignature} {arguments : List InferredExpression}
    {integerOrigins : List IntegerLiteralOrigin} {call : ExpressionId} {expected : Option Ty}
    {result : Detail.CandidateAttemptResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (cataloged : candidates ⊆ context.signatures.functions)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.selectFunctionCandidateFrom context name candidates arguments integerOrigins call expected state = .ok result) :
    FixesProtected protectedVars result.state := by
  obtain ⟨signature, member, tried⟩ := Detail.selectFunctionCandidateFrom_success_candidate accepted
  exact tryFunctionCandidate_fixes_protected catalog (cataloged member) ready bound argumentsBelow
    argumentsSafe expectedSafe live fixed tried

private theorem attach_inference (state : State) (entries : List Detail.ExpressionCoercions) :
    (Detail.attachExpressionCoercions state entries).inference = state.inference := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih => exact ih (state.modifyExpressionNode entry.expression
      (fun node => Detail.appendExpressionCoercions node entry.coercions))

theorem recordSelectedCall_fixes_protected {protectedVars : List TypeVarId}
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : Detail.CandidateAttemptResult)
    (fixed : FixesProtected protectedVars attempt.state) :
    FixesProtected protectedVars (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  fixed.of_substitution_eq (congrArg InferState.substitution (attach_inference _ _))

theorem recordSelectedCallResult_fixes_protected {protectedVars : List TypeVarId}
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : Detail.CandidateAttemptResult) (result : InferredExpression)
    (coercions : List CoercionStep) (state : State)
    (fixed : FixesProtected protectedVars state) :
    FixesProtected protectedVars (Detail.recordSelectedCallResult source callee name arguments attempt result coercions state).2 :=
  fixed.of_substitution_eq (congrArg InferState.substitution (attach_inference _ _))

theorem recordIndirectCall_fixes_protected {protectedVars : List TypeVarId}
    (source : Syntax.Expr) (callee : InferredExpression) (arguments : List InferredExpression)
    (application : Detail.IndirectApplicationResult)
    (fixed : FixesProtected protectedVars application.state) :
    FixesProtected protectedVars (Detail.recordIndirectCall source callee arguments application).2 :=
  fixed.of_substitution_eq rfl

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableCallContinuation
/-! The actual call dispatcher preserves fixed protected variables through
constructor, named, builtin and indirect alternatives. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem freshDataConstructorInstantiation_substitution (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (Detail.freshDataConstructorInstantiation dataType constructor state).2.inference.substitution =
      state.inference.substitution := by
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      (parameters.foldl (fun result _ =>
        (result.1 ++ [result.2.fresh.1], result.2.fresh.2)) accumulator).2.inference.substitution =
        accumulator.2.inference.substitution := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter rest ih => exact ih (accumulator.1 ++ [accumulator.2.fresh.1], accumulator.2.fresh.2)
  exact fold dataType.parameters ([],state)

theorem inferExprFuel_call_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression callee : Syntax.Expr} {sourceArguments : Syntax.DelimitedList Syntax.Expr}
    {expected : Option Ty} {initial : State}
    (expressionEq : expression.value = .call callee sourceArguments)
    (constructorInduction : ∀ instantiation state,
      InferConstructorApplicationFuelFixedness protectedVars fuel context expression
        initial.allocateExpressionId.1 instantiation sourceArguments.elements expected state)
    (argumentsInduction : InferExprsFuelFixedness protectedVars fuel context
      sourceArguments.elements initial.allocateExpressionId.2)
    (calleeInduction : ∀ state, InferExprFuelFixedness protectedVars fuel context callee none state) :
    InferExprFuelFixedness protectedVars (fuel+1) context expression expected initial := by
  intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id,allocated) := rfl
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateExpressionId ready
  have allocatedPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  have allocatedFixed : FixesProtected protectedVars allocated := fixed.of_substitution_eq rfl
  have allocatedLive : LiveBindersSafe protectedVars allocated := live.transport rfl allocatedPrivacy
  unfold inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases candidatesResult : constructorCalleeCandidates context allocated callee with
  | error error => simp [candidatesResult] at success
  | ok candidates =>
    simp only [candidatesResult] at success
    cases candidates with
    | cons candidate rest =>
      cases rest with
      | cons second tail => simp at success
      | nil =>
        rcases candidate with ⟨dataType, constructor⟩
        let freshResult := freshDataConstructorInstantiation dataType constructor allocated
        have candidateFacts := constructorCalleeCandidates_success_members candidatesResult dataType constructor (by simp)
        have payloadClosed := validated.data_constructor_payloadTypes_variablesBelow candidateFacts.1 candidateFacts.2 0
        have freshProperties := freshDataConstructorInstantiation_inferenceProperties dataType constructor allocated allocatedReady
          (fun type member => (payloadClosed type member).weaken (Nat.zero_le _))
        have freshPrivacy := fresh_constructor (dataType := dataType) allocatedReady bound payloadClosed
        have freshLive := allocatedLive.transport
          (congrArg LexicalScope.binders (freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor allocated)) freshPrivacy.1
        have freshWellFormed := (freshDataConstructorInstantiation_direct_progress dataType constructor allocated).wellFormed wellFormed
        have finished := constructorInduction freshResult.1 freshResult.2 freshProperties.2.1 freshWellFormed
          (fun v member => Nat.lt_of_lt_of_le (bound v member) freshProperties.1.next_le)
          freshLive (allocatedFixed.of_substitution_eq (freshDataConstructorInstantiation_substitution _ _ _)) catalog validated canonical freshProperties.2.2.2.1 freshPrivacy.2.1
          freshProperties.2.2.2.2 freshPrivacy.2.2
          (fun type member => (expectedBelow type member).weaken freshProperties.1.next_le)
          (fun type member => freshPrivacy.1 _ (expectedSafe type member)) result success
        exact finished
    | nil =>
      simp only at success
      split at success
      · cases success
      · next _ missing _ =>
        cases missing with
        | some missing => rcases missing with ⟨qualifiers,name⟩; simp at success
        | none =>
          cases argumentsResult : inferExprsFuel fuel context sourceArguments.elements allocated with
          | error error => simp [argumentsResult] at success
          | ok argumentsPair =>
            rcases argumentsPair with ⟨arguments, argumentState⟩
            simp only [argumentsResult] at success
            have argumentsProperties := inferExprsFuel_inferenceProperties allocatedReady validated canonical argumentsResult
            have argumentsPrivacy := inferExprsFuel_private protectedVars fuel context sourceArguments.elements allocated allocatedReady wellFormed bound allocatedLive catalog validated canonical
              (arguments,argumentState) argumentsResult
            have argumentsFixed := argumentsInduction allocatedReady wellFormed bound allocatedLive allocatedFixed catalog validated canonical
              (arguments,argumentState) argumentsResult
            have expectedAtArguments : ∀ type ∈ expected, type.VariablesBelow argumentState.inference.next :=
              fun type member => (expectedBelow type member).weaken argumentsProperties.1.next_le
            have expectedSafeAtArguments : ∀ type ∈ expected, Safe protectedVars argumentState type :=
              fun type member => argumentsPrivacy.1 _ (expectedSafe type member)
            have argumentBound : ∀ v ∈ protectedVars, v.index < argumentState.inference.next :=
              fun v member => Nat.lt_of_lt_of_le (bound v member) argumentsProperties.1.next_le
            have finishSelected (name : String) (candidates : List ProgramFunctionSignature)
                (subset : candidates ⊆ context.signatures.functions) (attempt : CandidateAttemptResult)
                (selectionSuccess : selectFunctionCandidateFrom context name candidates arguments
                  (relevantIntegerLiterals argumentState allocated.integerLiterals.length arguments) id expected argumentState = .ok attempt)
                (resultEq : recordSelectedCall expression callee name arguments attempt = result) :
                FixesProtected protectedVars result.2 := by
              have selected := selectFunctionCandidateFrom_fixes_protected catalog subset argumentsProperties.2.1 argumentBound
                argumentsProperties.2.2 argumentsPrivacy.2.1 expectedSafeAtArguments argumentsPrivacy.2.2.1 argumentsFixed selectionSuccess
              rw [← resultEq]
              exact recordSelectedCall_fixes_protected expression callee name arguments attempt selected
            have finishIndirect (calleeResult : InferredExpression) (calleeState : State)
                (calleeSuccess : inferExprFuel fuel context callee none argumentState = .ok (calleeResult,calleeState))
                (application : IndirectApplicationResult)
                (applicationSuccess : applyFunctionType context id calleeResult.type arguments expected calleeState = .ok application)
                (resultEq : recordIndirectCall expression calleeResult arguments application = result) :
                FixesProtected protectedVars result.2 := by
              have calleeProperties := inferExprFuel_inferenceProperties argumentsProperties.2.1 validated canonical (by simp) calleeSuccess
              have calleePrivacy := inferExprFuel_private protectedVars fuel context callee none argumentState argumentsProperties.2.1
                ((inferExprsFuel_direct_progress argumentsResult).wellFormed wellFormed) argumentBound argumentsPrivacy.2.2.1
                catalog validated canonical (by simp) (by simp) (calleeResult,calleeState) calleeSuccess
              have calleeFixed := calleeInduction argumentState argumentsProperties.2.1
                ((inferExprsFuel_direct_progress argumentsResult).wellFormed wellFormed) argumentBound argumentsPrivacy.2.2.1 argumentsFixed
                catalog validated canonical (by simp) (by simp) (calleeResult,calleeState) calleeSuccess
              have applied := applyFunctionType_fixes_protected calleeProperties.2.1
                (fun v member => Nat.lt_of_lt_of_le (argumentBound v member) calleeProperties.1.next_le)
                calleeProperties.2.2
                (fun argument member => (argumentsProperties.2.2 argument member).weaken calleeProperties.1.next_le)
                calleePrivacy.2.1 (fun argument member => calleePrivacy.1 _ (argumentsPrivacy.2.1 argument member))
                (fun type member => calleePrivacy.1 _ (expectedSafeAtArguments type member)) calleePrivacy.2.2.1 calleeFixed applicationSuccess
              rw [← resultEq]
              exact recordIndirectCall_fixes_protected expression calleeResult arguments application applied
            cases qualifiedEq : calleeQualifiedIdentifier? callee with
            | some qualified =>
                rcases qualified with ⟨namespacePath, name⟩
                simp only [qualifiedEq] at success
                cases binderEq :
                    argumentState.lookupBinder? namespacePath.head! with
                | some binder =>
                    simp only [binderEq] at success
                    cases calleeResult : inferExprFuel fuel context callee
                        none argumentState with
                    | error error =>
                        simp [calleeResult] at success
                    | ok calleePair =>
                        rcases calleePair with
                          ⟨inferredCallee, calleeState⟩
                        simp only [calleeResult] at success
                        cases applicationResult : applyFunctionType
                            context id inferredCallee.type arguments
                            expected calleeState with
                        | error error =>
                            simp [applicationResult]
                              at success
                        | ok application =>
                            simp only [applicationResult, pure, Pure.pure, Except.pure]
                              at success
                            injection success with resultEq
                            exact finishIndirect inferredCallee
                              calleeState calleeResult application
                              applicationResult resultEq
                | none =>
                    simp only [binderEq] at success
                    cases functionsResult : qualifiedFunctionsNamed
                        context namespacePath name with
                    | error error =>
                        simp [functionsResult]
                          at success
                    | ok candidatesOption =>
                        simp only [functionsResult]
                          at success
                        cases candidatesOption with
                        | some candidates =>
                            cases selectionResult :
                                selectFunctionCandidateFrom context
                                  (String.intercalate "."
                                    (namespacePath ++ [name]))
                                  candidates arguments
                                  (relevantIntegerLiterals
                                    argumentState
                                    allocated.integerLiterals.length
                                    arguments)
                                  id expected argumentState with
                            | error error =>
                                simp [selectionResult] at success
                            | ok attempt =>
                                simp only [selectionResult, pure, Pure.pure,
                                  Except.pure] at success
                                injection success with resultEq
                                exact finishSelected
                                  (String.intercalate "."
                                    (namespacePath ++ [name]))
                                  candidates
                                  (qualifiedFunctionsNamed_success_subset_catalog
                                    functionsResult)
                                  attempt selectionResult resultEq
                        | none =>
                            cases calleeResult : inferExprFuel fuel
                                context callee none argumentState with
                            | error error =>
                                simp [calleeResult]
                                  at success
                            | ok calleePair =>
                                rcases calleePair with
                                  ⟨inferredCallee, calleeState⟩
                                simp only [calleeResult] at success
                                cases applicationResult :
                                    applyFunctionType context id
                                      inferredCallee.type arguments
                                      expected calleeState with
                                | error error =>
                                    simp [applicationResult] at success
                                | ok application =>
                                    simp only [applicationResult, pure, Pure.pure,
                                      Except.pure] at success
                                    injection success with resultEq
                                    exact finishIndirect inferredCallee
                                      calleeState calleeResult
                                      application applicationResult
                                      resultEq
            | none =>
                simp only [qualifiedEq] at success
                cases identifierEq : calleeIdentifier? callee with
                | none =>
                    simp only [identifierEq] at success
                    cases calleeResult : inferExprFuel fuel context callee
                        none argumentState with
                    | error error =>
                        simp [calleeResult] at success
                    | ok calleePair =>
                        rcases calleePair with
                          ⟨inferredCallee, calleeState⟩
                        simp only [calleeResult] at success
                        cases applicationResult : applyFunctionType
                            context id inferredCallee.type arguments
                            expected calleeState with
                        | error error =>
                            simp [applicationResult]
                              at success
                        | ok application =>
                            simp only [applicationResult, pure, Pure.pure, Except.pure]
                              at success
                            injection success with resultEq
                            exact finishIndirect inferredCallee
                              calleeState calleeResult application
                              applicationResult resultEq
                | some name =>
                    simp only [identifierEq] at success
                    cases binderEq : argumentState.lookupBinder? name with
                    | some binder =>
                        simp only [binderEq] at success
                        cases calleeResult : inferExprFuel fuel context
                            callee none argumentState with
                        | error error =>
                            simp [calleeResult]
                              at success
                        | ok calleePair =>
                            rcases calleePair with
                              ⟨inferredCallee, calleeState⟩
                            simp only [calleeResult] at success
                            cases applicationResult : applyFunctionType
                                context id inferredCallee.type arguments
                                expected calleeState with
                            | error error =>
                                simp [applicationResult] at success
                            | ok application =>
                                simp only [applicationResult, pure, Pure.pure,
                                  Except.pure] at success
                                injection success with resultEq
                                exact finishIndirect inferredCallee
                                  calleeState calleeResult application
                                  applicationResult resultEq
                    | none =>
                        simp only [binderEq] at success
                        cases functionsResult : functionsNamed context
                            name with
                        | error error =>
                            simp [functionsResult]
                              at success
                        | ok candidates =>
                            simp only [functionsResult] at success
                            cases candidates with
                            | nil =>
                                cases builtinEq :
                                    builtinFunctionNamed? name with
                                | none =>
                                    simp [builtinEq] at success
                                | some function =>
                                    simp only [builtinEq] at success
                                    exact recordBuiltinFunctionCall_fixes_protected
                                      argumentsPrivacy.2.1 expectedSafeAtArguments argumentsFixed success
                            | cons candidate rest =>
                                cases selectionResult :
                                    selectFunctionCandidateFrom context
                                      name (candidate :: rest) arguments
                                      (relevantIntegerLiterals
                                        argumentState
                                        allocated.integerLiterals.length
                                        arguments)
                                      id expected argumentState with
                                | error error =>
                                    simp [selectionResult] at success
                                | ok attempt =>
                                    simp only [selectionResult, pure, Pure.pure,
                                      Except.pure] at success
                                    injection success with resultEq
                                    exact finishSelected name
                                      (candidate :: rest)
                                      (functionsNamed_success_subset_catalog
                                        functionsResult)
                                      attempt selectionResult resultEq

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableConstructorContinuation
/-! Contextual and explicit constructor expression dispatch preserves fixed
protected variables before delegating to the actual smaller application. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem inferExprFuel_dotConstructor_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option Ty} {initial : State}
    {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    {arguments : Option (Syntax.DelimitedList Syntax.Expr)}
    (expressionEq : expression.value = .dotConstructor dot name arguments)
    (constructorInduction : ∀ dataType constructor typeArguments,
      InferConstructorApplicationFuelFixedness protectedVars fuel context expression
        initial.allocateExpressionId.1 (instantiateDataConstructor dataType constructor typeArguments)
        (arguments.map (·.elements) |>.getD []) expected initial.allocateExpressionId.2) :
    InferExprFuelFixedness protectedVars (fuel+1) context expression expected initial := by
  intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id,allocated) := rfl
  have allocatedFixed : FixesProtected protectedVars allocated := fixed.of_substitution_eq rfl
  have allocationProperties : initial.InferenceProgress allocated ∧ allocated.InferenceReady :=
    ⟨.allocateExpressionId _ ready.solved, ready.allocateExpressionId⟩
  have expectedAtAllocated : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow allocated.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      allocationProperties.1.next_le
  have allocationTransport : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  have allocationPrivacy : SafeTransport protectedVars initial allocated ∧
      LiveBindersSafe protectedVars allocated ∧ allocated.requirements = initial.requirements :=
    ⟨allocationTransport, live.transport rfl allocationTransport, rfl⟩
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
  have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
    intro metavariable member
    rw [allocatedEq]
    change metavariable.index < initial.inference.next
    exact bound metavariable member
  have wfAllocated : allocated.RequirementsWellFormed := by
    rw [allocatedEq]
    change initial.RequirementsWellFormed
    exact wellFormed
  unfold inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases candidateResult : contextualConstructorCandidate context allocated
      expected name.value with
  | error error =>
      simp [candidateResult] at success
  | ok candidate =>
      rcases candidate with ⟨dataType, constructor, typeArguments⟩
      simp only [candidateResult] at success
      have instantiationBelow :=
        contextualConstructorCandidate_success_instantiation_variablesBelow
          allocationProperties.2 expectedAtAllocated validated
          candidateResult
      obtain ⟨dataMember, constructorMember, actual, expectedEq, nominalEq⟩ := contextualConstructorCandidate_success_facts candidateResult
      have instantiationSafe := contextual_constructor allocationProperties.2 validated
        (allocationPrivacy.1 _ (expectedSafe actual (by rw [expectedEq]; simp)))
        (by simpa only [expectedEq] using candidateResult)
      have finished := constructorInduction dataType constructor typeArguments allocationProperties.2 wfAllocated boundAllocated
        allocationPrivacy.2.1 allocatedFixed catalog validated canonical
        instantiationBelow.1 instantiationSafe.1 instantiationBelow.2 instantiationSafe.2
        expectedAtAllocated (fun type member => allocationPrivacy.1 _ (expectedSafe type member)) result success
      exact finished

theorem inferExprFuel_fieldConstructor_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression base : Syntax.Expr} {expected : Option Ty} {initial : State}
    {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    (expressionEq : expression.value = .field base dot name)
    (constructorInduction : ∀ instantiation state,
      InferConstructorApplicationFuelFixedness protectedVars fuel context expression
        initial.allocateExpressionId.1 instantiation [] expected state) :
    InferExprFuelFixedness protectedVars (fuel+1) context expression expected initial := by
  intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id,allocated) := rfl
  have allocatedFixed : FixesProtected protectedVars allocated := fixed.of_substitution_eq rfl
  have allocationProperties : initial.InferenceProgress allocated ∧ allocated.InferenceReady :=
    ⟨.allocateExpressionId _ ready.solved, ready.allocateExpressionId⟩
  have expectedAtAllocated : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow allocated.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      allocationProperties.1.next_le
  have allocationTransport : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  have allocationPrivacy : SafeTransport protectedVars initial allocated ∧
      LiveBindersSafe protectedVars allocated ∧ allocated.requirements = initial.requirements :=
    ⟨allocationTransport, live.transport rfl allocationTransport, rfl⟩
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
  have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
    intro metavariable member
    rw [allocatedEq]
    change metavariable.index < initial.inference.next
    exact bound metavariable member
  have wfAllocated : allocated.RequirementsWellFormed := by
    rw [allocatedEq]
    change initial.RequirementsWellFormed
    exact wellFormed
  unfold inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases candidatesResult :
      constructorCalleeCandidates context allocated expression with
  | error error =>
      simp [candidatesResult] at success
  | ok candidates =>
      simp only [candidatesResult] at success
      cases candidates with
      | nil =>
          simp only [] at success
          repeat' first | split at success
          all_goals contradiction
      | cons candidate rest =>
          cases rest with
          | cons second tail => simp at success
          | nil =>
              rcases candidate with ⟨dataType, constructor⟩
              let freshResult :=
                freshDataConstructorInstantiation dataType constructor
                  allocated
              have candidateFacts :=
                constructorCalleeCandidates_success_members candidatesResult
                  dataType constructor (by simp)
              have payloadTypesBelow :=
                validated.data_constructor_payloadTypes_variablesBelow
                  candidateFacts.1 candidateFacts.2
                  allocated.inference.next
              have freshProperties :=
                freshDataConstructorInstantiation_inferenceProperties
                  dataType constructor allocated allocationProperties.2
                  payloadTypesBelow
              have payloadClosed := validated.data_constructor_payloadTypes_variablesBelow candidateFacts.1 candidateFacts.2 0
              have freshPrivacy := fresh_constructor (dataType := dataType) allocationProperties.2 boundAllocated payloadClosed
              have freshLive := allocationPrivacy.2.1.transport
                (congrArg LexicalScope.binders (freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor allocated)) freshPrivacy.1
              have freshWF := (freshDataConstructorInstantiation_direct_progress dataType constructor allocated).wellFormed wfAllocated
              have finished := constructorInduction freshResult.1 freshResult.2 freshProperties.2.1 freshWF
                (fun metavariable member => Nat.lt_of_lt_of_le (boundAllocated metavariable member) freshProperties.1.next_le)
                freshLive (allocatedFixed.of_substitution_eq (freshDataConstructorInstantiation_substitution _ _ _)) catalog validated canonical freshProperties.2.2.2.1 freshPrivacy.2.1
                freshProperties.2.2.2.2 freshPrivacy.2.2
                (fun type member => (expectedAtAllocated type member).weaken freshProperties.1.next_le)
                (fun type member => freshPrivacy.1 _ (allocationPrivacy.1 _ (expectedSafe type member))) result
                (by simpa only [freshResult] using success)
              exact finished

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariablePatterns
/-! Protected variables remain fixed through actual recursive pattern inference. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem freshTypes_fields (count : Nat) (state : State) :
    (Detail.freshTypes count state).2.localBinders = state.localBinders ∧
      (Detail.freshTypes count state).2.requirements = state.requirements := by
  induction count generalizing state with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih => exact ih state.fresh.2

private theorem freshTypes_substitution (count : Nat) (state : State) :
    (Detail.freshTypes count state).2.inference.substitution = state.inference.substitution := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => exact ih state.fresh.2

private theorem freshConstructor_substitution (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (Detail.freshDataConstructorInstantiation dataType constructor state).2.inference.substitution =
      state.inference.substitution := by
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      (parameters.foldl (fun result _ =>
        (result.1 ++ [result.2.fresh.1], result.2.fresh.2)) accumulator).2.inference.substitution =
        accumulator.2.inference.substitution := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter rest ih => exact ih (accumulator.1 ++ [accumulator.2.fresh.1], accumulator.2.fresh.2)
  exact fold dataType.parameters ([],state)

private def PatternFixedProgress (protectedVars : List TypeVarId) (initial final : State) : Prop :=
  SafeTransport protectedVars initial final ∧ LiveBindersSafe protectedVars final ∧
    FixesProtected protectedVars final

private theorem PatternFixedProgress.trans {protectedVars : List TypeVarId} {first second third : State}
    (left : PatternFixedProgress protectedVars first second) (right : PatternFixedProgress protectedVars second third) :
    PatternFixedProgress protectedVars first third :=
  ⟨left.1.trans right.1, right.2.1, right.2.2⟩

private theorem PatternFixedProgress.of_unchanged {protectedVars : List TypeVarId} {initial final : State}
    (transport : SafeTransport protectedVars initial final) (live : LiveBindersSafe protectedVars final)
    (fixed : FixesProtected protectedVars final) : PatternFixedProgress protectedVars initial final :=
  ⟨transport, live, fixed⟩

private theorem integer_prefix_private {protectedVars : List TypeVarId} {state recorded final : State}
    {expected : Ty} {metavariable : TypeVarId} {normalized : Ty}
    (ready : state.InferenceReady)
    (bound : ∀ protectedVariable ∈ protectedVars, protectedVariable.index < state.inference.next)
    (expectedSafe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (freshType : state.fresh.1 = .variable metavariable)
    (unified : Detail.unify recorded (.variable metavariable) normalized = .ok final)
    (normalization : recorded.resolve expected = normalized)
    (inference : recorded.inference = state.fresh.2.inference)
    (binders : recorded.localBinders = state.localBinders) :
    PatternFixedProgress protectedVars state final := by
  have stage : SafeTransport protectedVars state.fresh.2 recorded :=
    .of_substitution_eq (congrArg InferState.substitution inference)
  have initialStage : SafeTransport protectedVars state recorded := fresh.trans stage
  have targetSafe : Safe protectedVars recorded (.variable metavariable) :=
    freshType ▸ stage _ (fresh_type ready bound)
  have recordedReady : recorded.InferenceReady := by
    apply State.InferenceReady.of_progress_of_binderEnvironment_eq ready.fresh
      (State.InferenceProgress.of_inference_eq ready.fresh.solved inference)
    simp only [State.binderEnvironment, binders]
    rfl
  have normalizedSafe : Safe protectedVars recorded normalized :=
    normalization ▸ safe_resolved recordedReady (initialStage _ expectedSafe)
  have transport := ProtectedVariables.unify targetSafe normalizedSafe unified
  exact ⟨initialStage.trans transport,
    (live.transport binders initialStage).unify targetSafe normalizedSafe unified,
    unify_fixes_protected ((fixed.of_substitution_eq (after := state.fresh.2) rfl).of_substitution_eq (congrArg InferState.substitution inference))
      targetSafe normalizedSafe unified⟩

private theorem contextual_prefix_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state final : State} {expected : Ty} {name : String}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature} {arguments : List Ty}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (safe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (selected : Detail.contextualConstructorCandidate context state (some expected) name = .ok (dataType,constructor,arguments))
    (unified : Detail.unify state (Detail.instantiateDataConstructor dataType constructor arguments).resultType expected = .ok final) :
    PatternFixedProgress protectedVars state final ∧ state.InferenceProgress final ∧ final.InferenceReady ∧
      (∀ type ∈ (Detail.instantiateDataConstructor dataType constructor arguments).payloadTypes,
        type.VariablesBelow final.inference.next ∧ Safe protectedVars final type) := by
  have privacy := contextual_constructor ready formation safe selected
  obtain ⟨dataMember, constructorMember, actual, expectedEq, nominalEq⟩ :=
    Detail.contextualConstructorCandidate_success_facts selected
  cases Option.some.inj expectedEq
  have resolvedBelow : (state.resolve expected).VariablesBelow state.inference.next :=
    ready.solved.variablesBelow_apply expectedBelow
  rw [nominalEq] at resolvedBelow
  have argumentsBelow := ((Ty.variablesBelow_applyMany_iff state.inference.next
    (.constructor (.declaration dataType.id)) arguments).mp
      (by simpa only [Ty.nominal] using resolvedBelow)).2
  have bounds := Detail.instantiateDataConstructor_types_variablesBelow (dataType := dataType) argumentsBelow
    (formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember state.inference.next)
  have progress := Detail.unify_inferenceProgress ready.solved bounds.2 expectedBelow unified
  have finalReady := Detail.unify_preserves_inferenceReady ready bounds.2 expectedBelow unified
  have transport := ProtectedVariables.unify privacy.2 safe unified
  exact ⟨PatternFixedProgress.of_unchanged transport (live.unify privacy.2 safe unified) (unify_fixes_protected fixed privacy.2 safe unified),
    progress, finalReady, fun type member => ⟨(bounds.1 type member).weaken progress.next_le, transport _ (privacy.1 type member)⟩⟩

private theorem explicit_prefix_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {state allocated final : State} {expected : Ty}
    {qualifiers : List String} {name : String} {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {instantiation : DataConstructorInstantiation}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ∀ protectedVariable ∈ protectedVars, protectedVariable.index < state.inference.next)
    (safe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (selected : Detail.explicitConstructorCandidate context qualifiers name = .ok (dataType,constructor))
    (allocation : Detail.freshDataConstructorInstantiation dataType constructor state = (instantiation,allocated))
    (unified : Detail.unify allocated instantiation.resultType expected = .ok final) :
    PatternFixedProgress protectedVars state final ∧ state.InferenceProgress final ∧ final.InferenceReady ∧
      (∀ type ∈ instantiation.payloadTypes, type.VariablesBelow final.inference.next ∧ Safe protectedVars final type) := by
  obtain ⟨dataMember, constructorMember, _⟩ := Detail.explicitConstructorCandidate_success_facts selected
  have payloadClosed := formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember 0
  have privacy := fresh_constructor (dataType := dataType) ready bound payloadClosed
  have properties := Detail.freshDataConstructorInstantiation_inferenceProperties dataType constructor state ready
    (fun type member => (payloadClosed type member).weaken (Nat.zero_le _))
  have lexical := Detail.freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor state
  have substitution := freshConstructor_substitution dataType constructor state
  rw [allocation] at privacy properties lexical substitution
  have allocatedBinders := congrArg LexicalScope.binders lexical
  have expectedBound := expectedBelow.weaken properties.1.next_le
  have expectedSafe := privacy.1 _ safe
  have transport := ProtectedVariables.unify privacy.2.2 expectedSafe unified
  have progress := Detail.unify_inferenceProgress properties.2.1.solved properties.2.2.2.2 expectedBound unified
  have finalReady := Detail.unify_preserves_inferenceReady properties.2.1 properties.2.2.2.2 expectedBound unified
  have finalLive := (live.transport allocatedBinders privacy.1).unify privacy.2.2 expectedSafe unified
  exact ⟨PatternFixedProgress.of_unchanged (privacy.1.trans transport) finalLive (unify_fixes_protected (fixed.of_substitution_eq substitution) privacy.2.2 expectedSafe unified),
    properties.1.trans progress, finalReady, fun type member => ⟨(properties.2.2.2.1 type member).weaken progress.next_le,
      transport _ (privacy.2.1 type member)⟩⟩

private theorem tuple_prefix_private {protectedVars : List TypeVarId} {state allocated final : State}
    {expected : Ty} {types : List Ty} {count : Nat}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (bound : ∀ protectedVariable ∈ protectedVars, protectedVariable.index < state.inference.next)
    (safe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (allocation : Detail.freshTypes count state = (types,allocated))
    (unified : Detail.unify allocated expected (Ty.productMany types) = .ok final) :
    PatternFixedProgress protectedVars state final ∧ state.InferenceProgress final ∧ final.InferenceReady ∧
      (∀ type ∈ types, type.VariablesBelow final.inference.next ∧ Safe protectedVars final type) := by
  have privacy := freshTypes count ready bound
  have properties := Detail.freshTypes_inferenceProperties count state ready
  have fields := freshTypes_fields count state
  have substitution := freshTypes_substitution count state
  rw [allocation] at privacy properties fields substitution
  have expectedSafe := privacy.1 _ safe
  have argumentsSafe := safe_productMany protectedVars allocated types privacy.2
  have expectedBound := expectedBelow.weaken properties.1.next_le
  have productBound := Ty.variablesBelow_productMany properties.2.2
  have progress := Detail.unify_inferenceProgress properties.2.1.solved expectedBound productBound unified
  have finalReady := Detail.unify_preserves_inferenceReady properties.2.1 expectedBound productBound unified
  have transport := ProtectedVariables.unify expectedSafe argumentsSafe unified
  have finalLive := (live.transport fields.1 privacy.1).unify expectedSafe argumentsSafe unified
  exact ⟨PatternFixedProgress.of_unchanged (privacy.1.trans transport) finalLive (unify_fixes_protected (fixed.of_substitution_eq substitution) expectedSafe argumentsSafe unified),
    properties.1.trans progress, finalReady, fun type member => ⟨(properties.2.2 type member).weaken progress.next_le, transport _ (privacy.2 type member)⟩⟩


private def PatternCallFixedness (protectedVars : List TypeVarId) (fuel : Nat)
    (context : SourceInference.Context) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result, state.InferenceReady → expected.VariablesBelow state.inference.next →
    ProgramSignatureFormationValidated context.signatures →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    Safe protectedVars state expected → LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result →
    PatternFixedProgress protectedVars state result.state

private def PatternsCallFixedness (protectedVars : List TypeVarId) (fuel : Nat)
    (context : SourceInference.Context) (patterns : List Syntax.Pattern) (expected : List Ty)
    (seen : List String) (state : State) : Prop :=
  ∀ result, state.InferenceReady →
    (∀ type ∈ expected, type.VariablesBelow state.inference.next) →
    ProgramSignatureFormationValidated context.signatures →
    (∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next) →
    (∀ type ∈ expected, Safe protectedVars state type) → LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    Detail.inferMatchPatternsFlatFuel fuel context patterns expected seen state = .ok result →
    PatternFixedProgress protectedVars state result.state

set_option maxHeartbeats 2000000 in
private theorem pattern_call_private (protectedVars : List TypeVarId) (fuel : Nat)
    (context : SourceInference.Context) (pattern : Syntax.Pattern) (expected : Ty)
    (seen : List String) (state : State) :
    PatternCallFixedness protectedVars fuel context pattern expected seen state := by
  apply Detail.inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      PatternCallFixedness protectedVars fuel context pattern expected seen state)
    (motive2 := fun fuel patterns expected seen state =>
      PatternsCallFixedness protectedVars fuel context patterns expected seen state)
  case case3 =>
    intros
    unfold PatternCallFixedness at *
    intro result ready expectedBelow formation bound expectedSafe live fixed success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      rename_i unified
      exact integer_prefix_private ready bound expectedSafe live fixed (by assumption) unified
        (by assumption) rfl rfl
  case case5 =>
    intros
    unfold PatternCallFixedness at *
    intro result ready expectedBelow formation bound expectedSafe live fixed success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals
      rename_i unified
      exact integer_prefix_private ready bound expectedSafe live fixed (by assumption) unified
        (by assumption) rfl rfl
  case case10 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments contextualBranch childrenIH
    unfold PatternCallFixedness at *
    intro result ready expectedBelow formation bound expectedSafe live fixed success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | have beforeChildren := contextual_prefix_private ready expectedBelow formation expectedSafe live fixed
          (by assumption) (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 beforeChildren.1.2.2 (by assumption)
        exact beforeChildren.1.trans child
      | have beforeChildren := explicit_prefix_private ready expectedBelow formation bound expectedSafe live fixed
          (by assumption) rfl (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 beforeChildren.1.2.2 (by assumption)
        exact beforeChildren.1.trans child
  case case11 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      leadingDot qualifiers constructorName sourceArguments patternEq branchEq
      flatArguments explicitBranch childrenIH
    unfold PatternCallFixedness at *
    intro result ready expectedBelow formation bound expectedSafe live fixed success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all [pure, Pure.pure, Except.pure]
    all_goals try subst_vars
    all_goals first
      | have beforeChildren := contextual_prefix_private ready expectedBelow formation expectedSafe live fixed
          (by assumption) (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 beforeChildren.1.2.2 (by assumption)
        exact beforeChildren.1.trans child
      | have beforeChildren := explicit_prefix_private ready expectedBelow formation bound expectedSafe live fixed
          (by assumption) rfl (by assumption)
        have child := childrenIH _ _ _ beforeChildren.2.2.1
          (fun type member => (beforeChildren.2.2.2 type member).1) formation
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
          (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 beforeChildren.1.2.2 (by assumption)
        exact beforeChildren.1.trans child
  case case13 =>
    intros sourcePattern sourceExpected sourceSeen inputState sourceFuel
      elements patternEq sources argumentTypes allocatedState freshEq childrenIH
    unfold PatternCallFixedness at *
    intro result ready expectedBelow formation bound expectedSafe live fixed success
    unfold Detail.inferMatchPatternFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals simp_all
    have argumentTypesEq : (Detail.freshTypes sources.length inputState).1 = argumentTypes :=
      congrArg Prod.fst freshEq
    have allocatedStateEq : (Detail.freshTypes sources.length inputState).2 = allocatedState :=
      congrArg Prod.snd freshEq
    have beforeChildren := tuple_prefix_private (count := sources.length) (types := argumentTypes)
      (allocated := allocatedState) ready expectedBelow bound expectedSafe live fixed freshEq (by
        rw [← allocatedStateEq, ← argumentTypesEq]
        simpa only [sources] using (by assumption))
    have child := childrenIH _ _ beforeChildren.2.2.1
      (fun type member => (beforeChildren.2.2.2 type member).1) formation
      (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) beforeChildren.2.1.next_le)
      (fun type member => (beforeChildren.2.2.2 type member).2) beforeChildren.1.2.1 beforeChildren.1.2.2 (by
        rw [← argumentTypesEq]
        simpa only [sources] using (by assumption))
    exact beforeChildren.1.trans child
  case case17 =>
    intros fuel head rest expectedHead expectedTail seen state ihHead ihTail
    unfold PatternsCallFixedness
    unfold PatternCallFixedness at ihHead
    unfold PatternsCallFixedness at ihTail
    intro result ready expectedBelow formation bound expectedSafe live fixed success
    simp only [Detail.inferMatchPatternsFlatFuel] at success
    cases headRun : Detail.inferMatchPatternFlatFuel fuel context head expectedHead seen state with
    | error error => simp [headRun, bind, Except.bind] at success
    | ok inferredHead =>
      simp only [headRun, bind, Except.bind] at success
      cases tailRun : Detail.inferMatchPatternsFlatFuel fuel context rest expectedTail inferredHead.names inferredHead.state with
      | error error => simp [tailRun] at success
      | ok inferredTail =>
        simp only [tailRun] at success
        injection success with resultEq
        subst result
        have headPrivacy := ihHead inferredHead ready (expectedBelow _ List.mem_cons_self) formation
          bound (expectedSafe _ List.mem_cons_self) live fixed headRun
        have headProperties := Detail.inferMatchPatternFlatFuel_inferenceProperties ready
          (expectedBelow _ List.mem_cons_self) formation headRun
        have tailPrivacy := ihTail inferredHead inferredTail headProperties.2
          (fun type member => (expectedBelow type (List.mem_cons_of_mem _ member)).weaken headProperties.1.next_le)
          formation (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) headProperties.1.next_le)
          (fun type member => headPrivacy.1 _ (expectedSafe type (List.mem_cons_of_mem _ member)))
          headPrivacy.2.1 headPrivacy.2.2 tailRun
        exact headPrivacy.trans tailPrivacy
  all_goals
    intros
    first | unfold PatternCallFixedness at * | unfold PatternsCallFixedness at *
    intro result ready expectedBelow formation bound expectedSafe live fixed success
    first | unfold Detail.inferMatchPatternFlatFuel at success | unfold Detail.inferMatchPatternsFlatFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all
    all_goals try exact PatternFixedProgress.of_unchanged (.refl _ _) live fixed
    all_goals try exact (by simpa only using ih1 _ ready expectedBelow formation bound expectedSafe live fixed (by assumption))
    all_goals
      try
        exact PatternFixedProgress.of_unchanged (.of_substitution_eq rfl)
          (allocate_mono_private _ _ _ (safe_resolved ready expectedSafe) live) (fixed.of_substitution_eq rfl)

/-- Exact flat pattern checking preserves the substitution on protected variables. -/
theorem inferMatchPatternFlatFuel_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {pattern : Syntax.Pattern} {expected : Ty} {seen : List String} {state : State}
    {result : Detail.InferredPattern}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (expectedSafe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result) :
    FixesProtected protectedVars result.state :=
  (pattern_call_private protectedVars fuel context pattern expected seen state result
    ready expectedBelow formation bound expectedSafe live fixed accepted).2.2

/-- The public wrapper returns the same substitution as the actual flat checker. -/
theorem inferMatchPatternFuel_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {pattern : Syntax.Pattern} {expected : Ty} {state : State}
    {result : TypedMatchPattern × State}
    (ready : state.InferenceReady) (expectedBelow : expected.VariablesBelow state.inference.next)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (expectedSafe : Safe protectedVars state expected) (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    FixesProtected protectedVars result.2 := by
  unfold Detail.inferMatchPatternFuel at accepted
  cases actual : Detail.inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [actual, bind, Except.bind] at accepted
  | ok inferred =>
    simp only [actual, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact inferMatchPatternFlatFuel_fixes_protected ready expectedBelow formation bound expectedSafe live fixed actual

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableForContinuation
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableLocalLookup
/-! Actual local lookup privacy uses allocator domain coverage. It does not
require uniqueness of the stored scheme quantifier list. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables.LocalVariableFrame
open Frontend SourceInference TypeSystem

private theorem instantiated_variable_origin {state : State} (ready : state.InferenceReady)
    (scheme : Scheme) (type : Ty)
    (metavariable : TypeVarId)
    (occurs : metavariable ∈ (state.resolve
      ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type)).freeVariables) :
    (∃ source, source ∈ type.freeVariables ∧ source ∉ scheme.quantified ∧
      metavariable ∈ (state.resolve (.variable source)).freeVariables) ∨
    (state.inference.next ≤ metavariable.index ∧
      metavariable.index < (scheme.instantiateWithSubstitution state.inference.next).next) := by
  let instantiated := scheme.instantiateWithSubstitution state.inference.next
  change metavariable ∈ (state.inference.substitution.apply
    (instantiated.substitution.apply type)).freeVariables at occurs
  rw [← Substitution.compose_apply] at occurs
  obtain ⟨source, sourceMember, image⟩ := apply_variable_origin _ _ _ occurs
  rw [Substitution.compose_apply] at image
  cases found : instantiated.substitution.lookup? source with
  | none =>
    apply Or.inl
    refine ⟨source, sourceMember, ?_, ?_⟩
    · intro quantified
      exact ((Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mp found)
        (Scheme.instantiateWithSubstitution_substitution_domain_covers scheme state.inference.next quantified)
    · simpa only [State.resolve, InferState.resolve, Substitution.apply, found, Option.getD_none] using image
  | some replacement =>
    obtain ⟨fresh, replacementEq, lower, upper⟩ :=
      Scheme.instantiateWithSubstitution_substitution_range_fresh scheme
        state.inference.next (Substitution.lookup?_eq_some_mem found)
    have same : metavariable = fresh := by
      change metavariable ∈ (state.resolve (instantiated.substitution.apply (.variable source))).freeVariables at image
      rw [Substitution.apply, found, Option.getD_some, replacementEq,
        resolve_fresh_variable ready fresh lower] at image
      simpa only [Ty.freeVariables, List.mem_singleton] using image
    subst metavariable
    exact Or.inr ⟨lower, upper⟩

private theorem safe_instantiated_type {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (scheme : Scheme) (type : Ty)
    (sourceSafe : ∀ metavariable ∈ type.freeVariables,
      metavariable ∉ scheme.quantified → Safe protectedVars state (.variable metavariable)) :
    Safe protectedVars state
      ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type) := by
  intro metavariable member protectedMember
  rcases instantiated_variable_origin ready scheme type metavariable member with old | fresh
  · obtain ⟨source, sourceMember, outside, image⟩ := old
    exact sourceSafe source sourceMember outside metavariable image protectedMember
  · exact (Nat.not_lt.mpr fresh.1) (bound metavariable protectedMember)

private theorem instantiated_predicate_safe {protectedVars : List TypeVarId} {state : State}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (scheme : Scheme) (predicate : ProgramPredicate)
    (sourceSafe : ∀ type ∈ predicate.subject :: predicate.arguments,
      ∀ metavariable ∈ type.freeVariables,
        metavariable ∉ scheme.quantified → Safe protectedVars state (.variable metavariable)) :
    PredicateSafe protectedVars (instantiatedState state scheme)
      (Detail.applyPredicate (instantiatedState state scheme)
        (TypedTraitResolution.applySubstitution
          (scheme.instantiateWithSubstitution state.inference.next).substitution predicate)) := by
  have each (type : Ty) (member : type ∈ predicate.subject :: predicate.arguments) :
      Safe protectedVars (instantiatedState state scheme)
        (state.resolve ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply type)) :=
    instantiate_transport _ _ _ _ (safe_resolved ready
      (safe_instantiated_type ready bound scheme type (sourceSafe type member)))
  intro type member
  change type ∈ state.resolve ((scheme.instantiateWithSubstitution state.inference.next).substitution.apply predicate.subject) ::
    (predicate.arguments.map (scheme.instantiateWithSubstitution state.inference.next).substitution.apply).map state.resolve at member
  rcases List.mem_cons.mp member with rfl | argument
  · exact each _ (by simp)
  · obtain ⟨instantiated, instMember, rfl⟩ := List.mem_map.mp argument
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp instMember
    exact each original (List.mem_cons.mpr (.inr originalMember))

private theorem local_instantiation_safe {protectedVars : List TypeVarId} {state : State}
    {binder : TypedBinder} (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (safe : BinderSafe protectedVars state binder) :
    SafeTransport protectedVars state (instantiatedState state binder.scheme) ∧
    Safe protectedVars (instantiatedState state binder.scheme)
      ((instantiatedState state binder.scheme).resolve
        (binder.scheme.instantiateWithSubstitution state.inference.next).body) ∧
    ∀ predicate ∈ binder.schemeRequirements.map (fun requirement =>
      Detail.applyPredicate (instantiatedState state binder.scheme)
        (TypedTraitResolution.applySubstitution
          (binder.scheme.instantiateWithSubstitution state.inference.next).substitution requirement.predicate)),
      PredicateSafe protectedVars (instantiatedState state binder.scheme) predicate := by
  refine ⟨instantiate_transport _ _ _, ?_, ?_⟩
  · apply instantiate_transport protectedVars state binder.scheme
    apply safe_resolved ready
    apply safe_instantiated_type ready bound binder.scheme binder.scheme.body
    intro v member outside
    exact safe.body v (List.mem_filter.mpr ⟨member, by simp [outside]⟩)
  · intro predicate member
    obtain ⟨requirement, requirementMember, rfl⟩ := List.mem_map.mp member
    exact instantiated_predicate_safe ready bound binder.scheme requirement.predicate
      (safe.requirements requirement requirementMember)

private theorem lookup_instantiation_safe {protectedVars : List TypeVarId} {state : State}
    {name : String} {binder : TypedBinder} (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (safe : LiveBindersSafe protectedVars state)
    (found : state.lookupBinder? name = some binder) :
    SafeTransport protectedVars state (instantiatedState state binder.scheme) ∧
    Safe protectedVars (instantiatedState state binder.scheme)
      ((instantiatedState state binder.scheme).resolve
        (binder.scheme.instantiateWithSubstitution state.inference.next).body) ∧
    ∀ predicate ∈ binder.schemeRequirements.map (fun requirement =>
      Detail.applyPredicate (instantiatedState state binder.scheme)
        (TypedTraitResolution.applySubstitution
          (binder.scheme.instantiateWithSubstitution state.inference.next).substitution requirement.predicate)),
      PredicateSafe protectedVars (instantiatedState state binder.scheme) predicate :=
  local_instantiation_safe ready bound
    (safe binder (State.lookupBinder?_eq_some_facts found).1)

theorem inferExprFuel_local_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {expected : Option Ty}
    {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result)
    (ready : initial.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < initial.inference.next)
    (live : LiveBindersSafe protectedVars initial)
    (fixed : FixesProtected protectedVars initial)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars initial type) :
    FixesProtected protectedVars result.2 := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have readyAllocated : allocated.InferenceReady := by
    rw [allocatedEq]
    exact ⟨ready.solved, ready.bindersBelow⟩
  have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
    intro metavariable member
    rw [allocatedEq]
    exact bound metavariable member
  have allocationTransport : SafeTransport protectedVars initial allocated := by
    apply SafeTransport.of_substitution_eq
    rw [allocatedEq]
    rfl
  have liveAllocated : LiveBindersSafe protectedVars allocated := by
    apply live.transport _ allocationTransport
    rw [allocatedEq]
    rfl
  have privacy := lookup_instantiation_safe readyAllocated boundAllocated liveAllocated found
  let advanced := instantiatedState allocated binder.scheme
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution
        (binder.scheme.instantiateWithSubstitution allocated.inference.next).substitution requirement.predicate)
  let recorded := (advanced.addRequirementsWithIds predicates).2
  have sameInference : recorded.inference = advanced.inference := requirementBatch_inference _ _
  have beforeFit : SafeTransport protectedVars initial recorded := by
    apply SafeTransport.of_substitution_eq
    rw [sameInference]
    change allocated.inference.substitution = initial.inference.substitution
    rw [allocatedEq]
    rfl
  have typeSafe : Safe protectedVars recorded (advanced.resolve
      (binder.scheme.instantiateWithSubstitution allocated.inference.next).body) := by
    simpa only [Safe, State.resolve, InferState.resolve, sameInference] using privacy.2.1
  have recordAccepted := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted
  change Detail.recordExpressionWithExpected context expression id
    (advanced.resolve (binder.scheme.instantiateWithSubstitution allocated.inference.next).body)
    (.reference name.value (.local binder.id)) (advanced.addRequirementsWithIds predicates).1 expected
    recorded (some allocated.inference.next) = .ok result at recordAccepted
  have recordedFixed : FixesProtected protectedVars recorded := by
    apply fixed.of_substitution_eq
    rw [sameInference]
    change allocated.inference.substitution = initial.inference.substitution
    rw [allocatedEq]
    rfl
  exact recordExpressionWithExpected_fixes_protected recordedFixed typeSafe
    (fun type member => beforeFit type (expectedSafe type member)) recordAccepted

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables.LocalVariableFrame
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableMatchContinuation
/-! A match arm follows its real pattern and body calls, restores the saved
lexical scope, and passes the reached state to the remaining arms. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem inferMatchCasesFuel_cons_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {scrutineeType expectedReturn : Ty} {outerScope : LexicalScope}
    {arm : Syntax.MatchCase} {rest : List Syntax.MatchCase} {initial : State}
    (bodyIH : ∀ state, InferStatementsFuelFixedness protectedVars fuel context
      arm.value.body.value expectedReturn state)
    (tailIH : ∀ body : BlockResult, InferMatchCasesFuelFixedness protectedVars fuel
      context scrutineeType expectedReturn outerScope rest
      (body.state.restoreLexicalScope outerScope)) :
    InferMatchCasesFuelFixedness protectedVars (fuel + 1) context scrutineeType
      expectedReturn outerScope (arm :: rest) initial := by
  intro ready wellFormed bound live fixed catalog validated canonical scrutineeBelow
    scrutineeSafe returnBelow returnSafe scopeEq result accepted
  subst outerScope
  unfold inferMatchCasesFuel at accepted
  simp only [bind, Except.bind] at accepted
  cases patternRun : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial with
  | error error => simp [patternRun] at accepted
  | ok patternPair =>
    rcases patternPair with ⟨pattern, patternState⟩
    simp only [patternRun] at accepted
    cases bodyRun : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState with
    | error error => simp [bodyRun] at accepted
    | ok body =>
      simp only [bodyRun] at accepted
      cases tailRun : inferMatchCasesFuel fuel context scrutineeType expectedReturn initial.lexicalScope
          rest (body.state.restoreLexicalScope initial.lexicalScope) with
      | error error => simp [tailRun] at accepted
      | ok tail =>
        simp only [tailRun, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        subst result
        have patternProperties := inferMatchPatternFuel_inferenceProperties ready
          scrutineeBelow validated patternRun
        have patternPrivacy := inferMatchPatternFuel_private ready scrutineeBelow validated
          bound scrutineeSafe live patternRun
        have patternFixed := inferMatchPatternFuel_fixes_protected ready scrutineeBelow validated
          bound scrutineeSafe live fixed patternRun
        have patternWellFormed := (inferMatchPatternFuel_direct_progress patternRun).wellFormed wellFormed
        have returnAtPattern := returnBelow.weaken patternProperties.1.next_le
        have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1
          validated canonical returnAtPattern bodyRun
        have bodyPrivacy := inferStatementsFuel_private protectedVars fuel context arm.value.body.value expectedReturn patternState patternProperties.2.1 patternWellFormed
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) patternProperties.1.next_le)
          patternPrivacy.2.1 catalog validated canonical returnAtPattern
          (patternPrivacy.1 _ returnSafe) body bodyRun
        have bodyFixed := bodyIH patternState patternProperties.2.1 patternWellFormed
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) patternProperties.1.next_le)
          patternPrivacy.2.1 patternFixed catalog validated canonical returnAtPattern
          (patternPrivacy.1 _ returnSafe) body bodyRun
        have throughBody := patternProperties.1.trans bodyProperties.1
        have privacyThroughBody := patternPrivacy.1.trans bodyPrivacy.1
        have restoredProperties := State.restoreLexicalScope_inferenceProperties ready throughBody
        let restored := body.state.restoreLexicalScope initial.lexicalScope
        have restoredPrivacy : SafeTransport protectedVars body.state restored := .of_substitution_eq rfl
        have privacyThroughRestored := privacyThroughBody.trans restoredPrivacy
        have restoredLive : LiveBindersSafe protectedVars restored := live.restore privacyThroughBody
        have restoredWellFormed : restored.RequirementsWellFormed :=
          State.restoreLexicalScope_preserves_requirementsWellFormed body.state initial.lexicalScope
            ((inferStatementsFuel_direct_progress bodyRun).wellFormed patternWellFormed)
        have tailFixed := tailIH body restoredProperties.2 restoredWellFormed
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) restoredProperties.1.next_le)
          restoredLive (bodyFixed.of_substitution_eq rfl) catalog validated canonical
          (scrutineeBelow.weaken restoredProperties.1.next_le)
          (privacyThroughRestored _ scrutineeSafe)
          (returnBelow.weaken restoredProperties.1.next_le)
          (privacyThroughRestored _ returnSafe) (by simp) tail tailRun
        exact tailFixed

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableMatchStatement
/-! Actual match statement inference preserves fixed protected variables through ordered
scrutinees, all arms, optional default inference and actual scope restoration. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

private def finishMatch (fuel : Nat) (context : SourceInference.Context)
    (statement : Syntax.Statement) (id : StatementId) (hidden : Resolved.LocalId)
    (scrutinee : InferredExpression) (arms : Syntax.Located Syntax.MatchArmsValue)
    (expectedReturn : Ty) (state : State) : Except Error StatementResult := do
  let outerScope := state.lexicalScope
  let checked ← inferMatchCasesFuel fuel context scrutinee.type expectedReturn outerScope arms.value.cases state
  let (defaultBody,state) ← match arms.value.defaultBody with
    | none => pure (none,checked.state)
    | some body => do
      let inferred ← inferStatementsFuel fuel context body.value expectedReturn checked.state
      pure (some (inferred.statements,inferred.sawReturn),inferred.state.restoreLexicalScope outerScope)
  let exhaustive := checked.hasWildcard || defaultBody.isSome ||
    exhaustsNominalConstructors context state scrutinee.type checked.cases
  if !exhaustive then throw (.nonExhaustiveMatch statement.span) else
    let requirements := checked.cases.flatMap fun arm => arm.pattern.requirements
    let defaultStatements := defaultBody.map (·.1)
    let defaultReturns := defaultBody.map (·.2) |>.getD true
    let sawReturn := checked.allReturn && defaultReturns
    let type := if sawReturn then state.resolve expectedReturn else .unit
    let state := state.recordNode (.statement {
      id := id
      span := statement.span
      type := type
      form := .matchWith {
        scrutinee := scrutinee.id
        hiddenScrutinee := hidden
        cases := checked.cases
        defaultBody := defaultStatements
        requirements := requirements
      }
    })
    pure {
      id := id
      type := type
      hasValue := sawReturn
      sawReturn := sawReturn
      state := state
    }


private theorem finishMatch_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {id : StatementId} {hidden : Resolved.LocalId}
    {scrutinee : InferredExpression} {arms : Syntax.Located Syntax.MatchArmsValue}
    {expectedReturn : Ty} {state : State}
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (bound : ∀ v ∈ protectedVars, v.index < state.inference.next)
    (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (scrutineeBelow : scrutinee.type.VariablesBelow state.inference.next)
    (scrutineeSafe : Safe protectedVars state scrutinee.type)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (returnSafe : Safe protectedVars state expectedReturn)
    (casesIH : InferMatchCasesFuelFixedness protectedVars fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelFixedness protectedVars fuel context body.value expectedReturn checked.state)
    {result : StatementResult}
    (success : finishMatch fuel context statement id hidden scrutinee arms expectedReturn state = .ok result) :
    FixesProtected protectedVars result.state := by
  unfold finishMatch at success
  simp only [bind,Except.bind] at success
  cases casesRun : inferMatchCasesFuel fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state with
  | error error => simp [casesRun] at success
  | ok checked =>
    simp only [casesRun] at success
    have casesProperties := inferMatchCasesFuel_inferenceProperties ready validated canonical scrutineeBelow returnBelow rfl casesRun
    have casesPrivacy := inferMatchCasesFuel_private protectedVars fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state ready wellFormed bound live catalog validated canonical
      scrutineeBelow scrutineeSafe returnBelow returnSafe rfl checked casesRun
    have casesFixed := casesIH ready wellFormed bound live fixed catalog validated canonical
      scrutineeBelow scrutineeSafe returnBelow returnSafe rfl checked casesRun
    cases defaultEq : arms.value.defaultBody with
    | none =>
      simp only [defaultEq,pure,Pure.pure,Except.pure] at success
      split at success
      · cases success
      · injection success with resultEq
        subst result
        exact casesFixed.of_substitution_eq rfl
    | some body =>
      cases bodyRun : inferStatementsFuel fuel context body.value expectedReturn checked.state with
      | error error => simp [defaultEq,bodyRun] at success
      | ok checkedBody =>
        simp only [defaultEq,bodyRun,pure,Pure.pure,Except.pure] at success
        have bodyProperties := inferStatementsFuel_inferenceProperties casesProperties.2.1 validated canonical
          (returnBelow.weaken casesProperties.1.next_le) bodyRun
        have bodyFixed := bodyIH checked body casesProperties.2.1
          ((inferMatchCasesFuel_direct_progress casesRun).wellFormed wellFormed)
          (fun v member => Nat.lt_of_lt_of_le (bound v member) casesProperties.1.next_le)
          casesPrivacy.2.1 casesFixed catalog validated canonical (returnBelow.weaken casesProperties.1.next_le)
          (casesPrivacy.1 _ returnSafe) checkedBody bodyRun
        split at success
        · cases success
        · injection success with resultEq
          subst result
          exact bodyFixed.of_substitution_eq rfl

theorem inferStatementFuel_match_single_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.Located Syntax.MatchArmsValue} {source : Syntax.Expr} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .matchWith scrutinees arms)
    (single : scrutinees.elements.toList = [source])
    (casesIH : ∀ (scrutinee : InferredExpression) (state : State),
      InferMatchCasesFuelFixedness protectedVars fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelFixedness protectedVars fuel context body.value expectedReturn checked.state)
    (sourceIH : InferExprFuelFixedness protectedVars fuel context source none initial.allocateStatementId.2) :
    InferStatementFuelFixedness protectedVars (fuel+1) context statement expectedReturn initial := by
  intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
  let allocated := initial.allocateStatementId.2
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  unfold inferStatementFuel at success
  simp only [form,single,bind,Except.bind] at success
  cases sourceRun : inferExprFuel fuel context source none allocated with
  | error error => simp [allocated,sourceRun] at success
  | ok pair =>
    rcases pair with ⟨scrutinee,sourceState⟩
    simp only [allocated,sourceRun] at success
    have sourceProperties := inferExprFuel_inferenceProperties allocatedReady validated canonical (by simp) sourceRun
    have sourcePrivacy := inferExprFuel_private protectedVars fuel context source none allocated allocatedReady wellFormed bound (live.transport rfl allocatedPrivacy)
      catalog validated canonical (by simp) (by simp) (scrutinee,sourceState) sourceRun
    have sourceFixed := sourceIH allocatedReady wellFormed bound (live.transport rfl allocatedPrivacy)
      (fixed.of_substitution_eq rfl) catalog validated canonical (by simp) (by simp) (scrutinee,sourceState) sourceRun
    let hiddenState := sourceState.allocateHiddenLocal.2
    have hiddenReady : hiddenState.InferenceReady := State.InferenceReady.allocateHiddenLocal sourceProperties.2.1
    have hiddenPrivacy : SafeTransport protectedVars sourceState hiddenState := .of_substitution_eq rfl
    have finishRun : finishMatch fuel context statement initial.allocateStatementId.1 sourceState.allocateHiddenLocal.1
        scrutinee arms expectedReturn hiddenState = .ok result := success
    have finished := finishMatch_fixes_protected hiddenReady
      ((inferExprFuel_direct_progress sourceRun).wellFormed wellFormed)
      (fun v member => Nat.lt_of_lt_of_le (bound v member) sourceProperties.1.next_le)
      (sourcePrivacy.2.2.1.transport rfl hiddenPrivacy) (sourceFixed.of_substitution_eq rfl) catalog validated canonical sourceProperties.2.2
      (hiddenPrivacy _ sourcePrivacy.2.1) (returnBelow.weaken sourceProperties.1.next_le)
      (sourcePrivacy.1 _ returnSafe) (casesIH scrutinee hiddenState) bodyIH finishRun
    exact finished


theorem inferStatementFuel_match_many_fixes_protected
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.Located Syntax.MatchArmsValue} {expectedReturn : Ty} {initial : State}
    (form : statement.value = .matchWith scrutinees arms)
    (notSingleton : ∀ source, scrutinees.elements.toList = [source] → False)
    (casesIH : ∀ (scrutinee : InferredExpression) (state : State),
      InferMatchCasesFuelFixedness protectedVars fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state)
    (bodyIH : ∀ (checked : MatchCasesResult) (body : Syntax.Located (List Syntax.Statement)),
      InferStatementsFuelFixedness protectedVars fuel context body.value expectedReturn checked.state)
    (sourcesIH : InferExprsFuelFixedness protectedVars fuel context scrutinees.elements.toList initial.allocateStatementId.2) :
    InferStatementFuelFixedness protectedVars (fuel+1) context statement expectedReturn initial := by
  intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
  let allocated := initial.allocateStatementId.2
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateStatementId ready
  have allocatedPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  unfold inferStatementFuel at success
  simp only [form] at success
  simp only [bind,Except.bind] at success
  cases sourcesRun : inferExprsFuel fuel context scrutinees.elements.toList initial.allocateStatementId.2 with
  | error error => simp [sourcesRun] at success
  | ok pair =>
    rcases pair with ⟨elements,elementState⟩
    simp only [sourcesRun,pure,Pure.pure,Except.pure] at success
    have properties := inferExprsFuel_inferenceProperties allocatedReady validated canonical sourcesRun
    have privacy := inferExprsFuel_private protectedVars fuel context scrutinees.elements.toList allocated allocatedReady wellFormed bound (live.transport rfl allocatedPrivacy)
      catalog validated canonical (elements,elementState) sourcesRun
    have sourcesFixed := sourcesIH allocatedReady wellFormed bound (live.transport rfl allocatedPrivacy)
      (fixed.of_substitution_eq rfl) catalog validated canonical (elements,elementState) sourcesRun
    let tuple : InferredExpression := {id := elementState.allocateExpressionId.1,type := Ty.productMany (elements.map (·.type))}
    let tupleState := elementState.allocateExpressionId.2.recordNode (.expression {
      id := tuple.id
      span := statement.span
      type := tuple.type
      form := .tuple (elements.map (·.id)) })
    have tupleReady : tupleState.InferenceReady := State.InferenceReady.recordNode _
      (State.InferenceReady.allocateExpressionId properties.2.1)
    have tuplePrivacy : SafeTransport protectedVars elementState tupleState := .of_substitution_eq rfl
    have tupleBelow : tuple.type.VariablesBelow tupleState.inference.next := by
      apply Ty.variablesBelow_productMany
      intro type member
      obtain ⟨element,elementMember,rfl⟩ := List.mem_map.mp member
      exact properties.2.2 element elementMember
    have tupleSafe : Safe protectedVars tupleState tuple.type := by
      apply safe_productMany
      intro type member
      obtain ⟨element,elementMember,rfl⟩ := List.mem_map.mp member
      exact tuplePrivacy _ (privacy.2.1 element elementMember)
    let hiddenState := tupleState.allocateHiddenLocal.2
    have hiddenReady : hiddenState.InferenceReady := State.InferenceReady.allocateHiddenLocal tupleReady
    have hiddenPrivacy : SafeTransport protectedVars tupleState hiddenState := .of_substitution_eq rfl
    have finishRun : finishMatch fuel context statement initial.allocateStatementId.1 tupleState.allocateHiddenLocal.1
        tuple arms expectedReturn hiddenState = .ok result := success
    have finished := finishMatch_fixes_protected hiddenReady
      ((inferExprsFuel_direct_progress sourcesRun).wellFormed wellFormed)
      (fun v member => Nat.lt_of_lt_of_le (bound v member) properties.1.next_le)
      ((privacy.2.2.1.transport rfl tuplePrivacy).transport rfl hiddenPrivacy) (sourcesFixed.of_substitution_eq rfl) catalog validated canonical tupleBelow
      (hiddenPrivacy _ tupleSafe) (returnBelow.weaken properties.1.next_le)
      (privacy.1 _ returnSafe) (casesIH tuple hiddenState) bodyIH finishRun
    exact finished

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProtectedVariableOperators
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private abbrev finishOperator (context : SourceInference.Context) (dispatch : Detail.OperatorDispatch)
    (operand builtin builtinResult resultType : Ty) (parameterTypes : List Ty)
    (hasOpenLiteralOperand : Bool) (state : State) : Except Error Detail.OperatorInferenceResult :=
  if operand = builtin then
    pure {type := builtinResult, requirements := [], state}
  else
    match dispatch with
    | .function name =>
      if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand builtin operand ||
          Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand builtin operand then
        pure {type := resultType, requirements := [], state}
      else throw (.unknownVariable name)
    | .traitMethod traitName methodName => do
      match ← Detail.operatorTrait? context traitName with
      | some trait =>
        let predicates ← Detail.operatorTraitPredicates context trait methodName operand parameterTypes [resultType]
        let (requirements,state) := state.addRequirementsWithIds predicates
        pure {type := resultType, requirements, state}
      | none =>
        if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand builtin operand ||
            Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand builtin operand then
          pure {type := resultType, requirements := [], state}
        else throw (.operatorNotSupported traitName operand)

private abbrev finishUnary (context : SourceInference.Context) (operator : Syntax.UnaryOp)
    (operandType : Ty) (hasOpenLiteralOperand : Bool) (state : State) :=
  let operand := state.resolve operandType
  let builtin := match operator with | .logicalNot => Ty.bool | .bitNot => Ty.word
  finishOperator context (Detail.unaryOperatorDispatch operator) operand builtin builtin
    (if operator == Syntax.UnaryOp.logicalNot then .bool else operand) [operand] hasOpenLiteralOperand state

private abbrev finishBinary (context : SourceInference.Context) (operator : Syntax.BinaryOp)
    (operandType : Ty) (hasOpenLiteralOperand : Bool) (state : State) :
    Except SourceInference.Error Detail.OperatorInferenceResult :=
  let operand := state.resolve operandType
  if Detail.fixedWordOperator operator operand then
    pure {
      type := if Detail.binaryResultIsBool operator then .bool else operand
      requirements := []
      state
    }
  else
    let builtin := Detail.binaryBuiltinType operator
    finishOperator context (Detail.binaryOperatorDispatch operator) operand builtin
      (if Detail.binaryResultIsBool operator then .bool else builtin)
      (if Detail.binaryResultIsBool operator then .bool else operand)
      [operand,operand] hasOpenLiteralOperand state

private theorem finishOperator_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {dispatch : Detail.OperatorDispatch}
    {operand builtin builtinResult resultType : Ty} {parameterTypes : List Ty}
    {hasOpenLiteralOperand : Bool} {state : State} {result : Detail.OperatorInferenceResult}
    (fixed : FixesProtected protectedVars state)
    (accepted : finishOperator context dispatch operand builtin builtinResult resultType
      parameterTypes hasOpenLiteralOperand state = .ok result) :
    FixesProtected protectedVars result.state := by
  unfold finishOperator at accepted
  split at accepted
  · cases Except.ok.inj accepted
    exact fixed
  · cases dispatch with
    | function name =>
      simp only at accepted
      split at accepted
      · cases Except.ok.inj accepted
        exact fixed
      · cases accepted
    | traitMethod traitName methodName =>
      cases traitResult : Detail.operatorTrait? context traitName with
      | error error => simp [traitResult, bind, Except.bind] at accepted
      | ok option =>
        cases option with
        | none =>
          simp only [traitResult, bind, Except.bind] at accepted
          split at accepted
          · cases Except.ok.inj accepted
            exact fixed
          · cases accepted
        | some trait =>
          simp only [traitResult, bind, Except.bind] at accepted
          cases predicatesResult : Detail.operatorTraitPredicates context trait methodName operand parameterTypes [resultType] with
          | error error => simp [predicatesResult] at accepted
          | ok predicates =>
            simp only [predicatesResult, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
            cases accepted
            exact fixed.of_substitution_eq (congrArg InferState.substitution (requirementBatch_inference _ _))

/-- The binary tail: the fixed-width integer types' builtin operators keep the
state, and every other operator goes through `finishOperator`. -/
private theorem finishBinary_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.BinaryOp} {operandType : Ty}
    {hasOpenLiteralOperand : Bool} {state : State} {result : Detail.OperatorInferenceResult}
    (fixed : FixesProtected protectedVars state)
    (accepted : finishBinary context operator operandType hasOpenLiteralOperand state = .ok result) :
    FixesProtected protectedVars result.state := by
  simp only [finishBinary] at accepted
  split at accepted
  · cases Except.ok.inj accepted
    exact fixed
  · exact finishOperator_fixes_protected fixed accepted

theorem inferUnaryOperator_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : Detail.OperatorInferenceResult}
    (ready : state.InferenceReady)
    (operandSafe : Safe protectedVars state operandType)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    FixesProtected protectedVars result.state := by
  let openLiteral := Detail.isOpenIntegerLiteralTarget state integerLiterals operandType
  unfold Detail.inferUnaryOperator at accepted
  cases expected with
  | none =>
    simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    exact finishOperator_fixes_protected fixed (show finishUnary context operator operandType openLiteral state = .ok result from accepted)
  | some expectedType =>
    have expectedSafe := expectedSafe expectedType (by simp)
    cases skip : (operator == Syntax.UnaryOp.logicalNot ||
        (state.resolve operandType).freeVariables.isEmpty || !openLiteral) with
    | true =>
      simp only [openLiteral, skip, if_true, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      exact finishOperator_fixes_protected fixed (show finishUnary context operator operandType openLiteral state = .ok result from accepted)
    | false =>
      simp only [openLiteral, skip, Bool.false_eq_true, if_false] at accepted
      cases unified : Detail.unify state (state.resolve operandType) expectedType with
      | error error => simp [unified, bind, Except.bind] at accepted
      | ok fitted =>
        simp only [unified, bind, Except.bind] at accepted
        have fittedFixed := unify_fixes_protected fixed (safe_resolved ready operandSafe) expectedSafe unified
        exact finishOperator_fixes_protected fittedFixed (show finishUnary context operator operandType openLiteral fitted = .ok result from accepted)

theorem inferBinaryOperator_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : Detail.OperatorInferenceResult}
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (leftSafe : Safe protectedVars state left) (rightSafe : Safe protectedVars state right)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    FixesProtected protectedVars result.state := by
  let openLiteral := Detail.isOpenIntegerLiteralTarget state integerLiterals left ||
    Detail.isOpenIntegerLiteralTarget state integerLiterals right
  by_cases shift : Detail.isShiftOperator operator = true
  · obtain ⟨_, _, valued, valueResult, amountResult⟩ :=
      Detail.inferBinaryOperator_shift_result shift accepted
    have wordSafe : ∀ any : State, Safe protectedVars any .word := by
      intro any metavariable member
      simp [Frontend.SourceInference.State.resolve, TypeSystem.InferState.resolve, TypeSystem.Ty.word,
        TypeSystem.Ty.freeVariables] at member
    have valuedFixed := unify_fixes_protected fixed leftSafe (wordSafe state) valueResult
    have valuedPrivacy := ProtectedVariables.unify leftSafe (wordSafe state) valueResult
    exact unify_fixes_protected valuedFixed (valuedPrivacy _ rightSafe) (wordSafe valued)
      amountResult
  by_cases unchecked : Detail.isUncheckedOperator operator = true
  · obtain ⟨unifiedState, prepared, unified, prepare, tailSuccess⟩ :=
      Detail.inferBinaryOperator_unchecked_result unchecked accepted
    have unifiedReady := Detail.unify_preserves_inferenceReady ready leftBelow rightBelow unified
    have unifiedPrivacy := ProtectedVariables.unify leftSafe rightSafe unified
    have operandSafe := unifiedPrivacy _ leftSafe
    have unifiedFixed := unify_fixes_protected fixed leftSafe rightSafe unified
    rcases prepare with preparedEq | wordResult
    · rw [preparedEq] at tailSuccess
      exact finishBinary_fixes_protected unifiedFixed
        (show finishBinary context operator left false unifiedState = .ok result from tailSuccess)
    · have wordSafe : Safe protectedVars unifiedState .word := by
        intro metavariable member
        simp [Frontend.SourceInference.State.resolve, TypeSystem.InferState.resolve, TypeSystem.Ty.word,
          TypeSystem.Ty.freeVariables] at member
      have preparedFixed := unify_fixes_protected unifiedFixed (safe_resolved unifiedReady operandSafe)
        wordSafe wordResult
      exact finishBinary_fixes_protected preparedFixed
        (show finishBinary context operator left false prepared = .ok result from tailSuccess)
  unfold Detail.inferBinaryOperator Detail.binaryOperatorTail at accepted
  rw [if_neg shift, if_neg unchecked] at accepted
  cases unified : Detail.unify state left right with
  | error error => simp [unified, bind, Except.bind] at accepted
  | ok unifiedState =>
    simp only [unified, bind, Except.bind] at accepted
    have unifiedReady := Detail.unify_preserves_inferenceReady ready leftBelow rightBelow unified
    have unifiedPrivacy := ProtectedVariables.unify leftSafe rightSafe unified
    have operandSafe := unifiedPrivacy _ leftSafe
    have unifiedFixed := unify_fixes_protected fixed leftSafe rightSafe unified
    cases expected with
    | none =>
      simp only [pure, Pure.pure, Except.pure] at accepted
      exact finishBinary_fixes_protected unifiedFixed (show finishBinary context operator left openLiteral unifiedState = .ok result from accepted)
    | some expectedType =>
      have expectedSafe := unifiedPrivacy _ (expectedSafe expectedType (by simp))
      cases skip : (Detail.binaryResultIsBool operator ||
          (unifiedState.resolve left).freeVariables.isEmpty || !openLiteral) with
      | true =>
        simp only [openLiteral, skip, if_true, pure, Pure.pure, Except.pure] at accepted
        exact finishBinary_fixes_protected unifiedFixed (show finishBinary context operator left openLiteral unifiedState = .ok result from accepted)
      | false =>
        simp only [openLiteral, skip, Bool.false_eq_true, if_false] at accepted
        cases fitted : Detail.unify unifiedState (unifiedState.resolve left) expectedType with
        | error error => simp [fitted] at accepted
        | ok fittedState =>
          simp only [fitted] at accepted
          have fittedFixed := unify_fixes_protected unifiedFixed (safe_resolved unifiedReady operandSafe) expectedSafe fitted
          exact finishBinary_fixes_protected fittedFixed (show finishBinary context operator left openLiteral fittedState = .ok result from accepted)

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end
