import Solcore.SourceSemantics.SourceInferenceExpressionLedgerInvariant
import Solcore.SourceSemantics.SourceInferenceExpressionCallDispatchSoundness

/-! Requirement and local-template ledgers follow every actual expression
branch. Recursive premises apply only to the computations returned by that
branch, including nested lambda statements and constructor payloads. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false

namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

private theorem lambdaPrefixLedger
    {context : Frontend.SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty}
    {initial final : State} {resultType : Ty} {pending : List RequirementId}
    (tracked : RecursiveLedgerInvariant initial pending)
    (facts : Detail.LambdaPrefixFacts context expected annotation types
      initial resultType final) : RecursiveLedgerInvariant final pending := by
  cases facts with
  | noExpectedPartsAnnotated => exact tracked
  | noExpectedPartsFresh _ _ fresh =>
    have stateEq : initial.fresh.2 = final := congrArg Prod.snd fresh
    rw [← stateEq]
    exact tracked.fresh
  | expectedPartsAnnotated _ unified => exact tracked.unify unified
  | expectedPartsInferred _ unified => exact tracked.unify unified

/-- One expression-fuel step preserves the actual ledger and any surrounding
pending template suffix. -/
theorem inferExprFuelLedgerPreservation_step
    {fuel : Nat}
    (expressionIH : InferExprFuelLedgerPreservation fuel)
    (expressionsIH : InferExprsFuelLedgerPreservation fuel)
    (statementsIH : InferStatementsFuelLedgerPreservation fuel) :
    InferExprFuelLedgerPreservation (fuel + 1) := by
  intro context expression expected initial final inferred pending accepted tracked
  have allocatedTracked := tracked.allocateExpressionId
  generalize allocation : initial.allocateExpressionId = allocatedPair at *
  rcases allocatedPair with ⟨id, allocated⟩
  have constructorIH : InferConstructorApplicationFuelLedgerPreservation fuel := inferConstructorApplicationFuelLedgerPreservation_of_arguments
    (inferConstructorArgumentsFuelLedgerPreservation_of_expr expressionIH)
  cases form : expression.value with
  | literal literal =>
    cases literalForm : literal.value with
    | string _ => simp [Detail.inferExprFuel, allocation, form, literalForm] at accepted
    | decimal spelling | hexadecimal spelling =>
      cases decoded : numericLiteralValue? literal.value with
      | none =>
        unfold Detail.inferExprFuel at accepted
        simp only [allocation, form] at accepted
        rw [literalForm] at decoded
        simp [literalForm, decoded, bind, Except.bind] at accepted
      | some rawValue =>
        obtain ⟨recorded, _, _⟩ := Detail.inferExprFuel_success_numericLiteral_record
          form rfl decoded allocation accepted
        exact ((allocatedTracked.fresh.addRequirementWithId _).withIntegerLiterals)
          |>.recordExpressionWithExpected recorded
  | identifier name =>
    cases found : allocated.lookupBinder? name.value with
    | some binder =>
      have recorded := Detail.inferExprFuel_success_localIdentifier_record
        form allocation found accepted
      exact ((allocatedTracked.withInference).addRequirementsWithIds _)
        |>.recordExpressionWithExpected recorded
    | none =>
      cases boolean : (name.value == "true" || name.value == "false") with
      | true =>
        exact allocatedTracked.recordExpressionWithExpected
          (Detail.inferExprFuel_success_builtinBooleanIdentifier_record
            form allocation found boolean accepted)
      | false =>
        cases functions : Detail.functionsNamed context name.value with
        | error error =>
          simp [Detail.inferExprFuel, allocation, form, found, boolean,
            functions, bind, Except.bind] at accepted
        | ok candidates =>
          cases candidates with
          | nil =>
            cases builtin : builtinFunctionNamed? name.value with
            | none =>
              simp [Detail.inferExprFuel, allocation, form, found, boolean,
                functions, builtin, bind, Except.bind] at accepted
            | some function =>
              exact allocatedTracked.recordExpressionWithExpected
                (Detail.inferExprFuel_success_builtinFunctionIdentifier_record
                  form allocation found boolean functions builtin accepted)
          | cons signature rest =>
            cases rest with
            | nil =>
              have recorded := Detail.inferExprFuel_success_declarationIdentifier_record
                form allocation found boolean functions accepted
              exact ((allocatedTracked.withInference).addRequirementsWithIds _)
                |>.recordExpressionWithExpected recorded
            | cons _ _ =>
              simp [Detail.inferExprFuel, allocation, form, found, boolean,
                functions, bind, Except.bind] at accepted
  | group inner =>
    obtain ⟨_, _, child, recorded⟩ := Detail.inferExprFuel_success_group_facts
      form allocation accepted
    exact (expressionIH child allocatedTracked).recordExpressionWithExpected recorded
  | tuple elements =>
    obtain ⟨_, _, children, recorded⟩ := Detail.inferExprFuel_success_tuple_facts
      form allocation accepted
    exact (expressionsIH children allocatedTracked).recordExpressionWithExpected recorded
  | unary operator operand =>
    obtain ⟨_, _, child, dispatch⟩ := Detail.inferExprFuel_success_unary_facts
      form allocation accepted
    have operandTracked := expressionIH child allocatedTracked
    cases dispatch with
    | directFunction _ _ operation recorded
    | traitMethod _ operation recorded =>
      exact (operandTracked.inferUnaryOperator operation).recordExpressionWithExpected recorded
    | selectedFunction _ _ selected recorded =>
      change RecursiveLedgerInvariant (inferred, final).2 pending
      rw [← recorded]
      exact (operandTracked.selectFunctionCandidateFrom selected).recordSelectedCall _ _ _ _
  | binary left operator right =>
    obtain ⟨_, _, _, _, first, second, dispatch⟩ := Detail.inferExprFuel_success_binary_facts
      form allocation accepted
    have operandTracked := expressionIH second (expressionIH first allocatedTracked)
    cases dispatch with
    | directFunction _ _ operation recorded
    | traitMethod _ operation recorded =>
      exact (operandTracked.inferBinaryOperator operation).recordExpressionWithExpected recorded
    | selectedFunction _ _ selected fitted recorded =>
      change RecursiveLedgerInvariant (inferred, final).2 pending
      rw [← recorded]
      exact ((operandTracked.selectFunctionCandidateFrom selected).withExpected fitted)
        |>.recordSelectedCallResult _ _ _ _ _ _ _
  | conditional condition question thenBranch colon elseBranch =>
    obtain ⟨_, _, _, _, _, _, _, first, second, third, unified, recorded⟩ :=
      Detail.inferExprFuel_success_conditional_facts form allocation accepted
    exact ((expressionIH third (expressionIH second
      (expressionIH first allocatedTracked))).unify unified).recordExpressionWithExpected recorded
  | lambda keyword parameters returnType body =>
    obtain ⟨_, _, _, _, _, _, _, _, parametersAccepted, headerFacts, bodyAccepted,
      unified, restored, recorded⟩ := Detail.inferExprFuel_success_lambda_facts
        form allocation accepted
    subst_vars
    exact (((statementsIH bodyAccepted
      (lambdaPrefixLedger (allocatedTracked.bindLambdaParameters parametersAccepted) headerFacts)).unify unified).restoreLexicalScope _).recordExpressionWithExpected recorded
  | call callee arguments =>
    have dispatch := inferExprFuel_success_call_dispatch_facts form allocation accepted
    cases dispatch with
    | @constructor dataType constructor instantiation constructorState _ fresh application =>
      have constructorTracked := allocatedTracked.freshDataConstructorInstantiation dataType constructor
      rw [fresh] at constructorTracked
      exact constructorIH application constructorTracked
    | selected argumentsAccepted _ selected recorded =>
      change RecursiveLedgerInvariant (inferred, final).2 pending
      rw [← recorded]
      exact ((expressionsIH argumentsAccepted allocatedTracked).selectFunctionCandidateFrom selected)
        |>.recordSelectedCall _ _ _ _
    | builtin argumentsAccepted recorded =>
      exact (expressionsIH argumentsAccepted allocatedTracked).recordBuiltinFunctionCall recorded
    | indirect argumentsAccepted calleeAccepted application recorded =>
      change RecursiveLedgerInvariant (inferred, final).2 pending
      rw [← recorded]
      exact ((expressionIH calleeAccepted
        (expressionsIH argumentsAccepted allocatedTracked)).applyFunctionType application)
        |>.recordIndirectCall _ _ _
  | proxy keyword sourceType =>
    obtain ⟨_, _, recorded⟩ := Detail.inferExprFuel_success_proxy_facts form allocation accepted
    exact allocatedTracked.recordExpressionWithExpected recorded
  | index base brackets key =>
    obtain ⟨_, _, _, _, _, _, _, _, _, first, keyFresh, valueFresh,
      unified, second, recorded⟩ := Detail.inferExprFuel_success_index_facts form allocation accepted
    have keyTracked := (expressionIH first allocatedTracked).fresh
    rw [keyFresh] at keyTracked
    have valueTracked := keyTracked.fresh
    rw [valueFresh] at valueTracked
    exact (expressionIH second (valueTracked.unify unified)).recordExpressionWithExpected recorded
  | dotConstructor keyword name arguments =>
    unfold Detail.inferExprFuel at accepted
    simp only [allocation, form, bind, Except.bind] at accepted
    split at accepted
    · contradiction
    · exact constructorIH accepted allocatedTracked
  | field base dot name =>
    unfold Detail.inferExprFuel at accepted
    simp only [allocation, form, bind, Except.bind] at accepted
    repeat' first | split at accepted
    all_goals try contradiction
    all_goals
      exact constructorIH accepted (allocatedTracked.freshDataConstructorInstantiation _ _)
  | array _ | error =>
    simp [Detail.inferExprFuel, allocation, form] at accepted

end Solcore.SourceSemantics.SourceInferenceSoundness
