import Solcore.SourceSemantics.SourceInferenceActualCaptureScopes
import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal

/-! Capture origins follow each actual child entry, using retained declarations
only for earlier statement and header calls in the same execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open SourceInferenceSoundness.ProtectedVariables ActualCaptureOrigins

theorem ChildStep.captureOrigins
    {parent destination : CallIndex} {whole : TypedSource}
    (step : ChildStep parent destination) (inputs : parent.Inputs)
    (origins : ActiveBinderCaptureOrigins parent.initial whole)
    (retained : ∀ {prior : CallIndex}, ChildStep parent prior → prior.CaptureRetained whole) :
    ActiveBinderCaptureOrigins destination.initial whole := by
  cases step with
  | @expression_group fuel context source inner expected initial allocated final childFinal id value childValue accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_tuple fuel context source elements expected initial allocated final childFinal id value values accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expressions_head fuel context source sources initial middle final value values accepted head =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @expressions_tail fuel context source sources initial middle final tailFinal value values tailValues accepted head tail =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.inferExprFuel head
  | @statements_head fuel context source sources expectedReturn initial result head accepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @statements_tail fuel context source sources expectedReturn initial result tail head accepted nonempty headAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have kept := retained (ChildStep.statements_head accepted headAccepted)
    exact statement_result headAccepted origins kept.nodes
  | @statement_initializer fuel context source expectedReturn initial allocated id result name sourceType initializer expected value final accepted form allocation annotation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_return fuel context source expectedReturn initial allocated id result value inferred final accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_expression fuel context source expectedReturn initial allocated id result value semicolon inferred final accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_block fuel context source expectedReturn initial allocated id result body bodyResult accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_if_condition fuel context source expectedReturn initial allocated id result condition thenBody elseBody conditionValue conditionState accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_if_then fuel context source expectedReturn initial allocated id result condition thenBody elseBody conditionValue conditionState thenResult accepted form allocation conditionAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact (origins.allocateStatementId allocation).inferExprFuel conditionAccepted
  | @statement_if_else fuel context source expectedReturn initial allocated id result condition thenBody elseBody conditionValue conditionState body thenResult elseResult accepted form allocation conditionAccepted hasElse thenAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact ((origins.allocateStatementId allocation).inferExprFuel conditionAccepted).restoreLexicalScope
  | @statement_assignment fuel context source expectedReturn initial allocated id result target value operator assignment inferred final accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_bitnot fuel context source expectedReturn initial allocated id result target operator place final accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_while_condition fuel context source expectedReturn initial allocated id result condition body conditionValue conditionState accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_while_body fuel context source expectedReturn initial allocated id result condition body conditionValue conditionState bodyResult accepted form allocation conditionAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact (origins.allocateStatementId allocation).inferExprFuel conditionAccepted
  | @statement_for_initializer fuel context source expectedReturn initial allocated id result span initializer post condition body initialized accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_for_condition fuel context source expectedReturn initial allocated id result span initializer post condition body initialized conditionValue conditionState accepted form allocation initializerAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have kept := retained (ChildStep.statement_for_initializer accepted form allocation initializerAccepted)
    exact headers_result initializerAccepted (origins.allocateStatementId allocation) kept.returned
  | @statement_for_body fuel context source expectedReturn initial allocated id result span initializer post condition body initialized conditionValue conditionState bodyResult accepted form allocation initializerAccepted conditionAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have kept := retained (ChildStep.statement_for_initializer accepted form allocation initializerAccepted)
    exact (headers_result initializerAccepted (origins.allocateStatementId allocation) kept.returned).inferExprFuel conditionAccepted
  | @statement_for_post fuel context source expectedReturn initial allocated id result span initializer post condition body initialized conditionValue conditionState bodyResult postResult accepted form allocation initializerAccepted conditionAccepted bodyAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have kept := retained (ChildStep.statement_for_initializer accepted form allocation initializerAccepted)
    exact (headers_result initializerAccepted (origins.allocateStatementId allocation) kept.returned).restoreLexicalScope
  | @forItems_head fuel context source sources initial final result value accepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @forItems_tail fuel context source sources initial middle result tail head accepted headAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have kept := retained (ChildStep.forItems_head accepted headAccepted)
    exact header_result headAccepted origins kept.returned
  | @forItem_initializer fuel context source initial final result name sourceType initializer expected value childFinal accepted form annotation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @forItem_expression fuel context source initial final result value inferred childFinal accepted form child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @forItem_assignment fuel context source initial final result target value operator assignment inferred childFinal accepted form child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @forItem_bitnot fuel context source initial final result target operator place childFinal accepted form child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @assignedValue_place fuel context target value operator initial final targetState assignment inferred place accepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @assignedValue_value fuel context target value operator initial final targetState assignment inferred place fitted childFinal childValue accepted targetAccepted fitting child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have targetOrigins := origins.inferPlaceFuel targetAccepted
    cases operator <;> simp only [pure, Pure.pure, Except.pure] at fitting
    all_goals first
    | (cases Except.ok.inj fitting; exact targetOrigins)
    | exact targetOrigins.unify fitting
  | @place_group fuel context source initial final result inner value childFinal accepted form child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @place_index_base fuel context source initial final result base key brackets value childFinal accepted form child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @place_index_key fuel context source initial final result base key brackets baseValue baseState keyState valueState fitted childFinal keyType valueType keyValue accepted form baseAccepted keyFresh valueFresh fitting child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have baseOrigins := origins.inferPlaceFuel baseAccepted
    have keyOrigins : ActiveBinderCaptureOrigins keyState whole := by
      have same : keyState = baseState.fresh.2 := (congrArg Prod.snd keyFresh).symm
      rw [same]
      exact baseOrigins.congr_localBinders rfl
    have valueOrigins : ActiveBinderCaptureOrigins valueState whole := by
      have same : valueState = keyState.fresh.2 := (congrArg Prod.snd valueFresh).symm
      rw [same]
      exact keyOrigins.congr_localBinders rfl
    exact valueOrigins.unify fitting
  | @constructorApplication_arguments fuel context source id instantiation sources expected initial fitted final childFinal value values accepted arity fitting child =>
    dsimp only [CallIndex.initial] at origins ⊢
    cases expected with
    | none => cases Except.ok.inj fitting; exact origins
    | some expected => exact origins.unify fitting
  | @constructorArguments_head fuel context source sources expected expectedTypes initial middle final values value accepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @constructorArguments_tail fuel context source sources expected expectedTypes initial middle final values value tailValues tailFinal accepted headAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.inferExprFuel headAccepted
  | @expression_unary fuel context source expected initial allocated final id value operator operand inferred childFinal accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_binary_left fuel context source expected initial allocated final id value operator left right leftValue leftState accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_binary_right fuel context source expected initial allocated final id value operator left right leftValue leftState rightValue rightState accepted form allocation leftAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact (origins.allocateExpressionId allocation).inferExprFuel leftAccepted
  | @expression_conditional_condition fuel context source expected initial allocated final id value condition thenBranch elseBranch question colon conditionValue conditionState accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_conditional_then fuel context source expected initial allocated final id value condition thenBranch elseBranch question colon conditionValue conditionState thenValue thenState accepted form allocation conditionAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact (origins.allocateExpressionId allocation).inferExprFuel conditionAccepted
  | @expression_conditional_else fuel context source expected initial allocated final id value condition thenBranch elseBranch question colon conditionValue conditionState thenValue elseValue thenState elseState accepted form allocation conditionAccepted thenAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact ((origins.allocateExpressionId allocation).inferExprFuel conditionAccepted).inferExprFuel thenAccepted
  | @expression_lambda_body fuel context source expected initial allocated final id value keyword parameters annotation body boundParameters parameterTypes parameterState bodyState resultType bodyResult accepted form allocation parametersAccepted prefixFacts child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact lambdaPrefix prefixFacts (lambdaParameters parametersAccepted (origins.allocateExpressionId allocation))
  | @expression_index_base fuel context source expected initial allocated final id value base key brackets inferred childFinal accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_index_key fuel context source expected initial allocated final id value base key brackets baseValue keyValue baseState keyState valueState fitted childFinal keyType valueType accepted form allocation baseAccepted keyFresh valueFresh fitting child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have baseOrigins := (origins.allocateExpressionId allocation).inferExprFuel baseAccepted
    have keyOrigins : ActiveBinderCaptureOrigins keyState whole := by
      have same : keyState = baseState.fresh.2 := (congrArg Prod.snd keyFresh).symm
      rw [same]
      exact baseOrigins.congr_localBinders rfl
    have valueOrigins : ActiveBinderCaptureOrigins valueState whole := by
      have same : valueState = keyState.fresh.2 := (congrArg Prod.snd valueFresh).symm
      rw [same]
      exact keyOrigins.congr_localBinders rfl
    exact valueOrigins.unify fitting
  | @expression_call_constructor fuel context source expected initial allocated final id value callee arguments dataType constructor instantiation instantiated childFinal inferred accepted form allocation selected fresh child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact freshConstructor (origins.allocateExpressionId allocation) fresh
  | @expression_call_arguments fuel context source expected initial allocated final id value callee arguments values childFinal accepted form allocation nonconstructor child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_call_callee fuel context source expected initial allocated final id value callee arguments values argumentState childFinal inferred accepted form allocation nonconstructor argumentsAccepted indirect child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact (origins.allocateExpressionId allocation).inferExprsFuel argumentsAccepted
  | @expression_contextual_constructor fuel context source expected initial allocated final id value dot name arguments dataType constructor typeArguments inferred childFinal accepted form allocation selected child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_field_constructor fuel context source expected initial allocated final id value base dot name dataType constructor instantiation instantiated childFinal inferred accepted form allocation selected fresh child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact freshConstructor (origins.allocateExpressionId allocation) fresh
  | @matchCases_body fuel context scrutineeType expectedReturn saved arm arms initial patternState pattern result body accepted patternAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact ActualCaptureOrigins.pattern patternAccepted origins
  | @matchCases_tail fuel context scrutineeType expectedReturn saved arm arms initial patternState pattern result body tail accepted patternAccepted bodyAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have savedEq : initial.lexicalScope = saved := inputs.bounds.2.2
    rw [← savedEq]
    exact origins.restoreLexicalScope
  | @statement_match_single fuel context source expectedReturn initial allocated id result scrutinees arms scrutinee value childFinal accepted form allocation single child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_match_many fuel context source expectedReturn initial allocated id result scrutinees arms values childFinal accepted form allocation multiple child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_match_cases fuel context source expectedReturn initial allocated id result scrutinees arms scrutinee scrutineeState hiddenState hidden checked accepted form allocation scrutineeAccepted hiddenAllocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact (ActualCaptureOrigins.scrutinee scrutineeAccepted (origins.allocateStatementId allocation)).allocateHiddenLocal hiddenAllocation
  | @statement_match_default fuel context source expectedReturn initial allocated id result scrutinees arms scrutinee scrutineeState hiddenState hidden checked body bodyResult accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have hiddenOrigins := (ActualCaptureOrigins.scrutinee scrutineeAccepted (origins.allocateStatementId allocation)).allocateHiddenLocal hiddenAllocation
    exact of_scope hiddenOrigins (inferMatchCasesFuel_success_lexicalScope_eq rfl casesAccepted)

end Solcore.SourceSemantics.SourceInferenceExecution
