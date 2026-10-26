import Solcore.Frontend.RustHull.DerivationExpressionCorrespondence
import Solcore.Frontend.RustHull.DerivationCallCorrespondence
import Solcore.Frontend.RustHull.DerivationFunctionCorrespondence
import Solcore.Frontend.RustHull.LoopDerivationCorrespondence
import Solcore.Frontend.RustHull.MatchDerivationCorrespondence
import Solcore.Frontend.RustHull.RevertCorrespondence
import Solcore.Frontend.RustHull.YulCorrespondence

/-! Finite independent Hull execution drives the mutual simulation proof.
Recursive function calls use their actual finite child derivations, without
restricting the program's call graph by a static rank. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationProgramCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution

theorem function_preserves_effects {supported : String → Prop} {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {effects : Semantics.ExternalSemantics σ}
    {fuel : Nat} {functions : List Function} {signatures : List Signature} {scope : Scope}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (codesCompiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes)
    (unique : (signatures.map Signature.name).Nodup)
    (covered : ScopeCoverage [] scope)
    (globals : GlobalEnvironmentRel codes locations scope Core.Renaming.id captured)
    (runtime : EffectEnvironmentRel slots scope Core.Renaming.id captured)
    (external : ExternalCallPreservation supported model slots effects)
    (reverting : RevertPreservation supported model slots effects)
    (assembling : AssemblyPreservation supported model slots effects)
    (eligible : ExecutableProgram supported functions)
    {function : Function} {sources : List Semantics.Value} {initial final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions effects function sources initial result final) :
    FunctionMotive (model := model) functions signatures codes locations captured function sources initial result final := by
  refine Semantics.EvalFunction.rec
    (motive_1 := fun env expression initial result final _ =>
      ExprMotive (supported := supported) (model := model) (slots := slots) functions signatures codes locations captured env expression initial result final)
    (motive_2 := fun env expressions initial result final _ =>
      ExprsMotive (supported := supported) (model := model) (slots := slots) functions signatures codes locations captured env expressions initial result final)
    (motive_3 := fun name _ sources initial result final _ =>
      CallSimulation (model := model) functions signatures codes locations captured name sources initial result final)
    (motive_4 := fun function sources initial result final _ =>
      FunctionMotive (model := model) functions signatures codes locations captured function sources initial result final)
    (motive_5 := fun env statement initial control final _ =>
      StmtMotive (supported := supported) (model := model) (slots := slots) functions signatures codes locations captured env statement initial control final)
    (motive_6 := fun env statements initial control final _ =>
      StatementsMotive (supported := supported) (model := model) (slots := slots) functions signatures codes locations captured env statements initial control final)
    (motive_7 := fun env test post body initial control final _ =>
      LoopDerivationCorrespondence.LoopMotive (supported := supported) (model := model) (slots := slots) functions signatures codes locations captured
        env test post body initial control final)
    (motive_8 := fun env target value alternatives initial control final _ =>
      MatchDerivationCorrespondence.AlternativesMotive (supported := supported) (model := model) (slots := slots) functions signatures codes locations captured
        env target value alternatives initial control final)
    ?word
    ?bool
    ?unit
    ?var
    ?pair
    ?pairFault
    ?fst
    ?snd
    ?inl
    ?inr
    ?inK
    ?call
    ?callFault
    ?ifTrue
    ?ifFalse
    ?ifFault
    ?ifInvalid
    ?nil
    ?cons
    ?fault
    ?function
    ?primitive
    ?external
    ?body
    ?arity
    ?declare
    ?declareInvalid
    ?assign
    ?assignFault
    ?assignInvalid
    ?expression
    ?expressionFault
    ?returned
    ?returnFault
    ?block
    ?forInit
    ?forLoop
    ?breaking
    ?continuing
    ?matchStmt
    ?matchFault
    ?assembly
    ?revert
    ?comment
    ?nil_1
    ?declare_1
    ?declareInvalid_1
    ?next
    ?stop
    ?done
    ?conditionFault
    ?conditionInvalid
    ?step
    ?bodyBreak
    ?bodyStop
    ?postBreak
    ?postStop
    ?nil_2
    ?matched
    ?next_1
    evaluated

  case word =>
    intro env expression state text kind _
    exact DerivationCorrespondence.word kind
  case bool =>
    intro env expression state value kind _
    exact DerivationCorrespondence.bool kind
  case unit =>
    intro env expression state kind _
    exact DerivationCorrespondence.unit kind
  case var =>
    intro env expression state name kind _
    exact DerivationCorrespondence.var kind
  case pair =>
    intro env expression initial middle final left right leftValue rightResult kind first second firstIH secondIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | pair leftAccepted rightAccepted =>
        exact DerivationCorrespondence.pair (firstIH leftAccepted) (secondIH rightAccepted) type span
  case fst =>
    intro env expression initial final operand result kind operandEvaluated operandIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | fst operandAccepted => exact projection (operandIH operandAccepted) false type span
  case snd =>
    intro env expression initial final operand result kind operandEvaluated operandIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | snd operandAccepted => exact projection (operandIH operandAccepted) true type span
  case inl =>
    intro env expression initial final target operand result kind operandEvaluated operandIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | inl operandAccepted => exact injection (operandIH operandAccepted) false type target span
  case inr =>
    intro env expression initial final target operand result kind operandEvaluated operandIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | inr operandAccepted => exact injection (operandIH operandAccepted) true type target span
  case inK =>
    intro env expression initial final index target operand result kind operandEvaluated operandIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | inK operandAccepted => exact indexedInjection (operandIH operandAccepted) index type target span
  case call =>
    intro env expression initial middle final name arguments values result kind argumentsEvaluated called argumentsIH callIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    have argumentsAccepted : ∀ argument ∈ arguments, ExecutableExpression supported functions argument := by
      cases accepted <;> assumption
    intro executionFuel executionScope lowered
    exact DerivationCallCorrespondence.call signaturesCompiled codesCompiled accepted external called
      (argumentsIH argumentsAccepted) callIH
  case ifTrue =>
    intro env expression initial middle final target condition yes no value result kind tested truth selected conditionIH branchIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | conditional conditionAccepted yesAccepted noAccepted =>
        exact conditional true truth (conditionIH conditionAccepted) (branchIH yesAccepted) type target span
  case ifFalse =>
    intro env expression initial middle final target condition yes no value result kind tested truth selected conditionIH branchIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | conditional conditionAccepted yesAccepted noAccepted =>
        exact conditional false truth (conditionIH conditionAccepted) (branchIH noAccepted) type target span
  case nil =>
    intro env state _
    exact DerivationCallCorrespondence.arguments_nil signatures codes locations captured env state
  case cons =>
    intro env expression rest initial middle final value values head tail headIH tailIH accepted
    exact DerivationCallCorrespondence.arguments_cons tail
      (headIH (accepted expression (List.mem_cons_self ..)))
      (tailIH (fun expression member => accepted expression (List.mem_cons_of_mem _ member)))
  case function =>
    intro name type arguments initial final function result selected called calledIH
    exact DerivationCallCorrespondence.call_function selected calledIH
  case primitive =>
    intro name type arguments state result absent computed
    exact DerivationCallCorrespondence.call_not_function absent
  case external =>
    intro name type arguments state result external absent notPrimitive called
    exact DerivationCallCorrespondence.call_not_function absent
  case body =>
    intro function arguments initial allocated final env control bound executed continued
    intro name code index selected signatureSelected codeFound
    obtain ⟨signatureCompiled, functionCompiled⟩ :=
      compiledFunction_at signaturesCompiled codesCompiled unique selected signatureSelected codeFound
    exact DerivationFunctionCorrespondence.function_simulation signatureCompiled functionCompiled covered globals runtime bound
      (continued (eligible function (List.mem_of_find?_eq_some selected)))
  case pairFault =>
    intro env expression initial final left right reason kind first firstIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | pair leftAccepted _ => exact pair_fault (firstIH leftAccepted) type span
  case callFault =>
    intro env expression initial final name arguments reason kind evaluated argumentsIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    have argumentsAccepted : ∀ argument ∈ arguments, ExecutableExpression supported functions argument := by
      cases accepted <;> assumption
    intro executionFuel executionScope lowered
    exact DerivationCallCorrespondence.call_fault signaturesCompiled codesCompiled accepted
      (argumentsIH argumentsAccepted)
  case ifFault =>
    intro env expression initial final target condition yes no reason kind tested testIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | conditional testAccepted _ _ => exact conditional_fault (testIH testAccepted) type target span
  case fault =>
    intro env expression rest initial final reason evaluated headIH accepted
    exact DerivationCallCorrespondence.arguments_fault (headIH (accepted expression (List.mem_cons_self ..)))
  case ifInvalid =>
    intro env expression initial final target condition yes no value kind tested invalid testIH accepted
    cases expression with | mk type expressionKind span =>
    cases kind
    cases accepted with
    | conditional testAccepted _ _ =>
        exact conditional_invalid (testIH testAccepted) invalid type target span
  case arity =>
    intro function arguments state mismatch name code index selected signatureSelected codeFound
    obtain ⟨signatureCompiled, _⟩ :=
      compiledFunction_at signaturesCompiled codesCompiled unique selected signatureSelected codeFound
    exact DerivationFunctionCorrespondence.arity signatureCompiled mismatch
  case declareInvalid =>
    intro env statement initial name type kind zero _
    exact DerivationStatementCorrespondence.declared_invalid kind zero
  case declareInvalid_1 =>
    intro env statement rest name type state kind zero _
    exact DerivationStatementCorrespondence.declare_invalid kind zero
  case assignFault =>
    intro env statement lhs rhs initial final reason kind evaluated rhsIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [ExecutableStatement] at accepted
    exact DerivationStatementCorrespondence.assign_fault rfl (rhsIH accepted)
  case assignInvalid =>
    intro env statement lhs rhs initial middle value reason kind evaluated invalid rhsIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [ExecutableStatement] at accepted
    exact DerivationStatementCorrespondence.assign_invalid rfl (rhsIH accepted) invalid
  case expressionFault =>
    intro env statement value initial final reason kind evaluated valueIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    exact DerivationStatementCorrespondence.expression_fault rfl
      (valueIH (by simpa only [ExecutableStatement] using accepted))
  case returnFault =>
    intro env statement value initial final reason kind evaluated valueIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    exact DerivationStatementCorrespondence.return_fault rfl
      (valueIH (by simpa only [ExecutableStatement] using accepted))
  case matchFault =>
    intro env statement target expression alternatives initial final reason kind evaluated exprIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have parts : ExecutableExpression supported functions expression ∧
        (∀ alternative ∈ alternatives, ∀ statement ∈ alternative.body, ExecutableStatement supported functions statement) := by
      simpa only [ExecutableStatement] using accepted
    intro executionFuel executionScope resultType loops coreExpression
    exact MatchDerivationCorrespondence.fault (statement := ⟨.matchStmt target expression alternatives, span⟩) rfl (exprIH parts.1)
  case nil_2 =>
    intro env target value state _
    exact MatchDerivationCorrespondence.nil
  case matched =>
    intro env target value alternative rest initial final payload control selected executed bodyIH accepted
    exact MatchDerivationCorrespondence.matched selected
      (bodyIH (accepted alternative (List.mem_cons_self ..)))
  case next_1 =>
    intro env target value alternative rest initial final control rejected executed tailIH accepted
    exact MatchDerivationCorrespondence.next rejected
      (tailIH (fun other member => accepted other (List.mem_cons_of_mem _ member)))
  case matchStmt =>
    intro env statement target expression alternatives initial middle final value control
      kind evaluated selected exprIH altIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have parts : ExecutableExpression supported functions expression ∧
        (∀ alternative ∈ alternatives, ∀ statement ∈ alternative.body, ExecutableStatement supported functions statement) := by
      simpa only [ExecutableStatement] using accepted
    intro executionFuel executionScope resultType loops coreExpression
    exact MatchDerivationCorrespondence.statement (statement := ⟨.matchStmt target expression alternatives, span⟩) rfl (exprIH parts.1) (altIH parts.2)
  case assembly =>
    intro env statement body initial final control kind executed accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [ExecutableStatement] at accepted
    exact assembling accepted executed
  case revert =>
    intro env statement message state external control kind executed accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [ExecutableStatement] at accepted
    exact reverting.statement accepted executed
  case block =>
    intro env statement body initial final control kind evaluated bodyIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    exact DerivationStatementCorrespondence.block rfl
      (bodyIH (by simpa only [ExecutableStatement] using accepted))
  case forInit =>
    intro env statement init test post body initial final control kind nonempty evaluated initIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have parts : (∀ statement ∈ init, ExecutableStatement supported functions statement) ∧
        ExecutableExpression supported functions test ∧
        (∀ statement ∈ post, ExecutableStatement supported functions statement) ∧
        (∀ statement ∈ body, ExecutableStatement supported functions statement) := by
      simpa only [ExecutableStatement] using accepted
    apply LoopDerivationCorrespondence.initialized_statement rfl nonempty
    apply initIH
    intro member selected
    rcases List.mem_append.mp selected with selected | selected
    · exact parts.1 member selected
    · simp only [List.mem_singleton] at selected
      subst member
      simpa only [ExecutableStatement, List.not_mem_nil, false_implies, implies_true, true_and] using parts.2
  case forLoop =>
    intro env statement test post body initial final control kind evaluated loopIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have parts : (∀ statement ∈ ([] : List Stmt), ExecutableStatement supported functions statement) ∧
        ExecutableExpression supported functions test ∧
        (∀ statement ∈ post, ExecutableStatement supported functions statement) ∧
        (∀ statement ∈ body, ExecutableStatement supported functions statement) := by
      simpa only [ExecutableStatement] using accepted
    intro executionFuel executionScope resultType loops coreExpression
    exact LoopDerivationCorrespondence.statement (statement := ⟨.forLoop [] test post body, span⟩) rfl (loopIH parts.2.1 parts.2.2.1 parts.2.2.2)
  case breaking =>
    intro env statement state kind _
    exact DerivationStatementCorrespondence.breaking kind
  case continuing =>
    intro env statement state kind _
    exact DerivationStatementCorrespondence.continuing kind
  case done =>
    intro env test post body initial final value tested truth testIH testEligible _ _
    exact LoopDerivationCorrespondence.done (testIH testEligible) truth
  case conditionFault =>
    intro env test post body initial final reason tested testIH testEligible _ _
    exact LoopDerivationCorrespondence.condition_fault (testIH testEligible)
  case conditionInvalid =>
    intro env test post body initial final value tested invalid testIH testEligible _ _
    exact LoopDerivationCorrespondence.condition_invalid (testIH testEligible) invalid
  case step =>
    intro env test post body initial testedState bodyState postState final value bodyControl postControl control
      tested truth bodyEvaluated bodyContinues postEvaluated postContinues next
      testIH bodyIH postIH nextIH testEligible postEligible bodyEligible
    exact LoopDerivationCorrespondence.step (testIH testEligible) truth
      (bodyIH bodyEligible) bodyContinues (postIH postEligible) postContinues
      (nextIH testEligible postEligible bodyEligible)
  case bodyBreak =>
    intro env test post body initial testedState final value tested truth bodyEvaluated
      testIH bodyIH testEligible _ bodyEligible
    exact LoopDerivationCorrespondence.body_break (testIH testEligible) truth (bodyIH bodyEligible)
  case bodyStop =>
    intro env test post body initial testedState final value control tested truth bodyEvaluated stopped
      testIH bodyIH testEligible _ bodyEligible
    exact LoopDerivationCorrespondence.body_stop (testIH testEligible) truth (bodyIH bodyEligible) stopped
  case postBreak =>
    intro env test post body initial testedState bodyState final value bodyControl tested truth
      bodyEvaluated bodyContinues postEvaluated testIH bodyIH postIH testEligible postEligible bodyEligible
    exact LoopDerivationCorrespondence.post_break (testIH testEligible) truth
      (bodyIH bodyEligible) bodyContinues (postIH postEligible)
  case postStop =>
    intro env test post body initial testedState bodyState final value bodyControl control tested truth
      bodyEvaluated bodyContinues postEvaluated stopped testIH bodyIH postIH testEligible postEligible bodyEligible
    exact LoopDerivationCorrespondence.post_stop (testIH testEligible) truth
      (bodyIH bodyEligible) bodyContinues (postIH postEligible) stopped
  case declare =>
    intro env statement initial name type value kind zero _
    exact DerivationStatementCorrespondence.declared kind zero
  case assign =>
    intro env statement lhs rhs initial middle final value kind evaluated assigned rhsIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [ExecutableStatement] at accepted
    exact DerivationStatementCorrespondence.assign rfl (rhsIH accepted) assigned
  case expression =>
    intro env statement value initial final sourceValue kind evaluated valueIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have valueAccepted : ExecutableExpression supported functions value := by
      simpa only [ExecutableStatement] using accepted
    intro executionFuel executionScope resultType loops coreExpression
    exact DerivationStatementCorrespondence.expression_statement (statement := ⟨.expression value, span⟩) rfl (valueIH valueAccepted)
  case returned =>
    intro env statement value initial final sourceValue kind evaluated valueIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have valueAccepted : ExecutableExpression supported functions value := by
      simpa only [ExecutableStatement] using accepted
    intro executionFuel executionScope resultType loops coreExpression
    exact DerivationStatementCorrespondence.returned (statement := ⟨.returnStmt value, span⟩) rfl (valueIH valueAccepted)
  case comment =>
    intro env statement state text kind _
    exact DerivationStatementCorrespondence.comment kind
  case nil_1 =>
    intro env state _
    exact DerivationStatementCorrespondence.nil
  case declare_1 =>
    intro env statement rest initial final name type value control kind zero evaluated continued accepted
    exact DerivationStatementCorrespondence.declare kind zero
      (continued (fun statement member => accepted statement (List.mem_cons_of_mem _ member)))
  case next =>
    intro env statement rest initial middle final control notDeclaration head tail headIH tailIH accepted
    exact DerivationStatementCorrespondence.next notDeclaration
      (headIH (accepted statement (List.mem_cons_self ..)))
      (tailIH (fun statement member => accepted statement (List.mem_cons_of_mem _ member)))
  case stop =>
    intro env statement rest initial final control notDeclaration head stopped headIH accepted
    exact DerivationStatementCorrespondence.stop notDeclaration
      (headIH (accepted statement (List.mem_cons_self ..))) stopped

theorem function_preserves {σ : Type} {model : StateModel σ} {slots : List EffectSlot} {effects : Semantics.ExternalSemantics σ}
    {fuel : Nat} {functions : List Function} {signatures : List Signature} {scope : Scope}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (codesCompiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes)
    (unique : (signatures.map Signature.name).Nodup)
    (covered : ScopeCoverage [] scope)
    (globals : GlobalEnvironmentRel codes locations scope Core.Renaming.id captured)
    (runtime : EffectEnvironmentRel slots scope Core.Renaming.id captured)
    (eligible : RecursiveProgram functions)
    {function : Function} {sources : List Semantics.Value} {initial final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions effects function sources initial result final) :
    FunctionMotive (model := model) functions signatures codes locations captured function sources initial result final :=
  function_preserves_effects signaturesCompiled codesCompiled unique covered globals runtime
    (ExternalCallPreservation.empty model slots effects) (RevertPreservation.empty model slots effects)
    (AssemblyPreservation.empty model slots effects) eligible evaluated

end Solcore.Frontend.RustHull.DerivationProgramCorrespondence
