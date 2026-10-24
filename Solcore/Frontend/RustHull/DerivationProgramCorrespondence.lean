import Solcore.Frontend.RustHull.DerivationExpressionCorrespondence
import Solcore.Frontend.RustHull.DerivationCallCorrespondence
import Solcore.Frontend.RustHull.DerivationFunctionCorrespondence
import Solcore.Frontend.RustHull.LoopDerivationCorrespondence

/-! Finite independent Hull execution drives the mutual simulation proof.
Recursive function calls use their actual finite child derivations, without
restricting the program's call graph by a static rank. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationProgramCorrespondence
open Correspondence DerivationCorrespondence ScalarExecution

theorem function_preserves {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {fuel : Nat} {functions : List Function} {signatures : List Signature} {scope : Scope}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (codesCompiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes)
    (unique : (signatures.map Signature.name).Nodup)
    (globals : GlobalEnvironmentRel codes locations scope Core.Renaming.id captured)
    (eligible : RecursiveProgram functions)
    {function : Function} {sources : List Semantics.Value} {initial final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction functions effects function sources initial result final) :
    FunctionMotive functions signatures codes locations captured function sources initial result final := by
  refine Semantics.EvalFunction.rec
    (motive_1 := fun env expression initial result final _ =>
      ExprMotive functions signatures codes locations captured env expression initial result final)
    (motive_2 := fun env expressions initial result final _ =>
      ExprsMotive functions signatures codes locations captured env expressions initial result final)
    (motive_3 := fun name _ sources initial result final _ =>
      CallSimulation functions signatures codes locations captured name sources initial result final)
    (motive_4 := fun function sources initial result final _ =>
      FunctionMotive functions signatures codes locations captured function sources initial result final)
    (motive_5 := fun env statement initial control final _ =>
      StmtMotive functions signatures codes locations captured env statement initial control final)
    (motive_6 := fun env statements initial control final _ =>
      StatementsMotive functions signatures codes locations captured env statements initial control final)
    (motive_7 := fun env test post body initial control final _ =>
      LoopDerivationCorrespondence.LoopMotive functions signatures codes locations captured
        env test post body initial control final)
    (motive_8 := fun _ _ _ _ _ _ _ _ => True)
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
    cases expression with | mk type expressionKind span =>
    cases kind
    exact ExprSimulation.of_pure (effects := effects) (.word rfl)
      (SignatureNames.compiled signaturesCompiled) (.word type text span) (by
        intro reason; unfold Semantics.literalResult; split <;> simp)
  case bool =>
    intro env expression state value kind _
    cases expression with | mk type expressionKind span =>
    cases kind
    exact ExprSimulation.of_pure (effects := effects) (.bool rfl)
      (SignatureNames.compiled signaturesCompiled) (.bool type value span) (by
        intro reason; unfold Semantics.booleanResult; split <;> simp)
  case unit =>
    intro env expression state kind _
    cases expression with | mk type expressionKind span =>
    cases kind
    exact ExprSimulation.of_pure (effects := effects) (.unit rfl)
      (SignatureNames.compiled signaturesCompiled) (.unit type span) (by intros; simp)
  case var =>
    intro env expression state name kind _
    cases expression with | mk type expressionKind span =>
    cases kind
    exact ExprSimulation.of_pure (effects := effects) (.var rfl)
      (SignatureNames.compiled signaturesCompiled) (.var type name span) (by
        intro reason; unfold Semantics.readResult; split
        · simp
        · split <;> simp)
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
    have argumentsAccepted : ∀ argument ∈ arguments, RecursiveExpression functions argument := by
      cases accepted <;> assumption
    exact DerivationCallCorrespondence.call signaturesCompiled codesCompiled accepted called
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
    exact DerivationFunctionCorrespondence.function_simulation signatureCompiled functionCompiled globals bound
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
    have argumentsAccepted : ∀ argument ∈ arguments, RecursiveExpression functions argument := by
      cases accepted <;> assumption
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
  case ifInvalid | arity | declareInvalid | declareInvalid_1 =>
    intros
    simp [ExprMotive, FunctionMotive, StmtMotive, StatementsMotive,
      ExprSimulation, FunctionSimulation, StmtSimulation, StatementsSimulation, SafeResult, SafeControl]
  case assignFault =>
    intro env statement lhs rhs initial final reason kind evaluated rhsIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    cases lhs with | mk sourceType lhsKind leftSpan =>
    cases lhsKind <;> simp only [RecursiveStatement] at accepted
    all_goals first
      | exact False.elim accepted
      | exact DerivationStatementCorrespondence.assign_fault rfl (rhsIH accepted)
  case assignInvalid =>
    intro env statement lhs rhs initial middle value reason kind evaluated invalid rhsIH accepted safe
    obtain ⟨word, rfl⟩ := (safeControl_fault_iff reason).mp safe
    exact False.elim (DerivationStatementCorrespondence.assignment_not_language env middle lhs value word invalid)
  case expressionFault =>
    intro env statement value initial final reason kind evaluated valueIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    exact DerivationStatementCorrespondence.expression_fault rfl
      (valueIH (by simpa only [RecursiveStatement] using accepted))
  case returnFault =>
    intro env statement value initial final reason kind evaluated valueIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    exact DerivationStatementCorrespondence.return_fault rfl
      (valueIH (by simpa only [RecursiveStatement] using accepted))
  case matchFault =>
    intro env statement target expression alternatives initial final reason kind evaluated exprIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [RecursiveStatement] at accepted
  case nil_2 | matched | next_1 =>
    intros
    trivial
  case matchStmt =>
    intro env statement target expression alternatives initial middle final value control
      kind evaluated selected exprIH altIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [RecursiveStatement] at accepted
  case assembly =>
    intro env statement body initial final control kind executed accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [RecursiveStatement] at accepted
  case revert =>
    intro env statement message state external control kind executed accepted
    cases statement with | mk statementKind span =>
    cases kind
    simp only [RecursiveStatement] at accepted
  case block =>
    intro env statement body initial final control kind evaluated bodyIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    exact DerivationStatementCorrespondence.block rfl
      (bodyIH (by simpa only [RecursiveStatement] using accepted))
  case forInit =>
    intro env statement init test post body initial final control kind nonempty evaluated initIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have parts : (∀ statement ∈ init, RecursiveStatement functions statement) ∧
        RecursiveExpression functions test ∧
        (∀ statement ∈ post, RecursiveStatement functions statement) ∧
        (∀ statement ∈ body, RecursiveStatement functions statement) := by
      simpa only [RecursiveStatement] using accepted
    apply LoopDerivationCorrespondence.initialized_statement rfl nonempty
    apply initIH
    intro member selected
    rcases List.mem_append.mp selected with selected | selected
    · exact parts.1 member selected
    · simp only [List.mem_singleton] at selected
      subst member
      simpa only [RecursiveStatement, List.not_mem_nil, false_implies, implies_true, true_and] using parts.2
  case forLoop =>
    intro env statement test post body initial final control kind evaluated loopIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have parts : (∀ statement ∈ ([] : List Stmt), RecursiveStatement functions statement) ∧
        RecursiveExpression functions test ∧
        (∀ statement ∈ post, RecursiveStatement functions statement) ∧
        (∀ statement ∈ body, RecursiveStatement functions statement) := by
      simpa only [RecursiveStatement] using accepted
    exact LoopDerivationCorrespondence.statement rfl (loopIH parts.2.1 parts.2.2.1 parts.2.2.2)
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
    intro env test post body initial final value tested invalid testIH _ _ _ safe
    cases safe
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
    cases lhs with | mk sourceType lhsKind leftSpan =>
    cases lhsKind <;> simp only [RecursiveStatement] at accepted
    all_goals first
      | exact False.elim accepted
      | exact DerivationStatementCorrespondence.assign_variable rfl (rhsIH accepted) assigned
  case expression =>
    intro env statement value initial final sourceValue kind evaluated valueIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have valueAccepted : RecursiveExpression functions value := by
      simpa only [RecursiveStatement] using accepted
    exact DerivationStatementCorrespondence.expression_statement rfl (valueIH valueAccepted)
  case returned =>
    intro env statement value initial final sourceValue kind evaluated valueIH accepted
    cases statement with | mk statementKind span =>
    cases kind
    have valueAccepted : RecursiveExpression functions value := by
      simpa only [RecursiveStatement] using accepted
    exact DerivationStatementCorrespondence.returned rfl (valueIH valueAccepted)
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

end Solcore.Frontend.RustHull.DerivationProgramCorrespondence
