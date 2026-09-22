import Solcore.Frontend.SourceRuntimeDeep.Evaluation

/-! The whole finite-graph evaluator deep-preservation theorem. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

/-- Every successful finite-fuel graph evaluation of a statically checked
expression preserves deep value typing and final-store typing.  The proof is
by fuel induction; source closures and globals use the same induction
hypothesis when their bodies are invoked through `applyValue`. -/
theorem evaluate_preserves_graph_type
    (program : Program) (wellTyped : program.IsWellTyped) :
    ∀ fuel, BodyPreservesGraphTyping program (evaluate fuel program) := by
  intro fuel
  induction fuel with
  | zero =>
      intro world definitions environment context store expression expected
        value finalStore environmentTyping staticTyping storeTyping completed
      simp [evaluate] at completed
  | succ remaining ih =>
      intro world definitions environment context store expression expected
        value finalStore environmentTyping staticTyping storeTyping completed
      cases expression with
      | unit =>
          exact evaluate_unit_done_deep environmentTyping staticTyping
            storeTyping completed
      | bool literal =>
          exact evaluate_bool_done_deep environmentTyping staticTyping
            storeTyping completed
      | word literal =>
          exact evaluate_word_done_deep environmentTyping staticTyping
            storeTyping completed
      | «local» id =>
          exact evaluate_local_done_deep environmentTyping staticTyping
            storeTyping completed
      | pair left right =>
          obtain ⟨leftType, rightType, leftTyping, rightTyping,
            expectedEq⟩ := staticTyping.pair_components
          subst expected
          exact evaluate_pair_done_deep ih environmentTyping leftTyping
            rightTyping storeTyping completed
      | unary op operand =>
          obtain ⟨operandTyping, expectedEq⟩ :=
            staticTyping.unary_components
          subst expected
          exact evaluate_unary_done_deep ih environmentTyping operandTyping
            storeTyping completed
      | binary op left right =>
          obtain ⟨leftTyping, rightTyping, expectedEq⟩ :=
            staticTyping.binary_components
          subst expected
          exact evaluate_binary_done_deep ih environmentTyping leftTyping
            rightTyping storeTyping completed
      | wordLt left right =>
          obtain ⟨leftTyping, rightTyping, expectedEq⟩ :=
            staticTyping.wordLt_components
          subst expected
          exact evaluate_wordLt_done_deep ih environmentTyping leftTyping
            rightTyping storeTyping completed
      | letE binder bound body =>
          obtain ⟨boundType, boundTyping, bodyTyping⟩ :=
            staticTyping.letE_components
          exact evaluate_let_done_deep ih environmentTyping boundTyping
            bodyTyping storeTyping completed
      | ifE condition thenBranch elseBranch =>
          obtain ⟨conditionTyping, thenTyping, elseTyping⟩ :=
            staticTyping.ifE_components
          exact evaluate_ifE_done_deep ih environmentTyping conditionTyping
            thenTyping elseTyping storeTyping completed
      | global key =>
          exact evaluate_global_done_deep wellTyped environmentTyping
            staticTyping storeTyping completed
      | lambda parameters resultType body =>
          exact evaluate_lambda_done_deep environmentTyping staticTyping
            storeTyping completed
      | apply function arguments =>
          exact evaluate_apply_done_deep ih wellTyped environmentTyping
            staticTyping storeTyping completed


end Solcore.Frontend.SourceRuntime
