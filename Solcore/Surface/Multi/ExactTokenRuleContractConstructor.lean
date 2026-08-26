import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace
open Lean Lean.Elab Lean.Elab.Tactic

elab "rwContractConstructorPlansMapM" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.plans?_eq_mapM
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] =>
      rewriteTarget (mkIdent declaration).raw false
  | _ => throwError "the declaration visitor has an unknown list theorem"

elab "unfoldContractConstructorOptionalMarkerCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalMarkerPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the declaration visitor has an unknown optional marker helper"

elab "unfoldContractConstructorMarkerCore" : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.markerPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] => unfoldTarget declaration
  | _ => throwError "the declaration visitor has an unknown marker helper"

private def optionalKeywordPlan
    {file : WorkspaceFile} {tokens : List Token} (keyword : HardKeyword) :
    Option (MatchedTerminal file tokens (.hardKeyword keyword)) → TokenPlan
  | none => .empty
  | some terminal => .exact (.hardKeyword keyword) terminal.span

private theorem optionalKeywordInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token} (keyword : HardKeyword)
    (value : Option (MatchedTerminal file tokens (.hardKeyword keyword))) :
    (EbnfValue.optional (.atom (.terminal (.hardKeyword keyword)))
      (value.map fun terminal =>
        EbnfValue.terminalAtom (.hardKeyword keyword) terminal)).tokenPlan?
        sourceRuleTokenPlanLayout =
      some (optionalKeywordPlan keyword value) := by
  cases value with
  | none => simp [optionalKeywordPlan]
  | some terminal =>
      simp [optionalKeywordPlan,
        MatchedTerminal.physicalTokenPlan_hardKeyword]

private theorem ruleAtomValues_tokenPlans?
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) (values : List (RuleValue rule)) :
    (values.map (EbnfValue.ruleAtom (file := file) (tokens := tokens)
      rule)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      values.mapM (ruleTokenPlan? rule) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      rw [List.map_cons, List.mapM_cons, List.mapM_cons]
      have headEq :
          (EbnfValue.ruleAtom (file := file) (tokens := tokens)
            rule value).tokenPlan? sourceRuleTokenPlanLayout =
          ruleTokenPlan? rule value :=
        EbnfValue.tokenPlan?_ruleAtom _ _ _
      rw [headEq, induction]

private theorem parameterRuleValues_tokenPlans?
    {file : WorkspaceFile} {tokens : List Token}
    (parameters : List Parameter) :
    (parameters.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .parameter)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      parameters.mapM parameterTokenPlan? := by
  rw [ruleAtomValues_tokenPlans? .parameter parameters]
  rfl

private theorem TokenSlot.ListMatches.constructorParensToPlain
    {openSpan closeSpan : SourceSpan}
    {prefixPlan parameters body : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        prefixPlan,
        .exact (.symbol .leftParen) openSpan,
        parameters,
        .exact (.symbol .rightParen) closeSpan,
        body]).slots actual) :
    TokenSlot.ListMatches
      (TokenPlan.concat [prefixPlan, .parens parameters, body]).slots actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, TokenPlan.parens,
    List.append_nil, List.singleton_append] at relation ⊢
  rcases relation.split_append with
    ⟨prefixActual, afterPrefixActual, rfl,
      prefixRelation, afterPrefixRelation⟩
  cases afterPrefixRelation with
  | required openMatch afterOpen =>
      rcases afterOpen.split_append with
        ⟨parameterActual, afterParameterActual, rfl,
          parameterRelation, afterParameterRelation⟩
      cases afterParameterRelation with
      | required closeMatch bodyRelation =>
          have openPlain := openMatch.toPlain
          change (ExpectedToken.plain
            (.symbol .leftParen)).Matches _ at openPlain
          have closePlain := closeMatch.toPlain
          change (ExpectedToken.plain
            (.symbol .rightParen)).Matches _ at closePlain
          exact prefixRelation.append <|
            .required openPlain <| by
              simpa [List.append_assoc] using
                parameterRelation.append
                  (.required closePlain bodyRelation)

private theorem optionalKeywordPlan_wellAnchored
    {file : WorkspaceFile} {tokens : List Token} (keyword : HardKeyword)
    (value : Option (MatchedTerminal file tokens (.hardKeyword keyword))) :
    (optionalKeywordPlan keyword value).WellAnchored := by
  cases value with
  | none => exact TokenPlan.WellAnchored.empty
  | some terminal => exact TokenPlan.WellAnchored.exact _ _

theorem contractConstructorDecl_tokenPlanSound :
    GrammarRuleTokenPlanSound .contractConstructorDecl := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  change TokenPlanEvidence (contractConstructorDeclPlan? output)
    (PhysicalTokens tokens origin finish)
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | contractConstructorDecl origin finish publicToken payableToken
      constructorKw openParen parameters closeParen body publicProjects
      payableProjects constructorProjects witness =>
      change List Parameter at parameters
      change Body at body
      rw [← inputEq] at inputEvidence
      have sourceCandidateEq :
          input.tokenPlan? sourceRuleTokenPlanLayout = (do
            let parameterPlans ← parameters.mapM parameterTokenPlan?
            let bodyPlan ← bodyTokenPlan? .braced body
            pure (TokenPlan.concat [
              optionalKeywordPlan .publicKw publicToken,
              optionalKeywordPlan .payableKw payableToken,
              .exact (.hardKeyword .constructorKw) constructorKw.span,
              .exact (.symbol .leftParen) openParen.span,
              .commaSeparated parameterPlans,
              .exact (.symbol .rightParen) closeParen.span,
              bodyPlan])) := by
        rw [inputEq]
        simp only [m2cV1, m2cV1Rhs, Grammar.sequence,
          Grammar.nonterminal, Grammar.hardKeyword, Grammar.symbol,
          Grammar.terminal, Grammar.list0, Grammar.optional]
        rw [EbnfValue.tokenPlan?_transport]
        rw [EbnfValue.tokenPlan?_sequence]
        rw [EbnfValues.tokenPlan?_cons]
        rw [optionalKeywordInput_tokenPlan? .publicKw publicToken]
        rw [EbnfValues.tokenPlan?_cons]
        rw [optionalKeywordInput_tokenPlan? .payableKw payableToken]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_terminalAtom]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_terminalAtom]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_list0]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_terminalAtom]
        rw [EbnfValues.tokenPlan?_cons]
        rw [EbnfValue.tokenPlan?_ruleAtom]
        rw [EbnfValues.tokenPlan?_nil]
        rw [parameterRuleValues_tokenPlans? parameters]
        simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?,
          MatchedTerminal.physicalTokenPlan_hardKeyword,
          MatchedTerminal.physicalTokenPlan_symbol]
        cases parameterEq : parameters.mapM parameterTokenPlan? <;>
        cases bodyEq : bodyTokenPlan? .braced body <;>
        simp [optionalKeywordPlan, TokenPlan.concat_cons]
      have physicalEvidence := inputEvidence.candidate_eq sourceCandidateEq
      cases parameterEq : parameters.mapM parameterTokenPlan? with
      | none =>
          simp [parameterEq, TokenPlanEvidence] at physicalEvidence
      | some parameterPlans =>
          cases bodyEq : bodyTokenPlan? .braced body with
          | none =>
              simp [parameterEq, bodyEq, TokenPlanEvidence]
                at physicalEvidence
          | some bodyPlan =>
              simp only [parameterEq, bodyEq] at physicalEvidence
              let prefixPlan := TokenPlan.concat [
                optionalKeywordPlan .publicKw publicToken,
                optionalKeywordPlan .payableKw payableToken,
                TokenPlan.exact (.hardKeyword .constructorKw)
                  constructorKw.span]
              let parameterCore := TokenPlan.commaSeparated parameterPlans
              let inner := TokenPlan.concat [
                optionalKeywordPlan .publicKw publicToken,
                optionalKeywordPlan .payableKw payableToken,
                TokenPlan.exact (.hardKeyword .constructorKw)
                  constructorKw.span,
                TokenPlan.parens parameterCore,
                bodyPlan]
              rcases physicalEvidence with
                ⟨sourcePlan, candidateEq, relation⟩
              injection candidateEq with sourcePlanEq
              subst sourcePlan
              have reshapedRelation : TokenSlot.ListMatches
                  (TokenPlan.concat [
                    prefixPlan,
                    .exact (.symbol .leftParen) openParen.span,
                    parameterCore,
                    .exact (.symbol .rightParen) closeParen.span,
                    bodyPlan]).slots
                  (PhysicalTokens tokens origin finish) := by
                simpa [prefixPlan, parameterCore, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using relation
              have innerRelation : TokenSlot.ListMatches inner.slots
                  (PhysicalTokens tokens origin finish) := by
                have converted := reshapedRelation.constructorParensToPlain
                simpa [prefixPlan, inner, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using converted
              have innerAnchored : inner.WellAnchored := by
                have bodyAnchored := bracedBodyTokenPlan?_wellAnchored
                  body bodyPlan bodyEq
                unfold inner
                apply TokenPlan.WellAnchored.concat
                intro plan member
                simp only [List.mem_cons, List.not_mem_nil, or_false]
                  at member
                rcases member with rfl | rfl | rfl | rfl | rfl
                · exact optionalKeywordPlan_wellAnchored
                    .publicKw publicToken
                · exact optionalKeywordPlan_wellAnchored
                    .payableKw payableToken
                · exact TokenPlan.WellAnchored.exact _ _
                · exact TokenPlan.WellAnchored.parens parameterCore
                · exact bodyAnchored
              have enclosed := TokenPlanEvidence.enclose
                (TokenPlanEvidence.some innerRelation)
                (fun plan success => by
                  simp only [Option.some.injEq] at success
                  subst plan
                  exact innerAnchored)
                witness.consumed
              simp only [RuleReduction.marker]
              cases publicToken <;> cases payableToken <;>
                unfold contractConstructorDeclPlan? <;>
                simp only [sourceLoc] <;>
                unfoldContractConstructorOptionalMarkerCore <;>
                unfoldContractConstructorMarkerCore <;>
                rwContractConstructorPlansMapM <;>
                simpa [RuleReduction.terminalLoc, parameterEq, bodyEq,
                  optionalKeywordPlan, inner, parameterCore,
                  TokenPlan.concat_cons] using enclosed

end Solcore.Surface.Multi
