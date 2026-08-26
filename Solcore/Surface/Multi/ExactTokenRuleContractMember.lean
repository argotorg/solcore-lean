import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace
open Lean Lean.Elab Lean.Elab.Tactic

elab "unfoldMemberOptionalPlanCore" "at" hypothesis:ident : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] =>
      withMainContext do
        unfoldLocalDecl declaration (← getFVarId hypothesis)
  | _ => throwError "the declaration visitor has an unknown optional helper"

elab "unfoldMemberOptionalMarkerCore" "at" hypothesis:ident : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalMarkerPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] =>
      withMainContext do
        unfoldLocalDecl declaration (← getFVarId hypothesis)
  | _ => throwError "the declaration visitor has an unknown marker helper"

elab "unfoldMemberMarkerCore" "at" hypothesis:ident : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.markerPlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] =>
      withMainContext do
        unfoldLocalDecl declaration (← getFVarId hypothesis)
  | _ => throwError "the declaration visitor has an unknown marker plan"

elab "unfoldMemberReturnCore" "at" hypothesis:ident : tactic => do
  let environment ← getEnv
  let suffix := `Solcore.Surface.Multi.optionalReturnTypePlan?
  let candidates := environment.constants.toList.filter fun entry =>
    suffix.isSuffixOf entry.1
  match candidates with
  | [(declaration, _)] =>
      withMainContext do
        unfoldLocalDecl declaration (← getFVarId hypothesis)
  | _ => throwError "the declaration visitor has an unknown return helper"

local syntax "contractMemberBranches!" : term
local macro_rules
  | `(contractMemberBranches!) =>
      `([.atom (.nonterminal .dataDecl),
        .atom (.nonterminal .typeAliasDecl),
        .atom (.nonterminal .fieldDecl),
        .atom (.nonterminal .functionDecl),
        .atom (.nonterminal .fallbackDecl),
        .atom (.nonterminal .contractConstructorDecl)])

private theorem TokenPlanEvidence.selectedChoice
    {file : WorkspaceFile} {tokens : List Token}
    (branches : List EbnfExpr)
    (value : (branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch))
    {actual : List Token}
    (evidence : TokenPlanEvidence
      ((EbnfValue.choice branches value).tokenPlan?
        sourceRuleTokenPlanLayout) actual) :
    TokenPlanEvidence
      (value.2.tokenPlan? sourceRuleTokenPlanLayout) actual := by
  exact evidence.candidate_eq
    (EbnfValue.tokenPlan?_choice
      sourceRuleTokenPlanLayout branches value)

private theorem TokenPlanEvidence.selectedRule
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) (value : RuleValue rule)
    {actual : List Token}
    (evidence : TokenPlanEvidence
      ((EbnfValue.ruleAtom (file := file) (tokens := tokens)
        rule value).tokenPlan? sourceRuleTokenPlanLayout) actual) :
    TokenPlanEvidence (ruleTokenPlan? rule value) actual := by
  exact evidence.candidate_eq
    (EbnfValue.tokenPlan?_ruleAtom
      sourceRuleTokenPlanLayout rule value)

private theorem optionMap_eq_bindPure
    {alpha beta : Type} (function : alpha → beta)
    (candidate : Option alpha) :
    candidate.map function = (do
      let value ← candidate
      pure (function value)) := by
  cases candidate <;> rfl

private theorem optionalGenericCandidate_wellAnchored
    (value : Option GenericPrefix) (plan : TokenPlan)
    (success : (match value with
      | none => some TokenPlan.empty
      | some generic => genericPrefixPlan? generic) = some plan) :
    plan.WellAnchored := by
  cases value with
  | none =>
      simp at success
      subst plan
      exact TokenPlan.WellAnchored.empty
  | some generic =>
      change genericPrefixPlan? generic = some plan at success
      exact genericPrefixPlan?_wellAnchored generic plan success

private theorem optionalMarkerCandidate_wellAnchored
    (role : SyntaxMarker) (kind : TokenKind)
    (value : Option Marker) (plan : TokenPlan)
    (success : (match value with
      | none => some TokenPlan.empty
      | some marker =>
          if marker.payload = role then
            some (TokenPlan.exact kind marker.span)
          else none) = some plan) :
    plan.WellAnchored := by
  cases value with
  | none =>
      simp at success
      subst plan
      exact TokenPlan.WellAnchored.empty
  | some marker =>
      by_cases roleEq : marker.payload = role
      · simp [roleEq] at success
        subst plan
        exact TokenPlan.WellAnchored.exact _ _
      · simp [roleEq] at success

private theorem markerCandidate_wellAnchored
    (role : SyntaxMarker) (kind : TokenKind)
    (marker : Marker) (plan : TokenPlan)
    (success : (if marker.payload = role then
      some (TokenPlan.exact kind marker.span) else none) = some plan) :
    plan.WellAnchored := by
  by_cases roleEq : marker.payload = role
  · simp [roleEq] at success
    subst plan
    exact TokenPlan.WellAnchored.exact _ _
  · simp [roleEq] at success

private theorem optionalReturnCandidate_wellAnchored
    (value : Option TypeExpr) (plan : TokenPlan)
    (success : (match value with
      | none => some TokenPlan.empty
      | some returnType => do
          let typePlan ← typeExprPlan? returnType
          pure (TokenPlan.append
            (TokenPlan.plain (.symbol .arrow)) typePlan)) = some plan) :
    plan.WellAnchored := by
  cases value with
  | none =>
      simp at success
      subst plan
      exact TokenPlan.WellAnchored.empty
  | some returnType =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨typePlan, typeEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.append
        (TokenPlan.WellAnchored.plain _)
        (typeExprPlan?_wellAnchored returnType typePlan typeEq)

private theorem fieldDeclPlan_wellAnchored
    (declaration : FieldDecl) (plan : TokenPlan)
    (success : fieldDeclPlan? declaration = some plan) :
    plan.WellAnchored := by
  unfold fieldDeclPlan? at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨typePlan, typeEq, success⟩
  cases initializerEq : declaration.payload.initializer with
  | none =>
      rw [initializerEq] at success
      injection success with planEq
      subst plan
      have typeAnchored := typeExprPlan?_wellAnchored
        declaration.payload.type typePlan typeEq
      apply TokenPlan.WellAnchored.enclose
      apply TokenPlan.WellAnchored.concat
      intro candidate member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact identifierPlan_wellAnchored _
      · exact TokenPlan.WellAnchored.plain _
      · exact typeAnchored
      · exact TokenPlan.WellAnchored.empty
      · exact TokenPlan.WellAnchored.plain _
  | some expression =>
      rw [initializerEq] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨expressionPlan, expressionEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      have initializerAnchored := TokenPlan.WellAnchored.append
        (TokenPlan.WellAnchored.plain (.symbol .equal))
        (expressionTokenPlan?_wellAnchored
          expression expressionPlan expressionEq)
      have typeAnchored := typeExprPlan?_wellAnchored
        declaration.payload.type typePlan typeEq
      apply TokenPlan.WellAnchored.enclose
      apply TokenPlan.WellAnchored.concat
      intro candidate member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact identifierPlan_wellAnchored _
      · exact TokenPlan.WellAnchored.plain _
      · exact typeAnchored
      · exact initializerAnchored
      · exact TokenPlan.WellAnchored.plain _

private theorem fallbackDeclPlan_wellAnchored
    (declaration : FallbackDecl) (plan : TokenPlan)
    (success : fallbackDeclPlan? declaration = some plan) :
    plan.WellAnchored := by
  unfold fallbackDeclPlan? at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨genericPlan, genericEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨publicPlan, publicEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨payablePlan, payableEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨markerPlan, markerEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨parameterPlans, _parameterEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨returnPlan, returnEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨bodyPlan, bodyEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  unfoldMemberOptionalPlanCore at genericEq
  unfoldMemberOptionalMarkerCore at publicEq
  unfoldMemberMarkerCore at publicEq
  unfoldMemberOptionalMarkerCore at payableEq
  unfoldMemberMarkerCore at payableEq
  unfoldMemberMarkerCore at markerEq
  unfoldMemberReturnCore at returnEq
  have genericAnchored : genericPlan.WellAnchored := by
    cases optionEq : declaration.payload.genericPrefix with
    | none =>
        rw [optionEq] at genericEq
        change some TokenPlan.empty = some genericPlan at genericEq
        injection genericEq with planEq
        subst genericPlan
        exact TokenPlan.WellAnchored.empty
    | some generic =>
        rw [optionEq] at genericEq
        change genericPrefixPlan? generic = some genericPlan at genericEq
        exact genericPrefixPlan?_wellAnchored generic genericPlan genericEq
  have publicAnchored : publicPlan.WellAnchored := by
    cases optionEq : declaration.payload.public with
    | none =>
        rw [optionEq] at publicEq
        change some TokenPlan.empty = some publicPlan at publicEq
        injection publicEq with planEq
        subst publicPlan
        exact TokenPlan.WellAnchored.empty
    | some marker =>
        rw [optionEq] at publicEq
        change (if marker.payload = .publicModifier then
          some (TokenPlan.exact (.hardKeyword .publicKw) marker.span)
          else none) = some publicPlan at publicEq
        by_cases roleEq : marker.payload = .publicModifier
        · simp [roleEq] at publicEq
          subst publicPlan
          exact TokenPlan.WellAnchored.exact _ _
        · simp [roleEq] at publicEq
  have payableAnchored : payablePlan.WellAnchored := by
    cases optionEq : declaration.payload.payable with
    | none =>
        rw [optionEq] at payableEq
        change some TokenPlan.empty = some payablePlan at payableEq
        injection payableEq with planEq
        subst payablePlan
        exact TokenPlan.WellAnchored.empty
    | some marker =>
        rw [optionEq] at payableEq
        change (if marker.payload = .payableModifier then
          some (TokenPlan.exact (.hardKeyword .payableKw) marker.span)
          else none) = some payablePlan at payableEq
        by_cases roleEq : marker.payload = .payableModifier
        · simp [roleEq] at payableEq
          subst payablePlan
          exact TokenPlan.WellAnchored.exact _ _
        · simp [roleEq] at payableEq
  have markerAnchored : markerPlan.WellAnchored := by
    change (if declaration.payload.marker.payload = .fallbackName then
      some (TokenPlan.exact (.hardKeyword .fallbackKw)
        declaration.payload.marker.span) else none) =
      some markerPlan at markerEq
    by_cases roleEq : declaration.payload.marker.payload = .fallbackName
    · simp [roleEq] at markerEq
      subst markerPlan
      exact TokenPlan.WellAnchored.exact _ _
    · simp [roleEq] at markerEq
  have returnAnchored : returnPlan.WellAnchored := by
    cases optionEq : declaration.payload.returnType with
    | none =>
        rw [optionEq] at returnEq
        change some TokenPlan.empty = some returnPlan at returnEq
        injection returnEq with planEq
        subst returnPlan
        exact TokenPlan.WellAnchored.empty
    | some returnType =>
        rw [optionEq] at returnEq
        change (do
          let typePlan ← typeExprPlan? returnType
          pure (TokenPlan.append
            (TokenPlan.plain (.symbol .arrow)) typePlan)) =
          some returnPlan at returnEq
        rcases Option.bind_eq_some_iff.mp returnEq with
          ⟨typePlan, typeEq, resultEq⟩
        injection resultEq with planEq
        subst returnPlan
        exact TokenPlan.WellAnchored.append
          (TokenPlan.WellAnchored.plain _)
          (typeExprPlan?_wellAnchored returnType typePlan typeEq)
  have bodyAnchored := bracedBodyTokenPlan?_wellAnchored
    declaration.payload.body bodyPlan bodyEq
  apply TokenPlan.WellAnchored.enclose
  apply TokenPlan.WellAnchored.concat
  intro candidate member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact genericAnchored
  · exact publicAnchored
  · exact payableAnchored
  · exact markerAnchored
  · exact TokenPlan.WellAnchored.parens _
  · exact returnAnchored
  · exact bodyAnchored

private theorem contractConstructorDeclPlan_wellAnchored
    (declaration : ContractConstructorDecl) (plan : TokenPlan)
    (success : contractConstructorDeclPlan? declaration = some plan) :
    plan.WellAnchored := by
  unfold contractConstructorDeclPlan? at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨publicPlan, publicEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨payablePlan, payableEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨markerPlan, markerEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨parameterPlans, _parameterEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨bodyPlan, bodyEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  unfoldMemberOptionalMarkerCore at publicEq
  unfoldMemberMarkerCore at publicEq
  unfoldMemberOptionalMarkerCore at payableEq
  unfoldMemberMarkerCore at payableEq
  unfoldMemberMarkerCore at markerEq
  have publicAnchored : publicPlan.WellAnchored := by
    cases optionEq : declaration.payload.public with
    | none =>
        rw [optionEq] at publicEq
        change some TokenPlan.empty = some publicPlan at publicEq
        injection publicEq with planEq
        subst publicPlan
        exact TokenPlan.WellAnchored.empty
    | some marker =>
        rw [optionEq] at publicEq
        change (if marker.payload = .publicModifier then
          some (TokenPlan.exact (.hardKeyword .publicKw) marker.span)
          else none) = some publicPlan at publicEq
        by_cases roleEq : marker.payload = .publicModifier
        · simp [roleEq] at publicEq
          subst publicPlan
          exact TokenPlan.WellAnchored.exact _ _
        · simp [roleEq] at publicEq
  have payableAnchored : payablePlan.WellAnchored := by
    cases optionEq : declaration.payload.payable with
    | none =>
        rw [optionEq] at payableEq
        change some TokenPlan.empty = some payablePlan at payableEq
        injection payableEq with planEq
        subst payablePlan
        exact TokenPlan.WellAnchored.empty
    | some marker =>
        rw [optionEq] at payableEq
        change (if marker.payload = .payableModifier then
          some (TokenPlan.exact (.hardKeyword .payableKw) marker.span)
          else none) = some payablePlan at payableEq
        by_cases roleEq : marker.payload = .payableModifier
        · simp [roleEq] at payableEq
          subst payablePlan
          exact TokenPlan.WellAnchored.exact _ _
        · simp [roleEq] at payableEq
  have markerAnchored : markerPlan.WellAnchored := by
    change (if declaration.payload.marker.payload =
        .contractConstructorName then
      some (TokenPlan.exact (.hardKeyword .constructorKw)
        declaration.payload.marker.span) else none) =
      some markerPlan at markerEq
    by_cases roleEq : declaration.payload.marker.payload =
        .contractConstructorName
    · simp [roleEq] at markerEq
      subst markerPlan
      exact TokenPlan.WellAnchored.exact _ _
    · simp [roleEq] at markerEq
  have bodyAnchored := bracedBodyTokenPlan?_wellAnchored
    declaration.payload.body bodyPlan bodyEq
  apply TokenPlan.WellAnchored.enclose
  apply TokenPlan.WellAnchored.concat
  intro candidate member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact publicAnchored
  · exact payableAnchored
  · exact markerAnchored
  · exact TokenPlan.WellAnchored.parens _
  · exact bodyAnchored

private theorem contractMemberPlan_inner_wellAnchored
    (member : ContractMember) (plan : TokenPlan)
    (success : (match member.payload with
      | .dataDecl declaration => dataDeclPlan? declaration
      | .typeAlias declaration => typeAliasDeclPlan? declaration
      | .field declaration => fieldDeclPlan? declaration
      | .function declaration => functionDeclPlan? declaration
      | .fallback declaration => fallbackDeclPlan? declaration
      | .constructor declaration =>
          contractConstructorDeclPlan? declaration) = some plan) :
    plan.WellAnchored := by
  rcases member with ⟨span, payload⟩
  cases payload with
  | dataDecl declaration =>
      exact dataDeclPlan?_wellAnchored declaration plan success
  | typeAlias declaration =>
      exact typeAliasDeclPlan?_wellAnchored declaration plan success
  | field declaration =>
      exact fieldDeclPlan_wellAnchored declaration plan success
  | function declaration =>
      exact functionDeclPlan?_wellAnchored declaration plan success
  | fallback declaration =>
      exact fallbackDeclPlan_wellAnchored declaration plan success
  | constructor declaration =>
      exact contractConstructorDeclPlan_wellAnchored
        declaration plan success

theorem contractMember_tokenPlanSound :
    GrammarRuleTokenPlanSound .contractMember := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | contractMemberData origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        contractMemberBranches!
        ⟨⟨0, by decide⟩, EbnfValue.ruleAtom .dataDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .dataDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (dataDeclPlan?_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | contractMemberTypeAlias origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        contractMemberBranches!
        ⟨⟨1, by decide⟩, EbnfValue.ruleAtom .typeAliasDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .typeAliasDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (typeAliasDeclPlan?_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | contractMemberField origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        contractMemberBranches!
        ⟨⟨2, by decide⟩, EbnfValue.ruleAtom .fieldDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .fieldDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (fieldDeclPlan_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | contractMemberFunction origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        contractMemberBranches!
        ⟨⟨3, by decide⟩, EbnfValue.ruleAtom .functionDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .functionDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (functionDeclPlan?_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | contractMemberFallback origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        contractMemberBranches!
        ⟨⟨4, by decide⟩, EbnfValue.ruleAtom .fallbackDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .fallbackDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (fallbackDeclPlan_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | contractMemberConstructor origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        contractMemberBranches!
        ⟨⟨5, by decide⟩,
          EbnfValue.ruleAtom .contractConstructorDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .contractConstructorDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (contractConstructorDeclPlan_wellAnchored declaration)
        witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl

end Solcore.Surface.Multi
