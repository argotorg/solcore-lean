import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

local syntax "topItemBranches!" : term
local macro_rules
  | `(topItemBranches!) =>
      `([.atom (.nonterminal .importDecl),
        .atom (.nonterminal .exportDecl),
        .atom (.nonterminal .pragmaDecl),
        .atom (.nonterminal .dataDecl),
        .atom (.nonterminal .typeAliasDecl),
        .atom (.nonterminal .classDecl),
        .atom (.nonterminal .instanceDecl),
        .atom (.nonterminal .contractDecl),
        .atom (.nonterminal .functionDecl)])

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

/-- Every top-level wrapper preserves exact token evidence while adding its
checked source span to the mandatory physical endpoints of the child plan. -/
theorem grammarRuleTokenPlanSound_topItem :
    GrammarRuleTokenPlanSound .topItem := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  cases reduces with
  | topItemImport origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        topItemBranches!
        ⟨⟨0, by decide⟩, EbnfValue.ruleAtom .importDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .importDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (importDeclPlan?_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | topItemExport origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        topItemBranches!
        ⟨⟨1, by decide⟩, EbnfValue.ruleAtom .exportDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .exportDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (exportDeclPlan?_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | topItemPragma origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        topItemBranches!
        ⟨⟨2, by decide⟩, EbnfValue.ruleAtom .pragmaDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .pragmaDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (pragmaDeclPlan?_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | topItemData origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        topItemBranches!
        ⟨⟨3, by decide⟩, EbnfValue.ruleAtom .dataDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .dataDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (dataDeclPlan?_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | topItemTypeAlias origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        topItemBranches!
        ⟨⟨4, by decide⟩, EbnfValue.ruleAtom .typeAliasDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .typeAliasDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (typeAliasDeclPlan?_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | topItemClass origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        topItemBranches!
        ⟨⟨5, by decide⟩, EbnfValue.ruleAtom .classDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .classDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (classDeclPlan?_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | topItemInstance origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        topItemBranches!
        ⟨⟨6, by decide⟩, EbnfValue.ruleAtom .instanceDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .instanceDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (instanceDeclPlan?_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | topItemContract origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        topItemBranches!
        ⟨⟨7, by decide⟩, EbnfValue.ruleAtom .contractDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .contractDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (contractDeclPlan?_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl
  | topItemFunction origin finish declaration witness =>
      rw [EbnfValue.tokenPlan?_transport] at inputEvidence
      have selected := TokenPlanEvidence.selectedChoice
        topItemBranches!
        ⟨⟨8, by decide⟩, EbnfValue.ruleAtom .functionDecl declaration⟩
        inputEvidence
      have innerEvidence := TokenPlanEvidence.selectedRule
        .functionDecl declaration selected
      have enclosed := TokenPlanEvidence.enclose innerEvidence
        (functionDeclPlan?_wellAnchored declaration) witness.consumed
      exact enclosed.candidate_eq <| by
        rw [optionMap_eq_bindPure]
        rfl

end Solcore.Surface.Multi
