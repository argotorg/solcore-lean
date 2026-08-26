import Solcore.Surface.Multi.ExactTokenRuleLayout
import Solcore.Surface.Multi.ExactTokenEvidence

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

@[simp] theorem AtomSite.pack_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : AtomSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.atom site).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (AtomSite.pack site values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.atom site).rhs values := by
  cases atomEq : site.atom with
  | terminal terminal =>
      rw [NonterminalValue.tokenPlan?_aux]
      rw [← EbnfValue.tokenPlan?_atShape layout
        site.expression_eq_atom]
      rw [← EbnfValue.tokenPlan?_transport layout
        (congrArg EbnfExpr.atom atomEq)]
      change EbnfValue.tokenPlan? layout
        (AtomSite.packAtAtom site (.terminal terminal) atomEq values) = _
      rw [AtomSite.pack_terminal_eq]
      rw [EbnfValue.tokenPlan?_terminalAtom]
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_atom site) values
      let atomValue := Eq.mp
        (congrArg (GrammarSymbolValue file tokens) site.symbol_eq) viewed.1
      calc
        _ = GrammarSymbolValue.tokenPlan? layout
              (EbnfAtom.terminal terminal).grammarSymbol
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                (congrArg EbnfAtom.grammarSymbol atomEq)) atomValue) := rfl
        _ = GrammarSymbolValue.tokenPlan? layout
              site.atom.grammarSymbol atomValue :=
            GrammarSymbolValue.tokenPlan?_transport layout
              (congrArg EbnfAtom.grammarSymbol atomEq) atomValue
        _ = GrammarSymbolValue.tokenPlan? layout site.symbol
              viewed.1 :=
            GrammarSymbolValue.tokenPlan?_transport layout
              site.symbol_eq viewed.1
        _ = GrammarSymbolValues.tokenPlan? layout [site.symbol]
              viewed := by
            exact (GrammarSymbolValues.tokenPlan?_singleton layout
              site.symbol viewed.1).symm
        _ = GrammarSymbolValues.tokenPlan? layout
              (ProductionId.atom site).rhs values :=
            GrammarSymbolValues.tokenPlan?_view layout
              (ProductionId.rhs_atom site) values
  | nonterminal rule =>
      rw [NonterminalValue.tokenPlan?_aux]
      rw [← EbnfValue.tokenPlan?_atShape layout
        site.expression_eq_atom]
      rw [← EbnfValue.tokenPlan?_transport layout
        (congrArg EbnfExpr.atom atomEq)]
      change EbnfValue.tokenPlan? layout
        (AtomSite.packAtAtom site (.nonterminal rule) atomEq values) = _
      rw [AtomSite.pack_rule_eq]
      rw [EbnfValue.tokenPlan?_ruleAtom]
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_atom site) values
      let atomValue := Eq.mp
        (congrArg (GrammarSymbolValue file tokens) site.symbol_eq) viewed.1
      calc
        _ = GrammarSymbolValue.tokenPlan? layout
              (EbnfAtom.nonterminal rule).grammarSymbol
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                (congrArg EbnfAtom.grammarSymbol atomEq)) atomValue) := rfl
        _ = GrammarSymbolValue.tokenPlan? layout
              site.atom.grammarSymbol atomValue :=
            GrammarSymbolValue.tokenPlan?_transport layout
              (congrArg EbnfAtom.grammarSymbol atomEq) atomValue
        _ = GrammarSymbolValue.tokenPlan? layout site.symbol
              viewed.1 :=
            GrammarSymbolValue.tokenPlan?_transport layout
              site.symbol_eq viewed.1
        _ = GrammarSymbolValues.tokenPlan? layout [site.symbol]
              viewed := by
            exact (GrammarSymbolValues.tokenPlan?_singleton layout
              site.symbol viewed.1).symm
        _ = GrammarSymbolValues.tokenPlan? layout
              (ProductionId.atom site).rhs values :=
            GrammarSymbolValues.tokenPlan?_view layout
              (ProductionId.rhs_atom site) values

@[simp] theorem SequenceSite.pack_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : SequenceSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.seq site).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (SequenceSite.pack site values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.seq site).rhs values := by
  rw [NonterminalValue.tokenPlan?_aux]
  rw [← EbnfValue.tokenPlan?_atShape layout
    site.expression_eq_sequence]
  rw [SequenceSite.pack_eq]
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_ofAuxiliaries]
  exact GrammarSymbolValues.tokenPlan?_view layout
    (ProductionId.rhs_seq site) values

@[simp] theorem GroupSite.pack_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : GroupSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.group site).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (GroupSite.pack site values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.group site).rhs values := by
  rw [NonterminalValue.tokenPlan?_aux]
  rw [← EbnfValue.tokenPlan?_atShape layout
    site.expression_eq_group]
  rw [GroupSite.pack_eq]
  rw [EbnfValue.tokenPlan?_group]
  calc
    _ = GrammarSymbolValues.tokenPlan? layout
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_group site) values) := by
        exact (GrammarSymbolValues.tokenPlan?_singleton layout
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_group site) values).1).symm
    _ = GrammarSymbolValues.tokenPlan? layout
          (ProductionId.group site).rhs values :=
        GrammarSymbolValues.tokenPlan?_view layout
          (ProductionId.rhs_group site) values

@[simp] theorem ChoiceSite.pack_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : ChoiceSite)
    (branch : Fin site.branchCount)
    (values : GrammarSymbolValues file tokens
      (ProductionId.choice site branch).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (ChoiceSite.pack site branch values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.choice site branch).rhs values := by
  rw [NonterminalValue.tokenPlan?_aux]
  rw [← EbnfValue.tokenPlan?_atShape layout
    site.expression_eq_choice]
  rw [ChoiceSite.pack_eq]
  rw [EbnfValue.tokenPlan?_choice]
  rw [EbnfValue.tokenPlan?_transport]
  calc
    _ = GrammarSymbolValues.tokenPlan? layout
          [.nonterminal (.aux (site.branch branch))]
          (GrammarSymbolValues.view
            (ProductionId.rhs_choice site branch) values) := by
        exact (GrammarSymbolValues.tokenPlan?_singleton layout
          (.nonterminal (.aux (site.branch branch)))
          (GrammarSymbolValues.view
            (ProductionId.rhs_choice site branch) values).1).symm
    _ = GrammarSymbolValues.tokenPlan? layout
          (ProductionId.choice site branch).rhs values :=
        GrammarSymbolValues.tokenPlan?_view layout
          (ProductionId.rhs_choice site branch) values

@[simp] theorem OptionalSite.pack_none_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .none).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (OptionalSite.pack site .none values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.opt site .none).rhs values := by
  rw [NonterminalValue.tokenPlan?_aux]
  rw [← EbnfValue.tokenPlan?_atShape layout
    site.expression_eq_optional]
  rw [OptionalSite.pack_none_eq]
  rw [EbnfValue.tokenPlan?_optional_none]
  exact GrammarSymbolValues.tokenPlan?_view layout
    (ProductionId.rhs_opt_none site) values

@[simp] theorem OptionalSite.pack_some_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .some).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (OptionalSite.pack site .some values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.opt site .some).rhs values := by
  rw [NonterminalValue.tokenPlan?_aux]
  rw [← EbnfValue.tokenPlan?_atShape layout
    site.expression_eq_optional]
  rw [OptionalSite.pack_some_eq]
  rw [EbnfValue.tokenPlan?_optional_some]
  calc
    _ = GrammarSymbolValues.tokenPlan? layout
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_opt_some site) values) := by
        exact (GrammarSymbolValues.tokenPlan?_singleton layout
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_opt_some site) values).1).symm
    _ = GrammarSymbolValues.tokenPlan? layout
          (ProductionId.opt site .some).rhs values :=
        GrammarSymbolValues.tokenPlan?_view layout
          (ProductionId.rhs_opt_some site) values

@[simp] theorem OptionalSite.pack_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : OptionalSite)
    (branch : OptionalBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site branch).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (OptionalSite.pack site branch values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.opt site branch).rhs values := by
  cases branch with
  | none => exact OptionalSite.pack_none_tokenPlan? layout site values
  | some => exact OptionalSite.pack_some_tokenPlan? layout site values

private theorem concat_mapM_cons
    {α : Type} (visit : α → Option TokenPlan)
    (head : α) (tail : List α) :
    (do
      let plans ← (head :: tail).mapM visit
      pure (TokenPlan.concat plans)) = (do
        let headPlan ← visit head
        let tailPlan ← (do
          let tailPlans ← tail.mapM visit
          pure (TokenPlan.concat tailPlans))
        pure (TokenPlan.append headPlan tailPlan)) := by
  rw [List.mapM_cons]
  generalize headEq : visit head = headPlan?
  cases headPlan? with
  | none => simp
  | some headPlan =>
      generalize tailEq : tail.mapM visit = tailPlans?
      cases tailPlans? with
      | none => simp
      | some tailPlans => simp

private theorem commaSeparated_mapM_cons
    {α : Type} (visit : α → Option TokenPlan)
    (head : α) (tail : List α) :
    (do
      let plans ← (head :: tail).mapM visit
      pure (TokenPlan.commaSeparated plans)) = (do
        let headPlan ← visit head
        let tailPlan ← (do
          let tailPlans ← tail.mapM visit
          pure (TokenPlan.commaTail tailPlans))
        pure (TokenPlan.append headPlan tailPlan)) := by
  rw [List.mapM_cons]
  generalize headEq : visit head = headPlan?
  cases headPlan? with
  | none => simp
  | some headPlan =>
      generalize tailEq : tail.mapM visit = tailPlans?
      cases tailPlans? with
      | none => simp
      | some tailPlans => simp

private theorem concat_bind_cons
    {α : Type} (visit : α → Option TokenPlan)
    (head : α) (tail : List α) :
    (do
      let headPlan ← visit head
      let tailPlans ← tail.mapM visit
      pure (TokenPlan.concat (headPlan :: tailPlans))) = (do
        let headPlan ← visit head
        let tailPlan ← (do
          let tailPlans ← tail.mapM visit
          pure (TokenPlan.concat tailPlans))
        pure (TokenPlan.append headPlan tailPlan)) := by
  generalize headEq : visit head = headPlan?
  cases headPlan? with
  | none => simp
  | some headPlan =>
      generalize tailEq : tail.mapM visit = tailPlans?
      cases tailPlans? with
      | none => simp
      | some tailPlans => simp

private theorem commaSeparated_bind_cons
    {α : Type} (visit : α → Option TokenPlan)
    (head : α) (tail : List α) :
    (do
      let headPlan ← visit head
      let tailPlans ← tail.mapM visit
      pure (TokenPlan.commaSeparated (headPlan :: tailPlans))) = (do
        let headPlan ← visit head
        let tailPlan ← (do
          let tailPlans ← tail.mapM visit
          pure (TokenPlan.commaTail tailPlans))
        pure (TokenPlan.append headPlan tailPlan)) := by
  generalize headEq : visit head = headPlan?
  cases headPlan? with
  | none => simp
  | some headPlan =>
      generalize tailEq : tail.mapM visit = tailPlans?
      cases tailPlans? with
      | none => simp
      | some tailPlans => simp

private theorem concat_bind_nonempty
    {α : Type} (visit : α → Option TokenPlan)
    (head tailHead : α) (tailRest : List α) :
    (do
      let headPlan ← visit head
      let tailPlans ← (tailHead :: tailRest).mapM visit
      pure (TokenPlan.concat (headPlan :: tailPlans))) = (do
        let headPlan ← visit head
        let tailPlan ← (do
          let tailHeadPlan ← visit tailHead
          let tailRestPlans ← tailRest.mapM visit
          pure (TokenPlan.concat (tailHeadPlan :: tailRestPlans)))
        pure (TokenPlan.append headPlan tailPlan)) := by
  rw [List.mapM_cons]
  generalize headEq : visit head = headPlan?
  cases headPlan? with
  | none => simp
  | some headPlan =>
      generalize tailHeadEq : visit tailHead = tailHeadPlan?
      cases tailHeadPlan? with
      | none => simp
      | some tailHeadPlan =>
          generalize tailRestEq : tailRest.mapM visit = tailRestPlans?
          cases tailRestPlans? with
          | none => simp
          | some tailRestPlans => simp

private theorem commaTail_mapM_cons
    {α : Type} (visit : α → Option TokenPlan)
    (head : α) (tail : List α) :
    (do
      let plans ← (head :: tail).mapM visit
      pure (TokenPlan.commaTail plans)) = (do
        let headPlan ← visit head
        let tailPlan ← (do
          let tailPlans ← tail.mapM visit
          pure (TokenPlan.commaTail tailPlans))
        pure (TokenPlan.append (TokenPlan.plain (.symbol .comma))
          (TokenPlan.append headPlan tailPlan))) := by
  rw [List.mapM_cons]
  generalize headEq : visit head = headPlan?
  cases headPlan? with
  | none => simp
  | some headPlan =>
      generalize tailEq : tail.mapM visit = tailPlans?
      cases tailPlans? with
      | none => simp
      | some tailPlans => simp [TokenPlan.append_assoc]

@[simp] theorem StarSite.pack_nil_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .nil).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (StarSite.pack site .nil values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.star site .nil).rhs values := by
  rw [NonterminalValue.tokenPlan?_aux]
  rw [← EbnfValue.tokenPlan?_atShape layout site.expression_eq_star]
  rw [StarSite.pack_nil_eq]
  rw [EbnfValue.tokenPlan?_star]
  exact GrammarSymbolValues.tokenPlan?_view layout
    (ProductionId.rhs_star_nil site) values

@[simp] theorem StarSite.pack_cons_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .cons).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (StarSite.pack site .cons values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.star site .cons).rhs values := by
  rw [NonterminalValue.tokenPlan?_aux]
  rw [← EbnfValue.tokenPlan?_atShape layout site.expression_eq_star]
  rw [StarSite.pack_cons_eq]
  rw [EbnfValue.tokenPlan?_star]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_star_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  change EbnfValue file tokens site.child.expression at head
  change (do
    let plans ←
      (head :: Eq.mp (ebnfValue_star_eq site.child.expression)
        (EbnfValue.atShape site.expression_eq_star tail)).mapM
        fun element => EbnfValue.tokenPlan? layout element
    pure (TokenPlan.concat plans)) = _
  rw [concat_mapM_cons
    (fun element : EbnfValue file tokens site.child.expression =>
      EbnfValue.tokenPlan? layout element)]
  rw [← EbnfValue.tokenPlan?_star_raw layout
    site.child.expression
    (EbnfValue.atShape site.expression_eq_star tail)]
  rw [EbnfValue.tokenPlan?_atShape]
  rw [← GrammarSymbolValues.tokenPlan?_view layout
    (ProductionId.rhs_star_cons site) values]
  rw [viewedEq]
  simp

@[simp] theorem StarSite.pack_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : StarSite)
    (branch : NilConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site branch).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (StarSite.pack site branch values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.star site branch).rhs values := by
  cases branch with
  | nil => exact StarSite.pack_nil_tokenPlan? layout site values
  | cons => exact StarSite.pack_cons_tokenPlan? layout site values

@[simp] theorem PlusSite.pack_one_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .one).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (PlusSite.pack site .one values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.plus site .one).rhs values := by
  rw [NonterminalValue.tokenPlan?_aux]
  rw [← EbnfValue.tokenPlan?_atShape layout site.expression_eq_plus]
  rw [PlusSite.pack_one_eq]
  rw [EbnfValue.tokenPlan?_plus]
  simp
  calc
    _ = GrammarSymbolValues.tokenPlan? layout
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_plus_one site) values) := by
        exact (GrammarSymbolValues.tokenPlan?_singleton layout
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_plus_one site) values).1).symm
    _ = GrammarSymbolValues.tokenPlan? layout
          (ProductionId.plus site .one).rhs values :=
        GrammarSymbolValues.tokenPlan?_view layout
          (ProductionId.rhs_plus_one site) values

@[simp] theorem PlusSite.pack_cons_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .cons).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (PlusSite.pack site .cons values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.plus site .cons).rhs values := by
  rw [NonterminalValue.tokenPlan?_aux]
  rw [← EbnfValue.tokenPlan?_atShape layout site.expression_eq_plus]
  rw [PlusSite.pack_cons_eq]
  rw [EbnfValue.tokenPlan?_plus]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_plus_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  change EbnfValue file tokens site.child.expression at head
  let tailElements := Eq.mp (ebnfValue_plus_eq site.child.expression)
    (EbnfValue.atShape site.expression_eq_plus tail)
  change (do
    let headPlan ← EbnfValue.tokenPlan? layout head
    let tailPlans ← (tailElements.head :: tailElements.tail).mapM
      fun element => EbnfValue.tokenPlan? layout element
    pure (TokenPlan.concat (headPlan :: tailPlans))) = _
  rw [concat_bind_nonempty
    (fun element : EbnfValue file tokens site.child.expression =>
      EbnfValue.tokenPlan? layout element)]
  rw [← EbnfValue.tokenPlan?_plus_raw layout
    site.child.expression
    (EbnfValue.atShape site.expression_eq_plus tail)]
  rw [EbnfValue.tokenPlan?_atShape]
  rw [← GrammarSymbolValues.tokenPlan?_view layout
    (ProductionId.rhs_plus_cons site) values]
  rw [viewedEq]
  simp

@[simp] theorem PlusSite.pack_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : PlusSite)
    (branch : OneConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site branch).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (PlusSite.pack site branch values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.plus site branch).rhs values := by
  cases branch with
  | one => exact PlusSite.pack_one_tokenPlan? layout site values
  | cons => exact PlusSite.pack_cons_tokenPlan? layout site values

@[simp] theorem List0Site.pack_nil_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .nil).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (List0Site.pack site .nil values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.list0 site .nil).rhs values := by
  rw [NonterminalValue.tokenPlan?_aux]
  rw [← EbnfValue.tokenPlan?_atShape layout site.expression_eq_list0]
  rw [List0Site.pack_nil_eq]
  rw [EbnfValue.tokenPlan?_list0]
  exact GrammarSymbolValues.tokenPlan?_view layout
    (ProductionId.rhs_list0_nil site) values

@[simp] theorem List0Site.pack_cons_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .cons).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (List0Site.pack site .cons values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.list0 site .cons).rhs values := by
  rw [NonterminalValue.tokenPlan?_aux]
  rw [← EbnfValue.tokenPlan?_atShape layout site.expression_eq_list0]
  rw [List0Site.pack_cons_eq]
  rw [EbnfValue.tokenPlan?_list0]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_list0_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  change EbnfValue file tokens site.element.expression at head
  let tailElements := Eq.mp
    (congrArg
      (fun element : GrammarSite =>
        List (EbnfValue file tokens element.expression))
      (Grammar.ListSite.element_list0 site)) tail
  change (do
    let plans ← (head :: tailElements).mapM
      fun element => EbnfValue.tokenPlan? layout element
    pure (TokenPlan.commaSeparated plans)) = _
  rw [commaSeparated_mapM_cons
    (fun element : EbnfValue file tokens site.element.expression =>
      EbnfValue.tokenPlan? layout element)]
  rw [EbnfValue.mapM_tokenPlan?_transport_site layout
    (Grammar.ListSite.element_list0 site) tail]
  rw [← NonterminalValue.tokenPlan?_tail layout (.list0 site) tail]
  rw [← GrammarSymbolValues.tokenPlan?_view layout
    (ProductionId.rhs_list0_cons site) values]
  rw [viewedEq]
  simp

@[simp] theorem List0Site.pack_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : List0Site)
    (branch : NilConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site branch).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (List0Site.pack site branch values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.list0 site branch).rhs values := by
  cases branch with
  | nil => exact List0Site.pack_nil_tokenPlan? layout site values
  | cons => exact List0Site.pack_cons_tokenPlan? layout site values

@[simp] theorem List1Site.pack_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : List1Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list1 site).rhs) :
    NonterminalValue.tokenPlan? layout (.aux site.site)
        (List1Site.pack site values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.list1 site).rhs values := by
  rw [NonterminalValue.tokenPlan?_aux]
  rw [← EbnfValue.tokenPlan?_atShape layout site.expression_eq_list1]
  rw [List1Site.pack_eq]
  rw [EbnfValue.tokenPlan?_list1]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_list1 site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  change EbnfValue file tokens site.element.expression at head
  let tailElements := Eq.mp
    (congrArg
      (fun element : GrammarSite =>
        List (EbnfValue file tokens element.expression))
      (Grammar.ListSite.element_list1 site)) tail
  change (do
    let headPlan ← EbnfValue.tokenPlan? layout head
    let tailPlans ← tailElements.mapM
      fun element => EbnfValue.tokenPlan? layout element
    pure (TokenPlan.commaSeparated (headPlan :: tailPlans))) = _
  rw [commaSeparated_bind_cons
    (fun element : EbnfValue file tokens site.element.expression =>
      EbnfValue.tokenPlan? layout element)]
  rw [EbnfValue.mapM_tokenPlan?_transport_site layout
    (Grammar.ListSite.element_list1 site) tail]
  rw [← NonterminalValue.tokenPlan?_tail layout (.list1 site) tail]
  rw [← GrammarSymbolValues.tokenPlan?_view layout
    (ProductionId.rhs_list1 site) values]
  rw [viewedEq]
  simp

@[simp] theorem ListSite.pack_nil_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .nil).rhs) :
    NonterminalValue.tokenPlan? layout (.tail site)
        (ListSite.pack site .nil values) =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.tail site .nil).rhs values := by
  rw [ListSite.pack_nil_eq]
  rw [NonterminalValue.tokenPlan?_tail]
  exact GrammarSymbolValues.tokenPlan?_view layout
    (ProductionId.rhs_tail_nil site) values

private theorem MatchedTerminal.commaPrefix_toPlain
    {file : WorkspaceFile} {tokens : List Token}
    (comma : MatchedTerminal file tokens (.symbol .comma))
    (rest : TokenPlan) {actual : List Token}
    (relation : TokenSlot.ListMatches
      (comma.physicalTokenPlan.append rest).slots actual) :
    TokenSlot.ListMatches
      ((TokenPlan.plain (.symbol .comma)).append rest).slots actual := by
  rcases comma with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases terminalAt with
  | retained token inRange lookup valid =>
      change TokenSlot.ListMatches
        (.required (ExpectedToken.exact token.payload token.span) ::
          rest.slots) actual at relation
      have weakened := relation.requiredHeadToPlain
      change TokenSlot.ListMatches
        (.required (ExpectedToken.plain token.payload) :: rest.slots)
        actual at weakened
      rw [matchedEvidence] at weakened
      exact weakened
  | endOfFile atEnd =>
      simp [TerminalMatches] at matchedEvidence

/-- Comma-tail packing preserves complete token evidence while weakening the
scanned comma's exact span constraint to the grammar-generated plain comma. -/
theorem ListSite.pack_cons_tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .cons).rhs)
    {actual : List Token}
    (inputEvidence : TokenPlanEvidence
      (GrammarSymbolValues.tokenPlan? layout
        (ProductionId.tail site .cons).rhs values) actual) :
    TokenPlanEvidence
      (NonterminalValue.tokenPlan? layout (.tail site)
        (ListSite.pack site .cons values)) actual := by
  rw [ListSite.pack_cons_eq]
  rw [NonterminalValue.tokenPlan?_tail]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_tail_cons site) values = viewed
  rcases viewed with ⟨comma, head, tail, restUnit⟩
  cases restUnit
  change EbnfValue file tokens site.element.expression at head
  rw [← GrammarSymbolValues.tokenPlan?_view layout
    (ProductionId.rhs_tail_cons site) values] at inputEvidence
  rw [viewedEq] at inputEvidence
  change TokenPlanEvidence
    (do
      let plans ← (head :: tail).mapM
        fun element => EbnfValue.tokenPlan? layout element
      pure (TokenPlan.commaTail plans)) actual
  rw [commaTail_mapM_cons
    (fun element : EbnfValue file tokens site.element.expression =>
      EbnfValue.tokenPlan? layout element)]
  generalize headEq : EbnfValue.tokenPlan? layout head = headPlan?
  cases headPlan? with
  | none =>
      rcases inputEvidence with ⟨plan, candidateEq, relation⟩
      simp [headEq] at candidateEq
  | some headPlan =>
      generalize tailEq : tail.mapM
        (fun value => EbnfValue.tokenPlan? layout value) = tailPlans?
      cases tailPlans? with
      | none =>
          rcases inputEvidence with ⟨plan, candidateEq, relation⟩
          simp [headEq, tailEq] at candidateEq
      | some tailPlans =>
          rcases inputEvidence with ⟨plan, candidateEq, relation⟩
          simp only [GrammarSymbolValues.tokenPlan?_cons,
            GrammarSymbolValues.tokenPlan?_nil,
            GrammarSymbolValue.tokenPlan?_terminal,
            GrammarSymbolValue.tokenPlan?_nonterminal,
            NonterminalValue.tokenPlan?_aux,
            NonterminalValue.tokenPlan?_tail] at candidateEq
          simp [headEq, tailEq] at candidateEq
          subst plan
          apply TokenPlanEvidence.some
          exact comma.commaPrefix_toPlain
            (headPlan.append (TokenPlan.commaTail tailPlans)) relation

/-- Every generated parser action preserves complete token-plan evidence.
Comma-tail cons packing performs the sole constraint weakening required by
the grammar-generated punctuation plan. -/
theorem ActionReduces.generated_tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout)
    {production : ProductionId}
    {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens production.rhs}
    {output : NonterminalValue file tokens production.lhs}
    (auxiliary : AuxiliaryProduction production)
    (reduces : ActionReduces file tokens (.actionFor production)
      origin finish input output)
    (inputEvidence : TokenPlanEvidence
      (GrammarSymbolValues.tokenPlan? layout production.rhs input)
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence
      (NonterminalValue.tokenPlan? layout production.lhs output)
      (PhysicalTokens tokens origin finish) := by
  cases reduces with
  | root rule origin finish input output reduction =>
      exact False.elim auxiliary
  | atom site origin finish input =>
      exact inputEvidence.candidate_eq
        (AtomSite.pack_tokenPlan? layout site input).symm
  | seq site origin finish input =>
      exact inputEvidence.candidate_eq
        (SequenceSite.pack_tokenPlan? layout site input).symm
  | group site origin finish input =>
      exact inputEvidence.candidate_eq
        (GroupSite.pack_tokenPlan? layout site input).symm
  | choice site branch origin finish input =>
      exact inputEvidence.candidate_eq
        (ChoiceSite.pack_tokenPlan? layout site branch input).symm
  | opt site branch origin finish input =>
      exact inputEvidence.candidate_eq
        (OptionalSite.pack_tokenPlan? layout site branch input).symm
  | star site branch origin finish input =>
      exact inputEvidence.candidate_eq
        (StarSite.pack_tokenPlan? layout site branch input).symm
  | plus site branch origin finish input =>
      exact inputEvidence.candidate_eq
        (PlusSite.pack_tokenPlan? layout site branch input).symm
  | list0 site branch origin finish input =>
      exact inputEvidence.candidate_eq
        (List0Site.pack_tokenPlan? layout site branch input).symm
  | list1 site origin finish input =>
      exact inputEvidence.candidate_eq
        (List1Site.pack_tokenPlan? layout site input).symm
  | tail site branch origin finish input =>
      cases branch with
      | nil =>
          exact inputEvidence.candidate_eq
            (ListSite.pack_nil_tokenPlan? layout site input).symm
      | cons =>
          exact ListSite.pack_cons_tokenPlanEvidence layout site input
            inputEvidence

end Solcore.Surface.Multi
