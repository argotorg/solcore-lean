import Solcore.Surface.Multi.SemanticLocation
import Solcore.Surface.Multi.ParserJudgment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

namespace LocationFragment

theorem merge_nil : merge [] = empty := by
  rfl

theorem merge_cons_as_pair
    (head : LocationFragment) (tail : List LocationFragment) :
    merge (head :: tail) = merge [head, merge tail] := by
  apply eq_of_fields <;> simp

end LocationFragment

@[simp] theorem EbnfValues.locationFragment_ofAuxiliaries
    {file : WorkspaceFile} {tokens : List Token}
    (sites : List GrammarSite)
    (values : GrammarSymbolValues file tokens
      (sites.map fun site => GrammarSymbol.nonterminal (.aux site))) :
    (EbnfValues.ofAuxiliaries sites values).locationFragment =
      GrammarSymbolValues.locationFragment
        (sites.map fun site => GrammarSymbol.nonterminal (.aux site)) values := by
  induction sites with
  | nil =>
      simp only [List.map] at values ⊢
      cases values
      rw [EbnfValues.locationFragment_nil_raw]
      rfl
  | cons site rest inductionHypothesis =>
      simp only [List.map] at values ⊢
      rcases values with ⟨head, tail⟩
      rw [EbnfValues.locationFragment_cons_raw]
      rw [EbnfValues.ofAuxiliaries_cons_eq]
      rw [inductionHypothesis]
      rfl

@[simp] theorem EbnfValue.locationFragment_star_raw
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (value : EbnfValue file tokens (.star child)) :
    value.locationFragment =
      LocationFragment.merge
        ((Eq.mp (ebnfValue_star_eq child) value).map fun element =>
          element.locationFragment) := by
  unfold EbnfValue.locationFragment
  rw [EbnfLocationFamily]

@[simp] theorem EbnfValue.locationFragment_plus_raw
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (value : EbnfValue file tokens (.plus child)) :
    value.locationFragment =
      let elements := Eq.mp (ebnfValue_plus_eq child) value
      LocationFragment.merge
        (elements.head.locationFragment ::
          elements.tail.map fun element => element.locationFragment) := by
  unfold EbnfValue.locationFragment
  rw [EbnfLocationFamily]

@[simp] theorem EbnfValue.locationFragment_list0_raw
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (value : EbnfValue file tokens (.list0 child)) :
    value.locationFragment =
      LocationFragment.merge
        ((Eq.mp (ebnfValue_list0_eq child) value).map fun element =>
          element.locationFragment) := by
  unfold EbnfValue.locationFragment
  rw [EbnfLocationFamily]

@[simp] theorem EbnfValue.locationFragment_list1_raw
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (value : EbnfValue file tokens (.list1 child)) :
    value.locationFragment =
      let elements := Eq.mp (ebnfValue_list1_eq child) value
      LocationFragment.merge
        (elements.head.locationFragment ::
          elements.tail.map fun element => element.locationFragment) := by
  unfold EbnfValue.locationFragment
  rw [EbnfLocationFamily]

theorem EbnfValue.merge_locationFragments_transport_site
    {file : WorkspaceFile} {tokens : List Token}
    {left right : GrammarSite}
    (equality : left = right)
    (values : List (EbnfValue file tokens left.expression)) :
    LocationFragment.merge
        ((Eq.mp
          (congrArg
            (fun site : GrammarSite =>
              List (EbnfValue file tokens site.expression))
            equality)
          values).map fun value => value.locationFragment) =
      LocationFragment.merge
        (values.map fun value => value.locationFragment) := by
  cases equality
  rfl

/-- Unpacking a source-rule root preserves the complete semantic fragment of
its canonical singleton input. -/
@[simp] theorem RootAction.unpack_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (values : GrammarSymbolValues file tokens
      (ProductionId.root rule).rhs) :
    (RootAction.unpack rule values).locationFragment =
      GrammarSymbolValues.locationFragment
        (ProductionId.root rule).rhs values := by
  rw [RootAction.unpack_eq]
  rw [EbnfValue.locationFragment_atShape]
  let viewed := GrammarSymbolValues.view
    (ProductionId.rhs_root rule) values
  calc
    _ = GrammarSymbolValues.locationFragment
          [.nonterminal (.aux (GrammarSite.root rule))] viewed := by
        exact (GrammarSymbolValues.locationFragment_singleton
          (.nonterminal (.aux (GrammarSite.root rule))) viewed.1).symm
    _ = GrammarSymbolValues.locationFragment
          (ProductionId.root rule).rhs values :=
        GrammarSymbolValues.locationFragment_view
          (ProductionId.rhs_root rule) values

@[simp] theorem AtomSite.pack_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : AtomSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.atom site).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (AtomSite.pack site values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.atom site).rhs values := by
  cases atomEq : site.atom with
  | terminal terminal =>
      rw [NonterminalValue.locationFragment_aux]
      rw [← EbnfValue.locationFragment_atShape site.expression_eq_atom]
      rw [← EbnfValue.locationFragment_transport
        (congrArg EbnfExpr.atom atomEq)]
      change (AtomSite.packAtAtom site (.terminal terminal) atomEq values).locationFragment = _
      rw [AtomSite.pack_terminal_eq]
      rw [EbnfValue.locationFragment_terminalAtom]
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_atom site) values
      let atomValue := Eq.mp
        (congrArg (GrammarSymbolValue file tokens) site.symbol_eq) viewed.1
      calc
        _ = GrammarSymbolValue.locationFragment
              (EbnfAtom.terminal terminal).grammarSymbol
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                (congrArg EbnfAtom.grammarSymbol atomEq)) atomValue) := rfl
        _ = GrammarSymbolValue.locationFragment site.atom.grammarSymbol
              atomValue :=
            GrammarSymbolValue.locationFragment_transport
              (congrArg EbnfAtom.grammarSymbol atomEq) atomValue
        _ = GrammarSymbolValue.locationFragment site.symbol viewed.1 := by
            exact GrammarSymbolValue.locationFragment_transport
              site.symbol_eq viewed.1
        _ = GrammarSymbolValues.locationFragment [site.symbol] viewed := by
            exact (GrammarSymbolValues.locationFragment_singleton
              site.symbol viewed.1).symm
        _ = GrammarSymbolValues.locationFragment
              (ProductionId.atom site).rhs values :=
            GrammarSymbolValues.locationFragment_view
              (ProductionId.rhs_atom site) values
  | nonterminal rule =>
      rw [NonterminalValue.locationFragment_aux]
      rw [← EbnfValue.locationFragment_atShape site.expression_eq_atom]
      rw [← EbnfValue.locationFragment_transport
        (congrArg EbnfExpr.atom atomEq)]
      change (AtomSite.packAtAtom site (.nonterminal rule) atomEq values).locationFragment = _
      rw [AtomSite.pack_rule_eq]
      rw [EbnfValue.locationFragment_ruleAtom]
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_atom site) values
      let atomValue := Eq.mp
        (congrArg (GrammarSymbolValue file tokens) site.symbol_eq) viewed.1
      calc
        _ = GrammarSymbolValue.locationFragment
              (EbnfAtom.nonterminal rule).grammarSymbol
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                (congrArg EbnfAtom.grammarSymbol atomEq)) atomValue) := rfl
        _ = GrammarSymbolValue.locationFragment site.atom.grammarSymbol
              atomValue :=
            GrammarSymbolValue.locationFragment_transport
              (congrArg EbnfAtom.grammarSymbol atomEq) atomValue
        _ = GrammarSymbolValue.locationFragment site.symbol viewed.1 := by
            exact GrammarSymbolValue.locationFragment_transport
              site.symbol_eq viewed.1
        _ = GrammarSymbolValues.locationFragment [site.symbol] viewed := by
            exact (GrammarSymbolValues.locationFragment_singleton
              site.symbol viewed.1).symm
        _ = GrammarSymbolValues.locationFragment
              (ProductionId.atom site).rhs values :=
            GrammarSymbolValues.locationFragment_view
              (ProductionId.rhs_atom site) values

@[simp] theorem SequenceSite.pack_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : SequenceSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.seq site).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (SequenceSite.pack site values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.seq site).rhs values := by
  rw [NonterminalValue.locationFragment_aux]
  rw [← EbnfValue.locationFragment_atShape site.expression_eq_sequence]
  rw [SequenceSite.pack_eq]
  rw [EbnfValue.locationFragment_sequence]
  rw [EbnfValues.locationFragment_ofAuxiliaries]
  exact GrammarSymbolValues.locationFragment_view
    (ProductionId.rhs_seq site) values

@[simp] theorem GroupSite.pack_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : GroupSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.group site).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (GroupSite.pack site values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.group site).rhs values := by
  rw [NonterminalValue.locationFragment_aux]
  rw [← EbnfValue.locationFragment_atShape site.expression_eq_group]
  rw [GroupSite.pack_eq]
  rw [EbnfValue.locationFragment_group]
  calc
    _ = GrammarSymbolValues.locationFragment
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_group site) values) := by
        exact (GrammarSymbolValues.locationFragment_singleton
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_group site) values).1).symm
    _ = GrammarSymbolValues.locationFragment
          (ProductionId.group site).rhs values :=
        GrammarSymbolValues.locationFragment_view
          (ProductionId.rhs_group site) values

@[simp] theorem ChoiceSite.pack_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : ChoiceSite) (branch : Fin site.branchCount)
    (values : GrammarSymbolValues file tokens
      (ProductionId.choice site branch).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (ChoiceSite.pack site branch values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.choice site branch).rhs values := by
  rw [NonterminalValue.locationFragment_aux]
  rw [← EbnfValue.locationFragment_atShape site.expression_eq_choice]
  rw [ChoiceSite.pack_eq]
  rw [EbnfValue.locationFragment_choice]
  rw [EbnfValue.locationFragment_transport]
  calc
    _ = GrammarSymbolValues.locationFragment
          [.nonterminal (.aux (site.branch branch))]
          (GrammarSymbolValues.view
            (ProductionId.rhs_choice site branch) values) := by
        exact (GrammarSymbolValues.locationFragment_singleton
          (.nonterminal (.aux (site.branch branch)))
          (GrammarSymbolValues.view
            (ProductionId.rhs_choice site branch) values).1).symm
    _ = GrammarSymbolValues.locationFragment
          (ProductionId.choice site branch).rhs values :=
        GrammarSymbolValues.locationFragment_view
          (ProductionId.rhs_choice site branch) values

@[simp] theorem OptionalSite.pack_none_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .none).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (OptionalSite.pack site .none values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.opt site .none).rhs values := by
  rw [NonterminalValue.locationFragment_aux]
  rw [← EbnfValue.locationFragment_atShape site.expression_eq_optional]
  rw [OptionalSite.pack_none_eq]
  rw [EbnfValue.locationFragment_optional_none]
  exact GrammarSymbolValues.locationFragment_view
    (ProductionId.rhs_opt_none site) values

@[simp] theorem OptionalSite.pack_some_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .some).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (OptionalSite.pack site .some values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.opt site .some).rhs values := by
  rw [NonterminalValue.locationFragment_aux]
  rw [← EbnfValue.locationFragment_atShape site.expression_eq_optional]
  rw [OptionalSite.pack_some_eq]
  rw [EbnfValue.locationFragment_optional_some]
  calc
    _ = GrammarSymbolValues.locationFragment
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_opt_some site) values) := by
        exact (GrammarSymbolValues.locationFragment_singleton
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_opt_some site) values).1).symm
    _ = GrammarSymbolValues.locationFragment
          (ProductionId.opt site .some).rhs values :=
        GrammarSymbolValues.locationFragment_view
          (ProductionId.rhs_opt_some site) values

@[simp] theorem StarSite.pack_nil_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .nil).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (StarSite.pack site .nil values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.star site .nil).rhs values := by
  rw [NonterminalValue.locationFragment_aux]
  rw [← EbnfValue.locationFragment_atShape site.expression_eq_star]
  rw [StarSite.pack_nil_eq]
  rw [EbnfValue.locationFragment_star]
  exact GrammarSymbolValues.locationFragment_view
    (ProductionId.rhs_star_nil site) values

@[simp] theorem StarSite.pack_cons_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .cons).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (StarSite.pack site .cons values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.star site .cons).rhs values := by
  rw [NonterminalValue.locationFragment_aux]
  rw [← EbnfValue.locationFragment_atShape site.expression_eq_star]
  rw [StarSite.pack_cons_eq]
  rw [EbnfValue.locationFragment_star]
  simp only [List.map]
  rw [LocationFragment.merge_cons_as_pair]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_star_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  change LocationFragment.merge [
      head.locationFragment,
      LocationFragment.merge
        ((Eq.mp (ebnfValue_star_eq site.child.expression)
          (EbnfValue.atShape site.expression_eq_star tail)).map
            fun element => element.locationFragment)] = _
  calc
    _ = LocationFragment.merge [
          head.locationFragment,
          (EbnfValue.atShape site.expression_eq_star tail).locationFragment] := by
        rw [EbnfValue.locationFragment_star_raw]
    _ = LocationFragment.merge [
          head.locationFragment,
          EbnfValue.locationFragment tail] := by
        rw [EbnfValue.locationFragment_atShape]
    _ = GrammarSymbolValues.locationFragment
          [.nonterminal (.aux site.child), .nonterminal (.aux site.site)]
          (head, (tail, ())) := by
        change LocationFragment.merge [
          head.locationFragment,
          EbnfValue.locationFragment tail] =
            LocationFragment.merge [
              head.locationFragment,
              GrammarSymbolValues.locationFragment
                [.nonterminal (.aux site.site)] (tail, ())]
        rw [GrammarSymbolValues.locationFragment_singleton]
        apply congrArg (fun fragment => LocationFragment.merge [
          GrammarSymbolValue.locationFragment
            (.nonterminal (.aux site.child)) head,
          fragment])
        exact (GrammarSymbolValue.locationFragment_nonterminal
          (.aux site.site) tail).symm
    _ = GrammarSymbolValues.locationFragment
          (ProductionId.star site .cons).rhs values :=
        by
          simpa [viewedEq] using
            (GrammarSymbolValues.locationFragment_view
              (ProductionId.rhs_star_cons site) values)

@[simp] theorem PlusSite.pack_one_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .one).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (PlusSite.pack site .one values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.plus site .one).rhs values := by
  rw [NonterminalValue.locationFragment_aux]
  rw [← EbnfValue.locationFragment_atShape site.expression_eq_plus]
  rw [PlusSite.pack_one_eq]
  rw [EbnfValue.locationFragment_plus]
  simp only [List.map]
  rw [LocationFragment.merge_cons_as_pair]
  rw [LocationFragment.merge_nil]
  rw [LocationFragment.merge_empty_right]
  calc
    _ = GrammarSymbolValues.locationFragment
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_plus_one site) values) := by
        exact (GrammarSymbolValues.locationFragment_singleton
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_plus_one site) values).1).symm
    _ = GrammarSymbolValues.locationFragment
          (ProductionId.plus site .one).rhs values :=
        GrammarSymbolValues.locationFragment_view
          (ProductionId.rhs_plus_one site) values

@[simp] theorem PlusSite.pack_cons_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .cons).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (PlusSite.pack site .cons values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.plus site .cons).rhs values := by
  rw [NonterminalValue.locationFragment_aux]
  rw [← EbnfValue.locationFragment_atShape site.expression_eq_plus]
  rw [PlusSite.pack_cons_eq]
  rw [EbnfValue.locationFragment_plus]
  simp only [List.map]
  rw [LocationFragment.merge_cons_as_pair]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_plus_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  change LocationFragment.merge [
      head.locationFragment,
      LocationFragment.merge
        ((Eq.mp (ebnfValue_plus_eq site.child.expression)
          (EbnfValue.atShape site.expression_eq_plus tail)).head.locationFragment ::
        (Eq.mp (ebnfValue_plus_eq site.child.expression)
          (EbnfValue.atShape site.expression_eq_plus tail)).tail.map
            fun element => element.locationFragment)] = _
  calc
    _ = LocationFragment.merge [
          head.locationFragment,
          (EbnfValue.atShape site.expression_eq_plus tail).locationFragment] := by
        rw [EbnfValue.locationFragment_plus_raw]
    _ = LocationFragment.merge [
          head.locationFragment,
          EbnfValue.locationFragment tail] := by
        rw [EbnfValue.locationFragment_atShape]
    _ = GrammarSymbolValues.locationFragment
          [.nonterminal (.aux site.child), .nonterminal (.aux site.site)]
          (head, (tail, ())) := by
        change LocationFragment.merge [
          head.locationFragment,
          EbnfValue.locationFragment tail] =
            LocationFragment.merge [
              head.locationFragment,
              GrammarSymbolValues.locationFragment
                [.nonterminal (.aux site.site)] (tail, ())]
        rw [GrammarSymbolValues.locationFragment_singleton]
        apply congrArg (fun fragment => LocationFragment.merge [
          GrammarSymbolValue.locationFragment
            (.nonterminal (.aux site.child)) head,
          fragment])
        exact (GrammarSymbolValue.locationFragment_nonterminal
          (.aux site.site) tail).symm
    _ = GrammarSymbolValues.locationFragment
          (ProductionId.plus site .cons).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.locationFragment_view
            (ProductionId.rhs_plus_cons site) values)

@[simp] theorem List0Site.pack_nil_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .nil).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (List0Site.pack site .nil values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.list0 site .nil).rhs values := by
  rw [NonterminalValue.locationFragment_aux]
  rw [← EbnfValue.locationFragment_atShape site.expression_eq_list0]
  rw [List0Site.pack_nil_eq]
  rw [EbnfValue.locationFragment_list0]
  exact GrammarSymbolValues.locationFragment_view
    (ProductionId.rhs_list0_nil site) values

@[simp] theorem List0Site.pack_cons_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .cons).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (List0Site.pack site .cons values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.list0 site .cons).rhs values := by
  rw [NonterminalValue.locationFragment_aux]
  rw [← EbnfValue.locationFragment_atShape site.expression_eq_list0]
  rw [List0Site.pack_cons_eq]
  rw [EbnfValue.locationFragment_list0]
  simp only [List.map]
  rw [LocationFragment.merge_cons_as_pair]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_list0_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  change LocationFragment.merge [
      head.locationFragment,
      LocationFragment.merge
        ((Eq.mp
          (congrArg
            (fun element : GrammarSite =>
              List (EbnfValue file tokens element.expression))
            (Grammar.ListSite.element_list0 site))
          tail).map fun element => element.locationFragment)] = _
  calc
    _ = LocationFragment.merge [
          head.locationFragment,
          LocationFragment.merge
            (tail.map fun element => element.locationFragment)] := by
        rw [EbnfValue.merge_locationFragments_transport_site
          (Grammar.ListSite.element_list0 site) tail]
    _ = GrammarSymbolValues.locationFragment
          [.nonterminal (.aux site.element),
            .nonterminal (.tail (.list0 site))]
          (head, (tail, ())) := by
        change LocationFragment.merge [
          head.locationFragment,
          LocationFragment.merge
            (tail.map fun element => element.locationFragment)] =
            LocationFragment.merge [
              head.locationFragment,
              GrammarSymbolValues.locationFragment
                [.nonterminal (.tail (.list0 site))] (tail, ())]
        rw [GrammarSymbolValues.locationFragment_singleton]
        apply congrArg (fun fragment => LocationFragment.merge [
          GrammarSymbolValue.locationFragment
            (.nonterminal (.aux site.element)) head,
          fragment])
        exact (GrammarSymbolValue.locationFragment_nonterminal
          (.tail (.list0 site)) tail).symm
    _ = GrammarSymbolValues.locationFragment
          (ProductionId.list0 site .cons).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.locationFragment_view
            (ProductionId.rhs_list0_cons site) values)

@[simp] theorem List1Site.pack_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : List1Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list1 site).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (List1Site.pack site values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.list1 site).rhs values := by
  rw [NonterminalValue.locationFragment_aux]
  rw [← EbnfValue.locationFragment_atShape site.expression_eq_list1]
  rw [List1Site.pack_eq]
  rw [EbnfValue.locationFragment_list1]
  rw [LocationFragment.merge_cons_as_pair]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_list1 site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  change LocationFragment.merge [
      head.locationFragment,
      LocationFragment.merge
        ((Eq.mp
          (congrArg
            (fun element : GrammarSite =>
              List (EbnfValue file tokens element.expression))
            (Grammar.ListSite.element_list1 site))
          tail).map fun element => element.locationFragment)] = _
  calc
    _ = LocationFragment.merge [
          head.locationFragment,
          LocationFragment.merge
            (tail.map fun element => element.locationFragment)] := by
        rw [EbnfValue.merge_locationFragments_transport_site
          (Grammar.ListSite.element_list1 site) tail]
    _ = GrammarSymbolValues.locationFragment
          [.nonterminal (.aux site.element),
            .nonterminal (.tail (.list1 site))]
          (head, (tail, ())) := by
        change LocationFragment.merge [
          head.locationFragment,
          LocationFragment.merge
            (tail.map fun element => element.locationFragment)] =
            LocationFragment.merge [
              head.locationFragment,
              GrammarSymbolValues.locationFragment
                [.nonterminal (.tail (.list1 site))] (tail, ())]
        rw [GrammarSymbolValues.locationFragment_singleton]
        apply congrArg (fun fragment => LocationFragment.merge [
          GrammarSymbolValue.locationFragment
            (.nonterminal (.aux site.element)) head,
          fragment])
        exact (GrammarSymbolValue.locationFragment_nonterminal
          (.tail (.list1 site)) tail).symm
    _ = GrammarSymbolValues.locationFragment
          (ProductionId.list1 site).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.locationFragment_view
            (ProductionId.rhs_list1 site) values)

@[simp] theorem ListSite.pack_nil_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .nil).rhs) :
    NonterminalValue.locationFragment (.tail site)
        (ListSite.pack site .nil values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.tail site .nil).rhs values := by
  rw [ListSite.pack_nil_eq]
  rw [NonterminalValue.locationFragment_tail]
  simp only [List.map]
  rw [LocationFragment.merge_nil]
  exact GrammarSymbolValues.locationFragment_view
    (ProductionId.rhs_tail_nil site) values

theorem ListSite.pack_cons_rhs_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .cons).rhs) :
    GrammarSymbolValues.locationFragment
        (ProductionId.tail site .cons).rhs values =
      LocationFragment.merge [
        (GrammarSymbolValues.view
          (ProductionId.rhs_tail_cons site) values).1.locationFragment,
        NonterminalValue.locationFragment (.tail site)
          (ListSite.pack site .cons values)] := by
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_tail_cons site) values = viewed
  rcases viewed with ⟨comma, head, tail, restUnit⟩
  cases restUnit
  rw [ListSite.pack_cons_eq]
  rw [viewedEq]
  rw [NonterminalValue.locationFragment_tail]
  simp only [List.map]
  calc
    _ = GrammarSymbolValues.locationFragment
          [.terminal (.symbol .comma),
            .nonterminal (.aux site.element),
            .nonterminal (.tail site)]
          (comma, (head, (tail, ()))) := by
        symm
        simpa [viewedEq] using
          (GrammarSymbolValues.locationFragment_view
            (ProductionId.rhs_tail_cons site) values)
    _ = LocationFragment.merge [
          comma.locationFragment,
          LocationFragment.merge
            (EbnfValue.locationFragment head ::
              tail.map fun element => element.locationFragment)] := by
        change LocationFragment.merge [
          comma.locationFragment,
          GrammarSymbolValues.locationFragment
            [.nonterminal (.aux site.element),
              .nonterminal (.tail site)]
            (head, (tail, ()))] = _
        apply congrArg (fun fragment => LocationFragment.merge [
          GrammarSymbolValue.locationFragment
            (.terminal (.symbol .comma)) comma,
          fragment])
        change LocationFragment.merge [
          GrammarSymbolValue.locationFragment
            (.nonterminal (.aux site.element)) head,
          GrammarSymbolValues.locationFragment
            [.nonterminal (.tail site)] (tail, ())] =
          LocationFragment.merge
            (EbnfValue.locationFragment head ::
              tail.map fun element => element.locationFragment)
        rw [GrammarSymbolValues.locationFragment_singleton]
        rw [GrammarSymbolValue.locationFragment_nonterminal
          (.aux site.element) head]
        rw [GrammarSymbolValue.locationFragment_nonterminal
          (.tail site) tail]
        exact (LocationFragment.merge_cons_as_pair
          (EbnfValue.locationFragment head)
          (tail.map fun element => element.locationFragment)).symm

@[simp] theorem OptionalSite.pack_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : OptionalSite) (branch : OptionalBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site branch).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (OptionalSite.pack site branch values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.opt site branch).rhs values := by
  cases branch with
  | none => exact OptionalSite.pack_none_locationFragment site values
  | some => exact OptionalSite.pack_some_locationFragment site values

@[simp] theorem StarSite.pack_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : StarSite) (branch : NilConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site branch).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (StarSite.pack site branch values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.star site branch).rhs values := by
  cases branch with
  | nil => exact StarSite.pack_nil_locationFragment site values
  | cons => exact StarSite.pack_cons_locationFragment site values

@[simp] theorem PlusSite.pack_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : PlusSite) (branch : OneConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site branch).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (PlusSite.pack site branch values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.plus site branch).rhs values := by
  cases branch with
  | one => exact PlusSite.pack_one_locationFragment site values
  | cons => exact PlusSite.pack_cons_locationFragment site values

@[simp] theorem List0Site.pack_locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (site : List0Site) (branch : NilConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site branch).rhs) :
    NonterminalValue.locationFragment (.aux site.site)
        (List0Site.pack site branch values) =
      GrammarSymbolValues.locationFragment
        (ProductionId.list0 site branch).rhs values := by
  cases branch with
  | nil => exact List0Site.pack_nil_locationFragment site values
  | cons => exact List0Site.pack_cons_locationFragment site values

/-- The location equation for a generated production.  Every generated
production preserves the full RHS fragment except comma-tail extension, whose
comma remains in the input fragment as a ghost anchor. -/
def AuxiliaryActionLocationEquation
    {file : WorkspaceFile} {tokens : List Token} :
    (production : ProductionId) →
      GrammarSymbolValues file tokens production.rhs →
      NonterminalValue file tokens production.lhs → Prop
  | .root _, _, _ => False
  | .atom site, input, output =>
      NonterminalValue.locationFragment (.aux site.site) output =
        GrammarSymbolValues.locationFragment
          (ProductionId.atom site).rhs input
  | .seq site, input, output =>
      NonterminalValue.locationFragment (.aux site.site) output =
        GrammarSymbolValues.locationFragment
          (ProductionId.seq site).rhs input
  | .group site, input, output =>
      NonterminalValue.locationFragment (.aux site.site) output =
        GrammarSymbolValues.locationFragment
          (ProductionId.group site).rhs input
  | .choice site branch, input, output =>
      NonterminalValue.locationFragment (.aux site.site) output =
        GrammarSymbolValues.locationFragment
          (ProductionId.choice site branch).rhs input
  | .opt site branch, input, output =>
      NonterminalValue.locationFragment (.aux site.site) output =
        GrammarSymbolValues.locationFragment
          (ProductionId.opt site branch).rhs input
  | .star site branch, input, output =>
      NonterminalValue.locationFragment (.aux site.site) output =
        GrammarSymbolValues.locationFragment
          (ProductionId.star site branch).rhs input
  | .plus site branch, input, output =>
      NonterminalValue.locationFragment (.aux site.site) output =
        GrammarSymbolValues.locationFragment
          (ProductionId.plus site branch).rhs input
  | .list0 site branch, input, output =>
      NonterminalValue.locationFragment (.aux site.site) output =
        GrammarSymbolValues.locationFragment
          (ProductionId.list0 site branch).rhs input
  | .list1 site, input, output =>
      NonterminalValue.locationFragment (.aux site.site) output =
        GrammarSymbolValues.locationFragment
          (ProductionId.list1 site).rhs input
  | .tail site .nil, input, output =>
      NonterminalValue.locationFragment (.tail site) output =
        GrammarSymbolValues.locationFragment
          (ProductionId.tail site .nil).rhs input
  | .tail site .cons, input, output =>
      GrammarSymbolValues.locationFragment
          (ProductionId.tail site .cons).rhs input =
        LocationFragment.merge [
          (GrammarSymbolValues.view
            (ProductionId.rhs_tail_cons site) input).1.locationFragment,
          NonterminalValue.locationFragment (.tail site) output]

/-- Every non-root action reduction satisfies its exact semantic location
equation. -/
theorem ActionReduces.auxiliary_locationEquation
    {file : WorkspaceFile} {tokens : List Token}
    {production : ProductionId}
    {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens production.rhs}
    {output : NonterminalValue file tokens production.lhs}
    (auxiliary : AuxiliaryProduction production)
    (reduces : ActionReduces file tokens (.actionFor production)
      origin finish input output) :
    AuxiliaryActionLocationEquation production input output := by
  cases reduces with
  | root rule origin finish input output reduction =>
      exact False.elim auxiliary
  | atom site origin finish input =>
      exact AtomSite.pack_locationFragment site input
  | seq site origin finish input =>
      exact SequenceSite.pack_locationFragment site input
  | group site origin finish input =>
      exact GroupSite.pack_locationFragment site input
  | choice site branch origin finish input =>
      exact ChoiceSite.pack_locationFragment site branch input
  | opt site branch origin finish input =>
      exact OptionalSite.pack_locationFragment site branch input
  | star site branch origin finish input =>
      exact StarSite.pack_locationFragment site branch input
  | plus site branch origin finish input =>
      exact PlusSite.pack_locationFragment site branch input
  | list0 site branch origin finish input =>
      exact List0Site.pack_locationFragment site branch input
  | list1 site origin finish input =>
      exact List1Site.pack_locationFragment site input
  | tail site branch origin finish input =>
      cases branch with
      | nil => exact ListSite.pack_nil_locationFragment site input
      | cons => exact ListSite.pack_cons_rhs_locationFragment site input

end Solcore.Surface.Multi
