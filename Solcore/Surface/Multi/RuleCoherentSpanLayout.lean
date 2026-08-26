import Solcore.Surface.Multi.RuleCoherentIntervalLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- A grammar-indexed choice of source spans retained in source order. -/
structure RuleSpanLayout where
  spans : (rule : GrammarRuleId) → RuleValue rule → List SourceSpan
  safe : ∀ {rule : GrammarRuleId} (value : RuleValue rule),
    spans rule value ≠ [] →
      rule ≠ .optionalComma ∧ rule ≠ .module

namespace FocusedSpanEvidence

/-- A nonempty focused trace proves that its enclosing parser interval retains
at least one physical token. -/
theorem occupied_of_spans_ne_nil
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens} {spans : List SourceSpan}
    (evidence : FocusedSpanEvidence file tokens origin finish spans)
    (nonempty : spans ≠ []) :
    origin.val < Nat.min finish.val tokens.length := by
  rcases evidence with ⟨anchors, anchorSpans, inside, _ordered⟩
  cases anchors with
  | nil =>
      exact False.elim (nonempty anchorSpans.symm)
  | cons anchor tail =>
      have anchorInside := inside anchor (by simp)
      have anchorOccupied := Nat.lt_min.mp anchor.occupied.2
      have outerFinish := Nat.lt_of_le_of_lt anchorInside.1
        (Nat.lt_of_lt_of_le anchorOccupied.1 anchorInside.2)
      have outerLength := Nat.lt_of_le_of_lt anchorInside.1
        anchorOccupied.2
      exact Nat.lt_min.mpr ⟨outerFinish, outerLength⟩

end FocusedSpanEvidence

def LayoutSpanFamily
    (focus : RuleSpanLayout) (file : WorkspaceFile) (tokens : List Token) :
    (index : EbnfValueIndex) → EbnfFamily file tokens index →
      List SourceSpan
  | .expression (.atom (.terminal terminal)), matched =>
      let matched := Eq.mp (ebnfValue_atom_terminal_eq terminal) matched
      if terminal = .endOfFile then [] else [matched.span]
  | .expression (.atom (.nonterminal rule)), value =>
      focus.spans rule
        (Eq.mp (ebnfValue_atom_nonterminal_eq rule) value)
  | .expression (.sequence children), values =>
      LayoutSpanFamily focus file tokens (.expressions children)
        (Eq.mp (ebnfValue_sequence_eq children) values)
  | .expression (.group child), value =>
      LayoutSpanFamily focus file tokens (.expression child)
        (Eq.mp (ebnfValue_group_eq child) value)
  | .expression (.choice branches), value =>
      let selected := Eq.mp (ebnfValue_choice_eq branches) value
      LayoutSpanFamily focus file tokens
        (.expression (branches.get selected.1)) selected.2
  | .expression (.optional child), value =>
      match Eq.mp (ebnfValue_optional_eq child) value with
      | none => []
      | some childValue =>
          LayoutSpanFamily focus file tokens (.expression child) childValue
  | .expression (.star child), values =>
      (Eq.mp (ebnfValue_star_eq child) values).flatMap fun value =>
        LayoutSpanFamily focus file tokens (.expression child) value
  | .expression (.plus child), values =>
      let viewed := Eq.mp (ebnfValue_plus_eq child) values
      LayoutSpanFamily focus file tokens (.expression child) viewed.head ++
        viewed.tail.flatMap fun value =>
          LayoutSpanFamily focus file tokens (.expression child) value
  | .expression (.list0 child), values =>
      (Eq.mp (ebnfValue_list0_eq child) values).flatMap fun value =>
        LayoutSpanFamily focus file tokens (.expression child) value
  | .expression (.list1 child), values =>
      let viewed := Eq.mp (ebnfValue_list1_eq child) values
      LayoutSpanFamily focus file tokens (.expression child) viewed.head ++
        viewed.tail.flatMap fun value =>
          LayoutSpanFamily focus file tokens (.expression child) value
  | .expressions [], _ => []
  | .expressions (child :: rest), values =>
      let viewed := Eq.mp (ebnfValues_cons_eq child rest) values
      LayoutSpanFamily focus file tokens (.expression child) viewed.1 ++
        LayoutSpanFamily focus file tokens (.expressions rest) viewed.2
termination_by index => index.measure
decreasing_by
  all_goals
    first
    | exact measure_sequence_lt _
    | exact measure_choice_get_lt _ _
    | exact measure_unary_child_lt .group _
    | exact measure_unary_child_lt .optional _
    | exact measure_unary_child_lt .star _
    | exact measure_unary_child_lt .plus _
    | exact measure_unary_child_lt .list0 _
    | exact measure_unary_child_lt .list1 _
    | exact measure_cons_head_lt _ _
    | exact measure_cons_tail_lt _ _

abbrev EbnfValue.layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) {expression : EbnfExpr}
    (value : EbnfValue file tokens expression) : List SourceSpan :=
  LayoutSpanFamily focus file tokens (.expression expression) value

abbrev EbnfValues.layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) {expressions : List EbnfExpr}
    (values : EbnfValues file tokens expressions) : List SourceSpan :=
  LayoutSpanFamily focus file tokens (.expressions expressions) values

@[simp] theorem EbnfValue.layoutSpans_terminalAtom
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    (EbnfValue.terminalAtom terminal matched).layoutSpans focus =
      if terminal = .endOfFile then [] else [matched.span] := by
  simp [EbnfValue.layoutSpans, LayoutSpanFamily,
    EbnfValue.terminalAtom, cast_cast]

@[simp] theorem EbnfValue.layoutSpans_ruleAtom
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (rule : GrammarRuleId)
    (value : RuleValue rule) :
    (EbnfValue.ruleAtom (file := file) (tokens := tokens)
      rule value).layoutSpans focus = focus.spans rule value := by
  simp [EbnfValue.layoutSpans, LayoutSpanFamily,
    EbnfValue.ruleAtom, cast_cast]

@[simp] theorem EbnfValue.layoutSpans_transport
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) {left right : EbnfExpr}
    (shape : left = right) (value : EbnfValue file tokens left) :
    (EbnfValue.transport shape value).layoutSpans focus =
      value.layoutSpans focus := by
  cases shape
  rfl

@[simp] theorem EbnfValue.layoutSpans_atShape
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) {site : GrammarSite} {expression : EbnfExpr}
    (shape : site.expression = expression)
    (value : EbnfValue file tokens site.expression) :
    (EbnfValue.atShape shape value).layoutSpans focus =
      value.layoutSpans focus := by
  exact EbnfValue.layoutSpans_transport focus shape value

@[simp] theorem EbnfValue.layoutSpans_sequence
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (children : List EbnfExpr)
    (values : EbnfValues file tokens children) :
    (EbnfValue.sequence children values).layoutSpans focus =
      values.layoutSpans focus := by
  simp [EbnfValue.layoutSpans, EbnfValues.layoutSpans,
    LayoutSpanFamily, EbnfValue.sequence, cast_cast]

@[simp] theorem EbnfValue.layoutSpans_group
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (child : EbnfExpr)
    (value : EbnfValue file tokens child) :
    (EbnfValue.group child value).layoutSpans focus =
      value.layoutSpans focus := by
  simp [EbnfValue.layoutSpans, LayoutSpanFamily,
    EbnfValue.group, cast_cast]

@[simp] theorem EbnfValue.layoutSpans_optional_none
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (child : EbnfExpr) :
    (EbnfValue.optional (file := file) (tokens := tokens)
      child none).layoutSpans focus = [] := by
  simp [EbnfValue.layoutSpans, LayoutSpanFamily,
    EbnfValue.optional, cast_cast]

@[simp] theorem EbnfValue.layoutSpans_optional_some
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (child : EbnfExpr)
    (value : EbnfValue file tokens child) :
    (EbnfValue.optional child (some value)).layoutSpans focus =
      value.layoutSpans focus := by
  simp [EbnfValue.layoutSpans, LayoutSpanFamily,
    EbnfValue.optional, cast_cast]

@[simp] theorem EbnfValue.layoutSpans_choice
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (branches : List EbnfExpr)
    (value : (branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch)) :
    (EbnfValue.choice branches value).layoutSpans focus =
      value.2.layoutSpans focus := by
  have viewed : Eq.mp (ebnfValue_choice_eq branches)
      (EbnfValue.choice branches value) = value := by
    unfold EbnfValue.choice
    change cast _ (cast _ value) = value
    rw [cast_cast]
    apply cast_eq
  unfold EbnfValue.layoutSpans
  rw [LayoutSpanFamily, viewed]

@[simp] theorem EbnfValue.layoutSpans_star
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (child : EbnfExpr)
    (values : List (EbnfValue file tokens child)) :
    (EbnfValue.star child values).layoutSpans focus =
      values.flatMap fun value => value.layoutSpans focus := by
  simp [EbnfValue.layoutSpans, LayoutSpanFamily,
    EbnfValue.star, cast_cast]

@[simp] theorem EbnfValue.layoutSpans_plus
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (child : EbnfExpr)
    (values : NonemptyList (EbnfValue file tokens child)) :
    (EbnfValue.plus child values).layoutSpans focus =
      values.head.layoutSpans focus ++
        values.tail.flatMap fun value => value.layoutSpans focus := by
  simp [EbnfValue.layoutSpans, LayoutSpanFamily,
    EbnfValue.plus, cast_cast]

@[simp] theorem EbnfValue.layoutSpans_list0
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (child : EbnfExpr)
    (values : List (EbnfValue file tokens child)) :
    (EbnfValue.list0 child values).layoutSpans focus =
      values.flatMap fun value => value.layoutSpans focus := by
  simp [EbnfValue.layoutSpans, LayoutSpanFamily,
    EbnfValue.list0, cast_cast]

@[simp] theorem EbnfValue.layoutSpans_list1
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (child : EbnfExpr)
    (values : NonemptyList (EbnfValue file tokens child)) :
    (EbnfValue.list1 child values).layoutSpans focus =
      values.head.layoutSpans focus ++
        values.tail.flatMap fun value => value.layoutSpans focus := by
  simp [EbnfValue.layoutSpans, LayoutSpanFamily,
    EbnfValue.list1, cast_cast]

@[simp] theorem EbnfValues.layoutSpans_nil
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) :
    (EbnfValues.nil (file := file) (tokens := tokens)).layoutSpans focus =
      [] := by
  simp [EbnfValues.layoutSpans, LayoutSpanFamily, EbnfValues.nil]

@[simp] theorem EbnfValues.layoutSpans_cons
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (child : EbnfExpr) (rest : List EbnfExpr)
    (head : EbnfValue file tokens child)
    (tail : EbnfValues file tokens rest) :
    (EbnfValues.cons child rest head tail).layoutSpans focus =
      head.layoutSpans focus ++ tail.layoutSpans focus := by
  simp [EbnfValues.layoutSpans, LayoutSpanFamily,
    EbnfValues.cons, cast_cast]

@[simp] theorem EbnfValues.layoutSpans_nil_raw
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (values : EbnfValues file tokens []) :
    values.layoutSpans focus = [] := by
  unfold EbnfValues.layoutSpans
  rw [LayoutSpanFamily]

@[simp] theorem EbnfValues.layoutSpans_cons_raw
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (child : EbnfExpr) (rest : List EbnfExpr)
    (values : EbnfValues file tokens (child :: rest)) :
    values.layoutSpans focus =
      (Eq.mp (ebnfValues_cons_eq child rest) values).1.layoutSpans focus ++
        (Eq.mp (ebnfValues_cons_eq child rest) values).2.layoutSpans focus := by
  unfold EbnfValues.layoutSpans
  rw [LayoutSpanFamily]

theorem EbnfValue.layoutSpans_sequence_raw
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (children : List EbnfExpr)
    (value : EbnfValue file tokens (.sequence children)) :
    value.layoutSpans focus =
      (Eq.mp (ebnfValue_sequence_eq children) value).layoutSpans focus := by
  unfold EbnfValue.layoutSpans
  rw [LayoutSpanFamily]

@[simp] theorem EbnfValue.layoutSpans_star_raw
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (child : EbnfExpr)
    (value : EbnfValue file tokens (.star child)) :
    value.layoutSpans focus =
      (Eq.mp (ebnfValue_star_eq child) value).flatMap fun element =>
        element.layoutSpans focus := by
  unfold EbnfValue.layoutSpans
  rw [LayoutSpanFamily]

@[simp] theorem EbnfValue.layoutSpans_plus_raw
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (child : EbnfExpr)
    (value : EbnfValue file tokens (.plus child)) :
    value.layoutSpans focus =
      let elements := Eq.mp (ebnfValue_plus_eq child) value
      elements.head.layoutSpans focus ++
        elements.tail.flatMap fun element => element.layoutSpans focus := by
  unfold EbnfValue.layoutSpans
  rw [LayoutSpanFamily]

theorem EbnfValue.flatMap_layoutSpans_transport_site
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) {left right : GrammarSite}
    (equality : left = right)
    (values : List (EbnfValue file tokens left.expression)) :
    (Eq.mp
        (congrArg
          (fun site : GrammarSite =>
            List (EbnfValue file tokens site.expression))
          equality)
        values).flatMap (fun value => value.layoutSpans focus) =
      values.flatMap fun value => value.layoutSpans focus := by
  cases equality
  rfl

def NonterminalValue.layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) :
    (symbol : NonterminalSymbol) → NonterminalValue file tokens symbol →
      List SourceSpan
  | .rule rule, value => focus.spans rule value
  | .aux _site, value => EbnfValue.layoutSpans focus value
  | .tail _site, values =>
      values.flatMap fun value => EbnfValue.layoutSpans focus value

def GrammarSymbolValue.layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) :
    (symbol : GrammarSymbol) → GrammarSymbolValue file tokens symbol →
      List SourceSpan
  | .terminal terminal, matched =>
      if terminal = .endOfFile then [] else [matched.span]
  | .nonterminal symbol, value =>
      NonterminalValue.layoutSpans focus symbol value

def GrammarSymbolValues.layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) :
    (symbols : List GrammarSymbol) → GrammarSymbolValues file tokens symbols →
      List SourceSpan
  | [], _values => []
  | symbol :: rest, values =>
      GrammarSymbolValue.layoutSpans focus symbol values.1 ++
        GrammarSymbolValues.layoutSpans focus rest values.2

@[simp] theorem NonterminalValue.layoutSpans_rule
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (rule : GrammarRuleId)
    (value : RuleValue rule) :
    NonterminalValue.layoutSpans (file := file) (tokens := tokens)
        focus (.rule rule) value =
      focus.spans rule value := by
  rfl

@[simp] theorem NonterminalValue.layoutSpans_aux
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : GrammarSite)
    (value : EbnfValue file tokens site.expression) :
    NonterminalValue.layoutSpans focus (.aux site) value =
      value.layoutSpans focus := by
  rfl

@[simp] theorem NonterminalValue.layoutSpans_tail
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : ListSite)
    (values : List (EbnfValue file tokens site.element.expression)) :
    NonterminalValue.layoutSpans focus (.tail site) values =
      values.flatMap fun value => value.layoutSpans focus := by
  rfl

@[simp] theorem GrammarSymbolValue.layoutSpans_terminal
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    GrammarSymbolValue.layoutSpans focus (.terminal terminal) matched =
      if terminal = .endOfFile then [] else [matched.span] := by
  rfl

@[simp] theorem GrammarSymbolValue.layoutSpans_nonterminal
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (symbol : NonterminalSymbol)
    (value : NonterminalValue file tokens symbol) :
    GrammarSymbolValue.layoutSpans focus (.nonterminal symbol) value =
      NonterminalValue.layoutSpans focus symbol value := by
  rfl

@[simp] theorem GrammarSymbolValue.layoutSpans_transport
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) {left right : GrammarSymbol}
    (shape : left = right) (value : GrammarSymbolValue file tokens left) :
    GrammarSymbolValue.layoutSpans focus right
        (Eq.mp (congrArg (GrammarSymbolValue file tokens) shape) value) =
      GrammarSymbolValue.layoutSpans focus left value := by
  cases shape
  rfl

@[simp] theorem GrammarSymbolValues.layoutSpans_append
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) {left right : List GrammarSymbol}
    (leftValues : GrammarSymbolValues file tokens left)
    (rightValues : GrammarSymbolValues file tokens right) :
    GrammarSymbolValues.layoutSpans focus (left ++ right)
        (GrammarSymbolValues.append leftValues rightValues) =
      GrammarSymbolValues.layoutSpans focus left leftValues ++
        GrammarSymbolValues.layoutSpans focus right rightValues := by
  induction left with
  | nil => rfl
  | cons symbol rest inductionHypothesis =>
      rcases leftValues with ⟨head, tail⟩
      change GrammarSymbolValue.layoutSpans focus symbol head ++
          GrammarSymbolValues.layoutSpans focus (rest ++ right)
            (GrammarSymbolValues.append tail rightValues) = _
      rw [inductionHypothesis tail]
      exact (List.append_assoc _ _ _).symm

@[simp] theorem GrammarSymbolValues.layoutSpans_transport
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) {left right : List GrammarSymbol}
    (shape : left = right) (values : GrammarSymbolValues file tokens left) :
    GrammarSymbolValues.layoutSpans focus right
        (GrammarSymbolValues.transport shape values) =
      GrammarSymbolValues.layoutSpans focus left values := by
  cases shape
  rfl

@[simp] theorem GrammarSymbolValues.layoutSpans_singleton
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (symbol : GrammarSymbol)
    (value : GrammarSymbolValue file tokens symbol) :
    GrammarSymbolValues.layoutSpans focus [symbol] (value, ()) =
      GrammarSymbolValue.layoutSpans focus symbol value := by
  simp [GrammarSymbolValues.layoutSpans]

@[simp] theorem GrammarSymbolValues.layoutSpans_view
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) {production : ProductionId}
    {canonicalRhs : List GrammarSymbol}
    (layout : production.rhs = canonicalRhs)
    (values : GrammarSymbolValues file tokens production.rhs) :
    GrammarSymbolValues.layoutSpans focus canonicalRhs
        (GrammarSymbolValues.view layout values) =
      GrammarSymbolValues.layoutSpans focus production.rhs values := by
  unfold GrammarSymbolValues.view
  exact GrammarSymbolValues.layoutSpans_transport focus layout values

@[simp] theorem EbnfValues.layoutSpans_ofAuxiliaries
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (sites : List GrammarSite)
    (values : GrammarSymbolValues file tokens
      (sites.map fun site => GrammarSymbol.nonterminal (.aux site))) :
    (EbnfValues.ofAuxiliaries sites values).layoutSpans focus =
      GrammarSymbolValues.layoutSpans focus
        (sites.map fun site => GrammarSymbol.nonterminal (.aux site)) values := by
  induction sites with
  | nil =>
      simp only [List.map] at values ⊢
      cases values
      rw [EbnfValues.layoutSpans_nil_raw]
      rfl
  | cons site rest inductionHypothesis =>
      simp only [List.map] at values ⊢
      rcases values with ⟨head, tail⟩
      rw [EbnfValues.layoutSpans_cons_raw]
      rw [EbnfValues.ofAuxiliaries_cons_eq]
      rw [inductionHypothesis]
      rfl

@[simp] theorem RootAction.unpack_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (rule : GrammarRuleId)
    (values : GrammarSymbolValues file tokens
      (ProductionId.root rule).rhs) :
    (RootAction.unpack rule values).layoutSpans focus =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.root rule).rhs values := by
  rw [RootAction.unpack_eq]
  rw [EbnfValue.layoutSpans_atShape]
  let viewed := GrammarSymbolValues.view
    (ProductionId.rhs_root rule) values
  calc
    _ = GrammarSymbolValues.layoutSpans focus
          [.nonterminal (.aux (GrammarSite.root rule))] viewed := by
        exact (GrammarSymbolValues.layoutSpans_singleton focus
          (.nonterminal (.aux (GrammarSite.root rule))) viewed.1).symm
    _ = GrammarSymbolValues.layoutSpans focus
          (ProductionId.root rule).rhs values :=
        GrammarSymbolValues.layoutSpans_view focus
          (ProductionId.rhs_root rule) values

abbrev PrefixValues.layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (item : ContextualItemKey tokens)
    (values : PrefixValues file tokens item) : List SourceSpan :=
  GrammarSymbolValues.layoutSpans focus
    (item.raw.production.rhs.take item.raw.dot.val) values

@[simp] theorem PrefixValues.layoutSpans_zeroValue
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (item : ContextualItemKey tokens)
    (zero : item.raw.dot.val = 0) :
    PrefixValues.layoutSpans focus item
      (PrefixValues.zeroValue (file := file) item zero) = [] := by
  unfold PrefixValues.layoutSpans
  unfold PrefixValues.zeroValue
  rw [GrammarSymbolValues.layoutSpans_transport]
  rfl

@[simp] theorem PrefixValues.layoutSpans_scanValue
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (before after : ContextualItemKey tokens)
    (terminal : TerminalSymbol) (next : NextSymbol before.raw (.terminal terminal))
    (matched : MatchedTerminal file tokens terminal)
    (advance : AdvanceItem before.raw matched.cursor.afterBoundary after.raw)
    (priorValues : PrefixValues file tokens before) :
    PrefixValues.layoutSpans focus after
        (PrefixValues.scanValue before after terminal next matched advance
          priorValues) =
      PrefixValues.layoutSpans focus before priorValues ++
        (if terminal = .endOfFile then [] else [matched.span]) := by
  unfold PrefixValues.layoutSpans PrefixValues.scanValue
  rw [GrammarSymbolValues.layoutSpans_transport]
  rw [GrammarSymbolValues.layoutSpans_append]
  simp [GrammarSymbolValues.layoutSpans,
    GrammarSymbolValue.layoutSpans]

@[simp] theorem PrefixValues.layoutSpans_completeValue
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (waiting finished after : ContextualItemKey tokens)
    (next : NextSymbol waiting.raw
      (.nonterminal finished.raw.production.lhs))
    (advance : AdvanceItem waiting.raw finished.raw.current after.raw)
    (priorValues : PrefixValues file tokens waiting)
    (childValue : NonterminalValue file tokens
      finished.raw.production.lhs) :
    PrefixValues.layoutSpans focus after
        (PrefixValues.completeValue waiting finished after next advance
          priorValues childValue) =
      PrefixValues.layoutSpans focus waiting priorValues ++
        NonterminalValue.layoutSpans focus
          finished.raw.production.lhs childValue := by
  unfold PrefixValues.layoutSpans PrefixValues.completeValue
  rw [GrammarSymbolValues.layoutSpans_transport]
  rw [GrammarSymbolValues.layoutSpans_append]
  simp [GrammarSymbolValues.layoutSpans,
    GrammarSymbolValue.layoutSpans]

@[simp] theorem PrefixValues.layoutSpans_fullValue
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (item : ContextualItemKey tokens)
    (complete : CompleteItem item.raw)
    (priorValues : PrefixValues file tokens item) :
    GrammarSymbolValues.layoutSpans focus item.raw.production.rhs
        (PrefixValues.fullValue item complete priorValues) =
      PrefixValues.layoutSpans focus item priorValues := by
  unfold PrefixValues.layoutSpans PrefixValues.fullValue
  rw [GrammarSymbolValues.layoutSpans_transport]

@[simp] theorem AtomSite.pack_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout)
    (site : AtomSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.atom site).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (AtomSite.pack site values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.atom site).rhs values := by
  cases atomEq : site.atom with
  | terminal terminal =>
      rw [NonterminalValue.layoutSpans_aux]
      rw [← EbnfValue.layoutSpans_atShape focus
        site.expression_eq_atom]
      rw [← EbnfValue.layoutSpans_transport focus
        (congrArg EbnfExpr.atom atomEq)]
      change EbnfValue.layoutSpans focus
        (AtomSite.packAtAtom site (.terminal terminal) atomEq values) = _
      rw [AtomSite.pack_terminal_eq]
      rw [EbnfValue.layoutSpans_terminalAtom]
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_atom site) values
      let atomValue := Eq.mp
        (congrArg (GrammarSymbolValue file tokens) site.symbol_eq) viewed.1
      calc
        _ = GrammarSymbolValue.layoutSpans focus
              (EbnfAtom.terminal terminal).grammarSymbol
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                (congrArg EbnfAtom.grammarSymbol atomEq)) atomValue) := rfl
        _ = GrammarSymbolValue.layoutSpans focus
              site.atom.grammarSymbol atomValue :=
            GrammarSymbolValue.layoutSpans_transport focus
              (congrArg EbnfAtom.grammarSymbol atomEq) atomValue
        _ = GrammarSymbolValue.layoutSpans focus site.symbol
              viewed.1 :=
            GrammarSymbolValue.layoutSpans_transport focus
              site.symbol_eq viewed.1
        _ = GrammarSymbolValues.layoutSpans focus [site.symbol]
              viewed := by
            exact (GrammarSymbolValues.layoutSpans_singleton focus
              site.symbol viewed.1).symm
        _ = GrammarSymbolValues.layoutSpans focus
              (ProductionId.atom site).rhs values :=
            GrammarSymbolValues.layoutSpans_view focus
              (ProductionId.rhs_atom site) values
  | nonterminal rule =>
      rw [NonterminalValue.layoutSpans_aux]
      rw [← EbnfValue.layoutSpans_atShape focus
        site.expression_eq_atom]
      rw [← EbnfValue.layoutSpans_transport focus
        (congrArg EbnfExpr.atom atomEq)]
      change EbnfValue.layoutSpans focus
        (AtomSite.packAtAtom site (.nonterminal rule) atomEq values) = _
      rw [AtomSite.pack_rule_eq]
      rw [EbnfValue.layoutSpans_ruleAtom]
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_atom site) values
      let atomValue := Eq.mp
        (congrArg (GrammarSymbolValue file tokens) site.symbol_eq) viewed.1
      calc
        _ = GrammarSymbolValue.layoutSpans focus
              (EbnfAtom.nonterminal rule).grammarSymbol
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                (congrArg EbnfAtom.grammarSymbol atomEq)) atomValue) := rfl
        _ = GrammarSymbolValue.layoutSpans focus
              site.atom.grammarSymbol atomValue :=
            GrammarSymbolValue.layoutSpans_transport focus
              (congrArg EbnfAtom.grammarSymbol atomEq) atomValue
        _ = GrammarSymbolValue.layoutSpans focus site.symbol
              viewed.1 :=
            GrammarSymbolValue.layoutSpans_transport focus
              site.symbol_eq viewed.1
        _ = GrammarSymbolValues.layoutSpans focus [site.symbol]
              viewed := by
            exact (GrammarSymbolValues.layoutSpans_singleton focus
              site.symbol viewed.1).symm
        _ = GrammarSymbolValues.layoutSpans focus
              (ProductionId.atom site).rhs values :=
            GrammarSymbolValues.layoutSpans_view focus
              (ProductionId.rhs_atom site) values

@[simp] theorem SequenceSite.pack_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : SequenceSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.seq site).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (SequenceSite.pack site values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.seq site).rhs values := by
  rw [NonterminalValue.layoutSpans_aux]
  rw [← EbnfValue.layoutSpans_atShape focus
    site.expression_eq_sequence]
  rw [SequenceSite.pack_eq]
  rw [EbnfValue.layoutSpans_sequence]
  rw [EbnfValues.layoutSpans_ofAuxiliaries]
  exact GrammarSymbolValues.layoutSpans_view focus
    (ProductionId.rhs_seq site) values

@[simp] theorem GroupSite.pack_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : GroupSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.group site).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (GroupSite.pack site values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.group site).rhs values := by
  rw [NonterminalValue.layoutSpans_aux]
  rw [← EbnfValue.layoutSpans_atShape focus
    site.expression_eq_group]
  rw [GroupSite.pack_eq]
  rw [EbnfValue.layoutSpans_group]
  calc
    _ = GrammarSymbolValues.layoutSpans focus
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_group site) values) := by
        exact (GrammarSymbolValues.layoutSpans_singleton focus
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_group site) values).1).symm
    _ = GrammarSymbolValues.layoutSpans focus
          (ProductionId.group site).rhs values :=
        GrammarSymbolValues.layoutSpans_view focus
          (ProductionId.rhs_group site) values

@[simp] theorem ChoiceSite.pack_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : ChoiceSite)
    (branch : Fin site.branchCount)
    (values : GrammarSymbolValues file tokens
      (ProductionId.choice site branch).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (ChoiceSite.pack site branch values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.choice site branch).rhs values := by
  rw [NonterminalValue.layoutSpans_aux]
  rw [← EbnfValue.layoutSpans_atShape focus
    site.expression_eq_choice]
  rw [ChoiceSite.pack_eq]
  rw [EbnfValue.layoutSpans_choice]
  rw [EbnfValue.layoutSpans_transport]
  calc
    _ = GrammarSymbolValues.layoutSpans focus
          [.nonterminal (.aux (site.branch branch))]
          (GrammarSymbolValues.view
            (ProductionId.rhs_choice site branch) values) := by
        exact (GrammarSymbolValues.layoutSpans_singleton focus
          (.nonterminal (.aux (site.branch branch)))
          (GrammarSymbolValues.view
            (ProductionId.rhs_choice site branch) values).1).symm
    _ = GrammarSymbolValues.layoutSpans focus
          (ProductionId.choice site branch).rhs values :=
        GrammarSymbolValues.layoutSpans_view focus
          (ProductionId.rhs_choice site branch) values

@[simp] theorem OptionalSite.pack_none_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .none).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (OptionalSite.pack site .none values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.opt site .none).rhs values := by
  rw [NonterminalValue.layoutSpans_aux]
  rw [← EbnfValue.layoutSpans_atShape focus
    site.expression_eq_optional]
  rw [OptionalSite.pack_none_eq]
  rw [EbnfValue.layoutSpans_optional_none]
  exact GrammarSymbolValues.layoutSpans_view focus
    (ProductionId.rhs_opt_none site) values

@[simp] theorem OptionalSite.pack_some_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .some).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (OptionalSite.pack site .some values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.opt site .some).rhs values := by
  rw [NonterminalValue.layoutSpans_aux]
  rw [← EbnfValue.layoutSpans_atShape focus
    site.expression_eq_optional]
  rw [OptionalSite.pack_some_eq]
  rw [EbnfValue.layoutSpans_optional_some]
  calc
    _ = GrammarSymbolValues.layoutSpans focus
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_opt_some site) values) := by
        exact (GrammarSymbolValues.layoutSpans_singleton focus
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_opt_some site) values).1).symm
    _ = GrammarSymbolValues.layoutSpans focus
          (ProductionId.opt site .some).rhs values :=
        GrammarSymbolValues.layoutSpans_view focus
          (ProductionId.rhs_opt_some site) values

@[simp] theorem OptionalSite.pack_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : OptionalSite)
    (branch : OptionalBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site branch).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (OptionalSite.pack site branch values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.opt site branch).rhs values := by
  cases branch with
  | none => exact OptionalSite.pack_none_layoutSpans focus site values
  | some => exact OptionalSite.pack_some_layoutSpans focus site values

@[simp] theorem StarSite.pack_nil_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .nil).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (StarSite.pack site .nil values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.star site .nil).rhs values := by
  rw [NonterminalValue.layoutSpans_aux]
  rw [← EbnfValue.layoutSpans_atShape focus site.expression_eq_star]
  rw [StarSite.pack_nil_eq]
  rw [EbnfValue.layoutSpans_star]
  exact GrammarSymbolValues.layoutSpans_view focus
    (ProductionId.rhs_star_nil site) values

@[simp] theorem StarSite.pack_cons_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .cons).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (StarSite.pack site .cons values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.star site .cons).rhs values := by
  rw [NonterminalValue.layoutSpans_aux]
  rw [← EbnfValue.layoutSpans_atShape focus site.expression_eq_star]
  rw [StarSite.pack_cons_eq]
  rw [EbnfValue.layoutSpans_star]
  simp only [List.flatMap_cons]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_star_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  change head.layoutSpans focus ++
      (Eq.mp (ebnfValue_star_eq site.child.expression)
        (EbnfValue.atShape site.expression_eq_star tail)).flatMap
          (fun element => element.layoutSpans focus) = _
  calc
    _ = head.layoutSpans focus ++
          EbnfValue.layoutSpans focus
            (EbnfValue.atShape site.expression_eq_star tail) := by
        rw [EbnfValue.layoutSpans_star_raw]
    _ = GrammarSymbolValue.layoutSpans focus
          (.nonterminal (.aux site.child)) head ++
          EbnfValue.layoutSpans focus tail := by
        rw [EbnfValue.layoutSpans_atShape]
    _ = GrammarSymbolValues.layoutSpans focus
          [.nonterminal (.aux site.child), .nonterminal (.aux site.site)]
          (head, (tail, ())) := by
        change _ = GrammarSymbolValue.layoutSpans focus
          (.nonterminal (.aux site.child)) head ++
            (GrammarSymbolValue.layoutSpans focus
              (.nonterminal (.aux site.site)) tail ++ [])
        simp only [GrammarSymbolValue.layoutSpans_nonterminal,
          NonterminalValue.layoutSpans_aux, List.append_nil]
    _ = GrammarSymbolValues.layoutSpans focus
          (ProductionId.star site .cons).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.layoutSpans_view focus
            (ProductionId.rhs_star_cons site) values)

@[simp] theorem StarSite.pack_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : StarSite)
    (branch : NilConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site branch).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (StarSite.pack site branch values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.star site branch).rhs values := by
  cases branch with
  | nil => exact StarSite.pack_nil_layoutSpans focus site values
  | cons => exact StarSite.pack_cons_layoutSpans focus site values

@[simp] theorem PlusSite.pack_one_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .one).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (PlusSite.pack site .one values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.plus site .one).rhs values := by
  rw [NonterminalValue.layoutSpans_aux]
  rw [← EbnfValue.layoutSpans_atShape focus site.expression_eq_plus]
  rw [PlusSite.pack_one_eq]
  rw [EbnfValue.layoutSpans_plus]
  simp only [List.flatMap_nil, List.append_nil]
  calc
    _ = GrammarSymbolValues.layoutSpans focus
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_plus_one site) values) := by
        exact (GrammarSymbolValues.layoutSpans_singleton focus
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_plus_one site) values).1).symm
    _ = GrammarSymbolValues.layoutSpans focus
          (ProductionId.plus site .one).rhs values :=
        GrammarSymbolValues.layoutSpans_view focus
          (ProductionId.rhs_plus_one site) values

@[simp] theorem PlusSite.pack_cons_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .cons).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (PlusSite.pack site .cons values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.plus site .cons).rhs values := by
  rw [NonterminalValue.layoutSpans_aux]
  rw [← EbnfValue.layoutSpans_atShape focus site.expression_eq_plus]
  rw [PlusSite.pack_cons_eq]
  rw [EbnfValue.layoutSpans_plus]
  simp only [List.flatMap_cons]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_plus_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  rw [← EbnfValue.layoutSpans_plus_raw focus
    site.child.expression
    (EbnfValue.atShape site.expression_eq_plus tail)]
  rw [EbnfValue.layoutSpans_atShape]
  calc
    _ = GrammarSymbolValues.layoutSpans focus
          [.nonterminal (.aux site.child), .nonterminal (.aux site.site)]
          (head, (tail, ())) := by
        change _ = GrammarSymbolValue.layoutSpans focus
          (.nonterminal (.aux site.child)) head ++
            (GrammarSymbolValue.layoutSpans focus
              (.nonterminal (.aux site.site)) tail ++ [])
        simp only [GrammarSymbolValue.layoutSpans_nonterminal,
          NonterminalValue.layoutSpans_aux, List.append_nil]
    _ = GrammarSymbolValues.layoutSpans focus
          (ProductionId.plus site .cons).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.layoutSpans_view focus
            (ProductionId.rhs_plus_cons site) values)

@[simp] theorem PlusSite.pack_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : PlusSite)
    (branch : OneConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site branch).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (PlusSite.pack site branch values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.plus site branch).rhs values := by
  cases branch with
  | one => exact PlusSite.pack_one_layoutSpans focus site values
  | cons => exact PlusSite.pack_cons_layoutSpans focus site values

@[simp] theorem List0Site.pack_nil_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .nil).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (List0Site.pack site .nil values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.list0 site .nil).rhs values := by
  rw [NonterminalValue.layoutSpans_aux]
  rw [← EbnfValue.layoutSpans_atShape focus site.expression_eq_list0]
  rw [List0Site.pack_nil_eq]
  rw [EbnfValue.layoutSpans_list0]
  exact GrammarSymbolValues.layoutSpans_view focus
    (ProductionId.rhs_list0_nil site) values

@[simp] theorem List0Site.pack_cons_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .cons).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (List0Site.pack site .cons values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.list0 site .cons).rhs values := by
  rw [NonterminalValue.layoutSpans_aux]
  rw [← EbnfValue.layoutSpans_atShape focus site.expression_eq_list0]
  rw [List0Site.pack_cons_eq]
  rw [EbnfValue.layoutSpans_list0]
  simp only [List.flatMap_cons]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_list0_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  rw [EbnfValue.flatMap_layoutSpans_transport_site focus
    (Grammar.ListSite.element_list0 site) tail]
  calc
    _ = GrammarSymbolValues.layoutSpans focus
          [.nonterminal (.aux site.element),
            .nonterminal (.tail (.list0 site))]
          (head, (tail, ())) := by
        change _ = GrammarSymbolValue.layoutSpans focus
          (.nonterminal (.aux site.element)) head ++
            (GrammarSymbolValue.layoutSpans focus
              (.nonterminal (.tail (.list0 site))) tail ++ [])
        simp only [GrammarSymbolValue.layoutSpans_nonterminal,
          NonterminalValue.layoutSpans_aux,
          NonterminalValue.layoutSpans_tail, List.append_nil]
    _ = GrammarSymbolValues.layoutSpans focus
          (ProductionId.list0 site .cons).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.layoutSpans_view focus
            (ProductionId.rhs_list0_cons site) values)

@[simp] theorem List0Site.pack_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : List0Site)
    (branch : NilConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site branch).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (List0Site.pack site branch values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.list0 site branch).rhs values := by
  cases branch with
  | nil => exact List0Site.pack_nil_layoutSpans focus site values
  | cons => exact List0Site.pack_cons_layoutSpans focus site values

@[simp] theorem List1Site.pack_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : List1Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list1 site).rhs) :
    NonterminalValue.layoutSpans focus (.aux site.site)
        (List1Site.pack site values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.list1 site).rhs values := by
  rw [NonterminalValue.layoutSpans_aux]
  rw [← EbnfValue.layoutSpans_atShape focus site.expression_eq_list1]
  rw [List1Site.pack_eq]
  rw [EbnfValue.layoutSpans_list1]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_list1 site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  rw [EbnfValue.flatMap_layoutSpans_transport_site focus
    (Grammar.ListSite.element_list1 site) tail]
  calc
    _ = GrammarSymbolValues.layoutSpans focus
          [.nonterminal (.aux site.element),
            .nonterminal (.tail (.list1 site))]
          (head, (tail, ())) := by
        change _ = GrammarSymbolValue.layoutSpans focus
          (.nonterminal (.aux site.element)) head ++
            (GrammarSymbolValue.layoutSpans focus
              (.nonterminal (.tail (.list1 site))) tail ++ [])
        simp only [GrammarSymbolValue.layoutSpans_nonterminal,
          NonterminalValue.layoutSpans_aux,
          NonterminalValue.layoutSpans_tail, List.append_nil]
    _ = GrammarSymbolValues.layoutSpans focus
          (ProductionId.list1 site).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.layoutSpans_view focus
            (ProductionId.rhs_list1 site) values)

@[simp] theorem ListSite.pack_nil_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .nil).rhs) :
    NonterminalValue.layoutSpans focus (.tail site)
        (ListSite.pack site .nil values) =
      GrammarSymbolValues.layoutSpans focus
        (ProductionId.tail site .nil).rhs values := by
  rw [ListSite.pack_nil_eq]
  rw [NonterminalValue.layoutSpans_tail]
  simp only [List.flatMap_nil]
  exact GrammarSymbolValues.layoutSpans_view focus
    (ProductionId.rhs_tail_nil site) values

theorem ListSite.pack_cons_rhs_layoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout) (site : ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .cons).rhs) :
    GrammarSymbolValues.layoutSpans focus
        (ProductionId.tail site .cons).rhs values =
      GrammarSymbolValue.layoutSpans focus (.terminal (.symbol .comma))
        (GrammarSymbolValues.view
          (ProductionId.rhs_tail_cons site) values).1 ++
        NonterminalValue.layoutSpans focus (.tail site)
          (ListSite.pack site .cons values) := by
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_tail_cons site) values = viewed
  rcases viewed with ⟨comma, head, tail, restUnit⟩
  cases restUnit
  rw [ListSite.pack_cons_eq]
  rw [viewedEq]
  rw [NonterminalValue.layoutSpans_tail]
  calc
    _ = GrammarSymbolValues.layoutSpans focus
          [.terminal (.symbol .comma),
            .nonterminal (.aux site.element),
            .nonterminal (.tail site)]
          (comma, (head, (tail, ()))) := by
        symm
        simpa [viewedEq] using
          (GrammarSymbolValues.layoutSpans_view focus
            (ProductionId.rhs_tail_cons site) values)
    _ = [comma.span] ++
          (head.layoutSpans focus ++
            tail.flatMap fun element => element.layoutSpans focus) := by
        change [comma.span] ++
            (GrammarSymbolValue.layoutSpans focus
              (.nonterminal (.aux site.element)) head ++
              (GrammarSymbolValue.layoutSpans focus
                (.nonterminal (.tail site)) tail ++ [])) = _
        simp only [GrammarSymbolValue.layoutSpans_nonterminal,
          NonterminalValue.layoutSpans_aux,
          NonterminalValue.layoutSpans_tail, List.append_nil]

theorem auxiliary_layoutSpans_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanLayout)
    {production : ProductionId}
    {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens production.rhs}
    {output : NonterminalValue file tokens production.lhs}
    (auxiliary : AuxiliaryProduction production)
    (reduces : ActionReduces file tokens (.actionFor production)
      origin finish input output) :
    (NonterminalValue.layoutSpans focus production.lhs output).Sublist
      (GrammarSymbolValues.layoutSpans focus production.rhs input) := by
  cases reduces with
  | root rule origin finish input output reduction =>
      exact False.elim auxiliary
  | atom site origin finish input =>
      change (NonterminalValue.layoutSpans focus (.aux site.site)
        (AtomSite.pack site input)).Sublist _
      rw [AtomSite.pack_layoutSpans focus site input]
      exact List.Sublist.refl _
  | seq site origin finish input =>
      change (NonterminalValue.layoutSpans focus (.aux site.site)
        (SequenceSite.pack site input)).Sublist _
      rw [SequenceSite.pack_layoutSpans focus site input]
      exact List.Sublist.refl _
  | group site origin finish input =>
      change (NonterminalValue.layoutSpans focus (.aux site.site)
        (GroupSite.pack site input)).Sublist _
      rw [GroupSite.pack_layoutSpans focus site input]
      exact List.Sublist.refl _
  | choice site branch origin finish input =>
      change (NonterminalValue.layoutSpans focus (.aux site.site)
        (ChoiceSite.pack site branch input)).Sublist _
      rw [ChoiceSite.pack_layoutSpans focus site branch input]
      exact List.Sublist.refl _
  | opt site branch origin finish input =>
      change (NonterminalValue.layoutSpans focus (.aux site.site)
        (OptionalSite.pack site branch input)).Sublist _
      rw [OptionalSite.pack_layoutSpans focus site branch input]
      exact List.Sublist.refl _
  | star site branch origin finish input =>
      change (NonterminalValue.layoutSpans focus (.aux site.site)
        (StarSite.pack site branch input)).Sublist _
      rw [StarSite.pack_layoutSpans focus site branch input]
      exact List.Sublist.refl _
  | plus site branch origin finish input =>
      change (NonterminalValue.layoutSpans focus (.aux site.site)
        (PlusSite.pack site branch input)).Sublist _
      rw [PlusSite.pack_layoutSpans focus site branch input]
      exact List.Sublist.refl _
  | list0 site branch origin finish input =>
      change (NonterminalValue.layoutSpans focus (.aux site.site)
        (List0Site.pack site branch input)).Sublist _
      rw [List0Site.pack_layoutSpans focus site branch input]
      exact List.Sublist.refl _
  | list1 site origin finish input =>
      change (NonterminalValue.layoutSpans focus (.aux site.site)
        (List1Site.pack site input)).Sublist _
      rw [List1Site.pack_layoutSpans focus site input]
      exact List.Sublist.refl _
  | tail site branch origin finish input =>
      cases branch with
      | nil =>
          change (NonterminalValue.layoutSpans focus (.tail site)
            (ListSite.pack site .nil input)).Sublist _
          rw [ListSite.pack_nil_layoutSpans focus site input]
          exact List.Sublist.refl _
      | cons =>
          change (NonterminalValue.layoutSpans focus (.tail site)
            (ListSite.pack site .cons input)).Sublist _
          rw [ListSite.pack_cons_rhs_layoutSpans focus site input]
          exact List.sublist_append_right _ _

private def PrefixLayoutSpanMotive
    (focus : RuleSpanLayout)
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (owned : TokensOwnedBy file tokens)
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    (coherent : CoherentPrefix file tokens memo correct final item values)
    (trace : SourceAnchorTrace file tokens)
    (_carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace) : Prop :=
  FocusedSpanEvidence file tokens item.raw.origin item.raw.current
    (PrefixValues.layoutSpans focus item values)

private def ReductionLayoutSpanMotive
    (focus : RuleSpanLayout)
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (owned : TokensOwnedBy file tokens)
    {item : ContextualItemKey tokens}
    {value : NonterminalValue file tokens item.raw.production.lhs}
    (coherent : CoherentReduction file tokens memo correct final item value)
    (trace : SourceAnchorTrace file tokens)
    (_carries : ReductionCarriesSourceTrace
      file tokens memo correct final owned coherent trace) : Prop :=
  FocusedSpanEvidence file tokens item.raw.origin item.raw.current
    (NonterminalValue.layoutSpans focus item.raw.production.lhs value)

private theorem prefixLayoutSpanZeroCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (focus : RuleSpanLayout) (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final item)
    (zero : item.raw.dot.val = 0) :
    PrefixLayoutSpanMotive focus file tokens memo correct final owned
      (.zero item reached zero) [] (.zero item reached zero) := by
  unfold PrefixLayoutSpanMotive
  rw [PrefixValues.layoutSpans_zeroValue]
  exact FocusedSpanEvidence.empty item.raw.origin item.raw.current

private theorem prefixLayoutSpanScanCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (focus : RuleSpanLayout) (owned : TokensOwnedBy file tokens)
    (before after : ContextualItemKey tokens)
    (cursor : TerminalCursor tokens)
    (priorValues : PrefixValues file tokens before)
    (witness : ScannedEdgeWitness
      file tokens before.raw after.raw cursor)
    (edge : ContextualEdgeReach file tokens memo correct final
      (.scanned before after cursor))
    (prior : CoherentPrefix file tokens memo correct final
      before priorValues)
    (priorTrace : SourceAnchorTrace file tokens)
    (priorCarries : PrefixCarriesSourceTrace
      file tokens memo correct final owned prior priorTrace)
    (priorIH : PrefixLayoutSpanMotive focus file tokens memo correct final
      owned prior priorTrace priorCarries) :
    PrefixLayoutSpanMotive focus file tokens memo correct final owned
      (.scan before after cursor priorValues witness edge prior)
      (priorTrace ++ witness.matched.sourceAnchorTrace owned)
      (.scan before after cursor priorValues witness edge prior priorTrace
        priorCarries) := by
  unfold PrefixLayoutSpanMotive at priorIH ⊢
  rcases priorIH with ⟨priorAnchors, priorSpans, priorInside,
    priorOrdered⟩
  refine ⟨priorAnchors ++ witness.matched.sourceAnchorTrace owned,
    ?_, ?_, ?_⟩
  · rw [SourceAnchorTrace.spans_append, priorSpans]
    rw [witness.matched.sourceAnchorTrace_spans owned]
    exact PrefixValues.layoutSpans_scanValue focus before after
      witness.terminal witness.next witness.matched witness.advance
        priorValues |>.symm
  · exact witness.sourceAnchorTrace_within owned
      (contextualReach_ordered edge.2.1) priorInside
  · exact witness.sourceAnchorTrace_ordered owned priorInside priorOrdered

private theorem prefixLayoutSpanCompleteCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (focus : RuleSpanLayout) (owned : TokensOwnedBy file tokens)
    (waiting finished after : ContextualItemKey tokens)
    (shared : Boundary tokens)
    (priorValues : PrefixValues file tokens waiting)
    (childValue : NonterminalValue file tokens
      finished.raw.production.lhs)
    (witness : CompletedEdgeWitness
      tokens waiting.raw finished.raw after.raw shared)
    (edge : ContextualEdgeReach file tokens memo correct final
      (.completed waiting finished after shared))
    (prior : CoherentPrefix file tokens memo correct final
      waiting priorValues)
    (child : CoherentReduction file tokens memo correct final
      finished childValue)
    (priorTrace childTrace : SourceAnchorTrace file tokens)
    (priorCarries : PrefixCarriesSourceTrace
      file tokens memo correct final owned prior priorTrace)
    (childCarries : ReductionCarriesSourceTrace
      file tokens memo correct final owned child childTrace)
    (priorIH : PrefixLayoutSpanMotive focus file tokens memo correct final
      owned prior priorTrace priorCarries)
    (childIH : ReductionLayoutSpanMotive focus file tokens memo correct final
      owned child childTrace childCarries) :
    PrefixLayoutSpanMotive focus file tokens memo correct final owned
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child)
      (priorTrace ++ childTrace)
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child priorTrace childTrace priorCarries childCarries) := by
  unfold PrefixLayoutSpanMotive at priorIH ⊢
  unfold ReductionLayoutSpanMotive at childIH
  rcases priorIH with ⟨priorAnchors, priorSpans, priorInside,
    priorOrdered⟩
  rcases childIH with ⟨childAnchors, childSpans, childInside,
    childOrdered⟩
  refine ⟨priorAnchors ++ childAnchors, ?_, ?_, ?_⟩
  · rw [SourceAnchorTrace.spans_append, priorSpans, childSpans]
    exact PrefixValues.layoutSpans_completeValue focus waiting finished after
      witness.next witness.advance priorValues childValue |>.symm
  · exact witness.sourceAnchorTraces_within
      (contextualReach_ordered edge.2.1)
      (contextualReach_ordered edge.2.2.1) priorInside childInside
  · exact witness.sourceAnchorTraces_ordered priorInside childInside
      priorOrdered childOrdered

/-- A source-rule callback may reshape the exact grammar-order input anchors
into the spans selected from that rule's semantic output. -/
def RootActionLayoutSpanSound (layout : RuleSpanLayout) : Prop :=
  ∀ {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens (ProductionId.root rule).rhs}
    {output : RuleValue rule},
    RuleReduction file tokens rule origin finish
        (RootAction.unpack rule input) output →
      (layout.spans rule output ≠ [] →
        origin.val < Nat.min finish.val tokens.length) →
      FocusedSpanEvidence file tokens origin finish
          (GrammarSymbolValues.layoutSpans layout
            (ProductionId.root rule).rhs input) →
        FocusedSpanEvidence file tokens origin finish
          (layout.spans rule output)

namespace ActionReduces

/-- Generated actions preserve layout spans structurally; source-rule actions
are delegated to the supplied semantic callback. -/
theorem layoutSpanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleSpanLayout)
    (rootSound : RootActionLayoutSpanSound layout)
    {actionId : ActionId} {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens actionId.production.rhs}
    {output : NonterminalValue file tokens actionId.production.lhs}
    (action : ActionReduces file tokens actionId origin finish input output)
    (rootOccupied : ∀ {rule : GrammarRuleId},
      actionId.production = .root rule →
        (rule ≠ .optionalComma ∧ rule ≠ .module) →
          origin.val < Nat.min finish.val tokens.length)
    (inputEvidence : FocusedSpanEvidence file tokens origin finish
      (GrammarSymbolValues.layoutSpans layout actionId.production.rhs input)) :
    FocusedSpanEvidence file tokens origin finish
      (NonterminalValue.layoutSpans layout actionId.production.lhs output) := by
  cases action with
  | root rule origin finish input output reduction =>
      simp only [ActionId.production_actionFor] at rootOccupied inputEvidence ⊢
      apply rootSound reduction
      · intro nonempty
        exact rootOccupied rfl (layout.safe output nonempty)
      · exact inputEvidence
  | atom site origin finish input =>
      exact inputEvidence.select
        (auxiliary_layoutSpans_sublist layout trivial
          (ActionReduces.atom site origin finish input))
  | seq site origin finish input =>
      exact inputEvidence.select
        (auxiliary_layoutSpans_sublist layout trivial
          (ActionReduces.seq site origin finish input))
  | group site origin finish input =>
      exact inputEvidence.select
        (auxiliary_layoutSpans_sublist layout trivial
          (ActionReduces.group site origin finish input))
  | choice site branch origin finish input =>
      exact inputEvidence.select
        (auxiliary_layoutSpans_sublist layout trivial
          (ActionReduces.choice site branch origin finish input))
  | opt site branch origin finish input =>
      exact inputEvidence.select
        (auxiliary_layoutSpans_sublist layout trivial
          (ActionReduces.opt site branch origin finish input))
  | star site branch origin finish input =>
      exact inputEvidence.select
        (auxiliary_layoutSpans_sublist layout trivial
          (ActionReduces.star site branch origin finish input))
  | plus site branch origin finish input =>
      exact inputEvidence.select
        (auxiliary_layoutSpans_sublist layout trivial
          (ActionReduces.plus site branch origin finish input))
  | list0 site branch origin finish input =>
      exact inputEvidence.select
        (auxiliary_layoutSpans_sublist layout trivial
          (ActionReduces.list0 site branch origin finish input))
  | list1 site origin finish input =>
      exact inputEvidence.select
        (auxiliary_layoutSpans_sublist layout trivial
          (ActionReduces.list1 site origin finish input))
  | tail site branch origin finish input =>
      exact inputEvidence.select
        (auxiliary_layoutSpans_sublist layout trivial
          (ActionReduces.tail site branch origin finish input))

end ActionReduces

private theorem reductionLayoutSpanCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (layout : RuleSpanLayout)
    (rootSound : RootActionLayoutSpanSound layout)
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (priorValues : PrefixValues file tokens item)
    (output : NonterminalValue file tokens item.raw.production.lhs)
    (reached : ContextualReach file tokens memo correct final item)
    (complete : CompleteItem item.raw)
    (coherentPrefix : CoherentPrefix file tokens memo correct final
      item priorValues)
    (action : ActionReduces file tokens (.actionFor item.raw.production)
      item.raw.origin item.raw.current
      (PrefixValues.fullValue item complete priorValues) output)
    (trace : SourceAnchorTrace file tokens)
    (prefixCarries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherentPrefix trace)
    (prefixIH : PrefixLayoutSpanMotive layout file tokens memo correct final
      owned coherentPrefix trace prefixCarries) :
    ReductionLayoutSpanMotive layout file tokens memo correct final owned
      (.reduce item priorValues output reached complete coherentPrefix action)
      trace
      (.reduce item priorValues output reached complete coherentPrefix action
        trace prefixCarries) := by
  unfold PrefixLayoutSpanMotive at prefixIH
  unfold ReductionLayoutSpanMotive
  apply action.layoutSpanEvidence layout rootSound
  · intro rule production safe
    exact completeRoot_occupied
      (by simpa only [ActionId.production_actionFor] using production)
      reached complete safe.1 safe.2
  simp only [ActionId.production_actionFor]
  rw [PrefixValues.layoutSpans_fullValue]
  exact prefixIH

namespace PrefixCarriesSourceTrace

/-- A coherent prefix carries the exact grammar-order span layout selected by
`layout`, provided each source-rule reduction preserves that layout. -/
theorem layoutSpanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (layout : RuleSpanLayout)
    (rootSound : RootActionLayoutSpanSound layout)
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    {coherent : CoherentPrefix file tokens memo correct final item values}
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    FocusedSpanEvidence file tokens item.raw.origin item.raw.current
      (PrefixValues.layoutSpans layout item values) :=
  PrefixCarriesSourceTrace.rec
    (motive_1 := PrefixLayoutSpanMotive
      layout file tokens memo correct final owned)
    (motive_2 := ReductionLayoutSpanMotive
      layout file tokens memo correct final owned)
    (prefixLayoutSpanZeroCase layout owned)
    (prefixLayoutSpanScanCase layout owned)
    (prefixLayoutSpanCompleteCase layout owned)
    (reductionLayoutSpanCase layout rootSound owned)
    carries

/-- At a completed canonical root item, layout evidence is stated directly on
the source-rule EBNF input. -/
theorem rootInputLayoutSpanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (layout : RuleSpanLayout)
    (rootSound : RootActionLayoutSpanSound layout)
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (RuleReduction.CanonicalRootLocationItem tokens rule origin finish context)}
    {complete : CompleteItem
      (RuleReduction.CanonicalRootLocationItem tokens rule origin finish context).raw}
    {coherent : CoherentPrefix file tokens memo correct final
      (RuleReduction.CanonicalRootLocationItem tokens rule origin finish context)
        priorValues}
    {ruleInput : EbnfValue file tokens (m2cV1.rhs rule)}
    (inputEq : ruleInput = RootAction.unpack rule
      (PrefixValues.fullValue
        (RuleReduction.CanonicalRootLocationItem tokens rule origin finish context)
        complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherent trace) :
    FocusedSpanEvidence file tokens origin finish
      (ruleInput.layoutSpans layout) := by
  have fullEvidence := carries.layoutSpanEvidence layout rootSound
  rw [← PrefixValues.layoutSpans_fullValue layout
    (RuleReduction.CanonicalRootLocationItem tokens rule origin finish context)
    complete priorValues] at fullEvidence
  change FocusedSpanEvidence file tokens origin finish
    (GrammarSymbolValues.layoutSpans layout (ProductionId.root rule).rhs
      (PrefixValues.fullValue
        (RuleReduction.CanonicalRootLocationItem tokens rule origin finish
          context) complete priorValues)) at fullEvidence
  rw [← RootAction.unpack_layoutSpans] at fullEvidence
  rw [← inputEq] at fullEvidence
  exact fullEvidence

end PrefixCarriesSourceTrace

namespace ReductionCarriesSourceTrace

/-- A coherent reduction carries the exact grammar-order span layout selected
by `layout`. -/
theorem layoutSpanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (layout : RuleSpanLayout)
    (rootSound : RootActionLayoutSpanSound layout)
    {item : ContextualItemKey tokens}
    {value : NonterminalValue file tokens item.raw.production.lhs}
    {coherent : CoherentReduction file tokens memo correct final item value}
    {trace : SourceAnchorTrace file tokens}
    (carries : ReductionCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    FocusedSpanEvidence file tokens item.raw.origin item.raw.current
      (NonterminalValue.layoutSpans layout
        item.raw.production.lhs value) :=
  ReductionCarriesSourceTrace.rec
    (motive_1 := PrefixLayoutSpanMotive
      layout file tokens memo correct final owned)
    (motive_2 := ReductionLayoutSpanMotive
      layout file tokens memo correct final owned)
    (prefixLayoutSpanZeroCase layout owned)
    (prefixLayoutSpanScanCase layout owned)
    (prefixLayoutSpanCompleteCase layout owned)
    (reductionLayoutSpanCase layout rootSound owned)
    carries

end ReductionCarriesSourceTrace

private theorem sublist_flatMap_of_mem
    {alpha beta : Type} (f : alpha → List beta)
    {value : alpha} {values : List alpha} (member : value ∈ values) :
    (f value).Sublist (values.flatMap f) := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact List.sublist_append_left _ _
      · exact (induction member).trans (List.sublist_append_right _ _)

theorem EbnfValue.ContainsRuleValue.layoutSpans_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleSpanLayout)
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    {rule : GrammarRuleId} {value : RuleValue rule}
    (inside : EbnfValue.ContainsRuleValue file tokens input rule value) :
    (layout.spans rule value).Sublist (input.layoutSpans layout) :=
  EbnfValue.ContainsRuleValue.rec
    (motive_1 := fun {expression} input rule value _inside =>
      (layout.spans rule value).Sublist (input.layoutSpans layout))
    (motive_2 := fun {expressions} input rule value _inside =>
      (layout.spans rule value).Sublist (input.layoutSpans layout))
    (fun rule value => by
      rw [EbnfValue.layoutSpans_ruleAtom]
      exact List.Sublist.refl _)
    (fun {left right} shape {input rule value} inside induction => by
      rw [EbnfValue.layoutSpans_transport]
      exact induction)
    (fun {children values rule value} inside induction => by
      rw [EbnfValue.layoutSpans_sequence]
      exact induction)
    (fun {child childValue rule value} inside induction => by
      rw [EbnfValue.layoutSpans_group]
      exact induction)
    (fun {branches} branch {branchValue rule value} inside induction => by
      rw [EbnfValue.layoutSpans_choice]
      exact induction)
    (fun {child childValue rule value} inside induction => by
      rw [EbnfValue.layoutSpans_optional_some]
      exact induction)
    (fun {child values childValue rule value} member inside induction => by
      rw [EbnfValue.layoutSpans_star]
      exact induction.trans (sublist_flatMap_of_mem _ member))
    (fun {child head tail rule value} inside induction => by
      rw [EbnfValue.layoutSpans_plus]
      exact induction.trans (List.sublist_append_left _ _))
    (fun {child head childValue tail rule value} member inside induction => by
      rw [EbnfValue.layoutSpans_plus]
      exact induction.trans
        ((sublist_flatMap_of_mem _ member).trans
          (List.sublist_append_right _ _)))
    (fun {child values childValue rule value} member inside induction => by
      rw [EbnfValue.layoutSpans_list0]
      exact induction.trans (sublist_flatMap_of_mem _ member))
    (fun {child head tail rule value} inside induction => by
      rw [EbnfValue.layoutSpans_list1]
      exact induction.trans (List.sublist_append_left _ _))
    (fun {child head childValue tail rule value} member inside induction => by
      rw [EbnfValue.layoutSpans_list1]
      exact induction.trans
        ((sublist_flatMap_of_mem _ member).trans
          (List.sublist_append_right _ _)))
    (fun {child rest childValue restValues rule value} inside induction => by
      rw [EbnfValues.layoutSpans_cons]
      exact induction.trans (List.sublist_append_left _ _))
    (fun {child rest childValue restValues rule value} inside induction => by
      rw [EbnfValues.layoutSpans_cons]
      exact induction.trans (List.sublist_append_right _ _))
    inside

end Solcore.Surface.Multi
