import Solcore.Surface.Multi.CoherentIntervalLocation
import Solcore.Surface.Multi.LocationSubfragment
import Solcore.Surface.Multi.RuleIntervalLocation
import Solcore.Surface.Multi.RootlessNormalizationDottedStaticPotential

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- Physical terminal anchors still represented directly by one EBNF value.
Source-rule children are leaves here; their own terminal traces remain on the
coherent reduction that produced them. -/
def DirectSourceTraceFamily
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    (index : EbnfValueIndex) → EbnfFamily file tokens index →
      SourceAnchorTrace file tokens
  | .expression (.atom (.terminal terminal)), matched =>
      (Eq.mp (ebnfValue_atom_terminal_eq terminal) matched).sourceAnchorTrace
        owned
  | .expression (.atom (.nonterminal _rule)), _value => []
  | .expression (.sequence children), values =>
      DirectSourceTraceFamily file tokens owned (.expressions children)
        (Eq.mp (ebnfValue_sequence_eq children) values)
  | .expression (.group child), value =>
      DirectSourceTraceFamily file tokens owned (.expression child)
        (Eq.mp (ebnfValue_group_eq child) value)
  | .expression (.choice branches), value =>
      let selected := Eq.mp (ebnfValue_choice_eq branches) value
      DirectSourceTraceFamily file tokens owned
        (.expression (branches.get selected.1)) selected.2
  | .expression (.optional child), value =>
      match Eq.mp (ebnfValue_optional_eq child) value with
      | none => []
      | some childValue =>
          DirectSourceTraceFamily file tokens owned (.expression child)
            childValue
  | .expression (.star child), values =>
      (Eq.mp (ebnfValue_star_eq child) values).flatMap fun value =>
        DirectSourceTraceFamily file tokens owned (.expression child) value
  | .expression (.plus child), values =>
      let viewed := Eq.mp (ebnfValue_plus_eq child) values
      DirectSourceTraceFamily file tokens owned (.expression child)
          viewed.head ++
        viewed.tail.flatMap fun value =>
          DirectSourceTraceFamily file tokens owned (.expression child) value
  | .expression (.list0 child), values =>
      (Eq.mp (ebnfValue_list0_eq child) values).flatMap fun value =>
        DirectSourceTraceFamily file tokens owned (.expression child) value
  | .expression (.list1 child), values =>
      let viewed := Eq.mp (ebnfValue_list1_eq child) values
      DirectSourceTraceFamily file tokens owned (.expression child)
          viewed.head ++
        viewed.tail.flatMap fun value =>
          DirectSourceTraceFamily file tokens owned (.expression child) value
  | .expressions [], _ => []
  | .expressions (child :: rest), values =>
      let viewed := Eq.mp (ebnfValues_cons_eq child rest) values
      DirectSourceTraceFamily file tokens owned (.expression child) viewed.1 ++
        DirectSourceTraceFamily file tokens owned (.expressions rest) viewed.2
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

abbrev EbnfValue.directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {expression : EbnfExpr}
    (value : EbnfValue file tokens expression) :
    SourceAnchorTrace file tokens :=
  DirectSourceTraceFamily file tokens owned (.expression expression) value

abbrev EbnfValues.directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {expressions : List EbnfExpr}
    (values : EbnfValues file tokens expressions) :
    SourceAnchorTrace file tokens :=
  DirectSourceTraceFamily file tokens owned (.expressions expressions) values

@[simp] theorem EbnfValue.directSourceTrace_transport
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {left right : EbnfExpr} (shape : left = right)
    (value : EbnfValue file tokens left) :
    (EbnfValue.transport shape value).directSourceTrace owned =
      value.directSourceTrace owned := by
  cases shape
  rfl

@[simp] theorem EbnfValue.directSourceTrace_atShape
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {site : GrammarSite} {expression : EbnfExpr}
    (shape : site.expression = expression)
    (value : EbnfValue file tokens site.expression) :
    (EbnfValue.atShape shape value).directSourceTrace owned =
      value.directSourceTrace owned := by
  exact EbnfValue.directSourceTrace_transport owned shape value

@[simp] theorem EbnfValue.directSourceTrace_ofShape
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {site : GrammarSite} {expression : EbnfExpr}
    (shape : site.expression = expression)
    (value : EbnfValue file tokens expression) :
    (EbnfValue.ofShape shape value).directSourceTrace owned =
      value.directSourceTrace owned := by
  exact EbnfValue.directSourceTrace_transport owned shape.symm value

@[simp] theorem EbnfValue.directSourceTrace_terminalAtom
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    (EbnfValue.terminalAtom terminal matched).directSourceTrace owned =
      matched.sourceAnchorTrace owned := by
  simp [EbnfValue.directSourceTrace, DirectSourceTraceFamily,
    EbnfValue.terminalAtom, cast_cast]

@[simp] theorem EbnfValue.directSourceTrace_ruleAtom
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (rule : GrammarRuleId) (value : RuleValue rule) :
    (EbnfValue.ruleAtom (file := file) (tokens := tokens)
      rule value).directSourceTrace owned = [] := by
  simp [EbnfValue.directSourceTrace, DirectSourceTraceFamily,
    EbnfValue.ruleAtom]

@[simp] theorem EbnfValue.directSourceTrace_sequence
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (children : List EbnfExpr)
    (values : EbnfValues file tokens children) :
    (EbnfValue.sequence children values).directSourceTrace owned =
      values.directSourceTrace owned := by
  simp [EbnfValue.directSourceTrace, EbnfValues.directSourceTrace,
    DirectSourceTraceFamily, EbnfValue.sequence, cast_cast]

@[simp] theorem EbnfValue.directSourceTrace_group
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (child : EbnfExpr) (value : EbnfValue file tokens child) :
    (EbnfValue.group child value).directSourceTrace owned =
      value.directSourceTrace owned := by
  simp [EbnfValue.directSourceTrace, DirectSourceTraceFamily,
    EbnfValue.group, cast_cast]

@[simp] theorem EbnfValue.directSourceTrace_optional_none
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (child : EbnfExpr) :
    (EbnfValue.optional (file := file) (tokens := tokens)
      child none).directSourceTrace owned = [] := by
  simp [EbnfValue.directSourceTrace, DirectSourceTraceFamily,
    EbnfValue.optional, cast_cast]

@[simp] theorem EbnfValue.directSourceTrace_optional_some
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (child : EbnfExpr)
    (value : EbnfValue file tokens child) :
    (EbnfValue.optional child (some value)).directSourceTrace owned =
      value.directSourceTrace owned := by
  simp [EbnfValue.directSourceTrace, DirectSourceTraceFamily,
    EbnfValue.optional, cast_cast]

@[simp] theorem EbnfValue.directSourceTrace_choice
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (branches : List EbnfExpr)
    (value : (branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch)) :
    (EbnfValue.choice branches value).directSourceTrace owned =
      value.2.directSourceTrace owned := by
  have viewed : Eq.mp (ebnfValue_choice_eq branches)
      (EbnfValue.choice branches value) = value := by
    unfold EbnfValue.choice
    change cast _ (cast _ value) = value
    rw [cast_cast]
    apply cast_eq
  unfold EbnfValue.directSourceTrace
  rw [DirectSourceTraceFamily, viewed]

@[simp] theorem EbnfValue.directSourceTrace_star
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (child : EbnfExpr) (values : List (EbnfValue file tokens child)) :
    (EbnfValue.star child values).directSourceTrace owned =
      values.flatMap fun value => value.directSourceTrace owned := by
  simp [EbnfValue.directSourceTrace, DirectSourceTraceFamily,
    EbnfValue.star, cast_cast]

@[simp] theorem EbnfValue.directSourceTrace_plus
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (child : EbnfExpr)
    (values : NonemptyList (EbnfValue file tokens child)) :
    (EbnfValue.plus child values).directSourceTrace owned =
      values.head.directSourceTrace owned ++
        values.tail.flatMap fun value => value.directSourceTrace owned := by
  simp [EbnfValue.directSourceTrace, DirectSourceTraceFamily,
    EbnfValue.plus, cast_cast]

@[simp] theorem EbnfValue.directSourceTrace_list0
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (child : EbnfExpr) (values : List (EbnfValue file tokens child)) :
    (EbnfValue.list0 child values).directSourceTrace owned =
      values.flatMap fun value => value.directSourceTrace owned := by
  simp [EbnfValue.directSourceTrace, DirectSourceTraceFamily,
    EbnfValue.list0, cast_cast]

@[simp] theorem EbnfValue.directSourceTrace_list1
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (child : EbnfExpr)
    (values : NonemptyList (EbnfValue file tokens child)) :
    (EbnfValue.list1 child values).directSourceTrace owned =
      values.head.directSourceTrace owned ++
        values.tail.flatMap fun value => value.directSourceTrace owned := by
  simp [EbnfValue.directSourceTrace, DirectSourceTraceFamily,
    EbnfValue.list1, cast_cast]

@[simp] theorem EbnfValues.directSourceTrace_nil
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (EbnfValues.nil (file := file) (tokens := tokens)).directSourceTrace owned =
      [] := by
  simp [EbnfValues.directSourceTrace, DirectSourceTraceFamily, EbnfValues.nil]

@[simp] theorem EbnfValues.directSourceTrace_cons
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (child : EbnfExpr) (rest : List EbnfExpr)
    (head : EbnfValue file tokens child)
    (tail : EbnfValues file tokens rest) :
    (EbnfValues.cons child rest head tail).directSourceTrace owned =
      head.directSourceTrace owned ++ tail.directSourceTrace owned := by
  simp [EbnfValues.directSourceTrace, DirectSourceTraceFamily,
    EbnfValues.cons, cast_cast]

@[simp] theorem EbnfValues.directSourceTrace_nil_raw
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (values : EbnfValues file tokens []) :
    values.directSourceTrace owned = [] := by
  unfold EbnfValues.directSourceTrace
  rw [DirectSourceTraceFamily]

@[simp] theorem EbnfValues.directSourceTrace_cons_raw
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (child : EbnfExpr) (rest : List EbnfExpr)
    (values : EbnfValues file tokens (child :: rest)) :
    values.directSourceTrace owned =
      (Eq.mp (ebnfValues_cons_eq child rest) values).1.directSourceTrace owned ++
        (Eq.mp (ebnfValues_cons_eq child rest) values).2.directSourceTrace
          owned := by
  unfold EbnfValues.directSourceTrace
  rw [DirectSourceTraceFamily]

/-- Direct trace equation for an arbitrary sequence-shaped value. -/
theorem EbnfValue.directSourceTrace_sequence_raw
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (children : List EbnfExpr)
    (value : EbnfValue file tokens (.sequence children)) :
    value.directSourceTrace owned =
      (Eq.mp (ebnfValue_sequence_eq children) value).directSourceTrace owned := by
  unfold EbnfValue.directSourceTrace
  rw [DirectSourceTraceFamily]

@[simp] theorem EbnfValue.directSourceTrace_star_raw
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (child : EbnfExpr) (value : EbnfValue file tokens (.star child)) :
    value.directSourceTrace owned =
      (Eq.mp (ebnfValue_star_eq child) value).flatMap fun element =>
        element.directSourceTrace owned := by
  unfold EbnfValue.directSourceTrace
  rw [DirectSourceTraceFamily]

@[simp] theorem EbnfValue.directSourceTrace_plus_raw
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (child : EbnfExpr) (value : EbnfValue file tokens (.plus child)) :
    value.directSourceTrace owned =
      let elements := Eq.mp (ebnfValue_plus_eq child) value
      elements.head.directSourceTrace owned ++
        elements.tail.flatMap fun element =>
          element.directSourceTrace owned := by
  unfold EbnfValue.directSourceTrace
  rw [DirectSourceTraceFamily]

theorem EbnfValue.flatMap_directSourceTrace_transport_site
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {left right : GrammarSite} (equality : left = right)
    (values : List (EbnfValue file tokens left.expression)) :
    (Eq.mp
        (congrArg
          (fun site : GrammarSite =>
            List (EbnfValue file tokens site.expression))
          equality)
        values).flatMap (fun value => value.directSourceTrace owned) =
      values.flatMap fun value => value.directSourceTrace owned := by
  cases equality
  rfl

def NonterminalValue.directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (symbol : NonterminalSymbol) → NonterminalValue file tokens symbol →
      SourceAnchorTrace file tokens
  | .rule _rule, _value => []
  | .aux _site, value => EbnfValue.directSourceTrace owned value
  | .tail _site, values =>
      values.flatMap fun value => EbnfValue.directSourceTrace owned value

@[simp] theorem NonterminalValue.directSourceTrace_rule
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (rule : GrammarRuleId) (value : RuleValue rule) :
    NonterminalValue.directSourceTrace owned (.rule rule) value = [] := by
  rfl

@[simp] theorem NonterminalValue.directSourceTrace_aux
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (site : GrammarSite)
    (value : EbnfValue file tokens site.expression) :
    NonterminalValue.directSourceTrace owned (.aux site) value =
      value.directSourceTrace owned := by
  rfl

@[simp] theorem NonterminalValue.directSourceTrace_tail
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (site : ListSite)
    (values : List (EbnfValue file tokens site.element.expression)) :
    NonterminalValue.directSourceTrace owned (.tail site) values =
      values.flatMap fun value => value.directSourceTrace owned := by
  rfl

def GrammarSymbolValue.directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (symbol : GrammarSymbol) → GrammarSymbolValue file tokens symbol →
      SourceAnchorTrace file tokens
  | .terminal _terminal, matched => matched.sourceAnchorTrace owned
  | .nonterminal symbol, value =>
      NonterminalValue.directSourceTrace owned symbol value

@[simp] theorem GrammarSymbolValue.directSourceTrace_terminal
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    GrammarSymbolValue.directSourceTrace owned (.terminal terminal) matched =
      matched.sourceAnchorTrace owned := by
  rfl

@[simp] theorem GrammarSymbolValue.directSourceTrace_nonterminal
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (symbol : NonterminalSymbol)
    (value : NonterminalValue file tokens symbol) :
    GrammarSymbolValue.directSourceTrace owned (.nonterminal symbol) value =
      NonterminalValue.directSourceTrace owned symbol value := by
  rfl

def GrammarSymbolValues.directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (symbols : List GrammarSymbol) → GrammarSymbolValues file tokens symbols →
      SourceAnchorTrace file tokens
  | [], _values => []
  | symbol :: rest, values =>
      GrammarSymbolValue.directSourceTrace owned symbol values.1 ++
        GrammarSymbolValues.directSourceTrace owned rest values.2

@[simp] theorem GrammarSymbolValue.directSourceTrace_transport
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {left right : GrammarSymbol} (shape : left = right)
    (value : GrammarSymbolValue file tokens left) :
    GrammarSymbolValue.directSourceTrace owned right
        (Eq.mp (congrArg (GrammarSymbolValue file tokens) shape) value) =
      GrammarSymbolValue.directSourceTrace owned left value := by
  cases shape
  rfl

@[simp] theorem GrammarSymbolValues.directSourceTrace_append
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {left right : List GrammarSymbol}
    (leftValues : GrammarSymbolValues file tokens left)
    (rightValues : GrammarSymbolValues file tokens right) :
    GrammarSymbolValues.directSourceTrace owned (left ++ right)
        (GrammarSymbolValues.append leftValues rightValues) =
      GrammarSymbolValues.directSourceTrace owned left leftValues ++
        GrammarSymbolValues.directSourceTrace owned right rightValues := by
  induction left with
  | nil => rfl
  | cons symbol rest inductionHypothesis =>
      rcases leftValues with ⟨head, tail⟩
      change GrammarSymbolValue.directSourceTrace owned symbol head ++
          GrammarSymbolValues.directSourceTrace owned (rest ++ right)
            (GrammarSymbolValues.append tail rightValues) = _
      rw [inductionHypothesis tail]
      exact (List.append_assoc _ _ _).symm

@[simp] theorem GrammarSymbolValues.directSourceTrace_transport
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {left right : List GrammarSymbol} (shape : left = right)
    (values : GrammarSymbolValues file tokens left) :
    GrammarSymbolValues.directSourceTrace owned right
        (GrammarSymbolValues.transport shape values) =
      GrammarSymbolValues.directSourceTrace owned left values := by
  cases shape
  rfl

@[simp] theorem GrammarSymbolValues.directSourceTrace_singleton
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (symbol : GrammarSymbol)
    (value : GrammarSymbolValue file tokens symbol) :
    GrammarSymbolValues.directSourceTrace owned [symbol] (value, ()) =
      GrammarSymbolValue.directSourceTrace owned symbol value := by
  simp [GrammarSymbolValues.directSourceTrace]

@[simp] theorem GrammarSymbolValues.directSourceTrace_view
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {production : ProductionId} {canonicalRhs : List GrammarSymbol}
    (layout : production.rhs = canonicalRhs)
    (values : GrammarSymbolValues file tokens production.rhs) :
    GrammarSymbolValues.directSourceTrace owned canonicalRhs
        (GrammarSymbolValues.view layout values) =
      GrammarSymbolValues.directSourceTrace owned production.rhs values := by
  unfold GrammarSymbolValues.view
  exact GrammarSymbolValues.directSourceTrace_transport owned layout values

@[simp] theorem EbnfValues.directSourceTrace_ofAuxiliaries
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (sites : List GrammarSite)
    (values : GrammarSymbolValues file tokens
      (sites.map fun site => GrammarSymbol.nonterminal (.aux site))) :
    (EbnfValues.ofAuxiliaries sites values).directSourceTrace owned =
      GrammarSymbolValues.directSourceTrace owned
        (sites.map fun site => GrammarSymbol.nonterminal (.aux site)) values := by
  induction sites with
  | nil =>
      simp only [List.map] at values ⊢
      cases values
      rw [EbnfValues.directSourceTrace_nil_raw]
      rfl
  | cons site rest inductionHypothesis =>
      simp only [List.map] at values ⊢
      rcases values with ⟨head, tail⟩
      rw [EbnfValues.directSourceTrace_cons_raw]
      rw [EbnfValues.ofAuxiliaries_cons_eq]
      rw [inductionHypothesis]
      rfl

@[simp] theorem RootAction.unpack_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (rule : GrammarRuleId)
    (values : GrammarSymbolValues file tokens
      (ProductionId.root rule).rhs) :
    (RootAction.unpack rule values).directSourceTrace owned =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.root rule).rhs values := by
  rw [RootAction.unpack_eq]
  rw [EbnfValue.directSourceTrace_atShape]
  let viewed := GrammarSymbolValues.view
    (ProductionId.rhs_root rule) values
  calc
    _ = GrammarSymbolValues.directSourceTrace owned
          [.nonterminal (.aux (GrammarSite.root rule))] viewed := by
        exact (GrammarSymbolValues.directSourceTrace_singleton owned
          (.nonterminal (.aux (GrammarSite.root rule))) viewed.1).symm
    _ = GrammarSymbolValues.directSourceTrace owned
          (ProductionId.root rule).rhs values :=
        GrammarSymbolValues.directSourceTrace_view owned
          (ProductionId.rhs_root rule) values

abbrev PrefixValues.directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (values : PrefixValues file tokens item) :
    SourceAnchorTrace file tokens :=
  GrammarSymbolValues.directSourceTrace owned
    (item.raw.production.rhs.take item.raw.dot.val) values

@[simp] theorem PrefixValues.directSourceTrace_zeroValue
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens) (zero : item.raw.dot.val = 0) :
    PrefixValues.directSourceTrace owned item
      (PrefixValues.zeroValue (file := file) item zero) = [] := by
  unfold PrefixValues.directSourceTrace PrefixValues.zeroValue
  rw [GrammarSymbolValues.directSourceTrace_transport]
  rfl

@[simp] theorem PrefixValues.directSourceTrace_scanValue
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (before after : ContextualItemKey tokens)
    (terminal : TerminalSymbol)
    (next : NextSymbol before.raw (.terminal terminal))
    (matched : MatchedTerminal file tokens terminal)
    (advance : AdvanceItem before.raw matched.cursor.afterBoundary after.raw)
    (prior : PrefixValues file tokens before) :
    PrefixValues.directSourceTrace owned after
        (PrefixValues.scanValue before after terminal next matched advance
          prior) =
      PrefixValues.directSourceTrace owned before prior ++
        matched.sourceAnchorTrace owned := by
  unfold PrefixValues.directSourceTrace PrefixValues.scanValue
  rw [GrammarSymbolValues.directSourceTrace_transport]
  rw [GrammarSymbolValues.directSourceTrace_append]
  simp [GrammarSymbolValues.directSourceTrace,
    GrammarSymbolValue.directSourceTrace]

@[simp] theorem PrefixValues.directSourceTrace_completeValue
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (waiting finished after : ContextualItemKey tokens)
    (next : NextSymbol waiting.raw
      (.nonterminal finished.raw.production.lhs))
    (advance : AdvanceItem waiting.raw finished.raw.current after.raw)
    (prior : PrefixValues file tokens waiting)
    (child : NonterminalValue file tokens finished.raw.production.lhs) :
    PrefixValues.directSourceTrace owned after
        (PrefixValues.completeValue waiting finished after next advance prior
          child) =
      PrefixValues.directSourceTrace owned waiting prior ++
        NonterminalValue.directSourceTrace owned
          finished.raw.production.lhs child := by
  unfold PrefixValues.directSourceTrace PrefixValues.completeValue
  rw [GrammarSymbolValues.directSourceTrace_transport]
  rw [GrammarSymbolValues.directSourceTrace_append]
  simp [GrammarSymbolValues.directSourceTrace,
    GrammarSymbolValue.directSourceTrace]

@[simp] theorem PrefixValues.directSourceTrace_fullValue
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens) (complete : CompleteItem item.raw)
    (prior : PrefixValues file tokens item) :
    GrammarSymbolValues.directSourceTrace owned item.raw.production.rhs
        (PrefixValues.fullValue item complete prior) =
      PrefixValues.directSourceTrace owned item prior := by
  unfold PrefixValues.directSourceTrace PrefixValues.fullValue
  rw [GrammarSymbolValues.directSourceTrace_transport]

@[simp] theorem AtomSite.pack_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (site : AtomSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.atom site).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (AtomSite.pack site values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.atom site).rhs values := by
  cases atomEq : site.atom with
  | terminal terminal =>
      rw [NonterminalValue.directSourceTrace_aux]
      rw [← EbnfValue.directSourceTrace_atShape owned
        site.expression_eq_atom]
      rw [← EbnfValue.directSourceTrace_transport owned
        (congrArg EbnfExpr.atom atomEq)]
      change EbnfValue.directSourceTrace owned
        (AtomSite.packAtAtom site (.terminal terminal) atomEq values) = _
      rw [AtomSite.pack_terminal_eq]
      rw [EbnfValue.directSourceTrace_terminalAtom]
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_atom site) values
      let atomValue := Eq.mp
        (congrArg (GrammarSymbolValue file tokens) site.symbol_eq) viewed.1
      calc
        _ = GrammarSymbolValue.directSourceTrace owned
              (EbnfAtom.terminal terminal).grammarSymbol
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                (congrArg EbnfAtom.grammarSymbol atomEq)) atomValue) := rfl
        _ = GrammarSymbolValue.directSourceTrace owned
              site.atom.grammarSymbol atomValue :=
            GrammarSymbolValue.directSourceTrace_transport owned
              (congrArg EbnfAtom.grammarSymbol atomEq) atomValue
        _ = GrammarSymbolValue.directSourceTrace owned site.symbol
              viewed.1 :=
            GrammarSymbolValue.directSourceTrace_transport owned
              site.symbol_eq viewed.1
        _ = GrammarSymbolValues.directSourceTrace owned [site.symbol]
              viewed := by
            exact (GrammarSymbolValues.directSourceTrace_singleton owned
              site.symbol viewed.1).symm
        _ = GrammarSymbolValues.directSourceTrace owned
              (ProductionId.atom site).rhs values :=
            GrammarSymbolValues.directSourceTrace_view owned
              (ProductionId.rhs_atom site) values
  | nonterminal rule =>
      rw [NonterminalValue.directSourceTrace_aux]
      rw [← EbnfValue.directSourceTrace_atShape owned
        site.expression_eq_atom]
      rw [← EbnfValue.directSourceTrace_transport owned
        (congrArg EbnfExpr.atom atomEq)]
      change EbnfValue.directSourceTrace owned
        (AtomSite.packAtAtom site (.nonterminal rule) atomEq values) = _
      rw [AtomSite.pack_rule_eq]
      rw [EbnfValue.directSourceTrace_ruleAtom]
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_atom site) values
      let atomValue := Eq.mp
        (congrArg (GrammarSymbolValue file tokens) site.symbol_eq) viewed.1
      calc
        _ = GrammarSymbolValue.directSourceTrace owned
              (EbnfAtom.nonterminal rule).grammarSymbol
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                (congrArg EbnfAtom.grammarSymbol atomEq)) atomValue) := rfl
        _ = GrammarSymbolValue.directSourceTrace owned
              site.atom.grammarSymbol atomValue :=
            GrammarSymbolValue.directSourceTrace_transport owned
              (congrArg EbnfAtom.grammarSymbol atomEq) atomValue
        _ = GrammarSymbolValue.directSourceTrace owned site.symbol
              viewed.1 :=
            GrammarSymbolValue.directSourceTrace_transport owned
              site.symbol_eq viewed.1
        _ = GrammarSymbolValues.directSourceTrace owned [site.symbol]
              viewed := by
            exact (GrammarSymbolValues.directSourceTrace_singleton owned
              site.symbol viewed.1).symm
        _ = GrammarSymbolValues.directSourceTrace owned
              (ProductionId.atom site).rhs values :=
            GrammarSymbolValues.directSourceTrace_view owned
              (ProductionId.rhs_atom site) values

@[simp] theorem SequenceSite.pack_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : SequenceSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.seq site).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (SequenceSite.pack site values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.seq site).rhs values := by
  rw [NonterminalValue.directSourceTrace_aux]
  rw [← EbnfValue.directSourceTrace_atShape owned
    site.expression_eq_sequence]
  rw [SequenceSite.pack_eq]
  rw [EbnfValue.directSourceTrace_sequence]
  rw [EbnfValues.directSourceTrace_ofAuxiliaries]
  exact GrammarSymbolValues.directSourceTrace_view owned
    (ProductionId.rhs_seq site) values

@[simp] theorem GroupSite.pack_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : GroupSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.group site).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (GroupSite.pack site values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.group site).rhs values := by
  rw [NonterminalValue.directSourceTrace_aux]
  rw [← EbnfValue.directSourceTrace_atShape owned
    site.expression_eq_group]
  rw [GroupSite.pack_eq]
  rw [EbnfValue.directSourceTrace_group]
  calc
    _ = GrammarSymbolValues.directSourceTrace owned
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_group site) values) := by
        exact (GrammarSymbolValues.directSourceTrace_singleton owned
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_group site) values).1).symm
    _ = GrammarSymbolValues.directSourceTrace owned
          (ProductionId.group site).rhs values :=
        GrammarSymbolValues.directSourceTrace_view owned
          (ProductionId.rhs_group site) values

@[simp] theorem ChoiceSite.pack_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : ChoiceSite)
    (branch : Fin site.branchCount)
    (values : GrammarSymbolValues file tokens
      (ProductionId.choice site branch).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (ChoiceSite.pack site branch values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.choice site branch).rhs values := by
  rw [NonterminalValue.directSourceTrace_aux]
  rw [← EbnfValue.directSourceTrace_atShape owned
    site.expression_eq_choice]
  rw [ChoiceSite.pack_eq]
  rw [EbnfValue.directSourceTrace_choice]
  rw [EbnfValue.directSourceTrace_transport]
  calc
    _ = GrammarSymbolValues.directSourceTrace owned
          [.nonterminal (.aux (site.branch branch))]
          (GrammarSymbolValues.view
            (ProductionId.rhs_choice site branch) values) := by
        exact (GrammarSymbolValues.directSourceTrace_singleton owned
          (.nonterminal (.aux (site.branch branch)))
          (GrammarSymbolValues.view
            (ProductionId.rhs_choice site branch) values).1).symm
    _ = GrammarSymbolValues.directSourceTrace owned
          (ProductionId.choice site branch).rhs values :=
        GrammarSymbolValues.directSourceTrace_view owned
          (ProductionId.rhs_choice site branch) values

@[simp] theorem OptionalSite.pack_none_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .none).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (OptionalSite.pack site .none values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.opt site .none).rhs values := by
  rw [NonterminalValue.directSourceTrace_aux]
  rw [← EbnfValue.directSourceTrace_atShape owned
    site.expression_eq_optional]
  rw [OptionalSite.pack_none_eq]
  rw [EbnfValue.directSourceTrace_optional_none]
  exact GrammarSymbolValues.directSourceTrace_view owned
    (ProductionId.rhs_opt_none site) values

@[simp] theorem OptionalSite.pack_some_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .some).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (OptionalSite.pack site .some values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.opt site .some).rhs values := by
  rw [NonterminalValue.directSourceTrace_aux]
  rw [← EbnfValue.directSourceTrace_atShape owned
    site.expression_eq_optional]
  rw [OptionalSite.pack_some_eq]
  rw [EbnfValue.directSourceTrace_optional_some]
  calc
    _ = GrammarSymbolValues.directSourceTrace owned
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_opt_some site) values) := by
        exact (GrammarSymbolValues.directSourceTrace_singleton owned
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_opt_some site) values).1).symm
    _ = GrammarSymbolValues.directSourceTrace owned
          (ProductionId.opt site .some).rhs values :=
        GrammarSymbolValues.directSourceTrace_view owned
          (ProductionId.rhs_opt_some site) values

@[simp] theorem OptionalSite.pack_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : OptionalSite)
    (branch : OptionalBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site branch).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (OptionalSite.pack site branch values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.opt site branch).rhs values := by
  cases branch with
  | none => exact OptionalSite.pack_none_directSourceTrace owned site values
  | some => exact OptionalSite.pack_some_directSourceTrace owned site values

@[simp] theorem StarSite.pack_nil_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .nil).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (StarSite.pack site .nil values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.star site .nil).rhs values := by
  rw [NonterminalValue.directSourceTrace_aux]
  rw [← EbnfValue.directSourceTrace_atShape owned site.expression_eq_star]
  rw [StarSite.pack_nil_eq]
  rw [EbnfValue.directSourceTrace_star]
  exact GrammarSymbolValues.directSourceTrace_view owned
    (ProductionId.rhs_star_nil site) values

@[simp] theorem StarSite.pack_cons_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .cons).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (StarSite.pack site .cons values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.star site .cons).rhs values := by
  rw [NonterminalValue.directSourceTrace_aux]
  rw [← EbnfValue.directSourceTrace_atShape owned site.expression_eq_star]
  rw [StarSite.pack_cons_eq]
  rw [EbnfValue.directSourceTrace_star]
  simp only [List.flatMap_cons]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_star_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  change head.directSourceTrace owned ++
      (Eq.mp (ebnfValue_star_eq site.child.expression)
        (EbnfValue.atShape site.expression_eq_star tail)).flatMap
          (fun element => element.directSourceTrace owned) = _
  calc
    _ = head.directSourceTrace owned ++
          EbnfValue.directSourceTrace owned
            (EbnfValue.atShape site.expression_eq_star tail) := by
        rw [EbnfValue.directSourceTrace_star_raw]
    _ = GrammarSymbolValue.directSourceTrace owned
          (.nonterminal (.aux site.child)) head ++
          EbnfValue.directSourceTrace owned tail := by
        rw [EbnfValue.directSourceTrace_atShape]
    _ = GrammarSymbolValues.directSourceTrace owned
          [.nonterminal (.aux site.child), .nonterminal (.aux site.site)]
          (head, (tail, ())) := by
        change _ = GrammarSymbolValue.directSourceTrace owned
          (.nonterminal (.aux site.child)) head ++
            (GrammarSymbolValue.directSourceTrace owned
              (.nonterminal (.aux site.site)) tail ++ [])
        simp only [GrammarSymbolValue.directSourceTrace_nonterminal,
          NonterminalValue.directSourceTrace_aux, List.append_nil]
    _ = GrammarSymbolValues.directSourceTrace owned
          (ProductionId.star site .cons).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.directSourceTrace_view owned
            (ProductionId.rhs_star_cons site) values)

@[simp] theorem StarSite.pack_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : StarSite)
    (branch : NilConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site branch).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (StarSite.pack site branch values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.star site branch).rhs values := by
  cases branch with
  | nil => exact StarSite.pack_nil_directSourceTrace owned site values
  | cons => exact StarSite.pack_cons_directSourceTrace owned site values

@[simp] theorem PlusSite.pack_one_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .one).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (PlusSite.pack site .one values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.plus site .one).rhs values := by
  rw [NonterminalValue.directSourceTrace_aux]
  rw [← EbnfValue.directSourceTrace_atShape owned site.expression_eq_plus]
  rw [PlusSite.pack_one_eq]
  rw [EbnfValue.directSourceTrace_plus]
  simp only [List.flatMap_nil, List.append_nil]
  calc
    _ = GrammarSymbolValues.directSourceTrace owned
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_plus_one site) values) := by
        exact (GrammarSymbolValues.directSourceTrace_singleton owned
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_plus_one site) values).1).symm
    _ = GrammarSymbolValues.directSourceTrace owned
          (ProductionId.plus site .one).rhs values :=
        GrammarSymbolValues.directSourceTrace_view owned
          (ProductionId.rhs_plus_one site) values

@[simp] theorem PlusSite.pack_cons_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .cons).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (PlusSite.pack site .cons values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.plus site .cons).rhs values := by
  rw [NonterminalValue.directSourceTrace_aux]
  rw [← EbnfValue.directSourceTrace_atShape owned site.expression_eq_plus]
  rw [PlusSite.pack_cons_eq]
  rw [EbnfValue.directSourceTrace_plus]
  simp only [List.flatMap_cons]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_plus_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  rw [← EbnfValue.directSourceTrace_plus_raw owned
    site.child.expression
    (EbnfValue.atShape site.expression_eq_plus tail)]
  rw [EbnfValue.directSourceTrace_atShape]
  calc
    _ = GrammarSymbolValues.directSourceTrace owned
          [.nonterminal (.aux site.child), .nonterminal (.aux site.site)]
          (head, (tail, ())) := by
        change _ = GrammarSymbolValue.directSourceTrace owned
          (.nonterminal (.aux site.child)) head ++
            (GrammarSymbolValue.directSourceTrace owned
              (.nonterminal (.aux site.site)) tail ++ [])
        simp only [GrammarSymbolValue.directSourceTrace_nonterminal,
          NonterminalValue.directSourceTrace_aux, List.append_nil]
    _ = GrammarSymbolValues.directSourceTrace owned
          (ProductionId.plus site .cons).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.directSourceTrace_view owned
            (ProductionId.rhs_plus_cons site) values)

@[simp] theorem PlusSite.pack_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : PlusSite)
    (branch : OneConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site branch).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (PlusSite.pack site branch values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.plus site branch).rhs values := by
  cases branch with
  | one => exact PlusSite.pack_one_directSourceTrace owned site values
  | cons => exact PlusSite.pack_cons_directSourceTrace owned site values

@[simp] theorem List0Site.pack_nil_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .nil).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (List0Site.pack site .nil values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.list0 site .nil).rhs values := by
  rw [NonterminalValue.directSourceTrace_aux]
  rw [← EbnfValue.directSourceTrace_atShape owned site.expression_eq_list0]
  rw [List0Site.pack_nil_eq]
  rw [EbnfValue.directSourceTrace_list0]
  exact GrammarSymbolValues.directSourceTrace_view owned
    (ProductionId.rhs_list0_nil site) values

@[simp] theorem List0Site.pack_cons_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .cons).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (List0Site.pack site .cons values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.list0 site .cons).rhs values := by
  rw [NonterminalValue.directSourceTrace_aux]
  rw [← EbnfValue.directSourceTrace_atShape owned site.expression_eq_list0]
  rw [List0Site.pack_cons_eq]
  rw [EbnfValue.directSourceTrace_list0]
  simp only [List.flatMap_cons]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_list0_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  rw [EbnfValue.flatMap_directSourceTrace_transport_site owned
    (Grammar.ListSite.element_list0 site) tail]
  calc
    _ = GrammarSymbolValues.directSourceTrace owned
          [.nonterminal (.aux site.element),
            .nonterminal (.tail (.list0 site))]
          (head, (tail, ())) := by
        change _ = GrammarSymbolValue.directSourceTrace owned
          (.nonterminal (.aux site.element)) head ++
            (GrammarSymbolValue.directSourceTrace owned
              (.nonterminal (.tail (.list0 site))) tail ++ [])
        simp only [GrammarSymbolValue.directSourceTrace_nonterminal,
          NonterminalValue.directSourceTrace_aux,
          NonterminalValue.directSourceTrace_tail, List.append_nil]
    _ = GrammarSymbolValues.directSourceTrace owned
          (ProductionId.list0 site .cons).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.directSourceTrace_view owned
            (ProductionId.rhs_list0_cons site) values)

@[simp] theorem List0Site.pack_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : List0Site)
    (branch : NilConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site branch).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (List0Site.pack site branch values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.list0 site branch).rhs values := by
  cases branch with
  | nil => exact List0Site.pack_nil_directSourceTrace owned site values
  | cons => exact List0Site.pack_cons_directSourceTrace owned site values

@[simp] theorem List1Site.pack_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : List1Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list1 site).rhs) :
    NonterminalValue.directSourceTrace owned (.aux site.site)
        (List1Site.pack site values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.list1 site).rhs values := by
  rw [NonterminalValue.directSourceTrace_aux]
  rw [← EbnfValue.directSourceTrace_atShape owned site.expression_eq_list1]
  rw [List1Site.pack_eq]
  rw [EbnfValue.directSourceTrace_list1]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_list1 site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  rw [EbnfValue.flatMap_directSourceTrace_transport_site owned
    (Grammar.ListSite.element_list1 site) tail]
  calc
    _ = GrammarSymbolValues.directSourceTrace owned
          [.nonterminal (.aux site.element),
            .nonterminal (.tail (.list1 site))]
          (head, (tail, ())) := by
        change _ = GrammarSymbolValue.directSourceTrace owned
          (.nonterminal (.aux site.element)) head ++
            (GrammarSymbolValue.directSourceTrace owned
              (.nonterminal (.tail (.list1 site))) tail ++ [])
        simp only [GrammarSymbolValue.directSourceTrace_nonterminal,
          NonterminalValue.directSourceTrace_aux,
          NonterminalValue.directSourceTrace_tail, List.append_nil]
    _ = GrammarSymbolValues.directSourceTrace owned
          (ProductionId.list1 site).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.directSourceTrace_view owned
            (ProductionId.rhs_list1 site) values)

@[simp] theorem ListSite.pack_nil_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .nil).rhs) :
    NonterminalValue.directSourceTrace owned (.tail site)
        (ListSite.pack site .nil values) =
      GrammarSymbolValues.directSourceTrace owned
        (ProductionId.tail site .nil).rhs values := by
  rw [ListSite.pack_nil_eq]
  rw [NonterminalValue.directSourceTrace_tail]
  simp only [List.flatMap_nil]
  exact GrammarSymbolValues.directSourceTrace_view owned
    (ProductionId.rhs_tail_nil site) values

theorem ListSite.pack_cons_rhs_directSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (site : ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .cons).rhs) :
    GrammarSymbolValues.directSourceTrace owned
        (ProductionId.tail site .cons).rhs values =
      (GrammarSymbolValues.view
          (ProductionId.rhs_tail_cons site) values).1.sourceAnchorTrace owned ++
        NonterminalValue.directSourceTrace owned (.tail site)
          (ListSite.pack site .cons values) := by
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_tail_cons site) values = viewed
  rcases viewed with ⟨comma, head, tail, restUnit⟩
  cases restUnit
  rw [ListSite.pack_cons_eq]
  rw [viewedEq]
  rw [NonterminalValue.directSourceTrace_tail]
  calc
    _ = GrammarSymbolValues.directSourceTrace owned
          [.terminal (.symbol .comma),
            .nonterminal (.aux site.element),
            .nonterminal (.tail site)]
          (comma, (head, (tail, ()))) := by
        symm
        simpa [viewedEq] using
          (GrammarSymbolValues.directSourceTrace_view owned
            (ProductionId.rhs_tail_cons site) values)
    _ = comma.sourceAnchorTrace owned ++
          (head.directSourceTrace owned ++
            tail.flatMap fun element => element.directSourceTrace owned) := by
        change comma.sourceAnchorTrace owned ++
            (GrammarSymbolValue.directSourceTrace owned
              (.nonterminal (.aux site.element)) head ++
              (GrammarSymbolValue.directSourceTrace owned
                (.nonterminal (.tail site)) tail ++ [])) = _
        simp only [GrammarSymbolValue.directSourceTrace_nonterminal,
          NonterminalValue.directSourceTrace_aux,
          NonterminalValue.directSourceTrace_tail, List.append_nil]

namespace ActionReduces

/-- Direct terminals retained by an auxiliary result occur in the input
terminal trace; comma-tail actions may discard their separator. -/
theorem auxiliary_directSourceTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {production : ProductionId}
    {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens production.rhs}
    {output : NonterminalValue file tokens production.lhs}
    (auxiliary : AuxiliaryProduction production)
    (reduces : ActionReduces file tokens (.actionFor production)
      origin finish input output) :
    (NonterminalValue.directSourceTrace owned production.lhs output).Sublist
      (GrammarSymbolValues.directSourceTrace owned production.rhs input) := by
  cases reduces with
  | root rule origin finish input output reduction =>
      exact False.elim auxiliary
  | atom site origin finish input =>
      change (NonterminalValue.directSourceTrace owned (.aux site.site)
        (AtomSite.pack site input)).Sublist _
      rw [AtomSite.pack_directSourceTrace owned site input]
      exact List.Sublist.refl _
  | seq site origin finish input =>
      change (NonterminalValue.directSourceTrace owned (.aux site.site)
        (SequenceSite.pack site input)).Sublist _
      rw [SequenceSite.pack_directSourceTrace owned site input]
      exact List.Sublist.refl _
  | group site origin finish input =>
      change (NonterminalValue.directSourceTrace owned (.aux site.site)
        (GroupSite.pack site input)).Sublist _
      rw [GroupSite.pack_directSourceTrace owned site input]
      exact List.Sublist.refl _
  | choice site branch origin finish input =>
      change (NonterminalValue.directSourceTrace owned (.aux site.site)
        (ChoiceSite.pack site branch input)).Sublist _
      rw [ChoiceSite.pack_directSourceTrace owned site branch input]
      exact List.Sublist.refl _
  | opt site branch origin finish input =>
      change (NonterminalValue.directSourceTrace owned (.aux site.site)
        (OptionalSite.pack site branch input)).Sublist _
      rw [OptionalSite.pack_directSourceTrace owned site branch input]
      exact List.Sublist.refl _
  | star site branch origin finish input =>
      change (NonterminalValue.directSourceTrace owned (.aux site.site)
        (StarSite.pack site branch input)).Sublist _
      rw [StarSite.pack_directSourceTrace owned site branch input]
      exact List.Sublist.refl _
  | plus site branch origin finish input =>
      change (NonterminalValue.directSourceTrace owned (.aux site.site)
        (PlusSite.pack site branch input)).Sublist _
      rw [PlusSite.pack_directSourceTrace owned site branch input]
      exact List.Sublist.refl _
  | list0 site branch origin finish input =>
      change (NonterminalValue.directSourceTrace owned (.aux site.site)
        (List0Site.pack site branch input)).Sublist _
      rw [List0Site.pack_directSourceTrace owned site branch input]
      exact List.Sublist.refl _
  | list1 site origin finish input =>
      change (NonterminalValue.directSourceTrace owned (.aux site.site)
        (List1Site.pack site input)).Sublist _
      rw [List1Site.pack_directSourceTrace owned site input]
      exact List.Sublist.refl _
  | tail site branch origin finish input =>
      cases branch with
      | nil =>
          change (NonterminalValue.directSourceTrace owned (.tail site)
            (ListSite.pack site .nil input)).Sublist _
          rw [ListSite.pack_nil_directSourceTrace owned site input]
          exact List.Sublist.refl _
      | cons =>
          change (NonterminalValue.directSourceTrace owned (.tail site)
            (ListSite.pack site .cons input)).Sublist _
          rw [ListSite.pack_cons_rhs_directSourceTrace owned site input]
          exact List.sublist_append_right _ _

/-- Every generated action preserves the direct terminal trace of its output
as a sublist of the trace presented to the action.  Source-rule outputs expose
no direct EBNF terminals, while auxiliary outputs satisfy the stronger
auxiliary theorem above. -/
theorem directSourceTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {production : ProductionId}
    {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens production.rhs}
    {output : NonterminalValue file tokens production.lhs}
    (reduces : ActionReduces file tokens (.actionFor production)
      origin finish input output) :
    (NonterminalValue.directSourceTrace owned production.lhs output).Sublist
      (GrammarSymbolValues.directSourceTrace owned production.rhs input) := by
  cases reduces with
  | root rule origin finish input output reduction =>
      change [].Sublist _
      exact List.nil_sublist _
  | atom site origin finish input =>
      exact auxiliary_directSourceTrace_sublist owned (by trivial)
        (.atom site origin finish input)
  | seq site origin finish input =>
      exact auxiliary_directSourceTrace_sublist owned (by trivial)
        (.seq site origin finish input)
  | group site origin finish input =>
      exact auxiliary_directSourceTrace_sublist owned (by trivial)
        (.group site origin finish input)
  | choice site branch origin finish input =>
      exact auxiliary_directSourceTrace_sublist owned (by trivial)
        (.choice site branch origin finish input)
  | opt site branch origin finish input =>
      exact auxiliary_directSourceTrace_sublist owned (by trivial)
        (.opt site branch origin finish input)
  | star site branch origin finish input =>
      exact auxiliary_directSourceTrace_sublist owned (by trivial)
        (.star site branch origin finish input)
  | plus site branch origin finish input =>
      exact auxiliary_directSourceTrace_sublist owned (by trivial)
        (.plus site branch origin finish input)
  | list0 site branch origin finish input =>
      exact auxiliary_directSourceTrace_sublist owned (by trivial)
        (.list0 site branch origin finish input)
  | list1 site origin finish input =>
      exact auxiliary_directSourceTrace_sublist owned (by trivial)
        (.list1 site origin finish input)
  | tail site branch origin finish input =>
      exact auxiliary_directSourceTrace_sublist owned (by trivial)
        (.tail site branch origin finish input)

end ActionReduces

private def PrefixDirectSourceTraceMotive
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
  (PrefixValues.directSourceTrace owned item values).Sublist trace

private def ReductionDirectSourceTraceMotive
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
  (NonterminalValue.directSourceTrace owned
    item.raw.production.lhs value).Sublist trace

private theorem prefixDirectSourceTraceZeroCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final item)
    (zero : item.raw.dot.val = 0) :
    PrefixDirectSourceTraceMotive file tokens memo correct final owned
      (.zero item reached zero) [] (.zero item reached zero) := by
  unfold PrefixDirectSourceTraceMotive
  rw [PrefixValues.directSourceTrace_zeroValue]
  exact List.Sublist.refl []

private theorem prefixDirectSourceTraceScanCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
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
    (priorIH : PrefixDirectSourceTraceMotive
      file tokens memo correct final owned prior priorTrace priorCarries) :
    PrefixDirectSourceTraceMotive file tokens memo correct final owned
      (.scan before after cursor priorValues witness edge prior)
      (priorTrace ++ witness.matched.sourceAnchorTrace owned)
      (.scan before after cursor priorValues witness edge prior priorTrace
        priorCarries) := by
  unfold PrefixDirectSourceTraceMotive at priorIH ⊢
  rw [PrefixValues.directSourceTrace_scanValue]
  exact priorIH.append
    (List.Sublist.refl (witness.matched.sourceAnchorTrace owned))

private theorem prefixDirectSourceTraceCompleteCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
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
    (priorIH : PrefixDirectSourceTraceMotive
      file tokens memo correct final owned prior priorTrace priorCarries)
    (childIH : ReductionDirectSourceTraceMotive
      file tokens memo correct final owned child childTrace childCarries) :
    PrefixDirectSourceTraceMotive file tokens memo correct final owned
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child)
      (priorTrace ++ childTrace)
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child priorTrace childTrace priorCarries childCarries) := by
  unfold PrefixDirectSourceTraceMotive at priorIH ⊢
  unfold ReductionDirectSourceTraceMotive at childIH
  rw [PrefixValues.directSourceTrace_completeValue]
  exact priorIH.append childIH

private theorem reductionDirectSourceTraceCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
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
    (prefixIH : PrefixDirectSourceTraceMotive
      file tokens memo correct final owned coherentPrefix trace
        prefixCarries) :
    ReductionDirectSourceTraceMotive file tokens memo correct final owned
      (.reduce item priorValues output reached complete coherentPrefix action)
      trace
      (.reduce item priorValues output reached complete coherentPrefix action
        trace prefixCarries) := by
  unfold PrefixDirectSourceTraceMotive at prefixIH
  unfold ReductionDirectSourceTraceMotive
  have fullInput :
      (GrammarSymbolValues.directSourceTrace owned item.raw.production.rhs
        (PrefixValues.fullValue item complete priorValues)).Sublist trace := by
    rw [PrefixValues.directSourceTrace_fullValue]
    exact prefixIH
  exact (ActionReduces.directSourceTrace_sublist owned action).trans fullInput

namespace PrefixCarriesSourceTrace

/-- Direct terminals still exposed by a coherent semantic prefix occur in its
exact physical trace in source order. -/
theorem directSourceTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    {coherent : CoherentPrefix file tokens memo correct final item values}
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    (PrefixValues.directSourceTrace owned item values).Sublist trace :=
  PrefixCarriesSourceTrace.rec
    (motive_1 := PrefixDirectSourceTraceMotive
      file tokens memo correct final owned)
    (motive_2 := ReductionDirectSourceTraceMotive
      file tokens memo correct final owned)
    (prefixDirectSourceTraceZeroCase owned)
    (prefixDirectSourceTraceScanCase owned)
    (prefixDirectSourceTraceCompleteCase owned)
    (reductionDirectSourceTraceCase owned)
    carries

/-- The semantic prefix's direct terminals inherit both interval containment
and physical source order from the exact coherent trace. -/
theorem directSourceTrace_within_and_ordered
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    {coherent : CoherentPrefix file tokens memo correct final item values}
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    (PrefixValues.directSourceTrace owned item values).Within
        item.raw.origin item.raw.current ∧
      (PrefixValues.directSourceTrace owned item values).Ordered := by
  have semanticSublist := carries.directSourceTrace_sublist
  have traceGeometry := carries.within_and_ordered
  constructor
  · intro anchor member
    exact traceGeometry.1 anchor (semanticSublist.subset member)
  · exact List.Pairwise.sublist semanticSublist traceGeometry.2

end PrefixCarriesSourceTrace

namespace ReductionCarriesSourceTrace

/-- Direct terminals retained by a coherent auxiliary result occur in its
exact physical trace.  Source-rule results expose no direct EBNF terminals. -/
theorem directSourceTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {value : NonterminalValue file tokens item.raw.production.lhs}
    {coherent : CoherentReduction file tokens memo correct final item value}
    {trace : SourceAnchorTrace file tokens}
    (carries : ReductionCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    (NonterminalValue.directSourceTrace owned
      item.raw.production.lhs value).Sublist trace :=
  ReductionCarriesSourceTrace.rec
    (motive_1 := PrefixDirectSourceTraceMotive
      file tokens memo correct final owned)
    (motive_2 := ReductionDirectSourceTraceMotive
      file tokens memo correct final owned)
    (prefixDirectSourceTraceZeroCase owned)
    (prefixDirectSourceTraceScanCase owned)
    (prefixDirectSourceTraceCompleteCase owned)
    (reductionDirectSourceTraceCase owned)
    carries

/-- The semantic reduction's direct terminals inherit both interval
containment and physical source order from the exact coherent trace. -/
theorem directSourceTrace_within_and_ordered
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {value : NonterminalValue file tokens item.raw.production.lhs}
    {coherent : CoherentReduction file tokens memo correct final item value}
    {trace : SourceAnchorTrace file tokens}
    (carries : ReductionCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    (NonterminalValue.directSourceTrace owned
        item.raw.production.lhs value).Within
        item.raw.origin item.raw.current ∧
      (NonterminalValue.directSourceTrace owned
        item.raw.production.lhs value).Ordered := by
  have semanticSublist := carries.directSourceTrace_sublist
  have traceGeometry := carries.within_and_ordered
  constructor
  · intro anchor member
    exact traceGeometry.1 anchor (semanticSublist.subset member)
  · exact List.Pairwise.sublist semanticSublist traceGeometry.2

end ReductionCarriesSourceTrace

namespace SourceAnchorTrace

/-- Any two anchors selected in source order from an ordered physical trace
have nonoverlapping parser intervals. -/
theorem finish_le_origin_of_pair_sublist
    {file : WorkspaceFile} {tokens : List Token}
    {left right : SourceAnchor file tokens}
    {trace : SourceAnchorTrace file tokens}
    (selected : [left, right].Sublist trace)
    (ordered : trace.Ordered) :
    left.finish.val ≤ right.origin.val := by
  have pairOrdered :
      List.Pairwise
        (fun earlier later : SourceAnchor file tokens =>
          earlier.finish.val ≤ later.origin.val)
        [left, right] :=
    List.Pairwise.sublist selected ordered
  simpa [List.pairwise_cons] using pairOrdered

end SourceAnchorTrace

namespace MatchedTerminal

/-- A pair of non-EOF terminals selected from an ordered semantic terminal
trace occurs in parser order. -/
theorem cursor_order_of_pair_sublist
    {file : WorkspaceFile} {tokens : List Token}
    {leftTerminal rightTerminal : TerminalSymbol}
    (owned : TokensOwnedBy file tokens)
    (left : MatchedTerminal file tokens leftTerminal)
    (right : MatchedTerminal file tokens rightTerminal)
    (leftNotEof : leftTerminal ≠ .endOfFile)
    (rightNotEof : rightTerminal ≠ .endOfFile)
    {trace : SourceAnchorTrace file tokens}
    (selected :
      [left.sourceAnchor owned leftNotEof,
        right.sourceAnchor owned rightNotEof].Sublist trace)
    (ordered : trace.Ordered) :
    left.cursor.afterBoundary.val ≤ right.cursor.beforeBoundary.val := by
  exact SourceAnchorTrace.finish_le_origin_of_pair_sublist selected ordered

end MatchedTerminal

namespace PrefixCarriesSourceTrace

/-- The direct terminals of a completed coherent prefix's full action input
form an ordered sublist of its exact physical trace. -/
theorem fullValue_directSourceTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {priorValues : PrefixValues file tokens item}
    {coherent : CoherentPrefix file tokens memo correct final item priorValues}
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace)
    (complete : CompleteItem item.raw) :
    (GrammarSymbolValues.directSourceTrace owned item.raw.production.rhs
      (PrefixValues.fullValue item complete priorValues)).Sublist trace := by
  rw [PrefixValues.directSourceTrace_fullValue]
  exact carries.directSourceTrace_sublist

/-- Direct terminals of a complete action input also inherit the enclosing
interval and source order. -/
theorem fullValue_directSourceTrace_within_and_ordered
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {priorValues : PrefixValues file tokens item}
    {coherent : CoherentPrefix file tokens memo correct final item priorValues}
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace)
    (complete : CompleteItem item.raw) :
    (GrammarSymbolValues.directSourceTrace owned item.raw.production.rhs
        (PrefixValues.fullValue item complete priorValues)).Within
        item.raw.origin item.raw.current ∧
      (GrammarSymbolValues.directSourceTrace owned item.raw.production.rhs
        (PrefixValues.fullValue item complete priorValues)).Ordered := by
  rw [PrefixValues.directSourceTrace_fullValue]
  exact carries.directSourceTrace_within_and_ordered

end PrefixCarriesSourceTrace

namespace RuleReduction

/-- The direct terminals visible in the exact EBNF input indexed by one
source-rule reduction. -/
abbrev inputDirectSourceTrace
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (_reduces : RuleReduction file tokens rule origin finish input output) :
    SourceAnchorTrace file tokens :=
  input.directSourceTrace owned

@[simp] theorem directSourceTrace_ruleAtoms
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (rule : GrammarRuleId) (values : List (RuleValue rule)) :
    (values.map
      (EbnfValue.ruleAtom (file := file) (tokens := tokens) rule)).flatMap
        (fun value => value.directSourceTrace owned) = [] := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

@[simp] theorem directSourceTrace_optional_ruleAtom
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (rule : GrammarRuleId) (value : Option (RuleValue rule)) :
    EbnfValue.directSourceTrace owned
      (EbnfValue.optional (.atom (.nonterminal rule))
        (value.map
          (EbnfValue.ruleAtom (file := file) (tokens := tokens) rule))) = [] := by
  cases value <;> simp

@[simp] theorem inputDirectSourceTrace_importDeclItems
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ImportSelectorEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (hidingValue : Option HidingClause)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    inputDirectSourceTrace owned
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness) =
      importKw.sourceAnchorTrace owned ++ dot.sourceAnchorTrace owned ++
        openBrace.sourceAnchorTrace owned ++
          closeBrace.sourceAnchorTrace owned ++
            semicolon.sourceAnchorTrace owned := by
  simp [inputDirectSourceTrace]

@[simp] theorem inputDirectSourceTrace_exportDeclLocal
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    inputDirectSourceTrace owned
        (RuleReduction.exportDeclLocal origin finish exportKw openBrace
          entries closeBrace semicolon witness) =
      exportKw.sourceAnchorTrace owned ++ openBrace.sourceAnchorTrace owned ++
        closeBrace.sourceAnchorTrace owned ++
          semicolon.sourceAnchorTrace owned := by
  simp [inputDirectSourceTrace]

end RuleReduction

namespace OccupiedConsumedSpan

/-- The exact span from the first token of an occupied left interval through
the last token of an occupied right interval. -/
theorem between
    {file : WorkspaceFile} {tokens : List Token}
    {leftOrigin leftFinish rightOrigin rightFinish : Boundary tokens}
    {leftSpan rightSpan : SourceSpan}
    (left : OccupiedConsumedSpan file tokens
      leftOrigin leftFinish leftSpan)
    (right : OccupiedConsumedSpan file tokens
      rightOrigin rightFinish rightSpan)
    (ordered : leftOrigin.val ≤ rightOrigin.val) :
    OccupiedConsumedSpan file tokens leftOrigin rightFinish
      (RuleReduction.between file leftSpan rightSpan ()).span := by
  rcases left with ⟨leftConsumed, leftOccupied⟩
  rcases right with ⟨rightConsumed, rightOccupied⟩
  unfold ConsumedSpan at leftConsumed rightConsumed
  rcases leftConsumed with ⟨owned, leftIntervalOrdered, leftShape⟩
  rcases rightConsumed with
    ⟨_rightOwned, rightIntervalOrdered, rightShape⟩
  have outerOrdered : leftOrigin.val ≤ rightFinish.val := by omega
  have outerOccupied :
      leftOrigin.val < Nat.min rightFinish.val tokens.length := by
    apply Nat.lt_min.mpr
    have rightBounds := Nat.lt_min.mp rightOccupied
    exact ⟨by omega, Nat.lt_of_lt_of_le leftOccupied
      (Nat.min_le_right _ _)⟩
  refine ⟨⟨owned, outerOrdered, ?_⟩, outerOccupied⟩
  simp only [outerOccupied, ↓reduceDIte]
  simp only [leftOccupied, ↓reduceDIte] at leftShape
  simp only [rightOccupied, ↓reduceDIte] at rightShape
  unfold RuleReduction.between
  simp only
  rw [leftShape, rightShape]

end OccupiedConsumedSpan

namespace SourceAnchor

/-- Join two occupied semantic endpoints into one exact synthetic anchor. -/
def between
    {file : WorkspaceFile} {tokens : List Token}
    (left right : SourceAnchor file tokens)
    (ordered : left.origin.val ≤ right.origin.val) :
    SourceAnchor file tokens := {
  origin := left.origin
  finish := right.finish
  span := (RuleReduction.between file left.span right.span ()).span
  occupied := left.occupied.between right.occupied ordered
}

@[simp] theorem between_origin
    {file : WorkspaceFile} {tokens : List Token}
    (left right : SourceAnchor file tokens)
    (ordered : left.origin.val ≤ right.origin.val) :
    (SourceAnchor.between left right ordered).origin = left.origin := by
  rfl

@[simp] theorem between_finish
    {file : WorkspaceFile} {tokens : List Token}
    (left right : SourceAnchor file tokens)
    (ordered : left.origin.val ≤ right.origin.val) :
    (SourceAnchor.between left right ordered).finish = right.finish := by
  rfl

@[simp] theorem between_span
    {file : WorkspaceFile} {tokens : List Token}
    (left right : SourceAnchor file tokens)
    (ordered : left.origin.val ≤ right.origin.val) :
    (SourceAnchor.between left right ordered).span =
      (RuleReduction.between file left.span right.span ()).span := by
  rfl

end SourceAnchor

namespace IntervalLocationEvidence

/-- Wrap children that occupy exactly the parser interval between two
source-ordered anchors.  This is the reusable synthetic-root step for infix,
postfix, and delimiter-bounded semantic nodes. -/
theorem locatedBetween
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (left right : SourceAnchor file tokens)
    (ordered : left.origin.val ≤ right.origin.val)
    {children : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (evidence : IntervalLocationEvidence file tokens
      left.origin right.finish children trace) :
    IntervalLocationEvidence file tokens left.origin right.finish
      (LocationFragment.located
        (RuleReduction.between file left.span right.span ()).span
        [children]) trace := by
  let anchor := SourceAnchor.between left right ordered
  have contains : children.RootsContainedBy anchor.span :=
    rootsContainedBy tokensOrdered anchor.occupied.1 evidence
  exact located tokensOrdered anchor evidence contains

/-- Install an anchored wrapper inside a larger parser interval. -/
theorem locatedInside
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {outerOrigin outerFinish : Boundary tokens}
    (anchor : SourceAnchor file tokens)
    {children : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (evidence : IntervalLocationEvidence file tokens
      outerOrigin outerFinish children trace)
    (inside : anchor.Within outerOrigin outerFinish)
    (contains : children.RootsContainedBy anchor.span) :
    IntervalLocationEvidence file tokens outerOrigin outerFinish
      (LocationFragment.located anchor.span [children]) trace := by
  rcases evidence with
    ⟨_childRoots, _childRootSpans, _childRootsWithin, traceWithin,
      traceOrdered, childValid, childNested⟩
  refine ⟨[anchor], rfl, ?_, traceWithin, traceOrdered, ?_, ?_⟩
  · intro selected member
    simp only [List.mem_singleton] at member
    subst selected
    exact inside
  · intro span member
    rw [LocationFragment.located_spans] at member
    rcases List.mem_cons.mp member with outer | childMember
    · subst span
      exact anchor.span_validFor tokensOrdered
    · exact childValid span (by simpa using childMember)
  · intro containment member
    rw [LocationFragment.located_containments] at member
    rcases List.mem_append.mp member with direct | nestedMember
    · rw [List.mem_map] at direct
      rcases direct with ⟨child, childMember, rfl⟩
      exact contains child (by simpa using childMember)
    · exact childNested containment (by simpa using nestedMember)

/-- Merge semantic inventories certified over the same parser interval while
retaining one unchanged physical trace. -/
theorem mergeSameInterval
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {leftFragment rightFragment : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (left : IntervalLocationEvidence file tokens origin finish
      leftFragment trace)
    (right : IntervalLocationEvidence file tokens origin finish
      rightFragment trace) :
    IntervalLocationEvidence file tokens origin finish
      (LocationFragment.merge [leftFragment, rightFragment]) trace := by
  rcases left with
    ⟨leftRoots, leftRootSpans, leftRootsWithin, traceWithin,
      traceOrdered, leftValid, leftNested⟩
  rcases right with
    ⟨rightRoots, rightRootSpans, rightRootsWithin, _rightTraceWithin,
      _rightTraceOrdered, rightValid, rightNested⟩
  refine ⟨leftRoots ++ rightRoots, ?_, ?_, traceWithin, traceOrdered, ?_, ?_⟩
  · simp [leftRootSpans, rightRootSpans]
  · rw [SourceAnchorTrace.within_append]
    exact ⟨leftRootsWithin, rightRootsWithin⟩
  · apply LocationFragment.merge_validFor
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact leftValid
    · exact rightValid
  · apply LocationFragment.merge_nested
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact leftNested
    · exact rightNested

end IntervalLocationEvidence

end Solcore.Surface.Multi
namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

mutual

inductive EbnfValue.DirectlyContainsMatchedTerminal
    (file : WorkspaceFile) (tokens : List Token) :
    {expression : EbnfExpr} → EbnfValue file tokens expression →
      (terminal : TerminalSymbol) →
      MatchedTerminal file tokens terminal → Prop where
  | terminal (terminal : TerminalSymbol)
      (matched : MatchedTerminal file tokens terminal) :
      EbnfValue.DirectlyContainsMatchedTerminal file tokens
        (EbnfValue.terminalAtom terminal matched) terminal matched
  | transport {left right : EbnfExpr} (shape : left = right)
      {input : EbnfValue file tokens left}
      {terminal : TerminalSymbol}
      {matched : MatchedTerminal file tokens terminal}
      (inside : EbnfValue.DirectlyContainsMatchedTerminal
        file tokens input terminal matched) :
      EbnfValue.DirectlyContainsMatchedTerminal file tokens
        (EbnfValue.transport shape input) terminal matched
  | sequence {children : List EbnfExpr}
      {values : EbnfValues file tokens children}
      {terminal : TerminalSymbol}
      {matched : MatchedTerminal file tokens terminal}
      (inside : EbnfValues.DirectlyContainsMatchedTerminal
        file tokens values terminal matched) :
      EbnfValue.DirectlyContainsMatchedTerminal file tokens
        (EbnfValue.sequence children values) terminal matched
  | group {child : EbnfExpr}
      {value : EbnfValue file tokens child}
      {terminal : TerminalSymbol}
      {matched : MatchedTerminal file tokens terminal}
      (inside : EbnfValue.DirectlyContainsMatchedTerminal
        file tokens value terminal matched) :
      EbnfValue.DirectlyContainsMatchedTerminal file tokens
        (EbnfValue.group child value) terminal matched
  | choice {branches : List EbnfExpr}
      (branch : Fin branches.length)
      {value : EbnfValue file tokens (branches.get branch)}
      {terminal : TerminalSymbol}
      {matched : MatchedTerminal file tokens terminal}
      (inside : EbnfValue.DirectlyContainsMatchedTerminal
        file tokens value terminal matched) :
      EbnfValue.DirectlyContainsMatchedTerminal file tokens
        (EbnfValue.choice branches ⟨branch, value⟩) terminal matched

inductive EbnfValues.DirectlyContainsMatchedTerminal
    (file : WorkspaceFile) (tokens : List Token) :
    {expressions : List EbnfExpr} → EbnfValues file tokens expressions →
      (terminal : TerminalSymbol) →
      MatchedTerminal file tokens terminal → Prop where
  | head {child : EbnfExpr} {rest : List EbnfExpr}
      {head : EbnfValue file tokens child}
      {tail : EbnfValues file tokens rest}
      {terminal : TerminalSymbol}
      {matched : MatchedTerminal file tokens terminal}
      (inside : EbnfValue.DirectlyContainsMatchedTerminal
        file tokens head terminal matched) :
      EbnfValues.DirectlyContainsMatchedTerminal file tokens
        (EbnfValues.cons child rest head tail) terminal matched
  | tail {child : EbnfExpr} {rest : List EbnfExpr}
      {head : EbnfValue file tokens child}
      {tail : EbnfValues file tokens rest}
      {terminal : TerminalSymbol}
      {matched : MatchedTerminal file tokens terminal}
      (inside : EbnfValues.DirectlyContainsMatchedTerminal
        file tokens tail terminal matched) :
      EbnfValues.DirectlyContainsMatchedTerminal file tokens
        (EbnfValues.cons child rest head tail) terminal matched

end

private def DirectTerminalValueTraceMotive
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    {expression : EbnfExpr} (input : EbnfValue file tokens expression)
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal)
    (_inside : EbnfValue.DirectlyContainsMatchedTerminal
      file tokens input terminal matched) : Prop :=
  (matched.sourceAnchorTrace owned).Sublist
    (input.directSourceTrace owned)

private def DirectTerminalValuesTraceMotive
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    {expressions : List EbnfExpr}
    (input : EbnfValues file tokens expressions)
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal)
    (_inside : EbnfValues.DirectlyContainsMatchedTerminal
      file tokens input terminal matched) : Prop :=
  (matched.sourceAnchorTrace owned).Sublist
    (input.directSourceTrace owned)

theorem EbnfValue.DirectlyContainsMatchedTerminal.sourceAnchorTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    {terminal : TerminalSymbol}
    {matched : MatchedTerminal file tokens terminal}
    (inside : EbnfValue.DirectlyContainsMatchedTerminal
      file tokens input terminal matched) :
    (matched.sourceAnchorTrace owned).Sublist
      (input.directSourceTrace owned) :=
  EbnfValue.DirectlyContainsMatchedTerminal.rec
    (motive_1 := DirectTerminalValueTraceMotive file tokens owned)
    (motive_2 := DirectTerminalValuesTraceMotive file tokens owned)
    (fun terminal matched => by
      unfold DirectTerminalValueTraceMotive
      simp)
    (fun {left right} shape {input terminal matched} inside
        inductionHypothesis => by
      unfold DirectTerminalValueTraceMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {children values terminal matched} inside inductionHypothesis => by
      unfold DirectTerminalValuesTraceMotive at inductionHypothesis
      unfold DirectTerminalValueTraceMotive
      simpa using inductionHypothesis)
    (fun {child value terminal matched} inside inductionHypothesis => by
      unfold DirectTerminalValueTraceMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {branches} branch {value terminal matched} inside
        inductionHypothesis => by
      unfold DirectTerminalValueTraceMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {child rest head tail terminal matched} inside
        inductionHypothesis => by
      unfold DirectTerminalValueTraceMotive at inductionHypothesis
      unfold DirectTerminalValuesTraceMotive
      rw [EbnfValues.directSourceTrace_cons]
      exact inductionHypothesis.trans (List.sublist_append_left _ _))
    (fun {child rest head tail terminal matched} inside
        inductionHypothesis => by
      unfold DirectTerminalValuesTraceMotive at inductionHypothesis ⊢
      rw [EbnfValues.directSourceTrace_cons]
      exact inductionHypothesis.trans (List.sublist_append_right _ _))
    inside

theorem EbnfValues.DirectlyContainsMatchedTerminal.sourceAnchorTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {expressions : List EbnfExpr}
    {input : EbnfValues file tokens expressions}
    {terminal : TerminalSymbol}
    {matched : MatchedTerminal file tokens terminal}
    (inside : EbnfValues.DirectlyContainsMatchedTerminal
      file tokens input terminal matched) :
    (matched.sourceAnchorTrace owned).Sublist
      (input.directSourceTrace owned) :=
  EbnfValues.DirectlyContainsMatchedTerminal.rec
    (motive_1 := DirectTerminalValueTraceMotive file tokens owned)
    (motive_2 := DirectTerminalValuesTraceMotive file tokens owned)
    (fun terminal matched => by
      unfold DirectTerminalValueTraceMotive
      simp)
    (fun {left right} shape {input terminal matched} inside
        inductionHypothesis => by
      unfold DirectTerminalValueTraceMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {children values terminal matched} inside inductionHypothesis => by
      unfold DirectTerminalValuesTraceMotive at inductionHypothesis
      unfold DirectTerminalValueTraceMotive
      simpa using inductionHypothesis)
    (fun {child value terminal matched} inside inductionHypothesis => by
      unfold DirectTerminalValueTraceMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {branches} branch {value terminal matched} inside
        inductionHypothesis => by
      unfold DirectTerminalValueTraceMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {child rest head tail terminal matched} inside
        inductionHypothesis => by
      unfold DirectTerminalValueTraceMotive at inductionHypothesis
      unfold DirectTerminalValuesTraceMotive
      rw [EbnfValues.directSourceTrace_cons]
      exact inductionHypothesis.trans (List.sublist_append_left _ _))
    (fun {child rest head tail terminal matched} inside
        inductionHypothesis => by
      unfold DirectTerminalValuesTraceMotive at inductionHypothesis ⊢
      rw [EbnfValues.directSourceTrace_cons]
      exact inductionHypothesis.trans (List.sublist_append_right _ _))
    inside


mutual

inductive EbnfValue.DirectlyContainsMatchedTerminalBefore
    (file : WorkspaceFile) (tokens : List Token) :
    {expression : EbnfExpr} → EbnfValue file tokens expression →
      {leftTerminal : TerminalSymbol} →
      MatchedTerminal file tokens leftTerminal →
      {rightTerminal : TerminalSymbol} →
      MatchedTerminal file tokens rightTerminal → Prop where
  | transport {left right : EbnfExpr} (shape : left = right)
      {input : EbnfValue file tokens left}
      {leftTerminal rightTerminal : TerminalSymbol}
      {leftMatched : MatchedTerminal file tokens leftTerminal}
      {rightMatched : MatchedTerminal file tokens rightTerminal}
      (inside : EbnfValue.DirectlyContainsMatchedTerminalBefore file tokens
        input leftMatched rightMatched) :
      EbnfValue.DirectlyContainsMatchedTerminalBefore file tokens
        (EbnfValue.transport shape input) leftMatched rightMatched
  | sequence {children : List EbnfExpr}
      {values : EbnfValues file tokens children}
      {leftTerminal rightTerminal : TerminalSymbol}
      {leftMatched : MatchedTerminal file tokens leftTerminal}
      {rightMatched : MatchedTerminal file tokens rightTerminal}
      (inside : EbnfValues.DirectlyContainsMatchedTerminalBefore file tokens
        values leftMatched rightMatched) :
      EbnfValue.DirectlyContainsMatchedTerminalBefore file tokens
        (EbnfValue.sequence children values) leftMatched rightMatched
  | group {child : EbnfExpr} {value : EbnfValue file tokens child}
      {leftTerminal rightTerminal : TerminalSymbol}
      {leftMatched : MatchedTerminal file tokens leftTerminal}
      {rightMatched : MatchedTerminal file tokens rightTerminal}
      (inside : EbnfValue.DirectlyContainsMatchedTerminalBefore file tokens
        value leftMatched rightMatched) :
      EbnfValue.DirectlyContainsMatchedTerminalBefore file tokens
        (EbnfValue.group child value) leftMatched rightMatched
  | choice {branches : List EbnfExpr} (branch : Fin branches.length)
      {value : EbnfValue file tokens (branches.get branch)}
      {leftTerminal rightTerminal : TerminalSymbol}
      {leftMatched : MatchedTerminal file tokens leftTerminal}
      {rightMatched : MatchedTerminal file tokens rightTerminal}
      (inside : EbnfValue.DirectlyContainsMatchedTerminalBefore file tokens
        value leftMatched rightMatched) :
      EbnfValue.DirectlyContainsMatchedTerminalBefore file tokens
        (EbnfValue.choice branches ⟨branch, value⟩) leftMatched rightMatched

inductive EbnfValues.DirectlyContainsMatchedTerminalBefore
    (file : WorkspaceFile) (tokens : List Token) :
    {expressions : List EbnfExpr} → EbnfValues file tokens expressions →
      {leftTerminal : TerminalSymbol} →
      MatchedTerminal file tokens leftTerminal →
      {rightTerminal : TerminalSymbol} →
      MatchedTerminal file tokens rightTerminal → Prop where
  | head {child : EbnfExpr} {rest : List EbnfExpr}
      {head : EbnfValue file tokens child}
      {tail : EbnfValues file tokens rest}
      {leftTerminal rightTerminal : TerminalSymbol}
      {leftMatched : MatchedTerminal file tokens leftTerminal}
      {rightMatched : MatchedTerminal file tokens rightTerminal}
      (inside : EbnfValue.DirectlyContainsMatchedTerminalBefore file tokens
        head leftMatched rightMatched) :
      EbnfValues.DirectlyContainsMatchedTerminalBefore file tokens
        (EbnfValues.cons child rest head tail) leftMatched rightMatched
  | cross {child : EbnfExpr} {rest : List EbnfExpr}
      {head : EbnfValue file tokens child}
      {tail : EbnfValues file tokens rest}
      {leftTerminal rightTerminal : TerminalSymbol}
      {leftMatched : MatchedTerminal file tokens leftTerminal}
      {rightMatched : MatchedTerminal file tokens rightTerminal}
      (leftInside : EbnfValue.DirectlyContainsMatchedTerminal file tokens
        head leftTerminal leftMatched)
      (rightInside : EbnfValues.DirectlyContainsMatchedTerminal file tokens
        tail rightTerminal rightMatched) :
      EbnfValues.DirectlyContainsMatchedTerminalBefore file tokens
        (EbnfValues.cons child rest head tail) leftMatched rightMatched
  | tail {child : EbnfExpr} {rest : List EbnfExpr}
      {head : EbnfValue file tokens child}
      {tail : EbnfValues file tokens rest}
      {leftTerminal rightTerminal : TerminalSymbol}
      {leftMatched : MatchedTerminal file tokens leftTerminal}
      {rightMatched : MatchedTerminal file tokens rightTerminal}
      (inside : EbnfValues.DirectlyContainsMatchedTerminalBefore file tokens
        tail leftMatched rightMatched) :
      EbnfValues.DirectlyContainsMatchedTerminalBefore file tokens
        (EbnfValues.cons child rest head tail) leftMatched rightMatched

end



private def DirectTerminalPairValueTraceMotive
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    {expression : EbnfExpr} (input : EbnfValue file tokens expression)
    {leftTerminal : TerminalSymbol}
    (leftMatched : MatchedTerminal file tokens leftTerminal)
    {rightTerminal : TerminalSymbol}
    (rightMatched : MatchedTerminal file tokens rightTerminal)
    (_inside : EbnfValue.DirectlyContainsMatchedTerminalBefore file tokens
      input leftMatched rightMatched) : Prop :=
  (leftMatched.sourceAnchorTrace owned ++
    rightMatched.sourceAnchorTrace owned).Sublist
      (input.directSourceTrace owned)

private def DirectTerminalPairValuesTraceMotive
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    {expressions : List EbnfExpr}
    (input : EbnfValues file tokens expressions)
    {leftTerminal : TerminalSymbol}
    (leftMatched : MatchedTerminal file tokens leftTerminal)
    {rightTerminal : TerminalSymbol}
    (rightMatched : MatchedTerminal file tokens rightTerminal)
    (_inside : EbnfValues.DirectlyContainsMatchedTerminalBefore file tokens
      input leftMatched rightMatched) : Prop :=
  (leftMatched.sourceAnchorTrace owned ++
    rightMatched.sourceAnchorTrace owned).Sublist
      (input.directSourceTrace owned)

theorem EbnfValue.DirectlyContainsMatchedTerminalBefore.sourceAnchorTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    {leftTerminal rightTerminal : TerminalSymbol}
    {leftMatched : MatchedTerminal file tokens leftTerminal}
    {rightMatched : MatchedTerminal file tokens rightTerminal}
    (inside : EbnfValue.DirectlyContainsMatchedTerminalBefore file tokens
      input leftMatched rightMatched) :
    (leftMatched.sourceAnchorTrace owned ++
      rightMatched.sourceAnchorTrace owned).Sublist
        (input.directSourceTrace owned) :=
  EbnfValue.DirectlyContainsMatchedTerminalBefore.rec
    (motive_1 := DirectTerminalPairValueTraceMotive file tokens owned)
    (motive_2 := DirectTerminalPairValuesTraceMotive file tokens owned)
    (fun {left right} shape
        {input leftTerminal rightTerminal leftMatched rightMatched}
        inside inductionHypothesis => by
      unfold DirectTerminalPairValueTraceMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {children values leftTerminal rightTerminal leftMatched rightMatched}
        inside inductionHypothesis => by
      unfold DirectTerminalPairValuesTraceMotive at inductionHypothesis
      unfold DirectTerminalPairValueTraceMotive
      simpa using inductionHypothesis)
    (fun {child value leftTerminal rightTerminal leftMatched rightMatched}
        inside inductionHypothesis => by
      unfold DirectTerminalPairValueTraceMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {branches} branch
        {value leftTerminal rightTerminal leftMatched rightMatched}
        inside inductionHypothesis => by
      unfold DirectTerminalPairValueTraceMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {child rest head tail leftTerminal rightTerminal leftMatched
        rightMatched} inside inductionHypothesis => by
      unfold DirectTerminalPairValueTraceMotive at inductionHypothesis
      unfold DirectTerminalPairValuesTraceMotive
      rw [EbnfValues.directSourceTrace_cons]
      exact inductionHypothesis.trans (List.sublist_append_left _ _))
    (fun {child rest head tail leftTerminal rightTerminal leftMatched
        rightMatched} leftInside rightInside => by
      unfold DirectTerminalPairValuesTraceMotive
      rw [EbnfValues.directSourceTrace_cons]
      exact (leftInside.sourceAnchorTrace_sublist owned).append
        (rightInside.sourceAnchorTrace_sublist owned))
    (fun {child rest head tail leftTerminal rightTerminal leftMatched
        rightMatched} inside inductionHypothesis => by
      unfold DirectTerminalPairValuesTraceMotive at inductionHypothesis ⊢
      rw [EbnfValues.directSourceTrace_cons]
      exact inductionHypothesis.trans (List.sublist_append_right _ _))
    inside

theorem EbnfValues.DirectlyContainsMatchedTerminalBefore.sourceAnchorTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {expressions : List EbnfExpr}
    {input : EbnfValues file tokens expressions}
    {leftTerminal rightTerminal : TerminalSymbol}
    {leftMatched : MatchedTerminal file tokens leftTerminal}
    {rightMatched : MatchedTerminal file tokens rightTerminal}
    (inside : EbnfValues.DirectlyContainsMatchedTerminalBefore file tokens
      input leftMatched rightMatched) :
    (leftMatched.sourceAnchorTrace owned ++
      rightMatched.sourceAnchorTrace owned).Sublist
        (input.directSourceTrace owned) :=
  EbnfValues.DirectlyContainsMatchedTerminalBefore.rec
    (motive_1 := DirectTerminalPairValueTraceMotive file tokens owned)
    (motive_2 := DirectTerminalPairValuesTraceMotive file tokens owned)
    (fun {left right} shape
        {input leftTerminal rightTerminal leftMatched rightMatched}
        inside inductionHypothesis => by
      unfold DirectTerminalPairValueTraceMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {children values leftTerminal rightTerminal leftMatched rightMatched}
        inside inductionHypothesis => by
      unfold DirectTerminalPairValuesTraceMotive at inductionHypothesis
      unfold DirectTerminalPairValueTraceMotive
      simpa using inductionHypothesis)
    (fun {child value leftTerminal rightTerminal leftMatched rightMatched}
        inside inductionHypothesis => by
      unfold DirectTerminalPairValueTraceMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {branches} branch
        {value leftTerminal rightTerminal leftMatched rightMatched}
        inside inductionHypothesis => by
      unfold DirectTerminalPairValueTraceMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {child rest head tail leftTerminal rightTerminal leftMatched
        rightMatched} inside inductionHypothesis => by
      unfold DirectTerminalPairValueTraceMotive at inductionHypothesis
      unfold DirectTerminalPairValuesTraceMotive
      rw [EbnfValues.directSourceTrace_cons]
      exact inductionHypothesis.trans (List.sublist_append_left _ _))
    (fun {child rest head tail leftTerminal rightTerminal leftMatched
        rightMatched} leftInside rightInside => by
      unfold DirectTerminalPairValuesTraceMotive
      rw [EbnfValues.directSourceTrace_cons]
      exact (leftInside.sourceAnchorTrace_sublist owned).append
        (rightInside.sourceAnchorTrace_sublist owned))
    (fun {child rest head tail leftTerminal rightTerminal leftMatched
        rightMatched} inside inductionHypothesis => by
      unfold DirectTerminalPairValuesTraceMotive at inductionHypothesis ⊢
      rw [EbnfValues.directSourceTrace_cons]
      exact inductionHypothesis.trans (List.sublist_append_right _ _))
    inside

private def DirectTerminalValueSubfragmentMotive
    (file : WorkspaceFile) (tokens : List Token)
    {expression : EbnfExpr} (input : EbnfValue file tokens expression)
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal)
    (_inside : EbnfValue.DirectlyContainsMatchedTerminal
      file tokens input terminal matched) : Prop :=
  matched.locationFragment.IsSubfragmentOf input.locationFragment

private def DirectTerminalValuesSubfragmentMotive
    (file : WorkspaceFile) (tokens : List Token)
    {expressions : List EbnfExpr} (input : EbnfValues file tokens expressions)
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal)
    (_inside : EbnfValues.DirectlyContainsMatchedTerminal
      file tokens input terminal matched) : Prop :=
  matched.locationFragment.IsSubfragmentOf input.locationFragment

private theorem directTerminalSubfragmentTerminalCase
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    DirectTerminalValueSubfragmentMotive file tokens
      (EbnfValue.terminalAtom terminal matched) terminal matched
      (.terminal terminal matched) := by
  unfold DirectTerminalValueSubfragmentMotive
  simpa using LocationFragment.IsSubfragmentOf.refl matched.locationFragment

private theorem directTerminalSubfragmentTransportCase
    {file : WorkspaceFile} {tokens : List Token}
    {left right : EbnfExpr} (shape : left = right)
    {input : EbnfValue file tokens left}
    {terminal : TerminalSymbol}
    {matched : MatchedTerminal file tokens terminal}
    (inside : EbnfValue.DirectlyContainsMatchedTerminal
      file tokens input terminal matched)
    (inductionHypothesis : DirectTerminalValueSubfragmentMotive
      file tokens input terminal matched inside) :
    DirectTerminalValueSubfragmentMotive file tokens
      (EbnfValue.transport shape input) terminal matched
      (.transport shape inside) := by
  unfold DirectTerminalValueSubfragmentMotive at inductionHypothesis ⊢
  simpa using inductionHypothesis

private theorem directTerminalSubfragmentSequenceCase
    {file : WorkspaceFile} {tokens : List Token}
    {children : List EbnfExpr}
    {values : EbnfValues file tokens children}
    {terminal : TerminalSymbol}
    {matched : MatchedTerminal file tokens terminal}
    (inside : EbnfValues.DirectlyContainsMatchedTerminal
      file tokens values terminal matched)
    (inductionHypothesis : DirectTerminalValuesSubfragmentMotive
      file tokens values terminal matched inside) :
    DirectTerminalValueSubfragmentMotive file tokens
      (EbnfValue.sequence children values) terminal matched
      (.sequence inside) := by
  unfold DirectTerminalValuesSubfragmentMotive at inductionHypothesis
  unfold DirectTerminalValueSubfragmentMotive
  simpa using inductionHypothesis

private theorem directTerminalSubfragmentGroupCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {value : EbnfValue file tokens child}
    {terminal : TerminalSymbol}
    {matched : MatchedTerminal file tokens terminal}
    (inside : EbnfValue.DirectlyContainsMatchedTerminal
      file tokens value terminal matched)
    (inductionHypothesis : DirectTerminalValueSubfragmentMotive
      file tokens value terminal matched inside) :
    DirectTerminalValueSubfragmentMotive file tokens
      (EbnfValue.group child value) terminal matched (.group inside) := by
  unfold DirectTerminalValueSubfragmentMotive at inductionHypothesis ⊢
  simpa using inductionHypothesis

private theorem directTerminalSubfragmentChoiceCase
    {file : WorkspaceFile} {tokens : List Token}
    {branches : List EbnfExpr} (branch : Fin branches.length)
    {value : EbnfValue file tokens (branches.get branch)}
    {terminal : TerminalSymbol}
    {matched : MatchedTerminal file tokens terminal}
    (inside : EbnfValue.DirectlyContainsMatchedTerminal
      file tokens value terminal matched)
    (inductionHypothesis : DirectTerminalValueSubfragmentMotive
      file tokens value terminal matched inside) :
    DirectTerminalValueSubfragmentMotive file tokens
      (EbnfValue.choice branches ⟨branch, value⟩) terminal matched
      (.choice branch inside) := by
  unfold DirectTerminalValueSubfragmentMotive at inductionHypothesis ⊢
  simpa using inductionHypothesis

private theorem directTerminalSubfragmentValuesHeadCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {rest : List EbnfExpr}
    {head : EbnfValue file tokens child}
    {tail : EbnfValues file tokens rest}
    {terminal : TerminalSymbol}
    {matched : MatchedTerminal file tokens terminal}
    (inside : EbnfValue.DirectlyContainsMatchedTerminal
      file tokens head terminal matched)
    (inductionHypothesis : DirectTerminalValueSubfragmentMotive
      file tokens head terminal matched inside) :
    DirectTerminalValuesSubfragmentMotive file tokens
      (EbnfValues.cons child rest head tail) terminal matched
      (.head inside) := by
  unfold DirectTerminalValueSubfragmentMotive at inductionHypothesis
  unfold DirectTerminalValuesSubfragmentMotive
  rw [EbnfValues.locationFragment_cons]
  exact inductionHypothesis.trans
    (LocationFragment.IsSubfragmentOf.of_mem_merge (by simp))

private theorem directTerminalSubfragmentValuesTailCase
    {file : WorkspaceFile} {tokens : List Token}
    {child : EbnfExpr} {rest : List EbnfExpr}
    {head : EbnfValue file tokens child}
    {tail : EbnfValues file tokens rest}
    {terminal : TerminalSymbol}
    {matched : MatchedTerminal file tokens terminal}
    (inside : EbnfValues.DirectlyContainsMatchedTerminal
      file tokens tail terminal matched)
    (inductionHypothesis : DirectTerminalValuesSubfragmentMotive
      file tokens tail terminal matched inside) :
    DirectTerminalValuesSubfragmentMotive file tokens
      (EbnfValues.cons child rest head tail) terminal matched
      (.tail inside) := by
  unfold DirectTerminalValuesSubfragmentMotive at inductionHypothesis ⊢
  rw [EbnfValues.locationFragment_cons]
  exact inductionHypothesis.trans
    (LocationFragment.IsSubfragmentOf.of_mem_merge (by simp))

namespace EbnfValue.DirectlyContainsMatchedTerminal

theorem locationFragment_isSubfragment
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    {terminal : TerminalSymbol}
    {matched : MatchedTerminal file tokens terminal}
    (inside : EbnfValue.DirectlyContainsMatchedTerminal
      file tokens input terminal matched) :
    matched.locationFragment.IsSubfragmentOf input.locationFragment :=
  EbnfValue.DirectlyContainsMatchedTerminal.rec
    (motive_1 := DirectTerminalValueSubfragmentMotive file tokens)
    (motive_2 := DirectTerminalValuesSubfragmentMotive file tokens)
    directTerminalSubfragmentTerminalCase
    directTerminalSubfragmentTransportCase
    directTerminalSubfragmentSequenceCase
    directTerminalSubfragmentGroupCase
    directTerminalSubfragmentChoiceCase
    directTerminalSubfragmentValuesHeadCase
    directTerminalSubfragmentValuesTailCase inside

end EbnfValue.DirectlyContainsMatchedTerminal

namespace RuleReduction

abbrev inputValue
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (_reduces : RuleReduction file tokens rule origin finish input output) :
    EbnfValue file tokens (m2cV1.rhs rule) :=
  input

abbrev inputLocationFragment
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (_reduces : RuleReduction file tokens rule origin finish input output) :
    LocationFragment :=
  input.locationFragment

theorem exportDeclWildcard_reference_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (star : MatchedTerminal file tokens (.symbol .star))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (starMarker : RuleReduction.MarkerProjects file tokens star .wildcard)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.ofModuleReference reference).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.exportDeclWildcard origin finish exportKw reference dot
          star semicolon starMarker witness)) := by
  let reduces := RuleReduction.exportDeclWildcard origin finish exportKw
    reference dot star semicolon starMarker witness
  have inside : EbnfValue.ContainsRuleValue file tokens
      (inputValue reduces) .moduleRef reference := by
    exact .choice ⟨3, by decide⟩
      (.sequence (.tail (.head (.rule .moduleRef reference))))
  exact inside.locationFragment_isSubfragment

theorem exportDeclWildcard_star_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (star : MatchedTerminal file tokens (.symbol .star))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (starMarker : RuleReduction.MarkerProjects file tokens star .wildcard)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.raw star.span).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.exportDeclWildcard origin finish exportKw reference dot
          star semicolon starMarker witness)) := by
  let reduces := RuleReduction.exportDeclWildcard origin finish exportKw
    reference dot star semicolon starMarker witness
  have inside : EbnfValue.DirectlyContainsMatchedTerminal file tokens
      (inputValue reduces) (.symbol .star) star := by
    exact .choice ⟨3, by decide⟩
      (.sequence (.tail (.tail (.tail (.head (.terminal _ star))))))
  simpa [MatchedTerminal.locationFragment] using
    inside.locationFragment_isSubfragment

theorem exportDeclWildcard_endpoint_directTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (star : MatchedTerminal file tokens (.symbol .star))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (starMarker : RuleReduction.MarkerProjects file tokens star .wildcard)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    [dot.sourceAnchor owned (by decide),
      star.sourceAnchor owned (by decide)].Sublist
      (inputDirectSourceTrace owned
        (RuleReduction.exportDeclWildcard origin finish exportKw reference dot
          star semicolon starMarker witness)) := by
  have inside :
      EbnfValue.DirectlyContainsMatchedTerminalBefore file tokens
        (inputValue
          (RuleReduction.exportDeclWildcard origin finish exportKw reference
            dot star semicolon starMarker witness)) dot star :=
    .choice ⟨3, by decide⟩
      (.sequence
        (.tail
          (.tail
            (.cross (.terminal _ dot) (.head (.terminal _ star))))))
  simpa [MatchedTerminal.sourceAnchorTrace] using
    inside.sourceAnchorTrace_sublist owned

end RuleReduction

namespace IntervalLocationEvidence

theorem locatedByWitnessUsing
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {origin finish : Boundary tokens}
    (witness : ConsumedSpanWitness file tokens origin finish)
    {outer children : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (outerEvidence : IntervalLocationEvidence file tokens
      origin finish outer trace)
    (childrenEvidence : IntervalLocationEvidence file tokens
      origin finish children trace)
    (hasOuterRoot : outer.roots ≠ []) :
    IntervalLocationEvidence file tokens origin finish
      (LocationFragment.located witness.span [children]) trace := by
  let anchor : SourceAnchor file tokens := {
    origin := origin
    finish := finish
    span := witness.span
    occupied := ⟨witness.consumed,
      occupied_of_roots_ne_nil outerEvidence hasOuterRoot⟩
  }
  exact located tokensOrdered anchor childrenEvidence
    (rootsContainedBy tokensOrdered witness.consumed childrenEvidence)

end IntervalLocationEvidence

namespace RuleReduction

theorem exportDeclWildcard_locationSound_of_endpoint_pair
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (star : MatchedTerminal file tokens (.symbol .star))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (starMarker : RuleReduction.MarkerProjects file tokens star .wildcard)
    (witness : ConsumedSpanWitness file tokens origin finish)
    (trace : SourceAnchorTrace file tokens)
    (selected :
      [dot.sourceAnchor owned (by decide),
        star.sourceAnchor owned (by decide)].Sublist trace)
    (traceWithin : trace.Within origin finish)
    (traceOrdered : trace.Ordered)
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.exportDeclWildcard origin finish exportKw reference dot
          star semicolon starMarker witness)) trace) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .exportDecl
        (sourceLoc witness (.from reference
          (RuleReduction.between file dot.span star.span
            (.dotWildcard (RuleReduction.marker star starMarker)))))) trace := by
  let reduces := RuleReduction.exportDeclWildcard origin finish exportKw
    reference dot star semicolon starMarker witness
  let dotAnchor := dot.sourceAnchor owned (by decide)
  let starAnchor := star.sourceAnchor owned (by decide)
  have endpointsOrdered : dotAnchor.finish.val ≤ starAnchor.origin.val :=
    SourceAnchorTrace.finish_le_origin_of_pair_sublist selected traceOrdered
  have dotIntervalOrdered : dotAnchor.origin.val ≤ dotAnchor.finish.val := by
    exact dotAnchor.occupied.1.2.1
  have originsOrdered : dotAnchor.origin.val ≤ starAnchor.origin.val :=
    Nat.le_trans dotIntervalOrdered endpointsOrdered
  let selectionAnchor := SourceAnchor.between dotAnchor starAnchor originsOrdered
  have dotMember : dotAnchor ∈ trace :=
    selected.subset (by simp [dotAnchor])
  have starMember : starAnchor ∈ trace :=
    selected.subset (by simp [starAnchor])
  have selectionInside : selectionAnchor.Within origin finish := by
    exact ⟨(traceWithin dotAnchor dotMember).1,
      (traceWithin starAnchor starMember).2⟩
  have starInside :
      starAnchor.Within selectionAnchor.origin selectionAnchor.finish := by
    exact ⟨originsOrdered, Nat.le_refl _⟩
  have selectionContainsStar : selectionAnchor.span.Contains star.span := by
    simpa [selectionAnchor, starAnchor] using
      starAnchor.containedBy tokensOrdered selectionAnchor.occupied.1 starInside
  have referenceSubfragment :=
    exportDeclWildcard_reference_subfragment origin finish exportKw reference
      dot star semicolon starMarker witness
  have starSubfragment :=
    exportDeclWildcard_star_subfragment origin finish exportKw reference dot
      star semicolon starMarker witness
  have referenceEvidence :=
    IntervalLocationEvidence.restrict referenceSubfragment inputEvidence
  have starEvidence :=
    IntervalLocationEvidence.restrict starSubfragment inputEvidence
  have starRootsContained :
      (LocationFragment.raw star.span).RootsContainedBy selectionAnchor.span := by
    intro root member
    simp only [LocationFragment.raw_roots, List.mem_singleton] at member
    subst root
    exact selectionContainsStar
  have selectionEvidence : IntervalLocationEvidence file tokens origin finish
      (LocationFragment.located selectionAnchor.span
        [LocationFragment.raw star.span]) trace :=
    IntervalLocationEvidence.locatedInside tokensOrdered selectionAnchor
      starEvidence selectionInside starRootsContained
  have coreEvidence := IntervalLocationEvidence.mergeSameInterval
    referenceEvidence selectionEvidence
  have inputHasRoot : (inputLocationFragment reduces).roots ≠ [] := by
    intro emptyRoots
    have member := starSubfragment.1 star.span (by simp)
    rw [emptyRoots] at member
    exact List.not_mem_nil member
  have wrapped := IntervalLocationEvidence.locatedByWitnessUsing
    tokensOrdered witness inputEvidence coreEvidence inputHasRoot
  apply IntervalLocationEvidence.replaceFragment _ wrapped
  simp only [RuleLocationView.ofRuleValue, sourceLoc,
    LocationFragment.ofExportDecl_from]
  unfold RuleReduction.between
  rw [LocationFragment.ofRemoteExportSelection_dotWildcard]
  simp [LocationFragment.leaf, RuleReduction.marker,
    RuleReduction.terminalLoc, selectionAnchor, dotAnchor, starAnchor]
  unfold RuleReduction.between
  rfl

end RuleReduction

namespace RuleReduction

inductive ExportDeclWildcardLocationCase
    {file : WorkspaceFile} {tokens : List Token} :
    {rule : GrammarRuleId} → {origin finish : Boundary tokens} →
      {input : EbnfValue file tokens (m2cV1.rhs rule)} →
      {output : RuleValue rule} →
      RuleReduction file tokens rule origin finish input output → Prop where
  | wildcard
      (origin finish : Boundary tokens)
      (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
      (reference : ModuleReference)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (star : MatchedTerminal file tokens (.symbol .star))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (starMarker : RuleReduction.MarkerProjects file tokens star .wildcard)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      ExportDeclWildcardLocationCase
        (RuleReduction.exportDeclWildcard origin finish exportKw reference dot
          star semicolon starMarker witness)

namespace ExportDeclWildcardLocationCase

abbrev CanonicalItem
    (tokens : List Token) (origin finish : Boundary tokens)
    (context : GuardContext tokens) : ContextualItemKey tokens :=
  CanonicalCompleteRootItem tokens .exportDecl origin finish context

theorem coherentRootLocationSound
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalItem tokens origin finish context)}
    {complete : CompleteItem
      (CanonicalItem tokens origin finish context).raw}
    {coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalItem tokens origin finish context) priorValues}
    {ruleInput : EbnfValue file tokens (m2cV1.rhs .exportDecl)}
    {output : RuleValue .exportDecl}
    (reduces : RuleReduction file tokens .exportDecl origin finish
      ruleInput output)
    (classified : RuleReduction.ExportDeclWildcardLocationCase reduces)
    (inputEq : ruleInput = RootAction.unpack .exportDecl
      (PrefixValues.fullValue (CanonicalItem tokens origin finish context)
        complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherentPrefix trace}
    : CoherentActionLocationSound complete coherentPrefix
      (ActionReduces.root
        (rule := GrammarRuleId.exportDecl)
        (origin := origin) (finish := finish)
        (input := PrefixValues.fullValue
          (CanonicalItem tokens origin finish context) complete priorValues)
        (output := output) (reduces := inputEq ▸ reduces)) trace carries := by
  cases classified with
  | wildcard origin finish exportKw reference dot star semicolon starMarker
      witness =>
      intro inputEvidence
      let rootInput := PrefixValues.fullValue
        (CanonicalItem tokens origin finish context) complete priorValues
      have inputTrace :
          (GrammarSymbolValues.directSourceTrace owned
            (ProductionId.root .exportDecl).rhs rootInput).Sublist trace := by
        exact carries.fullValue_directSourceTrace_sublist complete
      have endpointRuleInput :
          [dot.sourceAnchor owned (by decide),
            star.sourceAnchor owned (by decide)].Sublist
            (EbnfValue.directSourceTrace owned
              (RuleReduction.inputValue
                (RuleReduction.exportDeclWildcard origin finish exportKw
                  reference dot star semicolon starMarker witness))) :=
        RuleReduction.exportDeclWildcard_endpoint_directTrace_sublist owned
          origin finish exportKw reference dot star semicolon starMarker
            witness
      have endpointInput :
          [dot.sourceAnchor owned (by decide),
            star.sourceAnchor owned (by decide)].Sublist
            (GrammarSymbolValues.directSourceTrace owned
              (ProductionId.root .exportDecl).rhs rootInput) := by
        rw [← RootAction.unpack_directSourceTrace owned]
        rw [← inputEq]
        exact endpointRuleInput
      have inputEbnfEvidence : IntervalLocationEvidence file tokens
          origin finish
          (RuleReduction.inputLocationFragment
            (RuleReduction.exportDeclWildcard origin finish exportKw reference
              dot star semicolon starMarker witness)) trace := by
        have unpackEvidence := IntervalLocationEvidence.replaceFragment
          (RootAction.unpack_locationFragment .exportDecl rootInput).symm
          inputEvidence
        rw [← inputEq] at unpackEvidence
        exact unpackEvidence
      exact RuleReduction.exportDeclWildcard_locationSound_of_endpoint_pair
        owned tokensOrdered origin finish exportKw reference dot star semicolon
          starMarker witness trace (endpointInput.trans inputTrace)
            carries.within_and_ordered.1 carries.within_and_ordered.2
              inputEbnfEvidence

end ExportDeclWildcardLocationCase

end RuleReduction


namespace RuleReduction

theorem importDeclItems_endpoint_directTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ImportSelectorEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (hidingValue : Option HidingClause)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    [openBrace.sourceAnchor owned (by decide),
      closeBrace.sourceAnchor owned (by decide)].Sublist
      (inputDirectSourceTrace owned
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness)) := by
  simp [MatchedTerminal.sourceAnchorTrace]

theorem exportDeclLocal_endpoint_directTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    [openBrace.sourceAnchor owned (by decide),
      closeBrace.sourceAnchor owned (by decide)].Sublist
      (inputDirectSourceTrace owned
        (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
          closeBrace semicolon witness)) := by
  simp [MatchedTerminal.sourceAnchorTrace]

theorem exportDeclBraced_endpoint_directTrace_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List RemoteExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    [openBrace.sourceAnchor owned (by decide),
      closeBrace.sourceAnchor owned (by decide)].Sublist
      (inputDirectSourceTrace owned
        (RuleReduction.exportDeclBraced origin finish exportKw reference dot
          openBrace entries closeBrace semicolon witness)) := by
  have inside :
      EbnfValue.DirectlyContainsMatchedTerminalBefore file tokens
        (inputValue
          (RuleReduction.exportDeclBraced origin finish exportKw reference dot
            openBrace entries closeBrace semicolon witness))
        openBrace closeBrace :=
    .choice ⟨4, by decide⟩
      (.sequence
        (.tail
          (.tail
            (.tail
              (.cross (.terminal _ openBrace)
                (.tail (.head (.terminal _ closeBrace))))))))
  simpa [MatchedTerminal.sourceAnchorTrace] using
    inside.sourceAnchorTrace_sublist owned

end RuleReduction


mutual

inductive EbnfValue.ContainsEbnfValue
    (file : WorkspaceFile) (tokens : List Token) :
    {outerExpression : EbnfExpr} →
      EbnfValue file tokens outerExpression →
      {innerExpression : EbnfExpr} →
      EbnfValue file tokens innerExpression → Prop where
  | same {expression : EbnfExpr}
      (value : EbnfValue file tokens expression) :
      EbnfValue.ContainsEbnfValue file tokens value value
  | transport {left right : EbnfExpr} (shape : left = right)
      {outer : EbnfValue file tokens left}
      {innerExpression : EbnfExpr}
      {inner : EbnfValue file tokens innerExpression}
      (inside : EbnfValue.ContainsEbnfValue file tokens outer inner) :
      EbnfValue.ContainsEbnfValue file tokens
        (EbnfValue.transport shape outer) inner
  | sequence {children : List EbnfExpr}
      {values : EbnfValues file tokens children}
      {innerExpression : EbnfExpr}
      {inner : EbnfValue file tokens innerExpression}
      (inside : EbnfValues.ContainsEbnfValue file tokens values inner) :
      EbnfValue.ContainsEbnfValue file tokens
        (EbnfValue.sequence children values) inner
  | group {child : EbnfExpr} {outer : EbnfValue file tokens child}
      {innerExpression : EbnfExpr}
      {inner : EbnfValue file tokens innerExpression}
      (inside : EbnfValue.ContainsEbnfValue file tokens outer inner) :
      EbnfValue.ContainsEbnfValue file tokens
        (EbnfValue.group child outer) inner
  | choice {branches : List EbnfExpr} (branch : Fin branches.length)
      {outer : EbnfValue file tokens (branches.get branch)}
      {innerExpression : EbnfExpr}
      {inner : EbnfValue file tokens innerExpression}
      (inside : EbnfValue.ContainsEbnfValue file tokens outer inner) :
      EbnfValue.ContainsEbnfValue file tokens
        (EbnfValue.choice branches ⟨branch, outer⟩) inner

inductive EbnfValues.ContainsEbnfValue
    (file : WorkspaceFile) (tokens : List Token) :
    {outerExpressions : List EbnfExpr} →
      EbnfValues file tokens outerExpressions →
      {innerExpression : EbnfExpr} →
      EbnfValue file tokens innerExpression → Prop where
  | head {child : EbnfExpr} {rest : List EbnfExpr}
      {head : EbnfValue file tokens child}
      {tail : EbnfValues file tokens rest}
      {innerExpression : EbnfExpr}
      {inner : EbnfValue file tokens innerExpression}
      (inside : EbnfValue.ContainsEbnfValue file tokens head inner) :
      EbnfValues.ContainsEbnfValue file tokens
        (EbnfValues.cons child rest head tail) inner
  | tail {child : EbnfExpr} {rest : List EbnfExpr}
      {head : EbnfValue file tokens child}
      {tail : EbnfValues file tokens rest}
      {innerExpression : EbnfExpr}
      {inner : EbnfValue file tokens innerExpression}
      (inside : EbnfValues.ContainsEbnfValue file tokens tail inner) :
      EbnfValues.ContainsEbnfValue file tokens
        (EbnfValues.cons child rest head tail) inner

end

private def ContainsEbnfValueMotive
    (file : WorkspaceFile) (tokens : List Token)
    {outerExpression : EbnfExpr}
    (outer : EbnfValue file tokens outerExpression)
    {innerExpression : EbnfExpr}
    (inner : EbnfValue file tokens innerExpression)
    (_inside : EbnfValue.ContainsEbnfValue file tokens outer inner) : Prop :=
  inner.locationFragment.IsSubfragmentOf outer.locationFragment

private def ContainsEbnfValuesMotive
    (file : WorkspaceFile) (tokens : List Token)
    {outerExpressions : List EbnfExpr}
    (outer : EbnfValues file tokens outerExpressions)
    {innerExpression : EbnfExpr}
    (inner : EbnfValue file tokens innerExpression)
    (_inside : EbnfValues.ContainsEbnfValue file tokens outer inner) : Prop :=
  inner.locationFragment.IsSubfragmentOf outer.locationFragment

namespace EbnfValue.ContainsEbnfValue

theorem locationFragment_isSubfragment
    {file : WorkspaceFile} {tokens : List Token}
    {outerExpression innerExpression : EbnfExpr}
    {outer : EbnfValue file tokens outerExpression}
    {inner : EbnfValue file tokens innerExpression}
    (inside : EbnfValue.ContainsEbnfValue file tokens outer inner) :
    inner.locationFragment.IsSubfragmentOf outer.locationFragment :=
  EbnfValue.ContainsEbnfValue.rec
    (motive_1 := ContainsEbnfValueMotive file tokens)
    (motive_2 := ContainsEbnfValuesMotive file tokens)
    (fun value => by
      unfold ContainsEbnfValueMotive
      exact LocationFragment.IsSubfragmentOf.refl _)
    (fun {left right} shape {outer innerExpression inner} inside
        inductionHypothesis => by
      unfold ContainsEbnfValueMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {children values innerExpression inner} inside
        inductionHypothesis => by
      unfold ContainsEbnfValuesMotive at inductionHypothesis
      unfold ContainsEbnfValueMotive
      simpa using inductionHypothesis)
    (fun {child outer innerExpression inner} inside inductionHypothesis => by
      unfold ContainsEbnfValueMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {branches} branch {outer innerExpression inner} inside
        inductionHypothesis => by
      unfold ContainsEbnfValueMotive at inductionHypothesis ⊢
      simpa using inductionHypothesis)
    (fun {child rest head tail innerExpression inner} inside
        inductionHypothesis => by
      unfold ContainsEbnfValueMotive at inductionHypothesis
      unfold ContainsEbnfValuesMotive
      rw [EbnfValues.locationFragment_cons]
      exact inductionHypothesis.trans
        (LocationFragment.IsSubfragmentOf.of_mem_merge (by simp)))
    (fun {child rest head tail innerExpression inner} inside
        inductionHypothesis => by
      unfold ContainsEbnfValuesMotive at inductionHypothesis ⊢
      rw [EbnfValues.locationFragment_cons]
      exact inductionHypothesis.trans
        (LocationFragment.IsSubfragmentOf.of_mem_merge (by simp)))
    inside

end EbnfValue.ContainsEbnfValue


namespace RuleReduction

theorem exportDeclLocal_entries_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.merge
      (entries.map LocationFragment.ofExportEntry)).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
          closeBrace semicolon witness)) := by
  apply LocationFragment.IsSubfragmentOf.merge_map
  intro entry member
  have inside : EbnfValue.ContainsRuleValue file tokens
      (inputValue
        (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
          closeBrace semicolon witness)) .localExportEntry entry :=
    .choice ⟨0, by decide⟩
      (.sequence
        (.tail
          (.tail
            (.head
              (.list0 (List.mem_map_of_mem member)
                (.rule .localExportEntry entry))))))
  simpa [RuleLocationView.ofRuleValue] using
    inside.locationFragment_isSubfragment

theorem exportDeclLocal_openBrace_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.raw openBrace.span).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
          closeBrace semicolon witness)) := by
  have inside : EbnfValue.DirectlyContainsMatchedTerminal file tokens
      (inputValue
        (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
          closeBrace semicolon witness)) (.symbol .leftBrace) openBrace :=
    .choice ⟨0, by decide⟩
      (.sequence (.tail (.head (.terminal _ openBrace))))
  simpa [MatchedTerminal.locationFragment] using
    inside.locationFragment_isSubfragment

theorem exportDeclLocal_locationSound_of_endpoint_pair_and_entries
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish)
    (trace : SourceAnchorTrace file tokens)
    (selected :
      [openBrace.sourceAnchor owned (by decide),
        closeBrace.sourceAnchor owned (by decide)].Sublist trace)
    (traceWithin : trace.Within origin finish)
    (traceOrdered : trace.Ordered)
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
          closeBrace semicolon witness)) trace)
    (entriesContained :
      (LocationFragment.merge
        (entries.map LocationFragment.ofExportEntry)).RootsContainedBy
          (RuleReduction.between file openBrace.span closeBrace.span ()).span) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .exportDecl
        (sourceLoc witness (.local
          (RuleReduction.between file openBrace.span closeBrace.span
            { entries := entries })))) trace := by
  let openAnchor := openBrace.sourceAnchor owned (by decide)
  let closeAnchor := closeBrace.sourceAnchor owned (by decide)
  have endpointsOrdered : openAnchor.finish.val ≤ closeAnchor.origin.val :=
    SourceAnchorTrace.finish_le_origin_of_pair_sublist selected traceOrdered
  have openOrdered : openAnchor.origin.val ≤ openAnchor.finish.val :=
    openAnchor.occupied.1.2.1
  have originsOrdered : openAnchor.origin.val ≤ closeAnchor.origin.val :=
    Nat.le_trans openOrdered endpointsOrdered
  let selectionAnchor := SourceAnchor.between openAnchor closeAnchor
    originsOrdered
  have openMember : openAnchor ∈ trace := selected.subset (by simp [openAnchor])
  have closeMember : closeAnchor ∈ trace :=
    selected.subset (by simp [closeAnchor])
  have selectionInside : selectionAnchor.Within origin finish :=
    ⟨(traceWithin openAnchor openMember).1,
      (traceWithin closeAnchor closeMember).2⟩
  have entriesEvidence := IntervalLocationEvidence.restrict
    (exportDeclLocal_entries_subfragment origin finish exportKw openBrace
      entries closeBrace semicolon witness) inputEvidence
  have selectionEvidence := IntervalLocationEvidence.locatedInside
    tokensOrdered selectionAnchor entriesEvidence selectionInside (by
      simpa [selectionAnchor, openAnchor, closeAnchor] using entriesContained)
  have openSubfragment := exportDeclLocal_openBrace_subfragment
    origin finish exportKw openBrace entries closeBrace semicolon witness
  have inputHasRoot :
      (inputLocationFragment
        (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
          closeBrace semicolon witness)).roots ≠ [] := by
    intro emptyRoots
    have member := openSubfragment.1 openBrace.span (by simp)
    rw [emptyRoots] at member
    exact List.not_mem_nil member
  have wrapped := IntervalLocationEvidence.locatedByWitnessUsing
    tokensOrdered witness inputEvidence selectionEvidence inputHasRoot
  apply IntervalLocationEvidence.replaceFragment _ wrapped
  simp only [RuleLocationView.ofRuleValue, sourceLoc,
    LocationFragment.ofExportDecl_local]
  unfold RuleReduction.between
  rw [LocationFragment.ofLocalExportList_mk]
  simp [selectionAnchor, openAnchor, closeAnchor]
  unfold RuleReduction.between
  rfl

theorem exportDeclBraced_reference_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List RemoteExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.ofModuleReference reference).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.exportDeclBraced origin finish exportKw reference dot
          openBrace entries closeBrace semicolon witness)) := by
  have inside : EbnfValue.ContainsRuleValue file tokens
      (inputValue
        (RuleReduction.exportDeclBraced origin finish exportKw reference dot
          openBrace entries closeBrace semicolon witness))
      .moduleRef reference :=
    .choice ⟨4, by decide⟩
      (.sequence (.tail (.head (.rule .moduleRef reference))))
  exact inside.locationFragment_isSubfragment

theorem exportDeclBraced_entries_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List RemoteExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.merge
      (entries.map LocationFragment.ofRemoteExportEntry)).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.exportDeclBraced origin finish exportKw reference dot
          openBrace entries closeBrace semicolon witness)) := by
  apply LocationFragment.IsSubfragmentOf.merge_map
  intro entry member
  have inside : EbnfValue.ContainsRuleValue file tokens
      (inputValue
        (RuleReduction.exportDeclBraced origin finish exportKw reference dot
          openBrace entries closeBrace semicolon witness))
      .remoteExportEntry entry :=
    .choice ⟨4, by decide⟩
      (.sequence
        (.tail
          (.tail
            (.tail
              (.tail
                (.head
                  (.list0 (List.mem_map_of_mem member)
                    (.rule .remoteExportEntry entry))))))))
  simpa [RuleLocationView.ofRuleValue] using
    inside.locationFragment_isSubfragment

theorem exportDeclBraced_openBrace_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List RemoteExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.raw openBrace.span).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.exportDeclBraced origin finish exportKw reference dot
          openBrace entries closeBrace semicolon witness)) := by
  have inside : EbnfValue.DirectlyContainsMatchedTerminal file tokens
      (inputValue
        (RuleReduction.exportDeclBraced origin finish exportKw reference dot
          openBrace entries closeBrace semicolon witness))
      (.symbol .leftBrace) openBrace :=
    .choice ⟨4, by decide⟩
      (.sequence (.tail (.tail (.tail (.head (.terminal _ openBrace))))))
  simpa [MatchedTerminal.locationFragment] using
    inside.locationFragment_isSubfragment

theorem exportDeclBraced_locationSound_of_endpoint_pair_and_entries
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List RemoteExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish)
    (trace : SourceAnchorTrace file tokens)
    (selected :
      [openBrace.sourceAnchor owned (by decide),
        closeBrace.sourceAnchor owned (by decide)].Sublist trace)
    (traceWithin : trace.Within origin finish)
    (traceOrdered : trace.Ordered)
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.exportDeclBraced origin finish exportKw reference dot
          openBrace entries closeBrace semicolon witness)) trace)
    (entriesContained :
      (LocationFragment.merge
        (entries.map LocationFragment.ofRemoteExportEntry)).RootsContainedBy
          (RuleReduction.between file openBrace.span closeBrace.span ()).span) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .exportDecl
        (sourceLoc witness (.from reference
          (RuleReduction.between file openBrace.span closeBrace.span
            (.braced entries))))) trace := by
  let openAnchor := openBrace.sourceAnchor owned (by decide)
  let closeAnchor := closeBrace.sourceAnchor owned (by decide)
  have endpointsOrdered : openAnchor.finish.val ≤ closeAnchor.origin.val :=
    SourceAnchorTrace.finish_le_origin_of_pair_sublist selected traceOrdered
  have openOrdered : openAnchor.origin.val ≤ openAnchor.finish.val :=
    openAnchor.occupied.1.2.1
  have originsOrdered : openAnchor.origin.val ≤ closeAnchor.origin.val :=
    Nat.le_trans openOrdered endpointsOrdered
  let selectionAnchor := SourceAnchor.between openAnchor closeAnchor
    originsOrdered
  have openMember : openAnchor ∈ trace := selected.subset (by simp [openAnchor])
  have closeMember : closeAnchor ∈ trace :=
    selected.subset (by simp [closeAnchor])
  have selectionInside : selectionAnchor.Within origin finish :=
    ⟨(traceWithin openAnchor openMember).1,
      (traceWithin closeAnchor closeMember).2⟩
  have referenceEvidence := IntervalLocationEvidence.restrict
    (exportDeclBraced_reference_subfragment origin finish exportKw
      reference dot openBrace entries closeBrace semicolon witness)
    inputEvidence
  have entriesEvidence := IntervalLocationEvidence.restrict
    (exportDeclBraced_entries_subfragment origin finish exportKw reference
      dot openBrace entries closeBrace semicolon witness) inputEvidence
  have selectionEvidence := IntervalLocationEvidence.locatedInside
    tokensOrdered selectionAnchor entriesEvidence selectionInside (by
      simpa [selectionAnchor, openAnchor, closeAnchor] using entriesContained)
  have coreEvidence := IntervalLocationEvidence.mergeSameInterval
    referenceEvidence selectionEvidence
  have openSubfragment := exportDeclBraced_openBrace_subfragment
    origin finish exportKw reference dot openBrace entries closeBrace semicolon
      witness
  have inputHasRoot :
      (inputLocationFragment
        (RuleReduction.exportDeclBraced origin finish exportKw reference dot
          openBrace entries closeBrace semicolon witness)).roots ≠ [] := by
    intro emptyRoots
    have member := openSubfragment.1 openBrace.span (by simp)
    rw [emptyRoots] at member
    exact List.not_mem_nil member
  have wrapped := IntervalLocationEvidence.locatedByWitnessUsing
    tokensOrdered witness inputEvidence coreEvidence inputHasRoot
  apply IntervalLocationEvidence.replaceFragment _ wrapped
  simp only [RuleLocationView.ofRuleValue, sourceLoc,
    LocationFragment.ofExportDecl_from]
  unfold RuleReduction.between
  rw [LocationFragment.ofRemoteExportSelection_braced]
  simp [selectionAnchor, openAnchor, closeAnchor]
  unfold RuleReduction.between
  rfl

theorem importDeclItems_reference_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ImportSelectorEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (hidingValue : Option HidingClause)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.ofModuleReference reference).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness)) := by
  have inside : EbnfValue.ContainsRuleValue file tokens
      (inputValue
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness))
      .moduleRef reference :=
    .choice ⟨2, by decide⟩
      (.sequence (.tail (.head (.rule .moduleRef reference))))
  exact inside.locationFragment_isSubfragment

theorem importDeclItems_entries_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ImportSelectorEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (hidingValue : Option HidingClause)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.merge
      (entries.map LocationFragment.ofImportSelectorEntry)).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness)) := by
  apply LocationFragment.IsSubfragmentOf.merge_map
  intro entry member
  have inside : EbnfValue.ContainsRuleValue file tokens
      (inputValue
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness))
      .importEntry entry :=
    .choice ⟨2, by decide⟩
      (.sequence
        (.tail
          (.tail
            (.tail
              (.tail
                (.head
                  (.list0 (List.mem_map_of_mem member)
                    (.rule .importEntry entry))))))))
  simpa [RuleLocationView.ofRuleValue] using
    inside.locationFragment_isSubfragment

theorem importDeclItems_hiding_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ImportSelectorEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (hidingValue : Option HidingClause)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.ofOption LocationFragment.ofHidingClause
      hidingValue).IsSubfragmentOf
        (inputLocationFragment
          (RuleReduction.importDeclItems origin finish importKw reference dot
            openBrace entries closeBrace hidingValue semicolon witness)) := by
  cases hidingValue with
  | none =>
      exact LocationFragment.IsSubfragmentOf.empty _
  | some clause =>
      have inside : EbnfValue.ContainsRuleValue file tokens
          (inputValue
            (RuleReduction.importDeclItems origin finish importKw reference dot
              openBrace entries closeBrace (some clause) semicolon witness))
          .hidingClause clause :=
        .choice ⟨2, by decide⟩
          (.sequence
            (.tail
              (.tail
                (.tail
                  (.tail
                    (.tail
                      (.tail
                        (.head
                          (.optional
                            (.rule .hidingClause clause))))))))))
      change (LocationFragment.ofHidingClause clause).IsSubfragmentOf _
      simpa [RuleLocationView.ofRuleValue] using
        inside.locationFragment_isSubfragment

theorem importDeclItems_openBrace_subfragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ImportSelectorEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (hidingValue : Option HidingClause)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (LocationFragment.raw openBrace.span).IsSubfragmentOf
      (inputLocationFragment
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness)) := by
  have inside : EbnfValue.DirectlyContainsMatchedTerminal file tokens
      (inputValue
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness))
      (.symbol .leftBrace) openBrace :=
    .choice ⟨2, by decide⟩
      (.sequence (.tail (.tail (.tail (.head (.terminal _ openBrace))))))
  simpa [MatchedTerminal.locationFragment] using
    inside.locationFragment_isSubfragment

theorem importDeclItems_locationSound_of_endpoint_pair_and_entries
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ImportSelectorEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (hidingValue : Option HidingClause)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish)
    (trace : SourceAnchorTrace file tokens)
    (selected :
      [openBrace.sourceAnchor owned (by decide),
        closeBrace.sourceAnchor owned (by decide)].Sublist trace)
    (traceWithin : trace.Within origin finish)
    (traceOrdered : trace.Ordered)
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness)) trace)
    (entriesContained :
      (LocationFragment.merge
        (entries.map LocationFragment.ofImportSelectorEntry)).RootsContainedBy
          (RuleReduction.between file openBrace.span closeBrace.span ()).span) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .importDecl
        (sourceLoc witness {
          moduleRef := reference
          mode := .items
            (RuleReduction.between file openBrace.span closeBrace.span
              { entries := entries }) hidingValue
        })) trace := by
  let openAnchor := openBrace.sourceAnchor owned (by decide)
  let closeAnchor := closeBrace.sourceAnchor owned (by decide)
  have endpointsOrdered : openAnchor.finish.val ≤ closeAnchor.origin.val :=
    SourceAnchorTrace.finish_le_origin_of_pair_sublist selected traceOrdered
  have openOrdered : openAnchor.origin.val ≤ openAnchor.finish.val :=
    openAnchor.occupied.1.2.1
  have originsOrdered : openAnchor.origin.val ≤ closeAnchor.origin.val :=
    Nat.le_trans openOrdered endpointsOrdered
  let selectionAnchor := SourceAnchor.between openAnchor closeAnchor
    originsOrdered
  have openMember : openAnchor ∈ trace := selected.subset (by simp [openAnchor])
  have closeMember : closeAnchor ∈ trace :=
    selected.subset (by simp [closeAnchor])
  have selectionInside : selectionAnchor.Within origin finish :=
    ⟨(traceWithin openAnchor openMember).1,
      (traceWithin closeAnchor closeMember).2⟩
  have referenceEvidence := IntervalLocationEvidence.restrict
    (importDeclItems_reference_subfragment origin finish importKw reference
      dot openBrace entries closeBrace hidingValue semicolon witness)
    inputEvidence
  have entriesEvidence := IntervalLocationEvidence.restrict
    (importDeclItems_entries_subfragment origin finish importKw reference
      dot openBrace entries closeBrace hidingValue semicolon witness)
    inputEvidence
  have hidingEvidence := IntervalLocationEvidence.restrict
    (importDeclItems_hiding_subfragment origin finish importKw reference
      dot openBrace entries closeBrace hidingValue semicolon witness)
    inputEvidence
  have selectionEvidence := IntervalLocationEvidence.locatedInside
    tokensOrdered selectionAnchor entriesEvidence selectionInside (by
      simpa [selectionAnchor, openAnchor, closeAnchor] using entriesContained)
  have modeEvidence := IntervalLocationEvidence.mergeSameInterval
    selectionEvidence hidingEvidence
  have coreEvidence := IntervalLocationEvidence.mergeSameInterval
    referenceEvidence modeEvidence
  have openSubfragment := importDeclItems_openBrace_subfragment
    origin finish importKw reference dot openBrace entries closeBrace hidingValue
      semicolon witness
  have inputHasRoot :
      (inputLocationFragment
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness)).roots ≠ [] := by
    intro emptyRoots
    have member := openSubfragment.1 openBrace.span (by simp)
    rw [emptyRoots] at member
    exact List.not_mem_nil member
  have wrapped := IntervalLocationEvidence.locatedByWitnessUsing
    tokensOrdered witness inputEvidence coreEvidence inputHasRoot
  apply IntervalLocationEvidence.replaceFragment _ wrapped
  simp only [RuleLocationView.ofRuleValue, sourceLoc,
    LocationFragment.ofImportDecl_mk, LocationFragment.ofImportMode]
  unfold RuleReduction.between
  rw [LocationFragment.ofImportSelection_mk]
  simp [selectionAnchor, openAnchor, closeAnchor]
  unfold RuleReduction.between
  apply LocationFragment.eq_of_fields <;> simp

end RuleReduction


namespace RuleReduction

abbrev CanonicalRootLocationItem
    (tokens : List Token) (rule : GrammarRuleId)
    (origin finish : Boundary tokens) (context : GuardContext tokens) :
    ContextualItemKey tokens :=
  CanonicalCompleteRootItem tokens rule origin finish context

theorem coherentRootLocationSound_of_endpointPair
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {rule : GrammarRuleId}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalRootLocationItem tokens rule origin finish context)}
    {complete : CompleteItem
      (CanonicalRootLocationItem tokens rule origin finish context).raw}
    {coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalRootLocationItem tokens rule origin finish context) priorValues}
    {ruleInput : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (reduces : RuleReduction file tokens rule origin finish ruleInput output)
    (inputEq : ruleInput = RootAction.unpack rule
      (PrefixValues.fullValue
        (CanonicalRootLocationItem tokens rule origin finish context)
        complete priorValues))
    {left right : SourceAnchor file tokens}
    (endpointRuleInput : [left, right].Sublist
      (ruleInput.directSourceTrace owned))
    (sourceSound : ∀ trace : SourceAnchorTrace file tokens,
      [left, right].Sublist trace →
      trace.Within origin finish → trace.Ordered →
      IntervalLocationEvidence file tokens origin finish
        ruleInput.locationFragment trace →
      IntervalLocationEvidence file tokens origin finish
        (RuleLocationView.ofRuleValue rule output) trace)
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherentPrefix trace} :
    CoherentActionLocationSound complete coherentPrefix
      (ActionReduces.root rule origin finish
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens rule origin finish context)
          complete priorValues)
        output (inputEq ▸ reduces)) trace carries := by
  intro inputEvidence
  let rootInput := PrefixValues.fullValue
    (CanonicalRootLocationItem tokens rule origin finish context)
      complete priorValues
  have inputTrace :
      (GrammarSymbolValues.directSourceTrace owned
        (ProductionId.root rule).rhs rootInput).Sublist trace :=
    carries.fullValue_directSourceTrace_sublist complete
  have endpointInput : [left, right].Sublist
      (GrammarSymbolValues.directSourceTrace owned
        (ProductionId.root rule).rhs rootInput) := by
    rw [← RootAction.unpack_directSourceTrace owned]
    rw [← inputEq]
    exact endpointRuleInput
  have ruleInputEvidence : IntervalLocationEvidence file tokens origin finish
      ruleInput.locationFragment trace := by
    have unpackEvidence := IntervalLocationEvidence.replaceFragment
      (RootAction.unpack_locationFragment rule rootInput).symm inputEvidence
    rw [← inputEq] at unpackEvidence
    exact unpackEvidence
  exact sourceSound trace (endpointInput.trans inputTrace)
    carries.within_and_ordered.1 carries.within_and_ordered.2
      ruleInputEvidence

inductive ImportDeclItemsLocationCase
    {file : WorkspaceFile} {tokens : List Token} :
    {rule : GrammarRuleId} → {origin finish : Boundary tokens} →
      {input : EbnfValue file tokens (m2cV1.rhs rule)} →
      {output : RuleValue rule} →
      RuleReduction file tokens rule origin finish input output → Prop where
  | items
      (origin finish : Boundary tokens)
      (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
      (reference : ModuleReference)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (entries : List ImportSelectorEntry)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (hidingValue : Option HidingClause)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish)
      (entriesContained :
        (LocationFragment.merge
          (entries.map LocationFragment.ofImportSelectorEntry)).RootsContainedBy
              (RuleReduction.between file openBrace.span closeBrace.span
                ()).span) :
      ImportDeclItemsLocationCase
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness)

inductive ExportDeclLocalLocationCase
    {file : WorkspaceFile} {tokens : List Token} :
    {rule : GrammarRuleId} → {origin finish : Boundary tokens} →
      {input : EbnfValue file tokens (m2cV1.rhs rule)} →
      {output : RuleValue rule} →
      RuleReduction file tokens rule origin finish input output → Prop where
  | localCase
      (origin finish : Boundary tokens)
      (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (entries : List ExportEntry)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish)
      (entriesContained :
        (LocationFragment.merge
          (entries.map LocationFragment.ofExportEntry)).RootsContainedBy
            (RuleReduction.between file openBrace.span closeBrace.span
              ()).span) :
      ExportDeclLocalLocationCase
        (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
          closeBrace semicolon witness)

inductive ExportDeclBracedLocationCase
    {file : WorkspaceFile} {tokens : List Token} :
    {rule : GrammarRuleId} → {origin finish : Boundary tokens} →
      {input : EbnfValue file tokens (m2cV1.rhs rule)} →
      {output : RuleValue rule} →
      RuleReduction file tokens rule origin finish input output → Prop where
  | braced
      (origin finish : Boundary tokens)
      (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
      (reference : ModuleReference)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (entries : List RemoteExportEntry)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish)
      (entriesContained :
        (LocationFragment.merge
          (entries.map LocationFragment.ofRemoteExportEntry)).RootsContainedBy
            (RuleReduction.between file openBrace.span closeBrace.span
              ()).span) :
      ExportDeclBracedLocationCase
        (RuleReduction.exportDeclBraced origin finish exportKw reference dot
          openBrace entries closeBrace semicolon witness)

namespace ImportDeclItemsLocationCase

theorem coherentRootLocationSound
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalRootLocationItem tokens rule origin finish context)}
    {complete : CompleteItem
      (CanonicalRootLocationItem tokens rule origin finish context).raw}
    {coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalRootLocationItem tokens rule origin finish context) priorValues}
    {ruleInput : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (reduces : RuleReduction file tokens rule origin finish ruleInput output)
    (classified : RuleReduction.ImportDeclItemsLocationCase reduces)
    (inputEq : ruleInput = RootAction.unpack rule
      (PrefixValues.fullValue
        (CanonicalRootLocationItem tokens rule origin finish context)
        complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherentPrefix trace} :
    CoherentActionLocationSound complete coherentPrefix
      (ActionReduces.root rule origin finish
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens rule origin finish context)
          complete priorValues)
        output (inputEq ▸ reduces)) trace carries := by
  cases classified with
  | items origin finish importKw reference dot openBrace entries closeBrace
      hidingValue semicolon witness entriesContained =>
      apply coherentRootLocationSound_of_endpointPair
        (reduces := RuleReduction.importDeclItems origin finish importKw
          reference dot openBrace entries closeBrace hidingValue semicolon
            witness) inputEq
      · exact importDeclItems_endpoint_directTrace_sublist owned origin finish
          importKw reference dot openBrace entries closeBrace hidingValue
            semicolon witness
      · intro trace selected traceWithin traceOrdered inputEvidence
        exact importDeclItems_locationSound_of_endpoint_pair_and_entries owned
          tokensOrdered origin finish importKw reference dot openBrace entries
            closeBrace hidingValue semicolon witness trace selected traceWithin
              traceOrdered inputEvidence entriesContained

end ImportDeclItemsLocationCase

namespace ExportDeclLocalLocationCase

theorem coherentRootLocationSound
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalRootLocationItem tokens rule origin finish context)}
    {complete : CompleteItem
      (CanonicalRootLocationItem tokens rule origin finish context).raw}
    {coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalRootLocationItem tokens rule origin finish context) priorValues}
    {ruleInput : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (reduces : RuleReduction file tokens rule origin finish ruleInput output)
    (classified : RuleReduction.ExportDeclLocalLocationCase reduces)
    (inputEq : ruleInput = RootAction.unpack rule
      (PrefixValues.fullValue
        (CanonicalRootLocationItem tokens rule origin finish context)
        complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherentPrefix trace} :
    CoherentActionLocationSound complete coherentPrefix
      (ActionReduces.root rule origin finish
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens rule origin finish context)
          complete priorValues)
        output (inputEq ▸ reduces)) trace carries := by
  cases classified with
  | localCase origin finish exportKw openBrace entries closeBrace semicolon
      witness entriesContained =>
      apply coherentRootLocationSound_of_endpointPair
        (reduces := RuleReduction.exportDeclLocal origin finish exportKw
          openBrace entries closeBrace semicolon witness) inputEq
      · exact exportDeclLocal_endpoint_directTrace_sublist owned origin finish
          exportKw openBrace entries closeBrace semicolon witness
      · intro trace selected traceWithin traceOrdered inputEvidence
        exact exportDeclLocal_locationSound_of_endpoint_pair_and_entries owned
          tokensOrdered origin finish exportKw openBrace entries closeBrace
            semicolon witness trace selected traceWithin traceOrdered
              inputEvidence entriesContained

end ExportDeclLocalLocationCase

namespace ExportDeclBracedLocationCase

theorem coherentRootLocationSound
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalRootLocationItem tokens rule origin finish context)}
    {complete : CompleteItem
      (CanonicalRootLocationItem tokens rule origin finish context).raw}
    {coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalRootLocationItem tokens rule origin finish context) priorValues}
    {ruleInput : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (reduces : RuleReduction file tokens rule origin finish ruleInput output)
    (classified : RuleReduction.ExportDeclBracedLocationCase reduces)
    (inputEq : ruleInput = RootAction.unpack rule
      (PrefixValues.fullValue
        (CanonicalRootLocationItem tokens rule origin finish context)
        complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherentPrefix trace} :
    CoherentActionLocationSound complete coherentPrefix
      (ActionReduces.root rule origin finish
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens rule origin finish context)
          complete priorValues)
        output (inputEq ▸ reduces)) trace carries := by
  cases classified with
  | braced origin finish exportKw reference dot openBrace entries closeBrace
      semicolon witness entriesContained =>
      apply coherentRootLocationSound_of_endpointPair
        (reduces := RuleReduction.exportDeclBraced origin finish exportKw
          reference dot openBrace entries closeBrace semicolon witness) inputEq
      · exact exportDeclBraced_endpoint_directTrace_sublist owned origin finish
          exportKw reference dot openBrace entries closeBrace semicolon witness
      · intro trace selected traceWithin traceOrdered inputEvidence
        exact exportDeclBraced_locationSound_of_endpoint_pair_and_entries owned
          tokensOrdered origin finish exportKw reference dot openBrace entries
            closeBrace semicolon witness trace selected traceWithin traceOrdered
              inputEvidence entriesContained

end ExportDeclBracedLocationCase

end RuleReduction

end Solcore.Surface.Multi
namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

structure RuleSpanFocus where
  rule : GrammarRuleId
  span : RuleValue rule → SourceSpan
  nonnullable : rule ≠ .optionalComma
  notModule : rule ≠ .module
  consumed : ∀ {file : WorkspaceFile} {tokens : List Token}
      {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs rule)}
      {output : RuleValue rule},
    RuleReduction file tokens rule origin finish input output →
      ConsumedSpan file tokens origin finish (span output)

def RuleSpanFocus.ruleSpans (focus : RuleSpanFocus) :
    (rule : GrammarRuleId) → RuleValue rule → List SourceSpan :=
  fun rule value =>
    if equality : rule = focus.rule then
      [focus.span (equality ▸ value)]
    else
      []

def FocusedSpanFamily
    (focus : RuleSpanFocus) (file : WorkspaceFile) (tokens : List Token) :
    (index : EbnfValueIndex) → EbnfFamily file tokens index →
      List SourceSpan
  | .expression (.atom (.terminal terminal)), matched =>
      let matched := Eq.mp (ebnfValue_atom_terminal_eq terminal) matched
      if terminal = .endOfFile then [] else [matched.span]
  | .expression (.atom (.nonterminal rule)), value =>
      focus.ruleSpans rule
        (Eq.mp (ebnfValue_atom_nonterminal_eq rule) value)
  | .expression (.sequence children), values =>
      FocusedSpanFamily focus file tokens (.expressions children)
        (Eq.mp (ebnfValue_sequence_eq children) values)
  | .expression (.group child), value =>
      FocusedSpanFamily focus file tokens (.expression child)
        (Eq.mp (ebnfValue_group_eq child) value)
  | .expression (.choice branches), value =>
      let selected := Eq.mp (ebnfValue_choice_eq branches) value
      FocusedSpanFamily focus file tokens
        (.expression (branches.get selected.1)) selected.2
  | .expression (.optional child), value =>
      match Eq.mp (ebnfValue_optional_eq child) value with
      | none => []
      | some childValue =>
          FocusedSpanFamily focus file tokens (.expression child) childValue
  | .expression (.star child), values =>
      (Eq.mp (ebnfValue_star_eq child) values).flatMap fun value =>
        FocusedSpanFamily focus file tokens (.expression child) value
  | .expression (.plus child), values =>
      let viewed := Eq.mp (ebnfValue_plus_eq child) values
      FocusedSpanFamily focus file tokens (.expression child) viewed.head ++
        viewed.tail.flatMap fun value =>
          FocusedSpanFamily focus file tokens (.expression child) value
  | .expression (.list0 child), values =>
      (Eq.mp (ebnfValue_list0_eq child) values).flatMap fun value =>
        FocusedSpanFamily focus file tokens (.expression child) value
  | .expression (.list1 child), values =>
      let viewed := Eq.mp (ebnfValue_list1_eq child) values
      FocusedSpanFamily focus file tokens (.expression child) viewed.head ++
        viewed.tail.flatMap fun value =>
          FocusedSpanFamily focus file tokens (.expression child) value
  | .expressions [], _ => []
  | .expressions (child :: rest), values =>
      let viewed := Eq.mp (ebnfValues_cons_eq child rest) values
      FocusedSpanFamily focus file tokens (.expression child) viewed.1 ++
        FocusedSpanFamily focus file tokens (.expressions rest) viewed.2
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

abbrev EbnfValue.focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) {expression : EbnfExpr}
    (value : EbnfValue file tokens expression) : List SourceSpan :=
  FocusedSpanFamily focus file tokens (.expression expression) value

abbrev EbnfValues.focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) {expressions : List EbnfExpr}
    (values : EbnfValues file tokens expressions) : List SourceSpan :=
  FocusedSpanFamily focus file tokens (.expressions expressions) values

@[simp] theorem EbnfValue.focusedSpans_terminalAtom
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    (EbnfValue.terminalAtom terminal matched).focusedSpans focus =
      if terminal = .endOfFile then [] else [matched.span] := by
  simp [EbnfValue.focusedSpans, FocusedSpanFamily,
    EbnfValue.terminalAtom, cast_cast]

@[simp] theorem EbnfValue.focusedSpans_ruleAtom
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (rule : GrammarRuleId)
    (value : RuleValue rule) :
    (EbnfValue.ruleAtom (file := file) (tokens := tokens)
      rule value).focusedSpans focus = focus.ruleSpans rule value := by
  simp [EbnfValue.focusedSpans, FocusedSpanFamily,
    EbnfValue.ruleAtom, cast_cast]

@[simp] theorem EbnfValue.focusedSpans_transport
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) {left right : EbnfExpr}
    (shape : left = right) (value : EbnfValue file tokens left) :
    (EbnfValue.transport shape value).focusedSpans focus =
      value.focusedSpans focus := by
  cases shape
  rfl

@[simp] theorem EbnfValue.focusedSpans_atShape
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) {site : GrammarSite} {expression : EbnfExpr}
    (shape : site.expression = expression)
    (value : EbnfValue file tokens site.expression) :
    (EbnfValue.atShape shape value).focusedSpans focus =
      value.focusedSpans focus := by
  exact EbnfValue.focusedSpans_transport focus shape value

@[simp] theorem EbnfValue.focusedSpans_sequence
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (children : List EbnfExpr)
    (values : EbnfValues file tokens children) :
    (EbnfValue.sequence children values).focusedSpans focus =
      values.focusedSpans focus := by
  simp [EbnfValue.focusedSpans, EbnfValues.focusedSpans,
    FocusedSpanFamily, EbnfValue.sequence, cast_cast]

@[simp] theorem EbnfValue.focusedSpans_group
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (child : EbnfExpr)
    (value : EbnfValue file tokens child) :
    (EbnfValue.group child value).focusedSpans focus =
      value.focusedSpans focus := by
  simp [EbnfValue.focusedSpans, FocusedSpanFamily,
    EbnfValue.group, cast_cast]

@[simp] theorem EbnfValue.focusedSpans_optional_none
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (child : EbnfExpr) :
    (EbnfValue.optional (file := file) (tokens := tokens)
      child none).focusedSpans focus = [] := by
  simp [EbnfValue.focusedSpans, FocusedSpanFamily,
    EbnfValue.optional, cast_cast]

@[simp] theorem EbnfValue.focusedSpans_optional_some
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (child : EbnfExpr)
    (value : EbnfValue file tokens child) :
    (EbnfValue.optional child (some value)).focusedSpans focus =
      value.focusedSpans focus := by
  simp [EbnfValue.focusedSpans, FocusedSpanFamily,
    EbnfValue.optional, cast_cast]

@[simp] theorem EbnfValue.focusedSpans_choice
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (branches : List EbnfExpr)
    (value : (branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch)) :
    (EbnfValue.choice branches value).focusedSpans focus =
      value.2.focusedSpans focus := by
  have viewed : Eq.mp (ebnfValue_choice_eq branches)
      (EbnfValue.choice branches value) = value := by
    unfold EbnfValue.choice
    change cast _ (cast _ value) = value
    rw [cast_cast]
    apply cast_eq
  unfold EbnfValue.focusedSpans
  rw [FocusedSpanFamily, viewed]

@[simp] theorem EbnfValue.focusedSpans_star
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (child : EbnfExpr)
    (values : List (EbnfValue file tokens child)) :
    (EbnfValue.star child values).focusedSpans focus =
      values.flatMap fun value => value.focusedSpans focus := by
  simp [EbnfValue.focusedSpans, FocusedSpanFamily,
    EbnfValue.star, cast_cast]

@[simp] theorem EbnfValue.focusedSpans_plus
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (child : EbnfExpr)
    (values : NonemptyList (EbnfValue file tokens child)) :
    (EbnfValue.plus child values).focusedSpans focus =
      values.head.focusedSpans focus ++
        values.tail.flatMap fun value => value.focusedSpans focus := by
  simp [EbnfValue.focusedSpans, FocusedSpanFamily,
    EbnfValue.plus, cast_cast]

@[simp] theorem EbnfValue.focusedSpans_list0
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (child : EbnfExpr)
    (values : List (EbnfValue file tokens child)) :
    (EbnfValue.list0 child values).focusedSpans focus =
      values.flatMap fun value => value.focusedSpans focus := by
  simp [EbnfValue.focusedSpans, FocusedSpanFamily,
    EbnfValue.list0, cast_cast]

@[simp] theorem EbnfValue.focusedSpans_list1
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (child : EbnfExpr)
    (values : NonemptyList (EbnfValue file tokens child)) :
    (EbnfValue.list1 child values).focusedSpans focus =
      values.head.focusedSpans focus ++
        values.tail.flatMap fun value => value.focusedSpans focus := by
  simp [EbnfValue.focusedSpans, FocusedSpanFamily,
    EbnfValue.list1, cast_cast]

@[simp] theorem EbnfValues.focusedSpans_nil
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) :
    (EbnfValues.nil (file := file) (tokens := tokens)).focusedSpans focus =
      [] := by
  simp [EbnfValues.focusedSpans, FocusedSpanFamily, EbnfValues.nil]

@[simp] theorem EbnfValues.focusedSpans_cons
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (child : EbnfExpr) (rest : List EbnfExpr)
    (head : EbnfValue file tokens child)
    (tail : EbnfValues file tokens rest) :
    (EbnfValues.cons child rest head tail).focusedSpans focus =
      head.focusedSpans focus ++ tail.focusedSpans focus := by
  simp [EbnfValues.focusedSpans, FocusedSpanFamily,
    EbnfValues.cons, cast_cast]

@[simp] theorem EbnfValues.focusedSpans_nil_raw
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (values : EbnfValues file tokens []) :
    values.focusedSpans focus = [] := by
  unfold EbnfValues.focusedSpans
  rw [FocusedSpanFamily]

@[simp] theorem EbnfValues.focusedSpans_cons_raw
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (child : EbnfExpr) (rest : List EbnfExpr)
    (values : EbnfValues file tokens (child :: rest)) :
    values.focusedSpans focus =
      (Eq.mp (ebnfValues_cons_eq child rest) values).1.focusedSpans focus ++
        (Eq.mp (ebnfValues_cons_eq child rest) values).2.focusedSpans focus := by
  unfold EbnfValues.focusedSpans
  rw [FocusedSpanFamily]

theorem EbnfValue.focusedSpans_sequence_raw
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (children : List EbnfExpr)
    (value : EbnfValue file tokens (.sequence children)) :
    value.focusedSpans focus =
      (Eq.mp (ebnfValue_sequence_eq children) value).focusedSpans focus := by
  unfold EbnfValue.focusedSpans
  rw [FocusedSpanFamily]

@[simp] theorem EbnfValue.focusedSpans_star_raw
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (child : EbnfExpr)
    (value : EbnfValue file tokens (.star child)) :
    value.focusedSpans focus =
      (Eq.mp (ebnfValue_star_eq child) value).flatMap fun element =>
        element.focusedSpans focus := by
  unfold EbnfValue.focusedSpans
  rw [FocusedSpanFamily]

@[simp] theorem EbnfValue.focusedSpans_plus_raw
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (child : EbnfExpr)
    (value : EbnfValue file tokens (.plus child)) :
    value.focusedSpans focus =
      let elements := Eq.mp (ebnfValue_plus_eq child) value
      elements.head.focusedSpans focus ++
        elements.tail.flatMap fun element => element.focusedSpans focus := by
  unfold EbnfValue.focusedSpans
  rw [FocusedSpanFamily]

theorem EbnfValue.flatMap_focusedSpans_transport_site
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) {left right : GrammarSite}
    (equality : left = right)
    (values : List (EbnfValue file tokens left.expression)) :
    (Eq.mp
        (congrArg
          (fun site : GrammarSite =>
            List (EbnfValue file tokens site.expression))
          equality)
        values).flatMap (fun value => value.focusedSpans focus) =
      values.flatMap fun value => value.focusedSpans focus := by
  cases equality
  rfl

def NonterminalValue.focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) :
    (symbol : NonterminalSymbol) → NonterminalValue file tokens symbol →
      List SourceSpan
  | .rule rule, value => focus.ruleSpans rule value
  | .aux _site, value => EbnfValue.focusedSpans focus value
  | .tail _site, values =>
      values.flatMap fun value => EbnfValue.focusedSpans focus value

def GrammarSymbolValue.focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) :
    (symbol : GrammarSymbol) → GrammarSymbolValue file tokens symbol →
      List SourceSpan
  | .terminal terminal, matched =>
      if terminal = .endOfFile then [] else [matched.span]
  | .nonterminal symbol, value =>
      NonterminalValue.focusedSpans focus symbol value

def GrammarSymbolValues.focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) :
    (symbols : List GrammarSymbol) → GrammarSymbolValues file tokens symbols →
      List SourceSpan
  | [], _values => []
  | symbol :: rest, values =>
      GrammarSymbolValue.focusedSpans focus symbol values.1 ++
        GrammarSymbolValues.focusedSpans focus rest values.2

@[simp] theorem NonterminalValue.focusedSpans_rule
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (rule : GrammarRuleId)
    (value : RuleValue rule) :
    NonterminalValue.focusedSpans (file := file) (tokens := tokens)
        focus (.rule rule) value =
      focus.ruleSpans rule value := by
  rfl

@[simp] theorem NonterminalValue.focusedSpans_aux
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : GrammarSite)
    (value : EbnfValue file tokens site.expression) :
    NonterminalValue.focusedSpans focus (.aux site) value =
      value.focusedSpans focus := by
  rfl

@[simp] theorem NonterminalValue.focusedSpans_tail
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : ListSite)
    (values : List (EbnfValue file tokens site.element.expression)) :
    NonterminalValue.focusedSpans focus (.tail site) values =
      values.flatMap fun value => value.focusedSpans focus := by
  rfl

@[simp] theorem GrammarSymbolValue.focusedSpans_terminal
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    GrammarSymbolValue.focusedSpans focus (.terminal terminal) matched =
      if terminal = .endOfFile then [] else [matched.span] := by
  rfl

@[simp] theorem GrammarSymbolValue.focusedSpans_nonterminal
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (symbol : NonterminalSymbol)
    (value : NonterminalValue file tokens symbol) :
    GrammarSymbolValue.focusedSpans focus (.nonterminal symbol) value =
      NonterminalValue.focusedSpans focus symbol value := by
  rfl

@[simp] theorem GrammarSymbolValue.focusedSpans_transport
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) {left right : GrammarSymbol}
    (shape : left = right) (value : GrammarSymbolValue file tokens left) :
    GrammarSymbolValue.focusedSpans focus right
        (Eq.mp (congrArg (GrammarSymbolValue file tokens) shape) value) =
      GrammarSymbolValue.focusedSpans focus left value := by
  cases shape
  rfl

@[simp] theorem GrammarSymbolValues.focusedSpans_append
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) {left right : List GrammarSymbol}
    (leftValues : GrammarSymbolValues file tokens left)
    (rightValues : GrammarSymbolValues file tokens right) :
    GrammarSymbolValues.focusedSpans focus (left ++ right)
        (GrammarSymbolValues.append leftValues rightValues) =
      GrammarSymbolValues.focusedSpans focus left leftValues ++
        GrammarSymbolValues.focusedSpans focus right rightValues := by
  induction left with
  | nil => rfl
  | cons symbol rest inductionHypothesis =>
      rcases leftValues with ⟨head, tail⟩
      change GrammarSymbolValue.focusedSpans focus symbol head ++
          GrammarSymbolValues.focusedSpans focus (rest ++ right)
            (GrammarSymbolValues.append tail rightValues) = _
      rw [inductionHypothesis tail]
      exact (List.append_assoc _ _ _).symm

@[simp] theorem GrammarSymbolValues.focusedSpans_transport
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) {left right : List GrammarSymbol}
    (shape : left = right) (values : GrammarSymbolValues file tokens left) :
    GrammarSymbolValues.focusedSpans focus right
        (GrammarSymbolValues.transport shape values) =
      GrammarSymbolValues.focusedSpans focus left values := by
  cases shape
  rfl

@[simp] theorem GrammarSymbolValues.focusedSpans_singleton
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (symbol : GrammarSymbol)
    (value : GrammarSymbolValue file tokens symbol) :
    GrammarSymbolValues.focusedSpans focus [symbol] (value, ()) =
      GrammarSymbolValue.focusedSpans focus symbol value := by
  simp [GrammarSymbolValues.focusedSpans]

@[simp] theorem GrammarSymbolValues.focusedSpans_view
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) {production : ProductionId}
    {canonicalRhs : List GrammarSymbol}
    (layout : production.rhs = canonicalRhs)
    (values : GrammarSymbolValues file tokens production.rhs) :
    GrammarSymbolValues.focusedSpans focus canonicalRhs
        (GrammarSymbolValues.view layout values) =
      GrammarSymbolValues.focusedSpans focus production.rhs values := by
  unfold GrammarSymbolValues.view
  exact GrammarSymbolValues.focusedSpans_transport focus layout values

@[simp] theorem EbnfValues.focusedSpans_ofAuxiliaries
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (sites : List GrammarSite)
    (values : GrammarSymbolValues file tokens
      (sites.map fun site => GrammarSymbol.nonterminal (.aux site))) :
    (EbnfValues.ofAuxiliaries sites values).focusedSpans focus =
      GrammarSymbolValues.focusedSpans focus
        (sites.map fun site => GrammarSymbol.nonterminal (.aux site)) values := by
  induction sites with
  | nil =>
      simp only [List.map] at values ⊢
      cases values
      rw [EbnfValues.focusedSpans_nil_raw]
      rfl
  | cons site rest inductionHypothesis =>
      simp only [List.map] at values ⊢
      rcases values with ⟨head, tail⟩
      rw [EbnfValues.focusedSpans_cons_raw]
      rw [EbnfValues.ofAuxiliaries_cons_eq]
      rw [inductionHypothesis]
      rfl

@[simp] theorem RootAction.unpack_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (rule : GrammarRuleId)
    (values : GrammarSymbolValues file tokens
      (ProductionId.root rule).rhs) :
    (RootAction.unpack rule values).focusedSpans focus =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.root rule).rhs values := by
  rw [RootAction.unpack_eq]
  rw [EbnfValue.focusedSpans_atShape]
  let viewed := GrammarSymbolValues.view
    (ProductionId.rhs_root rule) values
  calc
    _ = GrammarSymbolValues.focusedSpans focus
          [.nonterminal (.aux (GrammarSite.root rule))] viewed := by
        exact (GrammarSymbolValues.focusedSpans_singleton focus
          (.nonterminal (.aux (GrammarSite.root rule))) viewed.1).symm
    _ = GrammarSymbolValues.focusedSpans focus
          (ProductionId.root rule).rhs values :=
        GrammarSymbolValues.focusedSpans_view focus
          (ProductionId.rhs_root rule) values

abbrev PrefixValues.focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (item : ContextualItemKey tokens)
    (values : PrefixValues file tokens item) : List SourceSpan :=
  GrammarSymbolValues.focusedSpans focus
    (item.raw.production.rhs.take item.raw.dot.val) values

@[simp] theorem PrefixValues.focusedSpans_zeroValue
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (item : ContextualItemKey tokens)
    (zero : item.raw.dot.val = 0) :
    PrefixValues.focusedSpans focus item
      (PrefixValues.zeroValue (file := file) item zero) = [] := by
  unfold PrefixValues.focusedSpans
  unfold PrefixValues.zeroValue
  rw [GrammarSymbolValues.focusedSpans_transport]
  rfl

@[simp] theorem PrefixValues.focusedSpans_scanValue
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (before after : ContextualItemKey tokens)
    (terminal : TerminalSymbol) (next : NextSymbol before.raw (.terminal terminal))
    (matched : MatchedTerminal file tokens terminal)
    (advance : AdvanceItem before.raw matched.cursor.afterBoundary after.raw)
    (priorValues : PrefixValues file tokens before) :
    PrefixValues.focusedSpans focus after
        (PrefixValues.scanValue before after terminal next matched advance
          priorValues) =
      PrefixValues.focusedSpans focus before priorValues ++
        (if terminal = .endOfFile then [] else [matched.span]) := by
  unfold PrefixValues.focusedSpans PrefixValues.scanValue
  rw [GrammarSymbolValues.focusedSpans_transport]
  rw [GrammarSymbolValues.focusedSpans_append]
  simp [GrammarSymbolValues.focusedSpans,
    GrammarSymbolValue.focusedSpans]

@[simp] theorem PrefixValues.focusedSpans_completeValue
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (waiting finished after : ContextualItemKey tokens)
    (next : NextSymbol waiting.raw
      (.nonterminal finished.raw.production.lhs))
    (advance : AdvanceItem waiting.raw finished.raw.current after.raw)
    (priorValues : PrefixValues file tokens waiting)
    (childValue : NonterminalValue file tokens
      finished.raw.production.lhs) :
    PrefixValues.focusedSpans focus after
        (PrefixValues.completeValue waiting finished after next advance
          priorValues childValue) =
      PrefixValues.focusedSpans focus waiting priorValues ++
        NonterminalValue.focusedSpans focus
          finished.raw.production.lhs childValue := by
  unfold PrefixValues.focusedSpans PrefixValues.completeValue
  rw [GrammarSymbolValues.focusedSpans_transport]
  rw [GrammarSymbolValues.focusedSpans_append]
  simp [GrammarSymbolValues.focusedSpans,
    GrammarSymbolValue.focusedSpans]

@[simp] theorem PrefixValues.focusedSpans_fullValue
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (item : ContextualItemKey tokens)
    (complete : CompleteItem item.raw)
    (priorValues : PrefixValues file tokens item) :
    GrammarSymbolValues.focusedSpans focus item.raw.production.rhs
        (PrefixValues.fullValue item complete priorValues) =
      PrefixValues.focusedSpans focus item priorValues := by
  unfold PrefixValues.focusedSpans PrefixValues.fullValue
  rw [GrammarSymbolValues.focusedSpans_transport]

@[simp] theorem AtomSite.pack_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus)
    (site : AtomSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.atom site).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (AtomSite.pack site values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.atom site).rhs values := by
  cases atomEq : site.atom with
  | terminal terminal =>
      rw [NonterminalValue.focusedSpans_aux]
      rw [← EbnfValue.focusedSpans_atShape focus
        site.expression_eq_atom]
      rw [← EbnfValue.focusedSpans_transport focus
        (congrArg EbnfExpr.atom atomEq)]
      change EbnfValue.focusedSpans focus
        (AtomSite.packAtAtom site (.terminal terminal) atomEq values) = _
      rw [AtomSite.pack_terminal_eq]
      rw [EbnfValue.focusedSpans_terminalAtom]
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_atom site) values
      let atomValue := Eq.mp
        (congrArg (GrammarSymbolValue file tokens) site.symbol_eq) viewed.1
      calc
        _ = GrammarSymbolValue.focusedSpans focus
              (EbnfAtom.terminal terminal).grammarSymbol
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                (congrArg EbnfAtom.grammarSymbol atomEq)) atomValue) := rfl
        _ = GrammarSymbolValue.focusedSpans focus
              site.atom.grammarSymbol atomValue :=
            GrammarSymbolValue.focusedSpans_transport focus
              (congrArg EbnfAtom.grammarSymbol atomEq) atomValue
        _ = GrammarSymbolValue.focusedSpans focus site.symbol
              viewed.1 :=
            GrammarSymbolValue.focusedSpans_transport focus
              site.symbol_eq viewed.1
        _ = GrammarSymbolValues.focusedSpans focus [site.symbol]
              viewed := by
            exact (GrammarSymbolValues.focusedSpans_singleton focus
              site.symbol viewed.1).symm
        _ = GrammarSymbolValues.focusedSpans focus
              (ProductionId.atom site).rhs values :=
            GrammarSymbolValues.focusedSpans_view focus
              (ProductionId.rhs_atom site) values
  | nonterminal rule =>
      rw [NonterminalValue.focusedSpans_aux]
      rw [← EbnfValue.focusedSpans_atShape focus
        site.expression_eq_atom]
      rw [← EbnfValue.focusedSpans_transport focus
        (congrArg EbnfExpr.atom atomEq)]
      change EbnfValue.focusedSpans focus
        (AtomSite.packAtAtom site (.nonterminal rule) atomEq values) = _
      rw [AtomSite.pack_rule_eq]
      rw [EbnfValue.focusedSpans_ruleAtom]
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_atom site) values
      let atomValue := Eq.mp
        (congrArg (GrammarSymbolValue file tokens) site.symbol_eq) viewed.1
      calc
        _ = GrammarSymbolValue.focusedSpans focus
              (EbnfAtom.nonterminal rule).grammarSymbol
              (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                (congrArg EbnfAtom.grammarSymbol atomEq)) atomValue) := rfl
        _ = GrammarSymbolValue.focusedSpans focus
              site.atom.grammarSymbol atomValue :=
            GrammarSymbolValue.focusedSpans_transport focus
              (congrArg EbnfAtom.grammarSymbol atomEq) atomValue
        _ = GrammarSymbolValue.focusedSpans focus site.symbol
              viewed.1 :=
            GrammarSymbolValue.focusedSpans_transport focus
              site.symbol_eq viewed.1
        _ = GrammarSymbolValues.focusedSpans focus [site.symbol]
              viewed := by
            exact (GrammarSymbolValues.focusedSpans_singleton focus
              site.symbol viewed.1).symm
        _ = GrammarSymbolValues.focusedSpans focus
              (ProductionId.atom site).rhs values :=
            GrammarSymbolValues.focusedSpans_view focus
              (ProductionId.rhs_atom site) values

@[simp] theorem SequenceSite.pack_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : SequenceSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.seq site).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (SequenceSite.pack site values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.seq site).rhs values := by
  rw [NonterminalValue.focusedSpans_aux]
  rw [← EbnfValue.focusedSpans_atShape focus
    site.expression_eq_sequence]
  rw [SequenceSite.pack_eq]
  rw [EbnfValue.focusedSpans_sequence]
  rw [EbnfValues.focusedSpans_ofAuxiliaries]
  exact GrammarSymbolValues.focusedSpans_view focus
    (ProductionId.rhs_seq site) values

@[simp] theorem GroupSite.pack_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : GroupSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.group site).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (GroupSite.pack site values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.group site).rhs values := by
  rw [NonterminalValue.focusedSpans_aux]
  rw [← EbnfValue.focusedSpans_atShape focus
    site.expression_eq_group]
  rw [GroupSite.pack_eq]
  rw [EbnfValue.focusedSpans_group]
  calc
    _ = GrammarSymbolValues.focusedSpans focus
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_group site) values) := by
        exact (GrammarSymbolValues.focusedSpans_singleton focus
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_group site) values).1).symm
    _ = GrammarSymbolValues.focusedSpans focus
          (ProductionId.group site).rhs values :=
        GrammarSymbolValues.focusedSpans_view focus
          (ProductionId.rhs_group site) values

@[simp] theorem ChoiceSite.pack_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : ChoiceSite)
    (branch : Fin site.branchCount)
    (values : GrammarSymbolValues file tokens
      (ProductionId.choice site branch).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (ChoiceSite.pack site branch values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.choice site branch).rhs values := by
  rw [NonterminalValue.focusedSpans_aux]
  rw [← EbnfValue.focusedSpans_atShape focus
    site.expression_eq_choice]
  rw [ChoiceSite.pack_eq]
  rw [EbnfValue.focusedSpans_choice]
  rw [EbnfValue.focusedSpans_transport]
  calc
    _ = GrammarSymbolValues.focusedSpans focus
          [.nonterminal (.aux (site.branch branch))]
          (GrammarSymbolValues.view
            (ProductionId.rhs_choice site branch) values) := by
        exact (GrammarSymbolValues.focusedSpans_singleton focus
          (.nonterminal (.aux (site.branch branch)))
          (GrammarSymbolValues.view
            (ProductionId.rhs_choice site branch) values).1).symm
    _ = GrammarSymbolValues.focusedSpans focus
          (ProductionId.choice site branch).rhs values :=
        GrammarSymbolValues.focusedSpans_view focus
          (ProductionId.rhs_choice site branch) values

@[simp] theorem OptionalSite.pack_none_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .none).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (OptionalSite.pack site .none values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.opt site .none).rhs values := by
  rw [NonterminalValue.focusedSpans_aux]
  rw [← EbnfValue.focusedSpans_atShape focus
    site.expression_eq_optional]
  rw [OptionalSite.pack_none_eq]
  rw [EbnfValue.focusedSpans_optional_none]
  exact GrammarSymbolValues.focusedSpans_view focus
    (ProductionId.rhs_opt_none site) values

@[simp] theorem OptionalSite.pack_some_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .some).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (OptionalSite.pack site .some values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.opt site .some).rhs values := by
  rw [NonterminalValue.focusedSpans_aux]
  rw [← EbnfValue.focusedSpans_atShape focus
    site.expression_eq_optional]
  rw [OptionalSite.pack_some_eq]
  rw [EbnfValue.focusedSpans_optional_some]
  calc
    _ = GrammarSymbolValues.focusedSpans focus
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_opt_some site) values) := by
        exact (GrammarSymbolValues.focusedSpans_singleton focus
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_opt_some site) values).1).symm
    _ = GrammarSymbolValues.focusedSpans focus
          (ProductionId.opt site .some).rhs values :=
        GrammarSymbolValues.focusedSpans_view focus
          (ProductionId.rhs_opt_some site) values

@[simp] theorem OptionalSite.pack_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : OptionalSite)
    (branch : OptionalBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site branch).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (OptionalSite.pack site branch values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.opt site branch).rhs values := by
  cases branch with
  | none => exact OptionalSite.pack_none_focusedSpans focus site values
  | some => exact OptionalSite.pack_some_focusedSpans focus site values

@[simp] theorem StarSite.pack_nil_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .nil).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (StarSite.pack site .nil values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.star site .nil).rhs values := by
  rw [NonterminalValue.focusedSpans_aux]
  rw [← EbnfValue.focusedSpans_atShape focus site.expression_eq_star]
  rw [StarSite.pack_nil_eq]
  rw [EbnfValue.focusedSpans_star]
  exact GrammarSymbolValues.focusedSpans_view focus
    (ProductionId.rhs_star_nil site) values

@[simp] theorem StarSite.pack_cons_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .cons).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (StarSite.pack site .cons values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.star site .cons).rhs values := by
  rw [NonterminalValue.focusedSpans_aux]
  rw [← EbnfValue.focusedSpans_atShape focus site.expression_eq_star]
  rw [StarSite.pack_cons_eq]
  rw [EbnfValue.focusedSpans_star]
  simp only [List.flatMap_cons]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_star_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  change head.focusedSpans focus ++
      (Eq.mp (ebnfValue_star_eq site.child.expression)
        (EbnfValue.atShape site.expression_eq_star tail)).flatMap
          (fun element => element.focusedSpans focus) = _
  calc
    _ = head.focusedSpans focus ++
          EbnfValue.focusedSpans focus
            (EbnfValue.atShape site.expression_eq_star tail) := by
        rw [EbnfValue.focusedSpans_star_raw]
    _ = GrammarSymbolValue.focusedSpans focus
          (.nonterminal (.aux site.child)) head ++
          EbnfValue.focusedSpans focus tail := by
        rw [EbnfValue.focusedSpans_atShape]
    _ = GrammarSymbolValues.focusedSpans focus
          [.nonterminal (.aux site.child), .nonterminal (.aux site.site)]
          (head, (tail, ())) := by
        change _ = GrammarSymbolValue.focusedSpans focus
          (.nonterminal (.aux site.child)) head ++
            (GrammarSymbolValue.focusedSpans focus
              (.nonterminal (.aux site.site)) tail ++ [])
        simp only [GrammarSymbolValue.focusedSpans_nonterminal,
          NonterminalValue.focusedSpans_aux, List.append_nil]
    _ = GrammarSymbolValues.focusedSpans focus
          (ProductionId.star site .cons).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.focusedSpans_view focus
            (ProductionId.rhs_star_cons site) values)

@[simp] theorem StarSite.pack_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : StarSite)
    (branch : NilConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site branch).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (StarSite.pack site branch values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.star site branch).rhs values := by
  cases branch with
  | nil => exact StarSite.pack_nil_focusedSpans focus site values
  | cons => exact StarSite.pack_cons_focusedSpans focus site values

@[simp] theorem PlusSite.pack_one_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .one).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (PlusSite.pack site .one values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.plus site .one).rhs values := by
  rw [NonterminalValue.focusedSpans_aux]
  rw [← EbnfValue.focusedSpans_atShape focus site.expression_eq_plus]
  rw [PlusSite.pack_one_eq]
  rw [EbnfValue.focusedSpans_plus]
  simp only [List.flatMap_nil, List.append_nil]
  calc
    _ = GrammarSymbolValues.focusedSpans focus
          [.nonterminal (.aux site.child)]
          (GrammarSymbolValues.view
            (ProductionId.rhs_plus_one site) values) := by
        exact (GrammarSymbolValues.focusedSpans_singleton focus
          (.nonterminal (.aux site.child))
          (GrammarSymbolValues.view
            (ProductionId.rhs_plus_one site) values).1).symm
    _ = GrammarSymbolValues.focusedSpans focus
          (ProductionId.plus site .one).rhs values :=
        GrammarSymbolValues.focusedSpans_view focus
          (ProductionId.rhs_plus_one site) values

@[simp] theorem PlusSite.pack_cons_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .cons).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (PlusSite.pack site .cons values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.plus site .cons).rhs values := by
  rw [NonterminalValue.focusedSpans_aux]
  rw [← EbnfValue.focusedSpans_atShape focus site.expression_eq_plus]
  rw [PlusSite.pack_cons_eq]
  rw [EbnfValue.focusedSpans_plus]
  simp only [List.flatMap_cons]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_plus_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  rw [← EbnfValue.focusedSpans_plus_raw focus
    site.child.expression
    (EbnfValue.atShape site.expression_eq_plus tail)]
  rw [EbnfValue.focusedSpans_atShape]
  calc
    _ = GrammarSymbolValues.focusedSpans focus
          [.nonterminal (.aux site.child), .nonterminal (.aux site.site)]
          (head, (tail, ())) := by
        change _ = GrammarSymbolValue.focusedSpans focus
          (.nonterminal (.aux site.child)) head ++
            (GrammarSymbolValue.focusedSpans focus
              (.nonterminal (.aux site.site)) tail ++ [])
        simp only [GrammarSymbolValue.focusedSpans_nonterminal,
          NonterminalValue.focusedSpans_aux, List.append_nil]
    _ = GrammarSymbolValues.focusedSpans focus
          (ProductionId.plus site .cons).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.focusedSpans_view focus
            (ProductionId.rhs_plus_cons site) values)

@[simp] theorem PlusSite.pack_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : PlusSite)
    (branch : OneConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site branch).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (PlusSite.pack site branch values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.plus site branch).rhs values := by
  cases branch with
  | one => exact PlusSite.pack_one_focusedSpans focus site values
  | cons => exact PlusSite.pack_cons_focusedSpans focus site values

@[simp] theorem List0Site.pack_nil_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .nil).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (List0Site.pack site .nil values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.list0 site .nil).rhs values := by
  rw [NonterminalValue.focusedSpans_aux]
  rw [← EbnfValue.focusedSpans_atShape focus site.expression_eq_list0]
  rw [List0Site.pack_nil_eq]
  rw [EbnfValue.focusedSpans_list0]
  exact GrammarSymbolValues.focusedSpans_view focus
    (ProductionId.rhs_list0_nil site) values

@[simp] theorem List0Site.pack_cons_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .cons).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (List0Site.pack site .cons values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.list0 site .cons).rhs values := by
  rw [NonterminalValue.focusedSpans_aux]
  rw [← EbnfValue.focusedSpans_atShape focus site.expression_eq_list0]
  rw [List0Site.pack_cons_eq]
  rw [EbnfValue.focusedSpans_list0]
  simp only [List.flatMap_cons]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_list0_cons site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  rw [EbnfValue.flatMap_focusedSpans_transport_site focus
    (Grammar.ListSite.element_list0 site) tail]
  calc
    _ = GrammarSymbolValues.focusedSpans focus
          [.nonterminal (.aux site.element),
            .nonterminal (.tail (.list0 site))]
          (head, (tail, ())) := by
        change _ = GrammarSymbolValue.focusedSpans focus
          (.nonterminal (.aux site.element)) head ++
            (GrammarSymbolValue.focusedSpans focus
              (.nonterminal (.tail (.list0 site))) tail ++ [])
        simp only [GrammarSymbolValue.focusedSpans_nonterminal,
          NonterminalValue.focusedSpans_aux,
          NonterminalValue.focusedSpans_tail, List.append_nil]
    _ = GrammarSymbolValues.focusedSpans focus
          (ProductionId.list0 site .cons).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.focusedSpans_view focus
            (ProductionId.rhs_list0_cons site) values)

@[simp] theorem List0Site.pack_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : List0Site)
    (branch : NilConsBranch)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site branch).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (List0Site.pack site branch values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.list0 site branch).rhs values := by
  cases branch with
  | nil => exact List0Site.pack_nil_focusedSpans focus site values
  | cons => exact List0Site.pack_cons_focusedSpans focus site values

@[simp] theorem List1Site.pack_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : List1Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list1 site).rhs) :
    NonterminalValue.focusedSpans focus (.aux site.site)
        (List1Site.pack site values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.list1 site).rhs values := by
  rw [NonterminalValue.focusedSpans_aux]
  rw [← EbnfValue.focusedSpans_atShape focus site.expression_eq_list1]
  rw [List1Site.pack_eq]
  rw [EbnfValue.focusedSpans_list1]
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_list1 site) values = viewed
  rcases viewed with ⟨head, tail, restUnit⟩
  cases restUnit
  rw [EbnfValue.flatMap_focusedSpans_transport_site focus
    (Grammar.ListSite.element_list1 site) tail]
  calc
    _ = GrammarSymbolValues.focusedSpans focus
          [.nonterminal (.aux site.element),
            .nonterminal (.tail (.list1 site))]
          (head, (tail, ())) := by
        change _ = GrammarSymbolValue.focusedSpans focus
          (.nonterminal (.aux site.element)) head ++
            (GrammarSymbolValue.focusedSpans focus
              (.nonterminal (.tail (.list1 site))) tail ++ [])
        simp only [GrammarSymbolValue.focusedSpans_nonterminal,
          NonterminalValue.focusedSpans_aux,
          NonterminalValue.focusedSpans_tail, List.append_nil]
    _ = GrammarSymbolValues.focusedSpans focus
          (ProductionId.list1 site).rhs values := by
        simpa [viewedEq] using
          (GrammarSymbolValues.focusedSpans_view focus
            (ProductionId.rhs_list1 site) values)

@[simp] theorem ListSite.pack_nil_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .nil).rhs) :
    NonterminalValue.focusedSpans focus (.tail site)
        (ListSite.pack site .nil values) =
      GrammarSymbolValues.focusedSpans focus
        (ProductionId.tail site .nil).rhs values := by
  rw [ListSite.pack_nil_eq]
  rw [NonterminalValue.focusedSpans_tail]
  simp only [List.flatMap_nil]
  exact GrammarSymbolValues.focusedSpans_view focus
    (ProductionId.rhs_tail_nil site) values

theorem ListSite.pack_cons_rhs_focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (site : ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .cons).rhs) :
    GrammarSymbolValues.focusedSpans focus
        (ProductionId.tail site .cons).rhs values =
      GrammarSymbolValue.focusedSpans focus (.terminal (.symbol .comma))
        (GrammarSymbolValues.view
          (ProductionId.rhs_tail_cons site) values).1 ++
        NonterminalValue.focusedSpans focus (.tail site)
          (ListSite.pack site .cons values) := by
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_tail_cons site) values = viewed
  rcases viewed with ⟨comma, head, tail, restUnit⟩
  cases restUnit
  rw [ListSite.pack_cons_eq]
  rw [viewedEq]
  rw [NonterminalValue.focusedSpans_tail]
  calc
    _ = GrammarSymbolValues.focusedSpans focus
          [.terminal (.symbol .comma),
            .nonterminal (.aux site.element),
            .nonterminal (.tail site)]
          (comma, (head, (tail, ()))) := by
        symm
        simpa [viewedEq] using
          (GrammarSymbolValues.focusedSpans_view focus
            (ProductionId.rhs_tail_cons site) values)
    _ = [comma.span] ++
          (head.focusedSpans focus ++
            tail.flatMap fun element => element.focusedSpans focus) := by
        change [comma.span] ++
            (GrammarSymbolValue.focusedSpans focus
              (.nonterminal (.aux site.element)) head ++
              (GrammarSymbolValue.focusedSpans focus
                (.nonterminal (.tail site)) tail ++ [])) = _
        simp only [GrammarSymbolValue.focusedSpans_nonterminal,
          NonterminalValue.focusedSpans_aux,
          NonterminalValue.focusedSpans_tail, List.append_nil]

theorem auxiliary_focusedSpans_sublist
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus)
    {production : ProductionId}
    {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens production.rhs}
    {output : NonterminalValue file tokens production.lhs}
    (auxiliary : AuxiliaryProduction production)
    (reduces : ActionReduces file tokens (.actionFor production)
      origin finish input output) :
    (NonterminalValue.focusedSpans focus production.lhs output).Sublist
      (GrammarSymbolValues.focusedSpans focus production.rhs input) := by
  cases reduces with
  | root rule origin finish input output reduction =>
      exact False.elim auxiliary
  | atom site origin finish input =>
      change (NonterminalValue.focusedSpans focus (.aux site.site)
        (AtomSite.pack site input)).Sublist _
      rw [AtomSite.pack_focusedSpans focus site input]
      exact List.Sublist.refl _
  | seq site origin finish input =>
      change (NonterminalValue.focusedSpans focus (.aux site.site)
        (SequenceSite.pack site input)).Sublist _
      rw [SequenceSite.pack_focusedSpans focus site input]
      exact List.Sublist.refl _
  | group site origin finish input =>
      change (NonterminalValue.focusedSpans focus (.aux site.site)
        (GroupSite.pack site input)).Sublist _
      rw [GroupSite.pack_focusedSpans focus site input]
      exact List.Sublist.refl _
  | choice site branch origin finish input =>
      change (NonterminalValue.focusedSpans focus (.aux site.site)
        (ChoiceSite.pack site branch input)).Sublist _
      rw [ChoiceSite.pack_focusedSpans focus site branch input]
      exact List.Sublist.refl _
  | opt site branch origin finish input =>
      change (NonterminalValue.focusedSpans focus (.aux site.site)
        (OptionalSite.pack site branch input)).Sublist _
      rw [OptionalSite.pack_focusedSpans focus site branch input]
      exact List.Sublist.refl _
  | star site branch origin finish input =>
      change (NonterminalValue.focusedSpans focus (.aux site.site)
        (StarSite.pack site branch input)).Sublist _
      rw [StarSite.pack_focusedSpans focus site branch input]
      exact List.Sublist.refl _
  | plus site branch origin finish input =>
      change (NonterminalValue.focusedSpans focus (.aux site.site)
        (PlusSite.pack site branch input)).Sublist _
      rw [PlusSite.pack_focusedSpans focus site branch input]
      exact List.Sublist.refl _
  | list0 site branch origin finish input =>
      change (NonterminalValue.focusedSpans focus (.aux site.site)
        (List0Site.pack site branch input)).Sublist _
      rw [List0Site.pack_focusedSpans focus site branch input]
      exact List.Sublist.refl _
  | list1 site origin finish input =>
      change (NonterminalValue.focusedSpans focus (.aux site.site)
        (List1Site.pack site input)).Sublist _
      rw [List1Site.pack_focusedSpans focus site input]
      exact List.Sublist.refl _
  | tail site branch origin finish input =>
      cases branch with
      | nil =>
          change (NonterminalValue.focusedSpans focus (.tail site)
            (ListSite.pack site .nil input)).Sublist _
          rw [ListSite.pack_nil_focusedSpans focus site input]
          exact List.Sublist.refl _
      | cons =>
          change (NonterminalValue.focusedSpans focus (.tail site)
            (ListSite.pack site .cons input)).Sublist _
          rw [ListSite.pack_cons_rhs_focusedSpans focus site input]
          exact List.sublist_append_right _ _

/-- Every generated action preserves the direct terminal trace of its output
as a sublist of the trace presented to the action.  Source-rule outputs expose
no direct EBNF terminals, while auxiliary outputs satisfy the stronger
auxiliary theorem above. -/

theorem List.exists_sublist_with_map_eq
    {α β : Type} (mapValue : α → β) {selected : List β}
    (available : List α)
    (sublist : selected.Sublist (available.map mapValue)) :
    ∃ chosen : List α,
      chosen.Sublist available ∧ chosen.map mapValue = selected := by
  induction available generalizing selected with
  | nil =>
      have empty : selected = [] := List.eq_nil_of_sublist_nil sublist
      subst selected
      exact ⟨[], .slnil, rfl⟩
  | cons head tail inductionHypothesis =>
      cases sublist with
      | cons _ restSublist =>
          rcases inductionHypothesis restSublist with
            ⟨chosen, chosenSublist, chosenMap⟩
          exact ⟨chosen, chosenSublist.cons head, chosenMap⟩
      | cons_cons _ restSublist =>
          rcases inductionHypothesis restSublist with
            ⟨chosen, chosenSublist, chosenMap⟩
          exact ⟨head :: chosen, chosenSublist.cons_cons head, by
            simp only [List.map_cons, chosenMap]⟩

def FocusedSpanEvidence
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens) (spans : List SourceSpan) : Prop :=
  ∃ anchors : SourceAnchorTrace file tokens,
    anchors.spans = spans ∧
      anchors.Within origin finish ∧ anchors.Ordered

namespace FocusedSpanEvidence

theorem empty
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) :
    FocusedSpanEvidence file tokens origin finish [] := by
  exact ⟨[], rfl, SourceAnchorTrace.within_nil,
    SourceAnchorTrace.ordered_nil⟩

theorem select
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {available selected : List SourceSpan}
    (evidence : FocusedSpanEvidence file tokens origin finish available)
    (sublist : selected.Sublist available) :
    FocusedSpanEvidence file tokens origin finish selected := by
  rcases evidence with ⟨anchors, anchorSpans, inside, ordered⟩
  have mappedSublist : selected.Sublist anchors.spans := by
    rw [anchorSpans]
    exact sublist
  rcases List.exists_sublist_with_map_eq SourceAnchor.span anchors
      (by simpa [SourceAnchorTrace.spans] using mappedSublist) with
      ⟨chosen, chosenSublist, chosenSpans⟩
  refine ⟨chosen, ?_, ?_, ?_⟩
  · simpa [SourceAnchorTrace.spans] using chosenSpans
  · intro anchor member
    exact inside anchor (chosenSublist.subset member)
  · exact List.Pairwise.sublist chosenSublist ordered

/-- Every span between two endpoints in an exact focused trace is contained by
the synthetic source span joining those endpoints. -/
theorem between_contains_of_member
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {origin finish : Boundary tokens}
    {openSpan closeSpan : SourceSpan}
    {middleSpans : List SourceSpan}
    (evidence : FocusedSpanEvidence file tokens origin finish
      (openSpan :: middleSpans ++ [closeSpan]))
    {middleSpan : SourceSpan}
    (member : middleSpan ∈ middleSpans) :
    (RuleReduction.between file openSpan closeSpan ()).span.Contains
      middleSpan := by
  rcases evidence with ⟨anchors, anchorSpans, _inside, ordered⟩
  have middleSublist : [middleSpan].Sublist middleSpans :=
    List.singleton_sublist.mpr member
  have selectedSpanSublist :
      [openSpan, middleSpan, closeSpan].Sublist anchors.spans := by
    rw [anchorSpans]
    exact List.Sublist.cons_cons openSpan
      (middleSublist.append (List.Sublist.refl [closeSpan]))
  have mappedSublist :
      [openSpan, middleSpan, closeSpan].Sublist
        (anchors.map SourceAnchor.span) := by
    simpa [SourceAnchorTrace.spans] using selectedSpanSublist
  rcases List.sublist_map_iff.mp mappedSublist with
    ⟨selected, selectedSublist, selectedSpans⟩
  cases selected with
  | nil => simp at selectedSpans
  | cons left selectedTail =>
      cases selectedTail with
      | nil => simp at selectedSpans
      | cons middle selectedTail =>
          cases selectedTail with
          | nil => simp at selectedSpans
          | cons right selectedTail =>
              cases selectedTail with
              | cons extra rest => simp at selectedSpans
              | nil =>
                  simp only [List.map_cons, List.map_nil,
                    List.cons.injEq, and_true] at selectedSpans
                  rcases selectedSpans with
                    ⟨openEq, middleEq, closeEq⟩
                  have leftMiddle :
                      left.finish.val ≤ middle.origin.val :=
                    SourceAnchorTrace.finish_le_origin_of_pair_sublist
                      (by
                        apply List.Sublist.trans
                          (l₂ := [left, middle, right])
                        · simp
                        · exact selectedSublist)
                      ordered
                  have middleRight :
                      middle.finish.val ≤ right.origin.val :=
                    SourceAnchorTrace.finish_le_origin_of_pair_sublist
                      (by
                        apply List.Sublist.trans
                          (l₂ := [left, middle, right])
                        · simp
                        · exact selectedSublist)
                      ordered
                  have leftOccupied := Nat.lt_min.mp left.occupied.2
                  have middleOccupied := Nat.lt_min.mp middle.occupied.2
                  have rightOccupied := Nat.lt_min.mp right.occupied.2
                  have leftRight : left.origin.val ≤ right.origin.val := by
                    omega
                  let outer := SourceAnchor.between left right leftRight
                  have middleInside :
                      middle.Within left.origin right.finish := by
                    exact ⟨by omega, by omega⟩
                  have contained := SourceAnchor.containedBy tokensOrdered
                    outer.occupied.1 middle middleInside
                  simpa [outer, openEq, middleEq, closeEq] using contained

end FocusedSpanEvidence

private def PrefixFocusedSpanMotive
    (focus : RuleSpanFocus)
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
    (PrefixValues.focusedSpans focus item values)

private def ReductionFocusedSpanMotive
    (focus : RuleSpanFocus)
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
    (NonterminalValue.focusedSpans focus item.raw.production.lhs value)

private theorem prefixFocusedSpanZeroCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (focus : RuleSpanFocus) (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final item)
    (zero : item.raw.dot.val = 0) :
    PrefixFocusedSpanMotive focus file tokens memo correct final owned
      (.zero item reached zero) [] (.zero item reached zero) := by
  unfold PrefixFocusedSpanMotive
  rw [PrefixValues.focusedSpans_zeroValue]
  exact FocusedSpanEvidence.empty item.raw.origin item.raw.current

private theorem prefixFocusedSpanScanCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (focus : RuleSpanFocus) (owned : TokensOwnedBy file tokens)
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
    (priorIH : PrefixFocusedSpanMotive focus file tokens memo correct final
      owned prior priorTrace priorCarries) :
    PrefixFocusedSpanMotive focus file tokens memo correct final owned
      (.scan before after cursor priorValues witness edge prior)
      (priorTrace ++ witness.matched.sourceAnchorTrace owned)
      (.scan before after cursor priorValues witness edge prior priorTrace
        priorCarries) := by
  unfold PrefixFocusedSpanMotive at priorIH ⊢
  rcases priorIH with ⟨priorAnchors, priorSpans, priorInside,
    priorOrdered⟩
  refine ⟨priorAnchors ++ witness.matched.sourceAnchorTrace owned,
    ?_, ?_, ?_⟩
  · rw [SourceAnchorTrace.spans_append, priorSpans]
    rw [witness.matched.sourceAnchorTrace_spans owned]
    exact PrefixValues.focusedSpans_scanValue focus before after
      witness.terminal witness.next witness.matched witness.advance
        priorValues |>.symm
  · exact witness.sourceAnchorTrace_within owned
      (contextualReach_ordered edge.2.1) priorInside
  · exact witness.sourceAnchorTrace_ordered owned priorInside priorOrdered

private theorem prefixFocusedSpanCompleteCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (focus : RuleSpanFocus) (owned : TokensOwnedBy file tokens)
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
    (priorIH : PrefixFocusedSpanMotive focus file tokens memo correct final
      owned prior priorTrace priorCarries)
    (childIH : ReductionFocusedSpanMotive focus file tokens memo correct final
      owned child childTrace childCarries) :
    PrefixFocusedSpanMotive focus file tokens memo correct final owned
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child)
      (priorTrace ++ childTrace)
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child priorTrace childTrace priorCarries childCarries) := by
  unfold PrefixFocusedSpanMotive at priorIH ⊢
  unfold ReductionFocusedSpanMotive at childIH
  rcases priorIH with ⟨priorAnchors, priorSpans, priorInside,
    priorOrdered⟩
  rcases childIH with ⟨childAnchors, childSpans, childInside,
    childOrdered⟩
  refine ⟨priorAnchors ++ childAnchors, ?_, ?_, ?_⟩
  · rw [SourceAnchorTrace.spans_append, priorSpans, childSpans]
    exact PrefixValues.focusedSpans_completeValue focus waiting finished after
      witness.next witness.advance priorValues childValue |>.symm
  · exact witness.sourceAnchorTraces_within
      (contextualReach_ordered edge.2.1)
      (contextualReach_ordered edge.2.2.1) priorInside childInside
  · exact witness.sourceAnchorTraces_ordered priorInside childInside
      priorOrdered childOrdered

theorem completeRoot_progress
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {rule : GrammarRuleId}
    {item : ContextualItemKey tokens}
    (production : item.raw.production = .root rule)
    (reached : ContextualReach file tokens memo correct final item)
    (complete : CompleteItem item.raw)
    (notOptionalComma : rule ≠ .optionalComma) :
    item.raw.origin.val < item.raw.current.val := by
  apply contextualReach_origin_lt_current_of_prefix_not_all
    dottedStaticNullableSymbol dottedStaticNullableSymbol_closed reached
  rw [prefix_full_layout item.raw complete]
  intro nullable
  have lhsNullable := dottedStaticNullableSymbol_closed
    item.raw.production nullable
  rw [production] at lhsNullable
  have equal : rule = .optionalComma := by
    simpa [ProductionId.lhs, dottedStaticNullableSymbol,
      dottedStaticNullableNonterminal, nullableGrammarRules_eq] using
        lhsNullable
  exact notOptionalComma equal

namespace ActionReduces

theorem focusedSpanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus)
    {actionId : ActionId} {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens actionId.production.rhs}
    {output : NonterminalValue file tokens actionId.production.lhs}
    (action : ActionReduces file tokens actionId origin finish input output)
    (selectedProgress :
      actionId.production = .root focus.rule →
        origin.val < Nat.min finish.val tokens.length)
    (inputEvidence : FocusedSpanEvidence file tokens origin finish
      (GrammarSymbolValues.focusedSpans focus actionId.production.rhs input)) :
    FocusedSpanEvidence file tokens origin finish
      (NonterminalValue.focusedSpans focus actionId.production.lhs output) := by
  cases action with
  | root rule origin finish input output reduction =>
      simp only [ActionId.production_actionFor] at selectedProgress inputEvidence ⊢
      change FocusedSpanEvidence file tokens origin finish
        (focus.ruleSpans rule output)
      by_cases selected : rule = focus.rule
      · subst rule
        let anchor : SourceAnchor file tokens := {
          origin := origin
          finish := finish
          span := focus.span output
          occupied := ⟨focus.consumed reduction, selectedProgress rfl⟩
        }
        refine ⟨[anchor], ?_, ?_, ?_⟩
        · simp [anchor, RuleSpanFocus.ruleSpans]
        · intro selectedAnchor member
          simp only [List.mem_singleton] at member
          subst selectedAnchor
          exact ⟨Nat.le_refl _, Nat.le_refl _⟩
        · exact SourceAnchorTrace.ordered_singleton anchor
      · rw [RuleSpanFocus.ruleSpans]
        simp only [selected, ↓reduceDIte]
        exact FocusedSpanEvidence.empty origin finish
  | atom site origin finish input =>
      exact inputEvidence.select
        (auxiliary_focusedSpans_sublist focus trivial
          (ActionReduces.atom site origin finish input))
  | seq site origin finish input =>
      exact inputEvidence.select
        (auxiliary_focusedSpans_sublist focus trivial
          (ActionReduces.seq site origin finish input))
  | group site origin finish input =>
      exact inputEvidence.select
        (auxiliary_focusedSpans_sublist focus trivial
          (ActionReduces.group site origin finish input))
  | choice site branch origin finish input =>
      exact inputEvidence.select
        (auxiliary_focusedSpans_sublist focus trivial
          (ActionReduces.choice site branch origin finish input))
  | opt site branch origin finish input =>
      exact inputEvidence.select
        (auxiliary_focusedSpans_sublist focus trivial
          (ActionReduces.opt site branch origin finish input))
  | star site branch origin finish input =>
      exact inputEvidence.select
        (auxiliary_focusedSpans_sublist focus trivial
          (ActionReduces.star site branch origin finish input))
  | plus site branch origin finish input =>
      exact inputEvidence.select
        (auxiliary_focusedSpans_sublist focus trivial
          (ActionReduces.plus site branch origin finish input))
  | list0 site branch origin finish input =>
      exact inputEvidence.select
        (auxiliary_focusedSpans_sublist focus trivial
          (ActionReduces.list0 site branch origin finish input))
  | list1 site origin finish input =>
      exact inputEvidence.select
        (auxiliary_focusedSpans_sublist focus trivial
          (ActionReduces.list1 site origin finish input))
  | tail site branch origin finish input =>
      exact inputEvidence.select
        (auxiliary_focusedSpans_sublist focus trivial
          (ActionReduces.tail site branch origin finish input))

end ActionReduces

private def focusedPostEofGrammarShapeBool : Bool :=
  allProductionIds.all fun production =>
    ((! production.rhs.contains (.terminal .endOfFile)) ||
      decide (production = .atom moduleEofAtomSite)) &&
    ((! production.rhs.contains
        (.nonterminal (.aux moduleEofGrammarSite))) ||
      decide (production = .seq moduleRootSequenceSite)) &&
    ((! production.rhs.contains
        (.nonterminal (.aux (GrammarSite.root .module)))) ||
      decide (production = .root .module))

set_option maxRecDepth 4000 in
private theorem focusedPostEofGrammarShapeBool_true :
    focusedPostEofGrammarShapeBool = true := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem ProductionId.focusedPostEof_shape
    (production : ProductionId) :
    (.terminal .endOfFile ∈ production.rhs →
      production = .atom moduleEofAtomSite) ∧
    (.nonterminal (.aux moduleEofGrammarSite) ∈ production.rhs →
      production = .seq moduleRootSequenceSite) ∧
    (.nonterminal (.aux (GrammarSite.root .module)) ∈ production.rhs →
      production = .root .module) := by
  have row := (List.all_eq_true.mp focusedPostEofGrammarShapeBool_true)
    production (allProductionIds_complete production)
  simp only [Bool.and_eq_true] at row
  refine ⟨?_, ?_, ?_⟩
  · intro member
    have accepted := row.1.1
    rw [Bool.or_eq_true] at accepted
    rcases accepted with absent | equal
    · have present : production.rhs.contains (.terminal .endOfFile) =
          true := List.contains_iff_mem.mpr member
      rw [present] at absent
      contradiction
    · exact of_decide_eq_true equal
  · intro member
    have accepted := row.1.2
    rw [Bool.or_eq_true] at accepted
    rcases accepted with absent | equal
    · have present : production.rhs.contains
          (.nonterminal (.aux moduleEofGrammarSite)) = true :=
        List.contains_iff_mem.mpr member
      rw [present] at absent
      contradiction
    · exact of_decide_eq_true equal
  · intro member
    have accepted := row.2
    rw [Bool.or_eq_true] at accepted
    rcases accepted with absent | equal
    · have present : production.rhs.contains
          (.nonterminal (.aux (GrammarSite.root .module))) = true :=
        List.contains_iff_mem.mpr member
      rw [present] at absent
      contradiction
    · exact of_decide_eq_true equal

private theorem ContextualReach.afterLogicalEOF_shape
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item)
    (current : item.raw.current = Boundary.afterLogicalEOF tokens) :
    (item.raw.production = .atom moduleEofAtomSite ∧
        CompleteItem item.raw) ∨
      (item.raw.production = .seq moduleRootSequenceSite ∧
        CompleteItem item.raw) ∨
      (item.raw.production = .root .module ∧ CompleteItem item.raw) := by
  induction reached with
  | root =>
      have values := congrArg Fin.val current
      simp [Boundary.start, Boundary.afterLogicalEOF] at values
  | predict waiting predicted reached next enabled induction =>
      rcases induction current with
          ⟨production, complete⟩ | ⟨production, complete⟩ |
            ⟨production, complete⟩
      all_goals
        unfold NextSymbol at next
        unfold CompleteItem at complete
        omega
  | scan before after cursor reached structural induction =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      have cursorAtEnd : cursor.val = tokens.length := by
        have values := congrArg Fin.val current
        rw [advance.2.2.2] at values
        change cursor.val + 1 = tokens.length + 1 at values
        omega
      cases terminalAt with
      | retained token inRange lookup valid => omega
      | endOfFile atEnd =>
          have terminalEq : terminal = .endOfFile := by
            cases terminal <;> simp [TerminalMatches] at terminalMatches ⊢
          subst terminal
          have beforeProduction : before.raw.production =
              .atom moduleEofAtomSite :=
            (ProductionId.focusedPostEof_shape before.raw.production).1
              (List.mem_of_getElem? next.2)
          have afterProduction : after.raw.production =
              .atom moduleEofAtomSite :=
            advance.1.trans beforeProduction
          have beforeRhs : before.raw.production.rhs =
              [.terminal .endOfFile] :=
            (congrArg ProductionId.rhs beforeProduction).trans
              ProductionId.rhs_moduleEofAtom
          have beforeDot : before.raw.dot.val = 0 := by
            have bound := next.1
            have rhsLength : before.raw.production.rhs.length = 1 :=
              congrArg List.length beforeRhs
            omega
          exact Or.inl ⟨afterProduction, by
            unfold CompleteItem
            rw [advance.2.1, beforeDot]
            have afterRhs : after.raw.production.rhs =
                [.terminal .endOfFile] :=
              (congrArg ProductionId.rhs afterProduction).trans
                ProductionId.rhs_moduleEofAtom
            rw [congrArg List.length afterRhs]
            rfl⟩
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingInduction finishedInduction =>
      rcases structural.1 with
        ⟨symbol, next, childComplete, lhsEq, waitingAtShared,
          finishedAtShared, advance⟩
      have finishedCurrent : finished.raw.current =
          Boundary.afterLogicalEOF tokens :=
        advance.2.2.2.symm.trans current
      rcases finishedInduction finishedCurrent with
          ⟨finishedProduction, finishedComplete⟩ |
          ⟨finishedProduction, finishedComplete⟩ |
          ⟨finishedProduction, finishedComplete⟩
      · have exactNext : waiting.raw.production.rhs[waiting.raw.dot.val]? =
            some (.nonterminal (.aux moduleEofGrammarSite)) := by
          calc
            _ = some (.nonterminal symbol) := next.2
            _ = some (.nonterminal finished.raw.production.lhs) := by
              rw [lhsEq]
            _ = _ := by
              rw [finishedProduction]
              rfl
        have waitingProduction : waiting.raw.production =
            .seq moduleRootSequenceSite :=
          (ProductionId.focusedPostEof_shape waiting.raw.production).2.1
            (List.mem_of_getElem? exactNext)
        have waitingRhs : waiting.raw.production.rhs =
            [.nonterminal (.aux moduleItemsGrammarSite),
              .nonterminal (.aux moduleEofGrammarSite)] :=
          (congrArg ProductionId.rhs waitingProduction).trans
            ProductionId.rhs_moduleRootSequence
        have waitingDot : waiting.raw.dot.val = 1 := by
          have bound := next.1
          have rhsLength : waiting.raw.production.rhs.length = 2 :=
            congrArg List.length waitingRhs
          have cases : waiting.raw.dot.val = 0 ∨
              waiting.raw.dot.val = 1 := by omega
          rcases cases with zero | one
          · have selected := exactNext
            rw [congrArg (fun rhs : List GrammarSymbol =>
              rhs[waiting.raw.dot.val]?) waitingRhs, zero] at selected
            simp [moduleItemsGrammarSite, moduleEofGrammarSite] at selected
          · exact one
        have afterProduction := advance.1.trans waitingProduction
        exact Or.inr (Or.inl ⟨afterProduction, by
          unfold CompleteItem
          rw [advance.2.1, waitingDot]
          have afterRhs : after.raw.production.rhs =
              [.nonterminal (.aux moduleItemsGrammarSite),
                .nonterminal (.aux moduleEofGrammarSite)] :=
            (congrArg ProductionId.rhs afterProduction).trans
              ProductionId.rhs_moduleRootSequence
          rw [congrArg List.length afterRhs]
          rfl⟩)
      · have exactNext : waiting.raw.production.rhs[waiting.raw.dot.val]? =
            some (.nonterminal (.aux (GrammarSite.root .module))) := by
          calc
            _ = some (.nonterminal symbol) := next.2
            _ = some (.nonterminal finished.raw.production.lhs) := by
              rw [lhsEq]
            _ = _ := by
              rw [finishedProduction]
              rfl
        have waitingProduction : waiting.raw.production = .root .module :=
          (ProductionId.focusedPostEof_shape waiting.raw.production).2.2
            (List.mem_of_getElem? exactNext)
        have waitingDot : waiting.raw.dot.val = 0 := by
          have bound := next.1
          have rhsLength : waiting.raw.production.rhs.length = 1 := by
            rw [waitingProduction]
            simp [ProductionId.rhs]
          omega
        have afterProduction := advance.1.trans waitingProduction
        exact Or.inr (Or.inr ⟨afterProduction, by
          unfold CompleteItem
          rw [advance.2.1, waitingDot]
          have afterRhs : after.raw.production.rhs =
              [.nonterminal (.aux (GrammarSite.root .module))] := by
            rw [afterProduction]
            rfl
          rw [congrArg List.length afterRhs]
          rfl⟩)
      · have exactNext : waiting.raw.production.rhs[waiting.raw.dot.val]? =
            some (.nonterminal (.rule .module)) := by
          calc
            _ = some (.nonterminal symbol) := next.2
            _ = some (.nonterminal finished.raw.production.lhs) := by
              rw [lhsEq]
            _ = _ := by
              rw [finishedProduction]
              rfl
        exact (ProductionId.rhs_no_moduleRule waiting.raw.production
          (List.mem_of_getElem? exactNext)).elim

private theorem contextualReach_complete_nonmoduleRoot_current_le_length
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {rule : GrammarRuleId}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item)
    (production : item.raw.production = .root rule)
    (_complete : CompleteItem item.raw)
    (notModule : rule ≠ .module) :
    item.raw.current.val ≤ tokens.length := by
  by_cases atMost : item.raw.current.val ≤ tokens.length
  · exact atMost
  have currentValue : item.raw.current.val = tokens.length + 1 := by
    have bound := item.raw.current.isLt
    omega
  have current : item.raw.current = Boundary.afterLogicalEOF tokens := by
    apply Fin.ext
    simpa [Boundary.afterLogicalEOF] using currentValue
  rcases reached.afterLogicalEOF_shape current with
      ⟨atEof, _complete⟩ | ⟨atSequence, _complete⟩ |
        ⟨atModule, _complete⟩
  · rw [production] at atEof
    contradiction
  · rw [production] at atSequence
    contradiction
  · rw [production] at atModule
    exact False.elim (notModule (ProductionId.root.inj atModule))

theorem completeRoot_occupied
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {rule : GrammarRuleId}
    {item : ContextualItemKey tokens}
    (production : item.raw.production = .root rule)
    (reached : ContextualReach file tokens memo correct final item)
    (complete : CompleteItem item.raw)
    (notOptionalComma : rule ≠ .optionalComma)
    (notModule : rule ≠ .module) :
    item.raw.origin.val <
      Nat.min item.raw.current.val tokens.length := by
  have progress := completeRoot_progress production reached complete
    notOptionalComma
  have currentBound :=
    contextualReach_complete_nonmoduleRoot_current_le_length reached
      production complete notModule
  exact Nat.lt_min.mpr ⟨progress,
    Nat.lt_of_lt_of_le progress currentBound⟩

private theorem reductionFocusedSpanCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (focus : RuleSpanFocus) (owned : TokensOwnedBy file tokens)
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
    (prefixIH : PrefixFocusedSpanMotive focus file tokens memo correct final
      owned coherentPrefix trace prefixCarries) :
    ReductionFocusedSpanMotive focus file tokens memo correct final owned
      (.reduce item priorValues output reached complete coherentPrefix action)
      trace
      (.reduce item priorValues output reached complete coherentPrefix action
        trace prefixCarries) := by
  unfold PrefixFocusedSpanMotive at prefixIH
  unfold ReductionFocusedSpanMotive
  apply action.focusedSpanEvidence focus
  · intro production
    exact completeRoot_occupied
      (by simpa only [ActionId.production_actionFor] using production)
      reached complete focus.nonnullable focus.notModule
  · simp only [ActionId.production_actionFor]
    rw [PrefixValues.focusedSpans_fullValue]
    exact prefixIH

namespace PrefixCarriesSourceTrace

/-- A coherent prefix carries all retained terminals and every selected
source-rule principal span in grammar order. -/
theorem focusedSpanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (focus : RuleSpanFocus)
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    {coherent : CoherentPrefix file tokens memo correct final item values}
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    FocusedSpanEvidence file tokens item.raw.origin item.raw.current
      (PrefixValues.focusedSpans focus item values) :=
  PrefixCarriesSourceTrace.rec
    (motive_1 := PrefixFocusedSpanMotive
      focus file tokens memo correct final owned)
    (motive_2 := ReductionFocusedSpanMotive
      focus file tokens memo correct final owned)
    (prefixFocusedSpanZeroCase focus owned)
    (prefixFocusedSpanScanCase focus owned)
    (prefixFocusedSpanCompleteCase focus owned)
    (reductionFocusedSpanCase focus owned)
    carries

/-- At a completed canonical root item, focused evidence can be stated on the
exact source-rule EBNF input instead of the parser prefix tuple. -/
theorem rootInputFocusedSpanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (focus : RuleSpanFocus)
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
      (ruleInput.focusedSpans focus) := by
  have fullEvidence := carries.focusedSpanEvidence focus
  rw [← PrefixValues.focusedSpans_fullValue focus
    (RuleReduction.CanonicalRootLocationItem tokens rule origin finish context)
    complete priorValues] at fullEvidence
  change FocusedSpanEvidence file tokens origin finish
    (GrammarSymbolValues.focusedSpans focus (ProductionId.root rule).rhs
      (PrefixValues.fullValue
        (RuleReduction.CanonicalRootLocationItem tokens rule origin finish
          context) complete priorValues)) at fullEvidence
  rw [← RootAction.unpack_focusedSpans] at fullEvidence
  rw [← inputEq] at fullEvidence
  exact fullEvidence

end PrefixCarriesSourceTrace

namespace ReductionCarriesSourceTrace

/-- A coherent reduction carries all retained terminals and every selected
source-rule principal span in grammar order. -/
theorem focusedSpanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (focus : RuleSpanFocus)
    {item : ContextualItemKey tokens}
    {value : NonterminalValue file tokens item.raw.production.lhs}
    {coherent : CoherentReduction file tokens memo correct final item value}
    {trace : SourceAnchorTrace file tokens}
    (carries : ReductionCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    FocusedSpanEvidence file tokens item.raw.origin item.raw.current
      (NonterminalValue.focusedSpans focus
        item.raw.production.lhs value) :=
  ReductionCarriesSourceTrace.rec
    (motive_1 := PrefixFocusedSpanMotive
      focus file tokens memo correct final owned)
    (motive_2 := ReductionFocusedSpanMotive
      focus file tokens memo correct final owned)
    (prefixFocusedSpanZeroCase focus owned)
    (prefixFocusedSpanScanCase focus owned)
    (prefixFocusedSpanCompleteCase focus owned)
    (reductionFocusedSpanCase focus owned)
    carries

end ReductionCarriesSourceTrace

def importEntrySpanFocus : RuleSpanFocus := {
  rule := .importEntry
  span := fun entry => entry.span
  nonnullable := by decide
  notModule := by decide
  consumed := by
    intro file tokens origin finish input output reduction
    cases reduction with
    | importEntryWildcard origin finish star starMarker witness =>
        exact witness.consumed
    | importEntryNamed origin finish name nameProjects witness =>
        exact witness.consumed
    | importEntryAliased origin finish name alias asKw nameProjects
        aliasProjects witness => exact witness.consumed
}

def localExportEntrySpanFocus : RuleSpanFocus := {
  rule := .localExportEntry
  span := fun entry => entry.span
  nonnullable := by decide
  notModule := by decide
  consumed := by
    intro file tokens origin finish input output reduction
    cases reduction with
    | localExportEntryWildcard origin finish star starMarker witness =>
        exact witness.consumed
    | localExportEntryItem origin finish item witness =>
        exact witness.consumed
    | localExportEntryAllFrom origin finish reference dot star starMarker
        witness => exact witness.consumed
}

def remoteExportEntrySpanFocus : RuleSpanFocus := {
  rule := .remoteExportEntry
  span := fun entry => entry.span
  nonnullable := by decide
  notModule := by decide
  consumed := by
    intro file tokens origin finish input output reduction
    cases reduction with
    | remoteExportEntryWildcard origin finish star starMarker witness =>
        exact witness.consumed
    | remoteExportEntryItem origin finish item witness =>
        exact witness.consumed
}

@[simp] theorem EbnfValue.focusedSpans_ruleAtoms_self
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (values : List (RuleValue focus.rule)) :
    (values.map
      (EbnfValue.ruleAtom (file := file) (tokens := tokens) focus.rule)).flatMap
        (fun value => value.focusedSpans focus) =
      values.map focus.span := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [RuleSpanFocus.ruleSpans, inductionHypothesis]

@[simp] theorem EbnfValue.focusedSpans_optional_ruleAtom_of_ne
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus) (rule : GrammarRuleId)
    (different : rule ≠ focus.rule) (value : Option (RuleValue rule)) :
    (EbnfValue.optional (.atom (.nonterminal rule))
      (value.map (EbnfValue.ruleAtom
        (file := file) (tokens := tokens) rule))).focusedSpans focus = [] := by
  cases value <;> simp [RuleSpanFocus.ruleSpans, different]

@[simp] theorem importEntrySpanFocus_ruleAtoms
    {file : WorkspaceFile} {tokens : List Token}
    (values : List ImportSelectorEntry) :
    (values.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .importEntry)).flatMap
        (fun value => value.focusedSpans importEntrySpanFocus) =
      values.map (fun entry => entry.span) := by
  exact EbnfValue.focusedSpans_ruleAtoms_self importEntrySpanFocus values

@[simp] theorem localExportEntrySpanFocus_ruleAtoms
    {file : WorkspaceFile} {tokens : List Token}
    (values : List ExportEntry) :
    (values.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .localExportEntry)).flatMap
        (fun value => value.focusedSpans localExportEntrySpanFocus) =
      values.map (fun entry => entry.span) := by
  exact EbnfValue.focusedSpans_ruleAtoms_self localExportEntrySpanFocus values

@[simp] theorem remoteExportEntrySpanFocus_ruleAtoms
    {file : WorkspaceFile} {tokens : List Token}
    (values : List RemoteExportEntry) :
    (values.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .remoteExportEntry)).flatMap
        (fun value => value.focusedSpans remoteExportEntrySpanFocus) =
      values.map (fun entry => entry.span) := by
  exact EbnfValue.focusedSpans_ruleAtoms_self remoteExportEntrySpanFocus values

namespace RuleReduction

local syntax "focusedEvs![" term,* "]" : term

local macro "focusedEvs![" values:term,* "]" : term => do
  let mut result ← `(EbnfValues.nil)
  for value in values.getElems.reverse do
    result ← `(EbnfValues.cons _ _ $value $result)
  return result

local syntax "focusedSeq![" term "|" term,* "]" : term

local macro "focusedSeq![" children:term "|" values:term,* "]" : term =>
  `(EbnfValue.sequence $children focusedEvs![$values,*])

/-- Focused grammar-order spans visible in the exact EBNF input of a source
rule reduction. -/
abbrev inputFocusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    (focus : RuleSpanFocus)
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (_reduces : RuleReduction file tokens rule origin finish input output) :
    List SourceSpan :=
  input.focusedSpans focus

@[simp] theorem inputFocusedSpans_importDeclItems
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ImportSelectorEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (hidingValue : Option HidingClause)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    inputFocusedSpans importEntrySpanFocus
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness) =
      [importKw.span, dot.span, openBrace.span] ++
        entries.map (fun entry => entry.span) ++
        [closeBrace.span, semicolon.span] := by
  simp [inputFocusedSpans, importEntrySpanFocus,
    RuleSpanFocus.ruleSpans,
    EbnfValue.focusedSpans_optional_ruleAtom_of_ne]
  exact importEntrySpanFocus_ruleAtoms entries

@[simp] theorem inputFocusedSpans_exportDeclLocal
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    inputFocusedSpans localExportEntrySpanFocus
        (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
          closeBrace semicolon witness) =
      [exportKw.span, openBrace.span] ++
        entries.map (fun entry => entry.span) ++
        [closeBrace.span, semicolon.span] := by
  simp [inputFocusedSpans, localExportEntrySpanFocus]
  exact localExportEntrySpanFocus_ruleAtoms entries

@[simp] theorem inputFocusedSpans_exportDeclBraced
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List RemoteExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    inputFocusedSpans remoteExportEntrySpanFocus
        (RuleReduction.exportDeclBraced origin finish exportKw reference dot
          openBrace entries closeBrace semicolon witness) =
      [exportKw.span, dot.span, openBrace.span] ++
        entries.map (fun entry => entry.span) ++
          [closeBrace.span, semicolon.span] := by
  change RuleValue .moduleRef at reference
  change List (RuleValue .remoteExportEntry) at entries
  let branches : List EbnfExpr := [
    .sequence [
      .atom (.terminal (.hardKeyword .exportKw)),
      .atom (.terminal (.symbol .leftBrace)),
      .list0 (.atom (.nonterminal .localExportEntry)),
      .atom (.terminal (.symbol .rightBrace)),
      .atom (.terminal (.symbol .semicolon))],
    .sequence [
      .atom (.terminal (.hardKeyword .exportKw)),
      .atom (.nonterminal .moduleRef),
      .atom (.terminal (.symbol .semicolon))],
    .sequence [
      .atom (.terminal (.hardKeyword .exportKw)),
      .atom (.nonterminal .moduleRef),
      .atom (.terminal (.hardKeyword .asKw)),
      .atom (.terminal (.category .identifier)),
      .atom (.terminal (.symbol .semicolon))],
    .sequence [
      .atom (.terminal (.hardKeyword .exportKw)),
      .atom (.nonterminal .moduleRef),
      .atom (.terminal (.symbol .dot)),
      .atom (.terminal (.symbol .star)),
      .atom (.terminal (.symbol .semicolon))],
    .sequence [
      .atom (.terminal (.hardKeyword .exportKw)),
      .atom (.nonterminal .moduleRef),
      .atom (.terminal (.symbol .dot)),
      .atom (.terminal (.symbol .leftBrace)),
      .list0 (.atom (.nonterminal .remoteExportEntry)),
      .atom (.terminal (.symbol .rightBrace)),
      .atom (.terminal (.symbol .semicolon))]]
  let children : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.symbol .leftBrace)),
    .list0 (.atom (.nonterminal .remoteExportEntry)),
    .atom (.terminal (.symbol .rightBrace)),
    .atom (.terminal (.symbol .semicolon))]
  let sequenceValue : EbnfValue file tokens (.sequence children) :=
    focusedSeq![children |
      EbnfValue.terminalAtom _ exportKw,
      EbnfValue.ruleAtom _ reference,
      EbnfValue.terminalAtom _ dot,
      EbnfValue.terminalAtom _ openBrace,
      EbnfValue.list0 _
        (entries.map (EbnfValue.ruleAtom .remoteExportEntry)),
      EbnfValue.terminalAtom _ closeBrace,
      EbnfValue.terminalAtom _ semicolon]
  let branch : Fin branches.length := ⟨4, by decide⟩
  have branchShape : EbnfExpr.sequence children = branches.get branch := by
    rfl
  have rootShape : EbnfExpr.choice branches = m2cV1.rhs .exportDecl := by
    rfl
  have inputEq :
      inputValue
          (RuleReduction.exportDeclBraced origin finish exportKw reference dot
            openBrace entries closeBrace semicolon witness) =
        EbnfValue.transport rootShape
          (EbnfValue.choice branches
            ⟨branch, EbnfValue.transport branchShape sequenceValue⟩) := by
    rfl
  have focusedInputEq := congrArg
    (EbnfValue.focusedSpans remoteExportEntrySpanFocus) inputEq
  calc
    _ = (EbnfValue.transport rootShape
          (EbnfValue.choice branches
            ⟨branch, EbnfValue.transport branchShape sequenceValue⟩)).focusedSpans
            remoteExportEntrySpanFocus := focusedInputEq
    _ = (EbnfValue.choice branches
          ⟨branch, EbnfValue.transport branchShape sequenceValue⟩).focusedSpans
            remoteExportEntrySpanFocus :=
      EbnfValue.focusedSpans_transport remoteExportEntrySpanFocus rootShape _
    _ = (EbnfValue.transport branchShape sequenceValue).focusedSpans
          remoteExportEntrySpanFocus :=
      EbnfValue.focusedSpans_choice remoteExportEntrySpanFocus branches _
    _ = sequenceValue.focusedSpans remoteExportEntrySpanFocus :=
      EbnfValue.focusedSpans_transport remoteExportEntrySpanFocus branchShape _
    _ = _ := by
      rw [EbnfValue.focusedSpans_sequence]
      simp [children, remoteExportEntrySpanFocus,
        RuleSpanFocus.ruleSpans]
      exact remoteExportEntrySpanFocus_ruleAtoms entries

theorem importDeclItems_entriesContained_of_focusedSpanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ImportSelectorEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (evidence : FocusedSpanEvidence file tokens origin finish
      ([importKw.span, dot.span, openBrace.span] ++
        entries.map (fun entry => entry.span) ++
          [closeBrace.span, semicolon.span])) :
    (LocationFragment.merge
      (entries.map LocationFragment.ofImportSelectorEntry)).RootsContainedBy
        (RuleReduction.between file openBrace.span closeBrace.span ()).span := by
  have bracedEvidence := evidence.select
    (selected := openBrace.span ::
      entries.map (fun entry => entry.span) ++ [closeBrace.span]) (by simp)
  rw [LocationFragment.RootsContainedBy]
  have rootsEq :
      (LocationFragment.merge
        (entries.map LocationFragment.ofImportSelectorEntry)).roots =
          entries.map (fun entry => entry.span) := by
    clear evidence bracedEvidence
    rw [LocationFragment.merge_roots]
    induction entries with
    | nil => rfl
    | cons entry rest induction =>
        simp only [List.map_cons, List.flatMap_cons,
          LocationFragment.ofImportSelectorEntry_roots, induction,
          List.singleton_append]
  rw [rootsEq]
  intro span member
  exact bracedEvidence.between_contains_of_member tokensOrdered member

theorem exportDeclLocal_entriesContained_of_focusedSpanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (evidence : FocusedSpanEvidence file tokens origin finish
      ([exportKw.span, openBrace.span] ++
        entries.map (fun entry => entry.span) ++
          [closeBrace.span, semicolon.span])) :
    (LocationFragment.merge
      (entries.map LocationFragment.ofExportEntry)).RootsContainedBy
        (RuleReduction.between file openBrace.span closeBrace.span ()).span := by
  have bracedEvidence := evidence.select
    (selected := openBrace.span ::
      entries.map (fun entry => entry.span) ++ [closeBrace.span]) (by simp)
  rw [LocationFragment.RootsContainedBy]
  have rootsEq :
      (LocationFragment.merge
        (entries.map LocationFragment.ofExportEntry)).roots =
          entries.map (fun entry => entry.span) := by
    clear evidence bracedEvidence
    rw [LocationFragment.merge_roots]
    induction entries with
    | nil => rfl
    | cons entry rest induction =>
        simp only [List.map_cons, List.flatMap_cons,
          LocationFragment.ofExportEntry_roots, induction,
          List.singleton_append]
  rw [rootsEq]
  intro span member
  exact bracedEvidence.between_contains_of_member tokensOrdered member

theorem exportDeclBraced_entriesContained_of_focusedSpanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List RemoteExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (evidence : FocusedSpanEvidence file tokens origin finish
      ([exportKw.span, dot.span, openBrace.span] ++
        entries.map (fun entry => entry.span) ++
          [closeBrace.span, semicolon.span])) :
    (LocationFragment.merge
      (entries.map LocationFragment.ofRemoteExportEntry)).RootsContainedBy
        (RuleReduction.between file openBrace.span closeBrace.span ()).span := by
  have bracedEvidence := evidence.select
    (selected := openBrace.span ::
      entries.map (fun entry => entry.span) ++ [closeBrace.span]) (by simp)
  rw [LocationFragment.RootsContainedBy]
  have rootsEq :
      (LocationFragment.merge
        (entries.map LocationFragment.ofRemoteExportEntry)).roots =
          entries.map (fun entry => entry.span) := by
    clear evidence bracedEvidence
    rw [LocationFragment.merge_roots]
    induction entries with
    | nil => rfl
    | cons entry rest induction =>
        simp only [List.map_cons, List.flatMap_cons,
          LocationFragment.ofRemoteExportEntry_roots, induction,
          List.singleton_append]
  rw [rootsEq]
  intro span member
  exact bracedEvidence.between_contains_of_member tokensOrdered member

theorem importDeclItems_entriesContained_of_coherentRoot
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ImportSelectorEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (hidingValue : Option HidingClause)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish)
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalRootLocationItem tokens .importDecl origin finish context)}
    {complete : CompleteItem
      (CanonicalRootLocationItem tokens .importDecl origin finish context).raw}
    {coherent : CoherentPrefix file tokens memo correct final
      (CanonicalRootLocationItem tokens .importDecl origin finish context)
        priorValues}
    (inputEq : inputValue
      (RuleReduction.importDeclItems origin finish importKw reference dot
        openBrace entries closeBrace hidingValue semicolon witness) =
      RootAction.unpack .importDecl
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens .importDecl origin finish context)
          complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherent trace) :
    (LocationFragment.merge
      (entries.map LocationFragment.ofImportSelectorEntry)).RootsContainedBy
        (RuleReduction.between file openBrace.span closeBrace.span ()).span := by
  have focusedEvidence := carries.rootInputFocusedSpanEvidence
    importEntrySpanFocus inputEq
  change FocusedSpanEvidence file tokens origin finish
    (inputFocusedSpans importEntrySpanFocus
      (RuleReduction.importDeclItems origin finish importKw reference dot
        openBrace entries closeBrace hidingValue semicolon witness)) at focusedEvidence
  rw [inputFocusedSpans_importDeclItems] at focusedEvidence
  exact importDeclItems_entriesContained_of_focusedSpanEvidence tokensOrdered
    origin finish importKw dot openBrace entries closeBrace semicolon
      focusedEvidence

theorem exportDeclLocal_entriesContained_of_coherentRoot
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish)
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalRootLocationItem tokens .exportDecl origin finish context)}
    {complete : CompleteItem
      (CanonicalRootLocationItem tokens .exportDecl origin finish context).raw}
    {coherent : CoherentPrefix file tokens memo correct final
      (CanonicalRootLocationItem tokens .exportDecl origin finish context)
        priorValues}
    (inputEq : inputValue
      (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
        closeBrace semicolon witness) =
      RootAction.unpack .exportDecl
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens .exportDecl origin finish context)
          complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherent trace) :
    (LocationFragment.merge
      (entries.map LocationFragment.ofExportEntry)).RootsContainedBy
        (RuleReduction.between file openBrace.span closeBrace.span ()).span := by
  have focusedEvidence := carries.rootInputFocusedSpanEvidence
    localExportEntrySpanFocus inputEq
  change FocusedSpanEvidence file tokens origin finish
    (inputFocusedSpans localExportEntrySpanFocus
      (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
        closeBrace semicolon witness)) at focusedEvidence
  rw [inputFocusedSpans_exportDeclLocal] at focusedEvidence
  exact exportDeclLocal_entriesContained_of_focusedSpanEvidence tokensOrdered
    origin finish exportKw openBrace entries closeBrace semicolon
      focusedEvidence

theorem exportDeclBraced_entriesContained_of_coherentRoot
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List RemoteExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish)
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalRootLocationItem tokens .exportDecl origin finish context)}
    {complete : CompleteItem
      (CanonicalRootLocationItem tokens .exportDecl origin finish context).raw}
    {coherent : CoherentPrefix file tokens memo correct final
      (CanonicalRootLocationItem tokens .exportDecl origin finish context)
        priorValues}
    (inputEq : inputValue
      (RuleReduction.exportDeclBraced origin finish exportKw reference dot
        openBrace entries closeBrace semicolon witness) =
      RootAction.unpack .exportDecl
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens .exportDecl origin finish context)
          complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherent trace) :
    (LocationFragment.merge
      (entries.map LocationFragment.ofRemoteExportEntry)).RootsContainedBy
        (RuleReduction.between file openBrace.span closeBrace.span ()).span := by
  have focusedEvidence := carries.rootInputFocusedSpanEvidence
    remoteExportEntrySpanFocus inputEq
  change FocusedSpanEvidence file tokens origin finish
    (inputFocusedSpans remoteExportEntrySpanFocus
      (RuleReduction.exportDeclBraced origin finish exportKw reference dot
        openBrace entries closeBrace semicolon witness)) at focusedEvidence
  rw [inputFocusedSpans_exportDeclBraced] at focusedEvidence
  exact exportDeclBraced_entriesContained_of_focusedSpanEvidence tokensOrdered
    origin finish exportKw dot openBrace entries closeBrace semicolon
      focusedEvidence

/-- The semantic result index of a checked source-rule reduction. -/
abbrev outputValue
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (_reduces : RuleReduction file tokens rule origin finish input output) :
    RuleValue rule :=
  output

theorem importDeclItems_coherentRootLocationSound
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ImportSelectorEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (hidingValue : Option HidingClause)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish)
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalRootLocationItem tokens .importDecl origin finish context)}
    {complete : CompleteItem
      (CanonicalRootLocationItem tokens .importDecl origin finish context).raw}
    {coherent : CoherentPrefix file tokens memo correct final
      (CanonicalRootLocationItem tokens .importDecl origin finish context)
        priorValues}
    (inputEq : inputValue
      (RuleReduction.importDeclItems origin finish importKw reference dot
        openBrace entries closeBrace hidingValue semicolon witness) =
      RootAction.unpack .importDecl
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens .importDecl origin finish context)
          complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherent trace} :
    CoherentActionLocationSound complete coherent
      (ActionReduces.root .importDecl origin finish
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens .importDecl origin finish context)
          complete priorValues)
        (outputValue
          (RuleReduction.importDeclItems origin finish importKw reference dot
            openBrace entries closeBrace hidingValue semicolon witness))
        (inputEq ▸
          RuleReduction.importDeclItems origin finish importKw reference dot
            openBrace entries closeBrace hidingValue semicolon witness))
      trace carries := by
  have entriesContained :=
    importDeclItems_entriesContained_of_coherentRoot tokensOrdered origin finish
      importKw reference dot openBrace entries closeBrace hidingValue semicolon
        witness inputEq carries
  exact ImportDeclItemsLocationCase.coherentRootLocationSound tokensOrdered
    (RuleReduction.importDeclItems origin finish importKw reference dot
      openBrace entries closeBrace hidingValue semicolon witness)
    (.items origin finish importKw reference dot openBrace entries closeBrace
      hidingValue semicolon witness entriesContained)
    inputEq

theorem exportDeclLocal_coherentRootLocationSound
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List ExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish)
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalRootLocationItem tokens .exportDecl origin finish context)}
    {complete : CompleteItem
      (CanonicalRootLocationItem tokens .exportDecl origin finish context).raw}
    {coherent : CoherentPrefix file tokens memo correct final
      (CanonicalRootLocationItem tokens .exportDecl origin finish context)
        priorValues}
    (inputEq : inputValue
      (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
        closeBrace semicolon witness) =
      RootAction.unpack .exportDecl
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens .exportDecl origin finish context)
          complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherent trace} :
    CoherentActionLocationSound complete coherent
      (ActionReduces.root .exportDecl origin finish
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens .exportDecl origin finish context)
          complete priorValues)
        (outputValue
          (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
            closeBrace semicolon witness))
        (inputEq ▸
          RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
            closeBrace semicolon witness))
      trace carries := by
  have entriesContained :=
    exportDeclLocal_entriesContained_of_coherentRoot tokensOrdered origin finish
      exportKw openBrace entries closeBrace semicolon witness inputEq carries
  exact ExportDeclLocalLocationCase.coherentRootLocationSound tokensOrdered
    (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
      closeBrace semicolon witness)
    (.localCase origin finish exportKw openBrace entries closeBrace semicolon
      witness entriesContained)
    inputEq

theorem exportDeclBraced_coherentRootLocationSound
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
    (reference : ModuleReference)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (entries : List RemoteExportEntry)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish)
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalRootLocationItem tokens .exportDecl origin finish context)}
    {complete : CompleteItem
      (CanonicalRootLocationItem tokens .exportDecl origin finish context).raw}
    {coherent : CoherentPrefix file tokens memo correct final
      (CanonicalRootLocationItem tokens .exportDecl origin finish context)
        priorValues}
    (inputEq : inputValue
      (RuleReduction.exportDeclBraced origin finish exportKw reference dot
        openBrace entries closeBrace semicolon witness) =
      RootAction.unpack .exportDecl
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens .exportDecl origin finish context)
          complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherent trace} :
    CoherentActionLocationSound complete coherent
      (ActionReduces.root .exportDecl origin finish
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens .exportDecl origin finish context)
          complete priorValues)
        (outputValue
          (RuleReduction.exportDeclBraced origin finish exportKw reference dot
            openBrace entries closeBrace semicolon witness))
        (inputEq ▸
          RuleReduction.exportDeclBraced origin finish exportKw reference dot
            openBrace entries closeBrace semicolon witness))
      trace carries := by
  have entriesContained :=
    exportDeclBraced_entriesContained_of_coherentRoot tokensOrdered origin finish
      exportKw reference dot openBrace entries closeBrace semicolon witness
        inputEq carries
  exact ExportDeclBracedLocationCase.coherentRootLocationSound tokensOrdered
    (RuleReduction.exportDeclBraced origin finish exportKw reference dot
      openBrace entries closeBrace semicolon witness)
    (.braced origin finish exportKw reference dot openBrace entries closeBrace
      semicolon witness entriesContained)
    inputEq

end RuleReduction

end Solcore.Surface.Multi
