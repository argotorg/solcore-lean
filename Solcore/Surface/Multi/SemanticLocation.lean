import Solcore.Surface.Multi.RuleLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- The physical location contributed by a matched terminal.  Logical end of
input has no physical source location. -/
def MatchedTerminal.locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal) : LocationFragment :=
  if terminal = .endOfFile then .empty else .raw matched.span

/-- Collect the semantic locations retained by one EBNF value or heterogeneous
sequence of values. -/
def EbnfLocationFamily
    (file : WorkspaceFile) (tokens : List Token) :
    (index : EbnfValueIndex) →
      EbnfFamily file tokens index → LocationFragment
  | .expression (.atom (.terminal terminal)), matched =>
      (Eq.mp (ebnfValue_atom_terminal_eq terminal) matched).locationFragment
  | .expression (.atom (.nonterminal rule)), value =>
      RuleLocationView.ofRuleValue rule
        (Eq.mp (ebnfValue_atom_nonterminal_eq rule) value)
  | .expression (.sequence children), values =>
      EbnfLocationFamily file tokens (.expressions children)
        (Eq.mp (ebnfValue_sequence_eq children) values)
  | .expression (.group child), value =>
      EbnfLocationFamily file tokens (.expression child)
        (Eq.mp (ebnfValue_group_eq child) value)
  | .expression (.choice branches), value =>
      let selected := Eq.mp (ebnfValue_choice_eq branches) value
      EbnfLocationFamily file tokens
        (.expression (branches.get selected.1)) selected.2
  | .expression (.optional child), value =>
      match Eq.mp (ebnfValue_optional_eq child) value with
      | none => .empty
      | some childValue =>
          EbnfLocationFamily file tokens (.expression child) childValue
  | .expression (.star child), values =>
      .merge ((Eq.mp (ebnfValue_star_eq child) values).map fun value =>
        EbnfLocationFamily file tokens (.expression child) value)
  | .expression (.plus child), values =>
      let viewed := Eq.mp (ebnfValue_plus_eq child) values
      .merge
        (EbnfLocationFamily file tokens (.expression child) viewed.head ::
          viewed.tail.map fun value =>
            EbnfLocationFamily file tokens (.expression child) value)
  | .expression (.list0 child), values =>
      .merge ((Eq.mp (ebnfValue_list0_eq child) values).map fun value =>
        EbnfLocationFamily file tokens (.expression child) value)
  | .expression (.list1 child), values =>
      let viewed := Eq.mp (ebnfValue_list1_eq child) values
      .merge
        (EbnfLocationFamily file tokens (.expression child) viewed.head ::
          viewed.tail.map fun value =>
            EbnfLocationFamily file tokens (.expression child) value)
  | .expressions [], _ => .empty
  | .expressions (child :: rest), values =>
      let viewed := Eq.mp (ebnfValues_cons_eq child rest) values
      .merge [
        EbnfLocationFamily file tokens (.expression child) viewed.1,
        EbnfLocationFamily file tokens (.expressions rest) viewed.2]
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

/-- The semantic location fragment of one checked EBNF expression value. -/
abbrev EbnfValue.locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr}
    (value : EbnfValue file tokens expression) : LocationFragment :=
  EbnfLocationFamily file tokens (.expression expression) value

/-- The semantic location fragment of one checked heterogeneous EBNF tuple. -/
abbrev EbnfValues.locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    {expressions : List EbnfExpr}
    (values : EbnfValues file tokens expressions) : LocationFragment :=
  EbnfLocationFamily file tokens (.expressions expressions) values

@[simp] theorem EbnfValue.locationFragment_transport
    {file : WorkspaceFile} {tokens : List Token}
    {left right : EbnfExpr}
    (equality : left = right)
    (value : EbnfValue file tokens left) :
    (EbnfValue.transport equality value).locationFragment =
      value.locationFragment := by
  cases equality
  rfl

@[simp] theorem EbnfValue.locationFragment_atShape
    {file : WorkspaceFile} {tokens : List Token}
    {site : GrammarSite} {expression : EbnfExpr}
    (shape : site.expression = expression)
    (value : EbnfValue file tokens site.expression) :
    (EbnfValue.atShape shape value).locationFragment =
      value.locationFragment :=
  EbnfValue.locationFragment_transport shape value

@[simp] theorem EbnfValue.locationFragment_ofShape
    {file : WorkspaceFile} {tokens : List Token}
    {site : GrammarSite} {expression : EbnfExpr}
    (shape : site.expression = expression)
    (value : EbnfValue file tokens expression) :
    (EbnfValue.ofShape shape value).locationFragment =
      value.locationFragment :=
  EbnfValue.locationFragment_transport shape.symm value

@[simp] theorem EbnfValue.locationFragment_terminalAtom
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    (EbnfValue.terminalAtom terminal matched).locationFragment =
      matched.locationFragment := by
  simp [EbnfValue.locationFragment, EbnfLocationFamily,
    EbnfValue.terminalAtom, cast_cast]

@[simp] theorem EbnfValue.locationFragment_ruleAtom
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (value : RuleValue rule) :
    (EbnfValue.ruleAtom (file := file) (tokens := tokens)
      rule value).locationFragment =
      RuleLocationView.ofRuleValue rule value := by
  simp [EbnfValue.locationFragment, EbnfLocationFamily,
    EbnfValue.ruleAtom, cast_cast]

@[simp] theorem EbnfValue.locationFragment_sequence
    {file : WorkspaceFile} {tokens : List Token}
    (children : List EbnfExpr)
    (values : EbnfValues file tokens children) :
    (EbnfValue.sequence children values).locationFragment =
      values.locationFragment := by
  simp [EbnfValue.locationFragment, EbnfValues.locationFragment,
    EbnfLocationFamily, EbnfValue.sequence, cast_cast]

@[simp] theorem EbnfValue.locationFragment_group
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (value : EbnfValue file tokens child) :
    (EbnfValue.group child value).locationFragment =
      value.locationFragment := by
  simp [EbnfValue.locationFragment, EbnfLocationFamily,
    EbnfValue.group, cast_cast]

@[simp] theorem EbnfValue.locationFragment_choice
    {file : WorkspaceFile} {tokens : List Token}
    (branches : List EbnfExpr)
    (value : (branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch)) :
    (EbnfValue.choice branches value).locationFragment =
      value.2.locationFragment := by
  have viewed : Eq.mp (ebnfValue_choice_eq branches)
      (EbnfValue.choice branches value) = value := by
    unfold EbnfValue.choice
    change cast _ (cast _ value) = value
    rw [cast_cast]
    apply cast_eq
  unfold EbnfValue.locationFragment
  rw [EbnfLocationFamily, viewed]

@[simp] theorem EbnfValue.locationFragment_optional_none
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) :
    (EbnfValue.optional (file := file) (tokens := tokens)
      child none).locationFragment = LocationFragment.empty := by
  simp [EbnfValue.locationFragment, EbnfLocationFamily,
    EbnfValue.optional, cast_cast]

@[simp] theorem EbnfValue.locationFragment_optional_some
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) (value : EbnfValue file tokens child) :
    (EbnfValue.optional child (some value)).locationFragment =
      value.locationFragment := by
  simp [EbnfValue.locationFragment, EbnfLocationFamily,
    EbnfValue.optional, cast_cast]

@[simp] theorem EbnfValue.locationFragment_star
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) (values : List (EbnfValue file tokens child)) :
    (EbnfValue.star child values).locationFragment =
      LocationFragment.merge
        (values.map fun value => value.locationFragment) := by
  simp [EbnfValue.locationFragment, EbnfLocationFamily,
    EbnfValue.star, cast_cast]

@[simp] theorem EbnfValue.locationFragment_plus
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (values : NonemptyList (EbnfValue file tokens child)) :
    (EbnfValue.plus child values).locationFragment =
      LocationFragment.merge
        (values.head.locationFragment ::
          values.tail.map fun value => value.locationFragment) := by
  simp [EbnfValue.locationFragment, EbnfLocationFamily,
    EbnfValue.plus, cast_cast]

@[simp] theorem EbnfValue.locationFragment_list0
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) (values : List (EbnfValue file tokens child)) :
    (EbnfValue.list0 child values).locationFragment =
      LocationFragment.merge
        (values.map fun value => value.locationFragment) := by
  simp [EbnfValue.locationFragment, EbnfLocationFamily,
    EbnfValue.list0, cast_cast]

@[simp] theorem EbnfValue.locationFragment_list1
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (values : NonemptyList (EbnfValue file tokens child)) :
    (EbnfValue.list1 child values).locationFragment =
      LocationFragment.merge
        (values.head.locationFragment ::
          values.tail.map fun value => value.locationFragment) := by
  simp [EbnfValue.locationFragment, EbnfLocationFamily,
    EbnfValue.list1, cast_cast]

@[simp] theorem EbnfValues.locationFragment_nil
    {file : WorkspaceFile} {tokens : List Token} :
    (EbnfValues.nil (file := file) (tokens := tokens)).locationFragment =
      LocationFragment.empty := by
  simp [EbnfValues.locationFragment, EbnfLocationFamily, EbnfValues.nil]

@[simp] theorem EbnfValues.locationFragment_cons
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) (rest : List EbnfExpr)
    (head : EbnfValue file tokens child)
    (tail : EbnfValues file tokens rest) :
    (EbnfValues.cons child rest head tail).locationFragment =
      LocationFragment.merge [head.locationFragment, tail.locationFragment] := by
  simp [EbnfValues.locationFragment, EbnfLocationFamily, EbnfValues.cons,
    cast_cast]

@[simp] theorem EbnfValues.locationFragment_nil_raw
    {file : WorkspaceFile} {tokens : List Token}
    (values : EbnfValues file tokens []) :
    values.locationFragment = LocationFragment.empty := by
  unfold EbnfValues.locationFragment
  rw [EbnfLocationFamily]

@[simp] theorem EbnfValues.locationFragment_cons_raw
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) (rest : List EbnfExpr)
    (values : EbnfValues file tokens (child :: rest)) :
    values.locationFragment = LocationFragment.merge [
      (Eq.mp (ebnfValues_cons_eq child rest) values).1.locationFragment,
      (Eq.mp (ebnfValues_cons_eq child rest) values).2.locationFragment] := by
  unfold EbnfValues.locationFragment
  rw [EbnfLocationFamily]

/-- The semantic location fragment carried by one completed nonterminal. -/
def NonterminalValue.locationFragment
    {file : WorkspaceFile} {tokens : List Token} :
    (symbol : NonterminalSymbol) →
      NonterminalValue file tokens symbol → LocationFragment
  | .rule rule, value => RuleLocationView.ofRuleValue rule value
  | .aux _site, value => EbnfValue.locationFragment value
  | .tail _site, values =>
      .merge (values.map fun value => EbnfValue.locationFragment value)

@[simp] theorem NonterminalValue.locationFragment_rule
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) (value : RuleValue rule) :
    NonterminalValue.locationFragment (file := file) (tokens := tokens)
        (.rule rule) value =
      RuleLocationView.ofRuleValue rule value := by
  rfl

@[simp] theorem NonterminalValue.locationFragment_aux
    {file : WorkspaceFile} {tokens : List Token}
    (site : GrammarSite)
    (value : EbnfValue file tokens site.expression) :
    NonterminalValue.locationFragment (.aux site) value =
      value.locationFragment := by
  rfl

@[simp] theorem NonterminalValue.locationFragment_tail
    {file : WorkspaceFile} {tokens : List Token}
    (site : ListSite)
    (values : List (EbnfValue file tokens site.element.expression)) :
    NonterminalValue.locationFragment (.tail site) values =
      LocationFragment.merge
        (values.map fun value => value.locationFragment) := by
  rfl

/-- The semantic location fragment carried by one grammar-symbol value. -/
def GrammarSymbolValue.locationFragment
    {file : WorkspaceFile} {tokens : List Token} :
    (symbol : GrammarSymbol) →
      GrammarSymbolValue file tokens symbol → LocationFragment
  | .terminal terminal, matched =>
      let viewed : MatchedTerminal file tokens terminal :=
        Eq.mp (by rfl) matched
      MatchedTerminal.locationFragment viewed
  | .nonterminal symbol, value =>
      let viewed : NonterminalValue file tokens symbol :=
        Eq.mp (by rfl) value
      NonterminalValue.locationFragment symbol viewed

@[simp] theorem GrammarSymbolValue.locationFragment_terminal
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    GrammarSymbolValue.locationFragment (.terminal terminal) matched =
      matched.locationFragment := by
  rfl

@[simp] theorem GrammarSymbolValue.locationFragment_nonterminal
    {file : WorkspaceFile} {tokens : List Token}
    (symbol : NonterminalSymbol)
    (value : NonterminalValue file tokens symbol) :
    GrammarSymbolValue.locationFragment (.nonterminal symbol) value =
      NonterminalValue.locationFragment symbol value := by
  rfl

@[simp] theorem GrammarSymbolValue.locationFragment_transport
    {file : WorkspaceFile} {tokens : List Token}
    {left right : GrammarSymbol}
    (equality : left = right)
    (value : GrammarSymbolValue file tokens left) :
    GrammarSymbolValue.locationFragment right
        (Eq.mp (congrArg (GrammarSymbolValue file tokens) equality) value) =
      GrammarSymbolValue.locationFragment left value := by
  cases equality
  rfl

/-- Merge semantic locations in the grammar order of a symbol tuple. -/
def GrammarSymbolValues.locationFragment
    {file : WorkspaceFile} {tokens : List Token} :
    (symbols : List GrammarSymbol) →
      GrammarSymbolValues file tokens symbols → LocationFragment
  | [], _ => .empty
  | symbol :: rest, values =>
      .merge [
        GrammarSymbolValue.locationFragment symbol values.1,
        GrammarSymbolValues.locationFragment rest values.2]

namespace LocationFragment

/-- Location fragments are equal when all three observable lists agree. -/
theorem eq_of_fields
    {left right : LocationFragment}
    (roots : left.roots = right.roots)
    (spans : left.inventory.spans = right.inventory.spans)
    (containments : left.inventory.containments =
      right.inventory.containments) :
    left = right := by
  cases left with
  | mk leftRoots leftInventory =>
      cases right with
      | mk rightRoots rightInventory =>
          cases leftInventory
          cases rightInventory
          simp only at roots spans containments
          subst_vars
          rfl

@[simp] theorem merge_empty_left (fragment : LocationFragment) :
    merge [empty, fragment] = fragment := by
  apply eq_of_fields <;> simp

@[simp] theorem merge_empty_right (fragment : LocationFragment) :
    merge [fragment, empty] = fragment := by
  apply eq_of_fields <;> simp

@[simp] theorem merge_two_assoc
    (first second third : LocationFragment) :
    merge [first, merge [second, third]] =
      merge [merge [first, second], third] := by
  apply eq_of_fields <;> simp [List.append_assoc]

@[simp] theorem empty_validFor (file : WorkspaceFile) :
    empty.ValidFor file := by
  simp [ValidFor, LocationInventory.ValidFor]

@[simp] theorem empty_nested : empty.Nested := by
  simp [Nested, LocationInventory.Nested]

/-- Merging source-valid sibling fragments preserves source validity. -/
theorem merge_validFor
    {file : WorkspaceFile} {fragments : List LocationFragment}
    (valid : ∀ fragment ∈ fragments, fragment.ValidFor file) :
    (merge fragments).ValidFor file := by
  intro span member
  rw [merge_spans, List.mem_flatMap] at member
  rcases member with ⟨fragment, fragmentMember, spanMember⟩
  exact valid fragment fragmentMember span spanMember

/-- Merging nested sibling fragments preserves all of their containment
edges. -/
theorem merge_nested
    {fragments : List LocationFragment}
    (nested : ∀ fragment ∈ fragments, fragment.Nested) :
    (merge fragments).Nested := by
  intro containment member
  rw [merge_containments, List.mem_flatMap] at member
  rcases member with ⟨fragment, fragmentMember, containmentMember⟩
  exact nested fragment fragmentMember containment containmentMember

/-- Every member of a source-valid merge is itself source-valid. -/
theorem validFor_of_mem_merge
    {file : WorkspaceFile} {fragments : List LocationFragment}
    {fragment : LocationFragment}
    (member : fragment ∈ fragments)
    (valid : (merge fragments).ValidFor file) :
    fragment.ValidFor file := by
  intro span spanMember
  apply valid span
  rw [merge_spans, List.mem_flatMap]
  exact ⟨fragment, member, spanMember⟩

/-- Every member of a nested merge retains its own nesting invariant. -/
theorem nested_of_mem_merge
    {fragments : List LocationFragment}
    {fragment : LocationFragment}
    (member : fragment ∈ fragments)
    (nested : (merge fragments).Nested) :
    fragment.Nested := by
  intro containment containmentMember
  apply nested containment
  rw [merge_containments, List.mem_flatMap]
  exact ⟨fragment, member, containmentMember⟩

end LocationFragment

@[simp] theorem GrammarSymbolValues.locationFragment_singleton
    {file : WorkspaceFile} {tokens : List Token}
    (symbol : GrammarSymbol)
    (value : GrammarSymbolValue file tokens symbol) :
    GrammarSymbolValues.locationFragment [symbol] (value, ()) =
      GrammarSymbolValue.locationFragment symbol value := by
  change LocationFragment.merge [
    GrammarSymbolValue.locationFragment symbol value,
    LocationFragment.empty] = _
  simp

@[simp] theorem GrammarSymbolValues.locationFragment_append
    {file : WorkspaceFile} {tokens : List Token}
    {left right : List GrammarSymbol}
    (leftValues : GrammarSymbolValues file tokens left)
    (rightValues : GrammarSymbolValues file tokens right) :
    GrammarSymbolValues.locationFragment (left ++ right)
        (GrammarSymbolValues.append leftValues rightValues) =
      LocationFragment.merge [
        GrammarSymbolValues.locationFragment left leftValues,
        GrammarSymbolValues.locationFragment right rightValues] := by
  induction left with
  | nil =>
      cases leftValues
      exact LocationFragment.merge_empty_left _ |>.symm
  | cons symbol rest inductionHypothesis =>
      change LocationFragment.merge [
          GrammarSymbolValue.locationFragment symbol leftValues.1,
          GrammarSymbolValues.locationFragment (rest ++ right)
            (GrammarSymbolValues.append leftValues.2 rightValues)] = _
      rw [inductionHypothesis leftValues.2]
      exact LocationFragment.merge_two_assoc _ _ _

@[simp] theorem GrammarSymbolValues.locationFragment_transport
    {file : WorkspaceFile} {tokens : List Token}
    {left right : List GrammarSymbol}
    (equality : left = right)
    (values : GrammarSymbolValues file tokens left) :
    GrammarSymbolValues.locationFragment right
        (GrammarSymbolValues.transport equality values) =
      GrammarSymbolValues.locationFragment left values := by
  cases equality
  rfl

@[simp] theorem GrammarSymbolValues.locationFragment_view
    {file : WorkspaceFile} {tokens : List Token}
    {production : ProductionId} {canonicalRhs : List GrammarSymbol}
    (layout : production.rhs = canonicalRhs)
    (values : GrammarSymbolValues file tokens production.rhs) :
    GrammarSymbolValues.locationFragment canonicalRhs
        (GrammarSymbolValues.view layout values) =
      GrammarSymbolValues.locationFragment production.rhs values := by
  unfold GrammarSymbolValues.view
  rw [GrammarSymbolValues.locationFragment_transport]

/-- The semantic location fragment carried by an item's consumed prefix. -/
abbrev PrefixValues.locationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (item : ContextualItemKey tokens)
    (values : PrefixValues file tokens item) : LocationFragment :=
  GrammarSymbolValues.locationFragment
    (item.raw.production.rhs.take item.raw.dot.val) values

@[simp] theorem PrefixValues.locationFragment_zeroValue
    {file : WorkspaceFile} {tokens : List Token}
    (item : ContextualItemKey tokens)
    (zero : item.raw.dot.val = 0) :
    PrefixValues.locationFragment item
        (PrefixValues.zeroValue (file := file) item zero) =
      LocationFragment.empty := by
  unfold PrefixValues.locationFragment PrefixValues.zeroValue
  rw [GrammarSymbolValues.locationFragment_transport]
  rfl

@[simp] theorem PrefixValues.locationFragment_scanValue
    {file : WorkspaceFile} {tokens : List Token}
    (before after : ContextualItemKey tokens)
    (terminal : TerminalSymbol)
    (next : NextSymbol before.raw (.terminal terminal))
    (matched : MatchedTerminal file tokens terminal)
    (advance : AdvanceItem before.raw matched.cursor.afterBoundary after.raw)
    (prior : PrefixValues file tokens before) :
    PrefixValues.locationFragment after
        (PrefixValues.scanValue before after terminal next matched advance prior) =
      LocationFragment.merge [
        PrefixValues.locationFragment before prior,
        matched.locationFragment] := by
  unfold PrefixValues.locationFragment PrefixValues.scanValue
  rw [GrammarSymbolValues.locationFragment_transport]
  rw [GrammarSymbolValues.locationFragment_append]
  simp

@[simp] theorem PrefixValues.locationFragment_completeValue
    {file : WorkspaceFile} {tokens : List Token}
    (waiting finished after : ContextualItemKey tokens)
    (next : NextSymbol waiting.raw
      (.nonterminal finished.raw.production.lhs))
    (advance : AdvanceItem waiting.raw finished.raw.current after.raw)
    (prior : PrefixValues file tokens waiting)
    (child : NonterminalValue file tokens finished.raw.production.lhs) :
    PrefixValues.locationFragment after
        (PrefixValues.completeValue waiting finished after next advance
          prior child) =
      LocationFragment.merge [
        PrefixValues.locationFragment waiting prior,
        NonterminalValue.locationFragment
          finished.raw.production.lhs child] := by
  unfold PrefixValues.locationFragment PrefixValues.completeValue
  rw [GrammarSymbolValues.locationFragment_transport]
  rw [GrammarSymbolValues.locationFragment_append]
  simp

@[simp] theorem PrefixValues.locationFragment_fullValue
    {file : WorkspaceFile} {tokens : List Token}
    (item : ContextualItemKey tokens)
    (complete : CompleteItem item.raw)
    (prior : PrefixValues file tokens item) :
    GrammarSymbolValues.locationFragment item.raw.production.rhs
        (PrefixValues.fullValue item complete prior) =
      PrefixValues.locationFragment item prior := by
  unfold PrefixValues.locationFragment PrefixValues.fullValue
  rw [GrammarSymbolValues.locationFragment_transport]

end Solcore.Surface.Multi
