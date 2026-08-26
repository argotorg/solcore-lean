import Solcore.Surface.Multi.ExactTokenInterval
import Solcore.Surface.Multi.ExactTokenRulePlan

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- A grammar-rule-indexed token-plan projection. Failure records a semantic
value whose shape is not the output of the corresponding source reduction. -/
structure RuleTokenPlanLayout where
  plan? : (rule : GrammarRuleId) → RuleValue rule → Option TokenPlan

/-- Construct the source token plan retained by an EBNF value, or reject when
one of its source-rule children is rejected by the selected rule layout. -/
def TokenPlanFamily
    (layout : RuleTokenPlanLayout) (file : WorkspaceFile)
    (tokens : List Token) :
    (index : EbnfValueIndex) → EbnfFamily file tokens index →
      Option TokenPlan
  | .expression (.atom (.terminal terminal)), matched =>
      some (MatchedTerminal.physicalTokenPlan
        (Eq.mp (ebnfValue_atom_terminal_eq terminal) matched))
  | .expression (.atom (.nonterminal rule)), value =>
      layout.plan? rule
        (Eq.mp (ebnfValue_atom_nonterminal_eq rule) value)
  | .expression (.sequence children), values =>
      TokenPlanFamily layout file tokens (.expressions children)
        (Eq.mp (ebnfValue_sequence_eq children) values)
  | .expression (.group child), value =>
      TokenPlanFamily layout file tokens (.expression child)
        (Eq.mp (ebnfValue_group_eq child) value)
  | .expression (.choice branches), value =>
      let selected := Eq.mp (ebnfValue_choice_eq branches) value
      TokenPlanFamily layout file tokens
        (.expression (branches.get selected.1)) selected.2
  | .expression (.optional child), value =>
      match Eq.mp (ebnfValue_optional_eq child) value with
      | none => some .empty
      | some childValue =>
          TokenPlanFamily layout file tokens (.expression child) childValue
  | .expression (.star child), values => do
      let plans ← (Eq.mp (ebnfValue_star_eq child) values).mapM fun value =>
        TokenPlanFamily layout file tokens (.expression child) value
      pure (.concat plans)
  | .expression (.plus child), values => do
      let viewed := Eq.mp (ebnfValue_plus_eq child) values
      let headPlan ←
        TokenPlanFamily layout file tokens (.expression child) viewed.head
      let tailPlans ← viewed.tail.mapM fun value =>
        TokenPlanFamily layout file tokens (.expression child) value
      pure (.concat (headPlan :: tailPlans))
  | .expression (.list0 child), values => do
      let plans ← (Eq.mp (ebnfValue_list0_eq child) values).mapM fun value =>
        TokenPlanFamily layout file tokens (.expression child) value
      pure (.commaSeparated plans)
  | .expression (.list1 child), values => do
      let viewed := Eq.mp (ebnfValue_list1_eq child) values
      let headPlan ←
        TokenPlanFamily layout file tokens (.expression child) viewed.head
      let tailPlans ← viewed.tail.mapM fun value =>
        TokenPlanFamily layout file tokens (.expression child) value
      pure (.commaSeparated (headPlan :: tailPlans))
  | .expressions [], _ => some .empty
  | .expressions (child :: rest), values => do
      let viewed := Eq.mp (ebnfValues_cons_eq child rest) values
      let headPlan ←
        TokenPlanFamily layout file tokens (.expression child) viewed.1
      let tailPlan ←
        TokenPlanFamily layout file tokens (.expressions rest) viewed.2
      pure (.append headPlan tailPlan)
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

abbrev EbnfValue.tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) {expression : EbnfExpr}
    (value : EbnfValue file tokens expression) : Option TokenPlan :=
  TokenPlanFamily layout file tokens (.expression expression) value

abbrev EbnfValues.tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) {expressions : List EbnfExpr}
    (values : EbnfValues file tokens expressions) : Option TokenPlan :=
  TokenPlanFamily layout file tokens (.expressions expressions) values

@[simp] theorem EbnfValue.tokenPlan?_terminalAtom
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    (EbnfValue.terminalAtom terminal matched).tokenPlan? layout =
      some matched.physicalTokenPlan := by
  simp [EbnfValue.tokenPlan?, TokenPlanFamily,
    EbnfValue.terminalAtom, cast_cast]

@[simp] theorem EbnfValue.tokenPlan?_ruleAtom
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (rule : GrammarRuleId)
    (value : RuleValue rule) :
    (EbnfValue.ruleAtom (file := file) (tokens := tokens)
      rule value).tokenPlan? layout = layout.plan? rule value := by
  simp [EbnfValue.tokenPlan?, TokenPlanFamily,
    EbnfValue.ruleAtom, cast_cast]

@[simp] theorem EbnfValue.tokenPlan?_transport
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) {left right : EbnfExpr}
    (shape : left = right) (value : EbnfValue file tokens left) :
    (EbnfValue.transport shape value).tokenPlan? layout =
      value.tokenPlan? layout := by
  cases shape
  rfl

@[simp] theorem EbnfValue.tokenPlan?_atShape
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) {site : GrammarSite}
    {expression : EbnfExpr} (shape : site.expression = expression)
    (value : EbnfValue file tokens site.expression) :
    (EbnfValue.atShape shape value).tokenPlan? layout =
      value.tokenPlan? layout := by
  exact EbnfValue.tokenPlan?_transport layout shape value

@[simp] theorem EbnfValue.tokenPlan?_sequence
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (children : List EbnfExpr)
    (values : EbnfValues file tokens children) :
    (EbnfValue.sequence children values).tokenPlan? layout =
      values.tokenPlan? layout := by
  simp [EbnfValue.tokenPlan?, EbnfValues.tokenPlan?, TokenPlanFamily,
    EbnfValue.sequence, cast_cast]

@[simp] theorem EbnfValue.tokenPlan?_group
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr)
    (value : EbnfValue file tokens child) :
    (EbnfValue.group child value).tokenPlan? layout =
      value.tokenPlan? layout := by
  simp [EbnfValue.tokenPlan?, TokenPlanFamily,
    EbnfValue.group, cast_cast]

@[simp] theorem EbnfValue.tokenPlan?_optional_none
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr) :
    (EbnfValue.optional (file := file) (tokens := tokens)
      child none).tokenPlan? layout = some .empty := by
  simp [EbnfValue.tokenPlan?, TokenPlanFamily,
    EbnfValue.optional, cast_cast]

@[simp] theorem EbnfValue.tokenPlan?_optional_some
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr)
    (value : EbnfValue file tokens child) :
    (EbnfValue.optional child (some value)).tokenPlan? layout =
      value.tokenPlan? layout := by
  simp [EbnfValue.tokenPlan?, TokenPlanFamily,
    EbnfValue.optional, cast_cast]

@[simp] theorem EbnfValue.tokenPlan?_choice
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (branches : List EbnfExpr)
    (value : (branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch)) :
    (EbnfValue.choice branches value).tokenPlan? layout =
      value.2.tokenPlan? layout := by
  have viewed : Eq.mp (ebnfValue_choice_eq branches)
      (EbnfValue.choice branches value) = value := by
    unfold EbnfValue.choice
    change cast _ (cast _ value) = value
    rw [cast_cast]
    apply cast_eq
  unfold EbnfValue.tokenPlan?
  rw [TokenPlanFamily, viewed]

@[simp] theorem EbnfValue.tokenPlan?_star
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr)
    (values : List (EbnfValue file tokens child)) :
    (EbnfValue.star child values).tokenPlan? layout = (do
      let plans ← values.mapM fun value => value.tokenPlan? layout
      pure (.concat plans)) := by
  simp [EbnfValue.tokenPlan?, TokenPlanFamily,
    EbnfValue.star, cast_cast]

@[simp] theorem EbnfValue.tokenPlan?_plus
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr)
    (values : NonemptyList (EbnfValue file tokens child)) :
    (EbnfValue.plus child values).tokenPlan? layout = (do
      let headPlan ← values.head.tokenPlan? layout
      let tailPlans ← values.tail.mapM fun value => value.tokenPlan? layout
      pure (.concat (headPlan :: tailPlans))) := by
  simp [EbnfValue.tokenPlan?, TokenPlanFamily,
    EbnfValue.plus, cast_cast]

@[simp] theorem EbnfValue.tokenPlan?_list0
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr)
    (values : List (EbnfValue file tokens child)) :
    (EbnfValue.list0 child values).tokenPlan? layout = (do
      let plans ← values.mapM fun value => value.tokenPlan? layout
      pure (.commaSeparated plans)) := by
  simp [EbnfValue.tokenPlan?, TokenPlanFamily,
    EbnfValue.list0, cast_cast]

@[simp] theorem EbnfValue.tokenPlan?_list1
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr)
    (values : NonemptyList (EbnfValue file tokens child)) :
    (EbnfValue.list1 child values).tokenPlan? layout = (do
      let headPlan ← values.head.tokenPlan? layout
      let tailPlans ← values.tail.mapM fun value => value.tokenPlan? layout
      pure (.commaSeparated (headPlan :: tailPlans))) := by
  simp [EbnfValue.tokenPlan?, TokenPlanFamily,
    EbnfValue.list1, cast_cast]

@[simp] theorem EbnfValues.tokenPlan?_nil
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) :
    (EbnfValues.nil (file := file) (tokens := tokens)).tokenPlan? layout =
      some .empty := by
  simp [EbnfValues.tokenPlan?, TokenPlanFamily, EbnfValues.nil]

@[simp] theorem EbnfValues.tokenPlan?_cons
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr)
    (rest : List EbnfExpr) (head : EbnfValue file tokens child)
    (tail : EbnfValues file tokens rest) :
    (EbnfValues.cons child rest head tail).tokenPlan? layout = (do
      let headPlan ← head.tokenPlan? layout
      let tailPlan ← tail.tokenPlan? layout
      pure (.append headPlan tailPlan)) := by
  simp [EbnfValues.tokenPlan?, TokenPlanFamily,
    EbnfValues.cons, cast_cast]

@[simp] theorem EbnfValues.tokenPlan?_nil_raw
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout)
    (values : EbnfValues file tokens []) :
    values.tokenPlan? layout = some .empty := by
  unfold EbnfValues.tokenPlan?
  rw [TokenPlanFamily]

@[simp] theorem EbnfValues.tokenPlan?_cons_raw
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr)
    (rest : List EbnfExpr)
    (values : EbnfValues file tokens (child :: rest)) :
    values.tokenPlan? layout = (do
      let viewed := Eq.mp (ebnfValues_cons_eq child rest) values
      let headPlan ← viewed.1.tokenPlan? layout
      let tailPlan ← viewed.2.tokenPlan? layout
      pure (.append headPlan tailPlan)) := by
  unfold EbnfValues.tokenPlan?
  rw [TokenPlanFamily]

theorem EbnfValue.tokenPlan?_sequence_raw
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (children : List EbnfExpr)
    (value : EbnfValue file tokens (.sequence children)) :
    value.tokenPlan? layout =
      (Eq.mp (ebnfValue_sequence_eq children) value).tokenPlan? layout := by
  unfold EbnfValue.tokenPlan?
  rw [TokenPlanFamily]

@[simp] theorem EbnfValue.tokenPlan?_star_raw
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr)
    (value : EbnfValue file tokens (.star child)) :
    value.tokenPlan? layout = (do
      let plans ← (Eq.mp (ebnfValue_star_eq child) value).mapM
        fun element => element.tokenPlan? layout
      pure (.concat plans)) := by
  unfold EbnfValue.tokenPlan?
  rw [TokenPlanFamily]

@[simp] theorem EbnfValue.tokenPlan?_plus_raw
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr)
    (value : EbnfValue file tokens (.plus child)) :
    value.tokenPlan? layout = (do
      let elements := Eq.mp (ebnfValue_plus_eq child) value
      let headPlan ← elements.head.tokenPlan? layout
      let tailPlans ← elements.tail.mapM
        fun element => element.tokenPlan? layout
      pure (.concat (headPlan :: tailPlans))) := by
  unfold EbnfValue.tokenPlan?
  rw [TokenPlanFamily]

@[simp] theorem EbnfValue.tokenPlan?_list0_raw
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr)
    (value : EbnfValue file tokens (.list0 child)) :
    value.tokenPlan? layout = (do
      let plans ← (Eq.mp (ebnfValue_list0_eq child) value).mapM
        fun element => element.tokenPlan? layout
      pure (.commaSeparated plans)) := by
  unfold EbnfValue.tokenPlan?
  rw [TokenPlanFamily]

@[simp] theorem EbnfValue.tokenPlan?_list1_raw
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (child : EbnfExpr)
    (value : EbnfValue file tokens (.list1 child)) :
    value.tokenPlan? layout = (do
      let elements := Eq.mp (ebnfValue_list1_eq child) value
      let headPlan ← elements.head.tokenPlan? layout
      let tailPlans ← elements.tail.mapM
        fun element => element.tokenPlan? layout
      pure (.commaSeparated (headPlan :: tailPlans))) := by
  unfold EbnfValue.tokenPlan?
  rw [TokenPlanFamily]

theorem EbnfValue.mapM_tokenPlan?_transport_site
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) {left right : GrammarSite}
    (equality : left = right)
    (values : List (EbnfValue file tokens left.expression)) :
    (Eq.mp
        (congrArg
          (fun site : GrammarSite =>
            List (EbnfValue file tokens site.expression))
          equality)
        values).mapM (fun value => value.tokenPlan? layout) =
      values.mapM fun value => value.tokenPlan? layout := by
  cases equality
  rfl

namespace TokenPlan

@[simp] theorem empty_append (plan : TokenPlan) :
    TokenPlan.empty.append plan = plan := by
  cases plan
  rfl

@[simp] theorem append_empty (plan : TokenPlan) :
    plan.append TokenPlan.empty = plan := by
  cases plan
  simp [TokenPlan.append, TokenPlan.empty]

theorem append_assoc (first second third : TokenPlan) :
    (first.append second).append third =
      first.append (second.append third) := by
  cases first
  cases second
  cases third
  simp [TokenPlan.append, List.append_assoc]

@[simp] theorem concat_nil : TokenPlan.concat [] = .empty := by
  rfl

@[simp] theorem concat_cons (head : TokenPlan) (tail : List TokenPlan) :
    TokenPlan.concat (head :: tail) =
      head.append (TokenPlan.concat tail) := by
  cases head
  induction tail with
  | nil => simp [TokenPlan.concat, TokenPlan.append]
  | cons next rest induction =>
      simp [TokenPlan.concat, TokenPlan.append]

/-- The punctuation contributed by the parser's recursive tail nonterminal. -/
def commaTail (plans : List TokenPlan) : TokenPlan :=
  .concat (plans.map fun plan =>
    TokenPlan.append (TokenPlan.plain (.symbol .comma)) plan)

@[simp] theorem commaTail_nil : TokenPlan.commaTail [] = .empty := by
  rfl

@[simp] theorem commaTail_cons (head : TokenPlan) (tail : List TokenPlan) :
    TokenPlan.commaTail (head :: tail) =
      (TokenPlan.append (TokenPlan.plain (.symbol .comma)) head).append
        (TokenPlan.commaTail tail) := by
  simp [TokenPlan.commaTail]

@[simp] theorem commaSeparated_nil : TokenPlan.commaSeparated [] = .empty := by
  rfl

@[simp] theorem commaSeparated_cons
    (head : TokenPlan) (tail : List TokenPlan) :
    TokenPlan.commaSeparated (head :: tail) =
      head.append (TokenPlan.commaTail tail) := by
  rfl

end TokenPlan

/-- Construct the plan of one parser nonterminal value. Comma-tail values do
not contain their scanned punctuation, so a mandatory comma is restored before
every represented child. -/
def NonterminalValue.tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) :
    (symbol : NonterminalSymbol) → NonterminalValue file tokens symbol →
      Option TokenPlan
  | .rule rule, value => layout.plan? rule value
  | .aux _site, value => EbnfValue.tokenPlan? layout value
  | .tail _site, values => do
      let plans ← values.mapM fun value =>
        EbnfValue.tokenPlan? layout value
      pure (.commaTail plans)

/-- Construct the plan of one terminal or nonterminal grammar symbol. -/
def GrammarSymbolValue.tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) :
    (symbol : GrammarSymbol) → GrammarSymbolValue file tokens symbol →
      Option TokenPlan
  | .terminal _terminal, matched =>
      some matched.physicalTokenPlan
  | .nonterminal symbol, value =>
      NonterminalValue.tokenPlan? layout symbol value

/-- Construct the concatenated plan of a heterogeneous grammar RHS tuple. -/
def GrammarSymbolValues.tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) :
    (symbols : List GrammarSymbol) →
      GrammarSymbolValues file tokens symbols → Option TokenPlan
  | [], _values => some .empty
  | symbol :: rest, values => do
      let headPlan ← GrammarSymbolValue.tokenPlan? layout symbol values.1
      let tailPlan ← GrammarSymbolValues.tokenPlan? layout rest values.2
      pure (.append headPlan tailPlan)

@[simp] theorem NonterminalValue.tokenPlan?_rule
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (rule : GrammarRuleId)
    (value : RuleValue rule) :
    NonterminalValue.tokenPlan? (file := file) (tokens := tokens)
        layout (.rule rule) value =
      layout.plan? rule value := by
  rfl

@[simp] theorem NonterminalValue.tokenPlan?_aux
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : GrammarSite)
    (value : EbnfValue file tokens site.expression) :
    NonterminalValue.tokenPlan? layout (.aux site) value =
      EbnfValue.tokenPlan? layout value := by
  rfl

@[simp] theorem NonterminalValue.tokenPlan?_tail
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (site : ListSite)
    (values : List (EbnfValue file tokens site.element.expression)) :
    NonterminalValue.tokenPlan? layout (.tail site) values = (do
      let plans ← values.mapM fun value =>
        EbnfValue.tokenPlan? layout value
      pure (.commaTail plans)) := by
  rfl

@[simp] theorem GrammarSymbolValue.tokenPlan?_terminal
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    GrammarSymbolValue.tokenPlan? layout (.terminal terminal) matched =
      some matched.physicalTokenPlan := by
  rfl

@[simp] theorem GrammarSymbolValue.tokenPlan?_nonterminal
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (symbol : NonterminalSymbol)
    (value : NonterminalValue file tokens symbol) :
    GrammarSymbolValue.tokenPlan? layout (.nonterminal symbol) value =
      NonterminalValue.tokenPlan? layout symbol value := by
  rfl

@[simp] theorem GrammarSymbolValue.tokenPlan?_transport
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) {left right : GrammarSymbol}
    (shape : left = right) (value : GrammarSymbolValue file tokens left) :
    GrammarSymbolValue.tokenPlan? layout right
        (Eq.mp (congrArg (GrammarSymbolValue file tokens) shape) value) =
      GrammarSymbolValue.tokenPlan? layout left value := by
  cases shape
  rfl

@[simp] theorem GrammarSymbolValues.append_nil
    {file : WorkspaceFile} {tokens : List Token}
    {right : List GrammarSymbol}
    (leftValues : GrammarSymbolValues file tokens [])
    (rightValues : GrammarSymbolValues file tokens right) :
    GrammarSymbolValues.append leftValues rightValues = rightValues := by
  cases leftValues
  rfl

@[simp] theorem GrammarSymbolValues.append_cons
    {file : WorkspaceFile} {tokens : List Token}
    (symbol : GrammarSymbol) (rest right : List GrammarSymbol)
    (head : GrammarSymbolValue file tokens symbol)
    (tail : GrammarSymbolValues file tokens rest)
    (rightValues : GrammarSymbolValues file tokens right) :
    GrammarSymbolValues.append (left := symbol :: rest)
        (right := right) (head, tail) rightValues =
      (head, GrammarSymbolValues.append tail rightValues) := by
  rfl

@[simp] theorem GrammarSymbolValues.tokenPlan?_nil
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout)
    (values : GrammarSymbolValues file tokens []) :
    GrammarSymbolValues.tokenPlan? layout [] values = some .empty := by
  cases values
  rfl

@[simp] theorem GrammarSymbolValues.tokenPlan?_cons
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (symbol : GrammarSymbol)
    (rest : List GrammarSymbol)
    (head : GrammarSymbolValue file tokens symbol)
    (tail : GrammarSymbolValues file tokens rest) :
    GrammarSymbolValues.tokenPlan? layout (symbol :: rest) (head, tail) =
      (do
        let headPlan ← GrammarSymbolValue.tokenPlan? layout symbol head
        let tailPlan ← GrammarSymbolValues.tokenPlan? layout rest tail
        pure (TokenPlan.append headPlan tailPlan)) := by
  rfl

@[simp] theorem GrammarSymbolValues.tokenPlan?_transport
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) {left right : List GrammarSymbol}
    (shape : left = right) (values : GrammarSymbolValues file tokens left) :
    GrammarSymbolValues.tokenPlan? layout right
        (GrammarSymbolValues.transport shape values) =
      GrammarSymbolValues.tokenPlan? layout left values := by
  cases shape
  rfl

@[simp] theorem GrammarSymbolValues.tokenPlan?_singleton
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (symbol : GrammarSymbol)
    (value : GrammarSymbolValue file tokens symbol) :
    GrammarSymbolValues.tokenPlan? layout [symbol] (value, ()) =
      GrammarSymbolValue.tokenPlan? layout symbol value := by
  simp [GrammarSymbolValues.tokenPlan?]

@[simp] theorem GrammarSymbolValues.tokenPlan?_view
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) {production : ProductionId}
    {canonicalRhs : List GrammarSymbol}
    (shape : production.rhs = canonicalRhs)
    (values : GrammarSymbolValues file tokens production.rhs) :
    GrammarSymbolValues.tokenPlan? layout canonicalRhs
        (GrammarSymbolValues.view shape values) =
      GrammarSymbolValues.tokenPlan? layout production.rhs values := by
  unfold GrammarSymbolValues.view
  exact GrammarSymbolValues.tokenPlan?_transport layout shape values

@[simp] theorem GrammarSymbolValues.tokenPlan?_append
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) {left right : List GrammarSymbol}
    (leftValues : GrammarSymbolValues file tokens left)
    (rightValues : GrammarSymbolValues file tokens right) :
    GrammarSymbolValues.tokenPlan? layout (left ++ right)
        (GrammarSymbolValues.append leftValues rightValues) = (do
      let leftPlan ←
        GrammarSymbolValues.tokenPlan? layout left leftValues
      let rightPlan ←
        GrammarSymbolValues.tokenPlan? layout right rightValues
      pure (.append leftPlan rightPlan)) := by
  induction left with
  | nil =>
      rw [GrammarSymbolValues.append_nil]
      simp
  | cons symbol rest inductionHypothesis =>
      rcases leftValues with ⟨head, tail⟩
      rw [GrammarSymbolValues.append_cons]
      change (do
        let headPlan ← GrammarSymbolValue.tokenPlan? layout symbol head
        let tailPlan ← GrammarSymbolValues.tokenPlan? layout
          (rest ++ right) (GrammarSymbolValues.append tail rightValues)
        pure (TokenPlan.append headPlan tailPlan)) = (do
          let leftPlan ← GrammarSymbolValues.tokenPlan? layout
            (symbol :: rest) (head, tail)
          let rightPlan ←
            GrammarSymbolValues.tokenPlan? layout right rightValues
          pure (TokenPlan.append leftPlan rightPlan))
      rw [GrammarSymbolValues.tokenPlan?_cons]
      rw [inductionHypothesis tail]
      generalize headEq :
        GrammarSymbolValue.tokenPlan? layout symbol head = headPlan?
      cases headPlan? with
      | none => simp
      | some headPlan =>
          generalize tailEq :
            GrammarSymbolValues.tokenPlan? layout rest tail = tailPlan?
          cases tailPlan? with
          | none => simp
          | some tailPlan =>
              generalize rightEq :
                GrammarSymbolValues.tokenPlan? layout right rightValues =
                  rightPlan?
              cases rightPlan? with
              | none => simp
              | some rightPlan =>
                  simp [TokenPlan.append_assoc]

@[simp] theorem EbnfValues.tokenPlan?_ofAuxiliaries
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (sites : List GrammarSite)
    (values : GrammarSymbolValues file tokens
      (sites.map fun site => GrammarSymbol.nonterminal (.aux site))) :
    (EbnfValues.ofAuxiliaries sites values).tokenPlan? layout =
      GrammarSymbolValues.tokenPlan? layout
        (sites.map fun site => GrammarSymbol.nonterminal (.aux site))
        values := by
  induction sites with
  | nil =>
      simp only [List.map] at values ⊢
      cases values
      rw [EbnfValues.tokenPlan?_nil_raw]
      rfl
  | cons site rest inductionHypothesis =>
      simp only [List.map] at values ⊢
      rcases values with ⟨head, tail⟩
      rw [EbnfValues.tokenPlan?_cons_raw]
      rw [EbnfValues.ofAuxiliaries_cons_eq]
      change (do
        let headPlan ← EbnfValue.tokenPlan? layout head
        let tailPlan ← EbnfValues.tokenPlan? layout
          (EbnfValues.ofAuxiliaries rest tail)
        pure (TokenPlan.append headPlan tailPlan)) = _
      rw [inductionHypothesis]
      rfl

@[simp] theorem RootAction.unpack_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (rule : GrammarRuleId)
    (values : GrammarSymbolValues file tokens
      (ProductionId.root rule).rhs) :
    (RootAction.unpack rule values).tokenPlan? layout =
      GrammarSymbolValues.tokenPlan? layout
        (ProductionId.root rule).rhs values := by
  rw [RootAction.unpack_eq]
  rw [EbnfValue.tokenPlan?_atShape]
  let viewed := GrammarSymbolValues.view
    (ProductionId.rhs_root rule) values
  calc
    _ = GrammarSymbolValues.tokenPlan? layout
          [.nonterminal (.aux (GrammarSite.root rule))] viewed := by
        exact (GrammarSymbolValues.tokenPlan?_singleton layout
          (.nonterminal (.aux (GrammarSite.root rule))) viewed.1).symm
    _ = GrammarSymbolValues.tokenPlan? layout
          (ProductionId.root rule).rhs values :=
        GrammarSymbolValues.tokenPlan?_view layout
          (ProductionId.rhs_root rule) values

/-- Token plan of the semantic values accumulated before a contextual item. -/
abbrev PrefixValues.tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (item : ContextualItemKey tokens)
    (values : PrefixValues file tokens item) : Option TokenPlan :=
  GrammarSymbolValues.tokenPlan? layout
    (item.raw.production.rhs.take item.raw.dot.val) values

@[simp] theorem PrefixValues.tokenPlan?_zeroValue
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (item : ContextualItemKey tokens)
    (zero : item.raw.dot.val = 0) :
    PrefixValues.tokenPlan? layout item
      (PrefixValues.zeroValue (file := file) item zero) = some .empty := by
  unfold PrefixValues.tokenPlan? PrefixValues.zeroValue
  rw [GrammarSymbolValues.tokenPlan?_transport]
  rfl

@[simp] theorem PrefixValues.tokenPlan?_scanValue
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout)
    (before after : ContextualItemKey tokens)
    (terminal : TerminalSymbol)
    (next : NextSymbol before.raw (.terminal terminal))
    (matched : MatchedTerminal file tokens terminal)
    (advance : AdvanceItem before.raw matched.cursor.afterBoundary after.raw)
    (priorValues : PrefixValues file tokens before) :
    PrefixValues.tokenPlan? layout after
        (PrefixValues.scanValue before after terminal next matched advance
          priorValues) = (do
      let priorPlan ← PrefixValues.tokenPlan? layout before priorValues
      pure (.append priorPlan matched.physicalTokenPlan)) := by
  unfold PrefixValues.tokenPlan? PrefixValues.scanValue
  rw [GrammarSymbolValues.tokenPlan?_transport]
  rw [GrammarSymbolValues.tokenPlan?_append]
  simp

@[simp] theorem PrefixValues.tokenPlan?_completeValue
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout)
    (waiting finished after : ContextualItemKey tokens)
    (next : NextSymbol waiting.raw
      (.nonterminal finished.raw.production.lhs))
    (advance : AdvanceItem waiting.raw finished.raw.current after.raw)
    (priorValues : PrefixValues file tokens waiting)
    (childValue : NonterminalValue file tokens
      finished.raw.production.lhs) :
    PrefixValues.tokenPlan? layout after
        (PrefixValues.completeValue waiting finished after next advance
          priorValues childValue) = (do
      let priorPlan ← PrefixValues.tokenPlan? layout waiting priorValues
      let childPlan ← NonterminalValue.tokenPlan? layout
        finished.raw.production.lhs childValue
      pure (.append priorPlan childPlan)) := by
  unfold PrefixValues.tokenPlan? PrefixValues.completeValue
  rw [GrammarSymbolValues.tokenPlan?_transport]
  rw [GrammarSymbolValues.tokenPlan?_append]
  simp

@[simp] theorem PrefixValues.tokenPlan?_fullValue
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (item : ContextualItemKey tokens)
    (complete : CompleteItem item.raw)
    (priorValues : PrefixValues file tokens item) :
    GrammarSymbolValues.tokenPlan? layout item.raw.production.rhs
        (PrefixValues.fullValue item complete priorValues) =
      PrefixValues.tokenPlan? layout item priorValues := by
  unfold PrefixValues.tokenPlan? PrefixValues.fullValue
  rw [GrammarSymbolValues.tokenPlan?_transport]

/-- The concrete source-rule visitor as a grammar layout. -/
def sourceRuleTokenPlanLayout : RuleTokenPlanLayout where
  plan? := ruleTokenPlan?

end Solcore.Surface.Multi
