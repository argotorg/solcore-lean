import Solcore.Surface.Multi.NonAssociativePassThroughSafety
namespace Solcore.Surface.Multi
open Grammar Solcore.Workspace
private def NATF (value : Expression) : Prop :=
  (∀ first, ¬ CompletedNonAssociativeValue .relational value first) ∧ ∀ first, ¬ CompletedNonAssociativeValue .equality value first
private def ETF (value : Expression) : Prop := ∀ first, ¬ CompletedNonAssociativeValue .equality value first
private def RSafe : (rule : GrammarRuleId) → RuleValue rule → Prop
  | .relational, value => ETF value
  | .bitOr, value | .bitXor, value | .bitAnd, value | .additive, value | .multiplicative, value
  | .prefix, value | .postfix, value | .atom, value | .lambda, value => NATF value
  | _, _ => True
private def EFam (file : WorkspaceFile) (tokens : List Token) :
    (index : EbnfValueIndex) → EbnfFamily file tokens index → Prop
  | .expression (.atom (.terminal _)), _ => True
  | .expression (.atom (.nonterminal rule)), value => RSafe rule (Eq.mp (ebnfValue_atom_nonterminal_eq rule) value)
  | .expression (.sequence children), value => EFam file tokens (.expressions children) (Eq.mp (ebnfValue_sequence_eq children) value)
  | .expression (.choice branches), value =>
      let viewed := Eq.mp (ebnfValue_choice_eq branches) value
      EFam file tokens (.expression (branches.get viewed.1)) viewed.2
  | .expression (.group _), _ | .expression (.optional _), _ | .expression (.star _), _
  | .expression (.plus _), _ | .expression (.list0 _), _ | .expression (.list1 _), _ => True
  | .expressions [], _ => True
  | .expressions (child :: rest), value =>
      let viewed := Eq.mp (ebnfValues_cons_eq child rest) value
      EFam file tokens (.expression child) viewed.1
termination_by index => index.measure
decreasing_by
  · exact measure_sequence_lt _
  · exact measure_choice_get_lt _ _
  · exact measure_cons_head_lt _ _
private abbrev ESafe (file : WorkspaceFile) (tokens : List Token) (expression : EbnfExpr)
    (value : EbnfValue file tokens expression) := EFam file tokens (.expression expression) value
private abbrev EVSafe (file : WorkspaceFile) (tokens : List Token) (expressions : List EbnfExpr)
    (values : EbnfValues file tokens expressions) := EFam file tokens (.expressions expressions) values
private def NTSafe (file : WorkspaceFile) (tokens : List Token) :
    (symbol : NonterminalSymbol) → NonterminalValue file tokens symbol → Prop
  | .rule rule, value => RSafe rule value
  | .aux site, value => ESafe file tokens site.expression value
  | .tail _, _ => True
private def GSafe (file : WorkspaceFile) (tokens : List Token) :
    (symbol : GrammarSymbol) → GrammarSymbolValue file tokens symbol → Prop
  | .terminal _, _ => True
  | .nonterminal symbol, value => NTSafe file tokens symbol value
private def SSafe (file : WorkspaceFile) (tokens : List Token) :
    (symbols : List GrammarSymbol) → GrammarSymbolValues file tokens symbols → Prop
  | [], _ => True
  | symbol :: _, values => GSafe file tokens symbol values.1
private theorem symbolTransportSelf {file : WorkspaceFile} {tokens : List Token} {symbol : GrammarSymbol}
    (e : symbol = symbol) (value : GrammarSymbolValue file tokens symbol) :
    Eq.mp (congrArg (GrammarSymbolValue file tokens) e) value = value := by
  have : e = rfl := Subsingleton.elim _ _; rw [this]; rfl
private theorem ssTransport {file : WorkspaceFile} {tokens : List Token} {left right : GrammarSymbol}
    (e : left = right) (value : GrammarSymbolValue file tokens left) (safe : GSafe file tokens left value) :
    GSafe file tokens right (Eq.mp (congrArg (GrammarSymbolValue file tokens) e) value) := by
  cases e
  simpa only [symbolTransportSelf] using safe
private theorem sTransport {file : WorkspaceFile} {tokens : List Token} {left right : List GrammarSymbol}
    (e : left = right) (values : GrammarSymbolValues file tokens left) (safe : SSafe file tokens left values) :
    SSafe file tokens right (GrammarSymbolValues.transport e values) := by
  subst right
  rw [GrammarSymbolValues.transport_self]
  exact safe
private theorem sAppend {file : WorkspaceFile} {tokens : List Token} : ∀ {left right : List GrammarSymbol}
    (lv : GrammarSymbolValues file tokens left) (rv : GrammarSymbolValues file tokens right),
    SSafe file tokens left lv → SSafe file tokens right rv → SSafe file tokens (left ++ right) (GrammarSymbolValues.append lv rv)
  | [], _, _, _, _, rs => rs
  | _ :: _, _, _, _, ls, _ => ls
private theorem eTransport {file : WorkspaceFile} {tokens : List Token} {left right : EbnfExpr}
    (e : left = right) (value : EbnfValue file tokens left) (safe : ESafe file tokens left value) :
    ESafe file tokens right (EbnfValue.transport e value) := by
  subst right
  rw [EbnfValue.transport_self]
  exact safe
private theorem eTransportIff {file : WorkspaceFile} {tokens : List Token} {left right : EbnfExpr}
    (e : left = right) (value : EbnfValue file tokens left) : ESafe file tokens right (EbnfValue.transport e value) ↔ ESafe file tokens left value := by
  subst right
  rw [EbnfValue.transport_self]
private theorem eRule {file : WorkspaceFile} {tokens : List Token} (rule : GrammarRuleId) (value : RuleValue rule) :
    ESafe file tokens (.atom (.nonterminal rule)) (EbnfValue.ruleAtom rule value) ↔ RSafe rule value := by
  simp [ESafe, EFam, EbnfValue.ruleAtom, cast_cast]
private theorem eSeq {file : WorkspaceFile} {tokens : List Token} (children : List EbnfExpr) (values : EbnfValues file tokens children) :
    ESafe file tokens (.sequence children) (EbnfValue.sequence children values) ↔ EVSafe file tokens children values := by
  simp [ESafe, EFam, EbnfValue.sequence, cast_cast]
private theorem eChoice {file : WorkspaceFile} {tokens : List Token} (branches : List EbnfExpr) (branch : Fin branches.length)
    (value : EbnfValue file tokens (branches.get branch)) :
    ESafe file tokens (.choice branches) (EbnfValue.choice branches ⟨branch, value⟩) ↔ ESafe file tokens (branches.get branch) value := by
  let packed : (branch : Fin branches.length) × EbnfValue file tokens (branches.get branch) := ⟨branch, value⟩
  have viewEq : Eq.mp (ebnfValue_choice_eq branches) (EbnfValue.choice branches packed) = packed := by
    change cast _ (cast _ packed) = packed
    rw [cast_cast]
    apply cast_eq
  simp only [ESafe, EFam]
  rw [viewEq]
private theorem evCons {file : WorkspaceFile} {tokens : List Token} (child : EbnfExpr) (rest : List EbnfExpr)
    (head : EbnfValue file tokens child) (tail : EbnfValues file tokens rest) :
    EVSafe file tokens (child :: rest) (EbnfValues.cons child rest head tail) ↔ ESafe file tokens child head := by
  simp [ESafe, EVSafe, EFam, EbnfValues.cons, cast_cast]
private theorem eHead {file : WorkspaceFile} {tokens : List Token} (child : EbnfExpr) (rest : List EbnfExpr)
    (head : EbnfValue file tokens child) (tail : EbnfValues file tokens rest)
    (safe : ESafe file tokens (.sequence (child :: rest)) (EbnfValue.sequence _ (EbnfValues.cons child rest head tail))) : ESafe file tokens child head :=
  (evCons child rest head tail).mp ((eSeq _ _).mp safe)
private theorem eFirst {file : WorkspaceFile} {tokens : List Token} (first second : EbnfExpr)
    (input : EbnfValue file tokens (.sequence [first, second])) (safe : ESafe file tokens _ input) :
    ESafe file tokens first (EbnfValue.sequence2View first second input).1 := by
  rw [← EbnfValue.sequence2_of_view first second input] at safe
  exact eHead _ _ _ _ safe
private theorem eView {file : WorkspaceFile} {tokens : List Token} (rule : GrammarRuleId)
    (input : EbnfValue file tokens (.atom (.nonterminal rule))) (safe : ESafe file tokens _ input) :
    RSafe rule (EbnfValue.ruleView rule input) := by
  rw [← EbnfValue.rule_of_view rule input] at safe
  exact (eRule _ _).mp safe
private theorem evAux {file : WorkspaceFile} {tokens : List Token} : ∀ (sites : List GrammarSite)
    (values : GrammarSymbolValues file tokens (sites.map fun site => .nonterminal (.aux site))),
    SSafe file tokens _ values → EVSafe file tokens (sites.map GrammarSite.expression) (EbnfValues.ofAuxiliaries sites values)
  | [], _, _ => by simp [EVSafe, EFam]
  | site :: rest, (head, tail), safe => by
      simp only [List.map_cons] at safe ⊢
      simp only [SSafe] at safe
      simp only [EFam]
      rw [EbnfValues.ofAuxiliaries_cons_eq]
      exact safe
private def OpSafe (operator : Located InfixOperator) : Prop :=
  operator.payload ∉ [.less, .greater, .lessEqual, .greaterEqual] ∧ operator.payload ∉ [.equal, .notEqual]
private theorem infixSafe (operator : Located InfixOperator) (left right : Expression) (safe : OpSafe operator) :
    NATF { span := left.span, payload := .infix operator left right } := by
  constructor <;> intro first completed
  · rcases completed with ⟨_, _, payload, member⟩; cases payload; exact safe.1 member
  · rcases completed with ⟨_, _, payload, member⟩; cases payload; exact safe.2 member
private theorem foldSafe (file : WorkspaceFile) (left : Expression) (rest : List (Located InfixOperator × Expression))
    (leftSafe : NATF left) (restSafe : ∀ pair, pair ∈ rest → OpSafe pair.1) : NATF (RuleReduction.foldInfixLeft file left rest) := by
  induction rest generalizing left with
  | nil => simpa [RuleReduction.foldInfixLeft] using leftSafe
  | cons head tail ih =>
      apply ih
      · exact infixSafe head.1 left head.2 (restSafe head (by simp))
      · intro pair member
        exact restSafe pair (by simp [member])
private theorem postfixSafe (file : WorkspaceFile) (receiver : Expression) (parts : List PostfixPartValue) (safe : NATF receiver) :
    NATF (RuleReduction.foldPostfix file receiver parts) := by
  induction parts generalizing receiver with
  | nil => simpa [RuleReduction.foldPostfix] using safe
  | cons part rest ih =>
      apply ih
      cases part <;> simp [NATF, CompletedNonAssociativeValue, RuleReduction.between]
private theorem reduceSafe {file : WorkspaceFile} {tokens : List Token} {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)} {output : RuleValue rule}
    (reduces : RuleReduction file tokens rule origin finish input output) (safe : ESafe file tokens (m2cV1.rhs rule) input) : RSafe rule output := by
  cases reduces
  case relationalNone =>
    change ETF _
    exact ((eRule _ _).mp (eHead _ _ _ _ safe)).2
  case bitOr rest | bitXor rest | bitAnd rest =>
    change NATF _
    apply foldSafe _ _ _ ((eRule _ _).mp (eHead _ _ _ _ safe))
    intro pair member
    simp only [List.mem_map] at member
    rcases member with ⟨source, _, rfl⟩
    simp [OpSafe, RuleReduction.infixOperator, RuleReduction.terminalLoc]
  case additive rest =>
    change NATF _
    apply foldSafe _ _ _ ((eRule _ _).mp (eHead _ _ _ _ safe))
    intro pair member
    simp only [List.mem_map] at member
    rcases member with ⟨source, _, rfl⟩
    cases source.1 <;> simp [OpSafe, RuleReduction.infixOperator, RuleReduction.terminalLoc]
  case multiplicative rest =>
    change NATF _
    apply foldSafe _ _ _ ((eRule _ _).mp (eHead _ _ _ _ safe))
    intro pair member
    simp only [List.mem_map] at member
    rcases member with ⟨source, _, rfl⟩
    rcases source.1 with left | right
    · simp [OpSafe, RuleReduction.infixOperator, RuleReduction.terminalLoc]
    · cases right <;> simp [OpSafe, RuleReduction.infixOperator, RuleReduction.terminalLoc]
  case prefixPostfix =>
    change NATF _
    have selected := (eChoice _ _ _).mp safe
    change ESafe _ _ (.atom (.nonterminal .postfix)) (EbnfValue.ruleAtom .postfix _) at selected
    exact (eRule _ _).mp selected
  case «postfix» =>
    change NATF _
    exact postfixSafe _ _ _ ((eRule _ _).mp (eHead _ _ _ _ safe))
  case atomLambda =>
    change NATF _
    have selected := (eChoice _ _ _).mp safe
    change ESafe _ _ (.atom (.nonterminal .lambda)) (EbnfValue.ruleAtom .lambda _) at selected
    exact (eRule _ _).mp selected
  all_goals simp [RSafe, NATF, ETF, CompletedNonAssociativeValue, sourceLoc,
    RuleReduction.infixOperator, RuleReduction.terminalLoc]
private theorem actionSafe {file : WorkspaceFile} {tokens : List Token} {action : ActionId} {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens action.production.rhs} {output : NonterminalValue file tokens action.production.lhs}
    (reduces : ActionReduces file tokens action origin finish input output) (safe : SSafe file tokens action.production.rhs input) :
    NTSafe file tokens action.production.lhs output := by
  cases reduces
  case root rule input output reduces =>
    have canonical := sTransport (ProductionId.rhs_root rule) input safe
    exact reduceSafe reduces (eTransport (GrammarSite.root_expression rule) (GrammarSymbolValues.view (ProductionId.rhs_root rule) input).1 canonical)
  case atom site input =>
    change ESafe file tokens site.site.expression (AtomSite.pack site input)
    exact match atomEq : site.atom with
      | .terminal terminal => by
        apply (eTransportIff (site.expression_eq_atom.trans (congrArg EbnfExpr.atom atomEq)) (AtomSite.pack site input)).mp
        rw [← EbnfValue.transport_trans]
        change ESafe file tokens (.atom (.terminal terminal)) (AtomSite.packAtAtom site (.terminal terminal) atomEq input)
        rw [AtomSite.pack_terminal_eq]
        simp [ESafe, EFam]
      | .nonterminal rule => by
        apply (eTransportIff (site.expression_eq_atom.trans (congrArg EbnfExpr.atom atomEq)) (AtomSite.pack site input)).mp
        rw [← EbnfValue.transport_trans]
        change ESafe file tokens (.atom (.nonterminal rule)) (AtomSite.packAtAtom site (.nonterminal rule) atomEq input)
        rw [AtomSite.pack_rule_eq]
        apply (eRule _ _).mpr
        have viewedSafe := sTransport (ProductionId.rhs_atom site) input safe
        exact ssTransport (congrArg EbnfAtom.grammarSymbol atomEq) _ (ssTransport site.symbol_eq _ viewedSafe)
  case seq site input =>
    change ESafe file tokens site.site.expression (SequenceSite.pack site input)
    apply (eTransportIff site.expression_eq_sequence (SequenceSite.pack site input)).mp
    change ESafe file tokens (.sequence (site.children.map GrammarSite.expression)) (EbnfValue.atShape site.expression_eq_sequence (SequenceSite.pack site input))
    rw [SequenceSite.pack_eq]
    apply (eSeq _ _).mpr
    exact evAux site.children _ (sTransport (ProductionId.rhs_seq site) input safe)
  case choice site branch input =>
    change ESafe file tokens site.site.expression (ChoiceSite.pack site branch input)
    apply (eTransportIff site.expression_eq_choice (ChoiceSite.pack site branch input)).mp
    change ESafe file tokens (.choice site.branchExpressions.toList) (EbnfValue.atShape site.expression_eq_choice (ChoiceSite.pack site branch input))
    rw [ChoiceSite.pack_eq]
    apply (eChoice _ _ _).mpr
    exact eTransport ((site.branch_expression branch).trans (site.branch_get_toList branch).symm) _
      (sTransport (ProductionId.rhs_choice site branch) input safe)
  case group site input =>
    change ESafe file tokens site.site.expression (GroupSite.pack site input)
    apply (eTransportIff site.expression_eq_group (GroupSite.pack site input)).mp
    simp [ESafe, EFam]
  case opt site branch input =>
    change ESafe file tokens site.site.expression (OptionalSite.pack site branch input)
    apply (eTransportIff site.expression_eq_optional (OptionalSite.pack site branch input)).mp
    simp [ESafe, EFam]
  case star site branch input =>
    change ESafe file tokens site.site.expression (StarSite.pack site branch input)
    apply (eTransportIff site.expression_eq_star (StarSite.pack site branch input)).mp
    simp [ESafe, EFam]
  case plus site branch input =>
    change ESafe file tokens site.site.expression (PlusSite.pack site branch input)
    apply (eTransportIff site.expression_eq_plus (PlusSite.pack site branch input)).mp
    simp [ESafe, EFam]
  case list0 site branch input =>
    change ESafe file tokens site.site.expression (List0Site.pack site branch input)
    apply (eTransportIff site.expression_eq_list0 (List0Site.pack site branch input)).mp
    simp [ESafe, EFam]
  case list1 site input =>
    change ESafe file tokens site.site.expression (List1Site.pack site input)
    apply (eTransportIff site.expression_eq_list1 (List1Site.pack site input)).mp
    simp [ESafe, EFam]
  case tail => trivial
private theorem coherentSafe {file : WorkspaceFile} {tokens : List Token} {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo} {final : AllGuardsFinal memo} {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item} (coherent : CoherentPrefix file tokens memo correct final item values) :
    SSafe file tokens (item.raw.production.rhs.take item.raw.dot.val) values := by
  apply CoherentPrefix.rec (memo := memo) (correct := correct) (final := final)
    (motive_1 := fun item values _ => SSafe file tokens (item.raw.production.rhs.take item.raw.dot.val) values)
    (motive_2 := fun item value _ => NTSafe file tokens item.raw.production.lhs value) (t := coherent)
  case zero =>
    intro item reached zero
    exact sTransport (prefix_zero_layout item.raw zero) () trivial
  case scan =>
    intro before after cursor priorValues witness edge prior priorIH
    exact sTransport (prefix_scan_layout before.raw after.raw witness.terminal witness.matched.cursor.afterBoundary witness.next witness.advance)
      (GrammarSymbolValues.append priorValues (witness.matched, ()))
      (sAppend (left := before.raw.production.rhs.take before.raw.dot.val) (right := [.terminal witness.terminal])
        priorValues (witness.matched, ()) priorIH trivial)
  case complete =>
    intro waiting finished after shared priorValues childValue witness edge prior child priorIH childIH
    exact sTransport (prefix_complete_layout waiting.raw finished.raw after.raw witness.next witness.advance)
      (GrammarSymbolValues.append priorValues (childValue, ()))
      (sAppend (left := waiting.raw.production.rhs.take waiting.raw.dot.val) (right := [.nonterminal finished.raw.production.lhs])
        priorValues (childValue, ()) priorIH childIH)
  case reduce =>
    intro item priorValues output reached complete coherent action prefixIH
    exact actionSafe action (sTransport (prefix_full_layout item.raw complete) priorValues prefixIH)
/-- Canonical coherent nonassociative inputs satisfy pass-through safety. -/
theorem coherentNonAssociativePassThroughSafe {file : WorkspaceFile} {tokens : List Token} {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo} {final : AllGuardsFinal memo} :
    CoherentNonAssociativePassThroughSafe file tokens memo correct final := by
  intro level origin finish context priorValues complete coherent
  have fullSafe := sTransport (prefix_full_layout (CanonicalCompleteRootItem tokens level.rule origin finish context).raw complete)
    priorValues (coherentSafe coherent)
  have rootSafe := sTransport (ProductionId.rhs_root level.rule)
    (PrefixValues.fullValue (CanonicalCompleteRootItem tokens level.rule origin finish context) complete priorValues) fullSafe
  have inputSafe := eTransport (GrammarSite.root_expression level.rule)
    (GrammarSymbolValues.view (ProductionId.rhs_root level.rule)
      (PrefixValues.fullValue (CanonicalCompleteRootItem tokens level.rule origin finish context) complete priorValues)).1 rootSafe
  cases level
  · intro _ first completed
    exact (eView .bitOr _ (eFirst (.atom (.nonterminal .bitOr)) (.optional NonAssociativeLevel.relational.tailExpr) _ inputSafe)).1 first completed
  · intro _ first completed
    exact eView .relational _ (eFirst (.atom (.nonterminal .relational)) (.optional NonAssociativeLevel.equality.tailExpr) _ inputSafe) first completed
end Solcore.Surface.Multi
