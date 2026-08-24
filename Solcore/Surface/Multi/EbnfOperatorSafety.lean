import Solcore.Surface.Multi.EbnfDelimiterSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar

/-- Whether one displayed grammar terminal is an operator forbidden at the
selected nonassociative operand level. -/
def grammarForbiddenTerminal :
    NonAssociativeLevel → TerminalSymbol → Bool
  | .relational, .symbol .less => true
  | .relational, .symbol .greater => true
  | .relational, .symbol .lessEqual => true
  | .relational, .symbol .greaterEqual => true
  | .equality, .symbol .equalEqual => true
  | .equality, .symbol .notEqual => true
  | _, _ => false

/-- Closed set of source rules allowed at base delimiter depth. -/
def grammarOperatorSafeRule :
    NonAssociativeLevel → GrammarRuleId → Bool
  | .equality, .relational => true
  | _, .bitOr => true
  | _, .bitXor => true
  | _, .bitAnd => true
  | _, .additive => true
  | _, .multiplicative => true
  | _, .prefix => true
  | _, .postfix => true
  | _, .postfixPart => true
  | _, .atom => true
  | _, .lambda => true
  | _, .literal => true
  | _, .body => true
  | _, .type => true
  | _, .typeAtom => true
  | _, .qualifiedName => true
  | _, _ => false

private theorem operator_measure_choice_lt (branches : List EbnfExpr) :
    EbnfValueIndex.measure (.expressions branches) <
      EbnfValueIndex.measure (.expression (.choice branches)) := by
  simp [EbnfValueIndex.measure, ebnfSize]
  omega

mutual

/-- Execute one EBNF delimiter skeleton while rejecting forbidden terminals
at base depth and checking only an explicitly closed source-rule set there. -/
def grammarOperatorEffect? :
    NonAssociativeLevel → EbnfExpr → DelimiterStack → Option DelimiterStack
  | level, .atom (.terminal terminal), before =>
      if terminal = .endOfFile then
        none
      else if before = [] ∧
          grammarForbiddenTerminal level terminal = true then
          none
        else
          grammarTerminalDelimiterStep? before terminal
  | level, .atom (.nonterminal rule), before =>
      if rule = .module then
        none
      else if before = [] then
        if grammarOperatorSafeRule level rule then some before else none
      else
        some before
  | level, .sequence children, before =>
      grammarOperatorEffects? level children before
  | level, .group child, before => grammarOperatorEffect? level child before
  | level, .choice branches, before =>
      grammarOperatorChoicesEffect? level branches before
  | level, .optional child, before
  | level, .star child, before
  | level, .plus child, before
  | level, .list0 child, before
  | level, .list1 child, before =>
      match grammarOperatorEffect? level child before with
      | some after => if after = before then some before else none
      | none => none
termination_by _level expression =>
  EbnfValueIndex.measure (.expression expression)
decreasing_by
  · exact measure_sequence_lt _
  · exact measure_unary_child_lt .group _
  · exact operator_measure_choice_lt _
  · exact measure_unary_child_lt .optional _
  · exact measure_unary_child_lt .star _
  · exact measure_unary_child_lt .plus _
  · exact measure_unary_child_lt .list0 _
  · exact measure_unary_child_lt .list1 _

def grammarOperatorEffects? :
    NonAssociativeLevel → List EbnfExpr → DelimiterStack →
      Option DelimiterStack
  | _, [], before => some before
  | level, child :: rest, before =>
      match grammarOperatorEffect? level child before with
      | some middle => grammarOperatorEffects? level rest middle
      | none => none
termination_by _level expressions =>
  EbnfValueIndex.measure (.expressions expressions)
decreasing_by
  · exact measure_cons_head_lt _ _
  · exact measure_cons_tail_lt _ _

def grammarOperatorChoicesEffect? :
    NonAssociativeLevel → List EbnfExpr → DelimiterStack →
      Option DelimiterStack
  | _, [], _ => none
  | level, branch :: rest, before =>
      match grammarOperatorEffect? level branch before with
      | none => none
      | some after =>
          if grammarOperatorEffectsAgree level rest before after then
            some after
          else
            none
termination_by _level expressions =>
  EbnfValueIndex.measure (.expressions expressions)
decreasing_by
  · exact measure_cons_head_lt _ _
  · exact measure_cons_tail_lt _ _

def grammarOperatorEffectsAgree :
    NonAssociativeLevel → List EbnfExpr → DelimiterStack →
      DelimiterStack → Bool
  | _, [], _, _ => true
  | level, candidate :: rest, before, after =>
      if grammarOperatorEffect? level candidate before = some after then
        grammarOperatorEffectsAgree level rest before after
      else
        false
termination_by _level expressions =>
  EbnfValueIndex.measure (.expressions expressions)
decreasing_by
  · exact measure_cons_head_lt _ _
  · exact measure_cons_tail_lt _ _

end

/-- The two levels whose operand closures are checked. -/
def allOperatorSafetyLevels : List NonAssociativeLevel :=
  [.relational, .equality]

/-- Finite closure check for every source rule admitted at base depth. -/
def grammarOperatorSafeRulesBool : Bool :=
  allOperatorSafetyLevels.all fun level =>
    allGrammarRuleIds.all fun rule =>
      !grammarOperatorSafeRule level rule ||
        decide (grammarOperatorEffect? level (m2cV1.rhs rule) [] = some [])

set_option linter.unusedSimpArgs false in
theorem grammarOperatorSafeRulesBool_eq_true :
    grammarOperatorSafeRulesBool = true := by
  simp [grammarOperatorSafeRulesBool, allOperatorSafetyLevels,
    allGrammarRuleIds, grammarOperatorSafeRule, grammarForbiddenTerminal,
    grammarOperatorEffect?, grammarOperatorEffects?,
    grammarOperatorChoicesEffect?, grammarOperatorEffectsAgree,
    grammarTerminalDelimiterStep?, m2cV1, m2cV1Rhs, Grammar.terminal,
    Grammar.hardKeyword, Grammar.contextualKeyword, Grammar.pragmaName,
    Grammar.symbol, Grammar.category, Grammar.nonterminal, Grammar.sequence,
    Grammar.choice, Grammar.group, Grammar.optional, Grammar.star,
    Grammar.plus, Grammar.list0, Grammar.list1, Grammar.identifier,
    Grammar.pathComponent]

theorem allOperatorSafetyLevels_complete (level : NonAssociativeLevel) :
    level ∈ allOperatorSafetyLevels := by
  cases level <;> simp [allOperatorSafetyLevels]

/-- Every admitted source row passes the operator-safety skeleton check. -/
theorem grammarOperatorSafeRule_effect
    (level : NonAssociativeLevel) (rule : GrammarRuleId)
    (safe : grammarOperatorSafeRule level rule = true) :
    grammarOperatorEffect? level (m2cV1.rhs rule) [] = some [] := by
  have levelAccepted := (List.all_eq_true.mp
    grammarOperatorSafeRulesBool_eq_true) level
      (allOperatorSafetyLevels_complete level)
  have ruleAccepted := (List.all_eq_true.mp levelAccepted) rule
    (by cases rule <;> simp [allGrammarRuleIds])
  simp [safe] at ruleAccepted
  exact ruleAccepted

/-- The operand rule for either nonassociative level belongs to the checked
base-depth closure. -/
theorem grammarOperatorSafeRule_operand
    (level : NonAssociativeLevel) :
    grammarOperatorSafeRule level level.operandRule = true := by
  cases level <;> rfl

end Solcore.Surface.Multi
