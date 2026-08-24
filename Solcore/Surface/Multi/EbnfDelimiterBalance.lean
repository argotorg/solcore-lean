import Solcore.Surface.Multi.EbnfRecognitionExtraction

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- Static delimiter effect of one grammar terminal. -/
def grammarTerminalDelimiterStep? :
    DelimiterStack → TerminalSymbol → Option DelimiterStack
  | before, .symbol .leftParen => some (.rightParen :: before)
  | before, .symbol .leftBracket => some (.rightBracket :: before)
  | before, .symbol .leftBrace => some (.rightBrace :: before)
  | .rightParen :: rest, .symbol .rightParen => some rest
  | .rightBracket :: rest, .symbol .rightBracket => some rest
  | .rightBrace :: rest, .symbol .rightBrace => some rest
  | _, .symbol .rightParen => none
  | _, .symbol .rightBracket => none
  | _, .symbol .rightBrace => none
  | before, _ => some before

private theorem measure_choice_lt (branches : List EbnfExpr) :
    EbnfValueIndex.measure (.expressions branches) <
      EbnfValueIndex.measure (.expression (.choice branches)) := by
  simp [EbnfValueIndex.measure, ebnfSize]
  omega

mutual

/-- Execute the delimiter skeleton of one EBNF expression, treating a source
nonterminal call as one stack-preserving opaque operation. -/
def grammarDelimiterEffect? :
    EbnfExpr → DelimiterStack → Option DelimiterStack
  | .atom (.terminal terminal), before =>
      grammarTerminalDelimiterStep? before terminal
  | .atom (.nonterminal _), before => some before
  | .sequence children, before =>
      grammarDelimiterEffects? children before
  | .group child, before => grammarDelimiterEffect? child before
  | .choice branches, before =>
      grammarDelimiterChoicesEffect? branches before
  | .optional child, before
  | .star child, before
  | .plus child, before
  | .list0 child, before
  | .list1 child, before =>
      match grammarDelimiterEffect? child before with
      | some after => if after = before then some before else none
      | none => none
termination_by expression =>
  EbnfValueIndex.measure (.expression expression)
decreasing_by
  · exact measure_sequence_lt _
  · exact measure_unary_child_lt .group _
  · exact measure_choice_lt _
  · exact measure_unary_child_lt .optional _
  · exact measure_unary_child_lt .star _
  · exact measure_unary_child_lt .plus _
  · exact measure_unary_child_lt .list0 _
  · exact measure_unary_child_lt .list1 _

/-- Execute displayed sequence children in order. -/
def grammarDelimiterEffects? :
    List EbnfExpr → DelimiterStack → Option DelimiterStack
  | [], before => some before
  | child :: rest, before =>
      match grammarDelimiterEffect? child before with
      | some middle => grammarDelimiterEffects? rest middle
      | none => none
termination_by expressions =>
  EbnfValueIndex.measure (.expressions expressions)
decreasing_by
  · exact measure_cons_head_lt _ _
  · exact measure_cons_tail_lt _ _

/-- A choice has a static effect only when every displayed branch has the
same effect. -/
def grammarDelimiterChoicesEffect? :
    List EbnfExpr → DelimiterStack → Option DelimiterStack
  | [], _ => none
  | branch :: rest, before =>
      match grammarDelimiterEffect? branch before with
      | none => none
      | some after =>
          if grammarDelimiterEffectsAgree rest before after then
            some after
          else
            none
termination_by expressions =>
  EbnfValueIndex.measure (.expressions expressions)
decreasing_by
  · exact measure_cons_head_lt _ _
  · exact measure_cons_tail_lt _ _

def grammarDelimiterEffectsAgree :
    List EbnfExpr → DelimiterStack → DelimiterStack → Bool
  | [], _, _ => true
  | candidate :: rest, before, after =>
      if grammarDelimiterEffect? candidate before = some after then
        grammarDelimiterEffectsAgree rest before after
      else
        false
termination_by expressions =>
  EbnfValueIndex.measure (.expressions expressions)
decreasing_by
  · exact measure_cons_head_lt _ _
  · exact measure_cons_tail_lt _ _

end

/-- Finite static check that every source-rule skeleton balances from the
empty delimiter stack. -/
def grammarRulesDelimiterBalancedBool : Bool :=
  allGrammarRuleIds.all fun rule =>
    decide (grammarDelimiterEffect? (m2cV1.rhs rule) [] = some [])

set_option linter.unusedSimpArgs false in
theorem grammarRulesDelimiterBalancedBool_eq_true :
    grammarRulesDelimiterBalancedBool = true := by
  simp [grammarRulesDelimiterBalancedBool, allGrammarRuleIds,
    grammarDelimiterEffect?, grammarDelimiterEffects?,
    grammarDelimiterChoicesEffect?, grammarDelimiterEffectsAgree,
    grammarTerminalDelimiterStep?, m2cV1, m2cV1Rhs,
    Grammar.terminal, Grammar.hardKeyword, Grammar.contextualKeyword,
    Grammar.pragmaName, Grammar.symbol, Grammar.category,
    Grammar.nonterminal, Grammar.sequence, Grammar.choice, Grammar.group,
    Grammar.optional, Grammar.star, Grammar.plus, Grammar.list0,
    Grammar.list1, Grammar.identifier, Grammar.pathComponent]

/-- Every checked source-rule skeleton balances from the empty stack. -/
theorem grammarRule_delimiterEffect_empty
    (rule : GrammarRuleId) :
    grammarDelimiterEffect? (m2cV1.rhs rule) [] = some [] := by
  have accepted := (List.all_eq_true.mp
    grammarRulesDelimiterBalancedBool_eq_true) rule
      (by cases rule <;> simp [allGrammarRuleIds])
  exact of_decide_eq_true accepted

end Solcore.Surface.Multi
