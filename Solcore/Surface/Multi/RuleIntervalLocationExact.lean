import Solcore.Surface.Multi.RuleIntervalLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

namespace RuleReduction

/-- The complete semantic fragment is unchanged by a source-rule action. -/
def PreservesExactLocationFragment
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (_reduces : RuleReduction file tokens rule origin finish input output) :
    Prop :=
  input.locationFragment = RuleLocationView.ofRuleValue rule output

private theorem ruleAtom_locationFragments
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) (values : List (RuleValue rule)) :
    (values.map
        (EbnfValue.ruleAtom (file := file) (tokens := tokens) rule)).map
          (fun value => value.locationFragment) =
      values.map (RuleLocationView.ofRuleValue rule) := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

private theorem expressionRuleAtom_locationFragments
    {file : WorkspaceFile} {tokens : List Token}
    (expressions : List (RuleValue .expression)) :
    (expressions.map
        (EbnfValue.ruleAtom (file := file) (tokens := tokens) .expression)).map
          (fun value => value.locationFragment) =
      expressions.map LocationFragment.ofExpression := by
  induction expressions with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis, RuleLocationView.ofRuleValue]
      rfl

/-- Non-pass-through source-rule reductions whose complete input and output
location fragments are structurally equal. -/
inductive ExactResult
    {file : WorkspaceFile} {tokens : List Token} :
    {rule : GrammarRuleId} -> {origin finish : Boundary tokens} ->
      {input : EbnfValue file tokens (m2cV1.rhs rule)} ->
      {output : RuleValue rule} ->
      RuleReduction file tokens rule origin finish input output -> Prop where
  | optionalCommaAbsent (origin finish : Boundary tokens) :
      ExactResult (RuleReduction.optionalCommaAbsent
        (file := file) origin finish)
  | optionalCommaPresent (origin finish : Boundary tokens)
      (comma : MatchedTerminal file tokens (.symbol .comma)) :
      ExactResult (RuleReduction.optionalCommaPresent origin finish comma)
  | predicateList (origin finish : Boundary tokens)
      (predicates : NonemptyList Predicate) :
      ExactResult (RuleReduction.predicateList
        (file := file) (tokens := tokens) origin finish predicates)
  | assignmentOperatorEqual (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .equal)) :
      ExactResult (RuleReduction.assignmentOperatorEqual
        origin finish terminal)
  | assignmentOperatorAddEqual (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .plusEqual)) :
      ExactResult (RuleReduction.assignmentOperatorAddEqual
        origin finish terminal)
  | assignmentOperatorSubtractEqual (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .minusEqual)) :
      ExactResult (RuleReduction.assignmentOperatorSubtractEqual
        origin finish terminal)
  | assignmentOperatorBitXorEqual (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .caretEqual)) :
      ExactResult (RuleReduction.assignmentOperatorBitXorEqual
        origin finish terminal)
  | assignmentOperatorBitAndEqual (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .ampEqual)) :
      ExactResult (RuleReduction.assignmentOperatorBitAndEqual
        origin finish terminal)
  | assignmentOperatorBitOrEqual (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .pipeEqual)) :
      ExactResult (RuleReduction.assignmentOperatorBitOrEqual
        origin finish terminal)
  | assignmentOperatorModuloEqual (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.symbol .percentEqual)) :
      ExactResult (RuleReduction.assignmentOperatorModuloEqual
        origin finish terminal)
  | postfixPartCall (origin finish : Boundary tokens)
      (openParen : MatchedTerminal file tokens (.symbol .leftParen))
      (arguments : List Expression)
      (closeParen : MatchedTerminal file tokens (.symbol .rightParen)) :
      ExactResult (RuleReduction.postfixPartCall
        origin finish openParen arguments closeParen)
  | postfixPartSelect (origin finish : Boundary tokens)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (field : MatchedTerminal file tokens (.category .identifier))
      (spelling : String) (parsed : Identifier)
      (projects : IdentifierProjects field spelling parsed) :
      ExactResult (RuleReduction.postfixPartSelect
        origin finish dot field spelling parsed projects)
  | postfixPartIndex (origin finish : Boundary tokens)
      (openBracket : MatchedTerminal file tokens (.symbol .leftBracket))
      (index : Expression)
      (closeBracket : MatchedTerminal file tokens (.symbol .rightBracket)) :
      ExactResult (RuleReduction.postfixPartIndex
        origin finish openBracket index closeBracket)
  | literalDecimal (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.category .decimalLiteral))
      (payload : LiteralPayload)
      (projects : LiteralProjects terminal payload) :
      ExactResult (RuleReduction.literalDecimal
        origin finish terminal payload projects)
  | literalHexadecimal (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.category .hexadecimalLiteral))
      (payload : LiteralPayload)
      (projects : LiteralProjects terminal payload) :
      ExactResult (RuleReduction.literalHexadecimal
        origin finish terminal payload projects)
  | literalString (origin finish : Boundary tokens)
      (terminal : MatchedTerminal file tokens (.category .stringLiteral))
      (payload : LiteralPayload)
      (projects : LiteralProjects terminal payload) :
      ExactResult (RuleReduction.literalString
        origin finish terminal payload projects)

/-- The 38 source-rule actions that add no semantic location wrapper: the 22
retained-child pass-throughs and the 16 exact result constructors. -/
inductive ExactLocation
    {file : WorkspaceFile} {tokens : List Token} :
    {rule : GrammarRuleId} -> {origin finish : Boundary tokens} ->
      {input : EbnfValue file tokens (m2cV1.rhs rule)} ->
      {output : RuleValue rule} ->
      RuleReduction file tokens rule origin finish input output -> Prop where
  | semanticPassThrough
      {rule : GrammarRuleId} {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs rule)}
      {output : RuleValue rule}
      {reduces : RuleReduction file tokens rule origin finish input output}
      (passThrough : RuleReduction.SemanticPassThrough reduces) :
      ExactLocation reduces
  | exactResult
      {rule : GrammarRuleId} {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs rule)}
      {output : RuleValue rule}
      {reduces : RuleReduction file tokens rule origin finish input output}
      (exact : RuleReduction.ExactResult reduces) :
      ExactLocation reduces

/-- The absent optional comma carries the empty fragment on both sides. -/
theorem optionalCommaAbsent_preservesExactLocationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) :
    PreservesExactLocationFragment
      (RuleReduction.optionalCommaAbsent
        (file := file) origin finish) := by
  unfold PreservesExactLocationFragment
  simp [RuleLocationView.ofRuleValue, RuleLocationView.ofOptionalCommaValue]

/-- A present optional comma retains its terminal span exactly. -/
theorem optionalCommaPresent_preservesExactLocationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (comma : MatchedTerminal file tokens (.symbol .comma)) :
    PreservesExactLocationFragment
      (RuleReduction.optionalCommaPresent origin finish comma) := by
  unfold PreservesExactLocationFragment
  simp [RuleLocationView.ofRuleValue, RuleLocationView.ofOptionalCommaValue,
    MatchedTerminal.locationFragment]

/-- A predicate list retains every predicate fragment in list order. -/
theorem predicateList_preservesExactLocationFragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (predicates : NonemptyList Predicate) :
    PreservesExactLocationFragment
      (RuleReduction.predicateList
        (file := file) (tokens := tokens) origin finish predicates) := by
  change NonemptyList (RuleValue .predicate) at predicates
  unfold PreservesExactLocationFragment
  refine (EbnfValue.locationFragment_transport _ _).trans ?_
  rw [EbnfValue.locationFragment_list1]
  change LocationFragment.merge
      ((EbnfValue.ruleAtom .predicate predicates.head).locationFragment ::
        ((predicates.tail.map (EbnfValue.ruleAtom .predicate)).map
          fun value => value.locationFragment)) = _
  rw [ruleAtom_locationFragments .predicate predicates.tail]
  simp [RuleLocationView.ofRuleValue, RuleLocationView.ofPredicateList]
  rfl

private theorem assignmentOperatorEqual_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (terminal : MatchedTerminal file tokens (.symbol .equal)) :
    PreservesExactLocationFragment
      (RuleReduction.assignmentOperatorEqual origin finish terminal) := by
  unfold PreservesExactLocationFragment
  calc
    _ = (EbnfValue.terminalAtom (.symbol .equal) terminal).locationFragment :=
      EbnfValue.locationFragment_choice _ _
    _ = terminal.locationFragment :=
      EbnfValue.locationFragment_terminalAtom _ _
    _ = _ := by
      apply LocationFragment.eq_of_fields <;>
        simp [RuleLocationView.ofRuleValue, RuleReduction.assignmentOperator,
          RuleReduction.terminalLoc, MatchedTerminal.locationFragment]

private theorem assignmentOperatorAddEqual_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (terminal : MatchedTerminal file tokens (.symbol .plusEqual)) :
    PreservesExactLocationFragment
      (RuleReduction.assignmentOperatorAddEqual origin finish terminal) := by
  unfold PreservesExactLocationFragment
  calc
    _ = (EbnfValue.terminalAtom
          (.symbol .plusEqual) terminal).locationFragment :=
      EbnfValue.locationFragment_choice _ _
    _ = terminal.locationFragment :=
      EbnfValue.locationFragment_terminalAtom _ _
    _ = _ := by
      apply LocationFragment.eq_of_fields <;>
        simp [RuleLocationView.ofRuleValue, RuleReduction.assignmentOperator,
          RuleReduction.terminalLoc, MatchedTerminal.locationFragment]

private theorem assignmentOperatorSubtractEqual_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (terminal : MatchedTerminal file tokens (.symbol .minusEqual)) :
    PreservesExactLocationFragment
      (RuleReduction.assignmentOperatorSubtractEqual
        origin finish terminal) := by
  unfold PreservesExactLocationFragment
  calc
    _ = (EbnfValue.terminalAtom
          (.symbol .minusEqual) terminal).locationFragment :=
      EbnfValue.locationFragment_choice _ _
    _ = terminal.locationFragment :=
      EbnfValue.locationFragment_terminalAtom _ _
    _ = _ := by
      apply LocationFragment.eq_of_fields <;>
        simp [RuleLocationView.ofRuleValue, RuleReduction.assignmentOperator,
          RuleReduction.terminalLoc, MatchedTerminal.locationFragment]

private theorem assignmentOperatorBitXorEqual_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (terminal : MatchedTerminal file tokens (.symbol .caretEqual)) :
    PreservesExactLocationFragment
      (RuleReduction.assignmentOperatorBitXorEqual
        origin finish terminal) := by
  unfold PreservesExactLocationFragment
  calc
    _ = (EbnfValue.terminalAtom
          (.symbol .caretEqual) terminal).locationFragment :=
      EbnfValue.locationFragment_choice _ _
    _ = terminal.locationFragment :=
      EbnfValue.locationFragment_terminalAtom _ _
    _ = _ := by
      apply LocationFragment.eq_of_fields <;>
        simp [RuleLocationView.ofRuleValue, RuleReduction.assignmentOperator,
          RuleReduction.terminalLoc, MatchedTerminal.locationFragment]

private theorem assignmentOperatorBitAndEqual_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (terminal : MatchedTerminal file tokens (.symbol .ampEqual)) :
    PreservesExactLocationFragment
      (RuleReduction.assignmentOperatorBitAndEqual
        origin finish terminal) := by
  unfold PreservesExactLocationFragment
  calc
    _ = (EbnfValue.terminalAtom
          (.symbol .ampEqual) terminal).locationFragment :=
      EbnfValue.locationFragment_choice _ _
    _ = terminal.locationFragment :=
      EbnfValue.locationFragment_terminalAtom _ _
    _ = _ := by
      apply LocationFragment.eq_of_fields <;>
        simp [RuleLocationView.ofRuleValue, RuleReduction.assignmentOperator,
          RuleReduction.terminalLoc, MatchedTerminal.locationFragment]

private theorem assignmentOperatorBitOrEqual_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (terminal : MatchedTerminal file tokens (.symbol .pipeEqual)) :
    PreservesExactLocationFragment
      (RuleReduction.assignmentOperatorBitOrEqual
        origin finish terminal) := by
  unfold PreservesExactLocationFragment
  calc
    _ = (EbnfValue.terminalAtom
          (.symbol .pipeEqual) terminal).locationFragment :=
      EbnfValue.locationFragment_choice _ _
    _ = terminal.locationFragment :=
      EbnfValue.locationFragment_terminalAtom _ _
    _ = _ := by
      apply LocationFragment.eq_of_fields <;>
        simp [RuleLocationView.ofRuleValue, RuleReduction.assignmentOperator,
          RuleReduction.terminalLoc, MatchedTerminal.locationFragment]

private theorem assignmentOperatorModuloEqual_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (terminal : MatchedTerminal file tokens (.symbol .percentEqual)) :
    PreservesExactLocationFragment
      (RuleReduction.assignmentOperatorModuloEqual
        origin finish terminal) := by
  unfold PreservesExactLocationFragment
  calc
    _ = (EbnfValue.terminalAtom
          (.symbol .percentEqual) terminal).locationFragment :=
      EbnfValue.locationFragment_choice _ _
    _ = terminal.locationFragment :=
      EbnfValue.locationFragment_terminalAtom _ _
    _ = _ := by
      apply LocationFragment.eq_of_fields <;>
        simp [RuleLocationView.ofRuleValue, RuleReduction.assignmentOperator,
          RuleReduction.terminalLoc, MatchedTerminal.locationFragment]

private theorem postfixPartCall_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (arguments : List Expression)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen)) :
    PreservesExactLocationFragment
      (RuleReduction.postfixPartCall
        origin finish openParen arguments closeParen) := by
  change List (RuleValue .expression) at arguments
  unfold PreservesExactLocationFragment
  refine (EbnfValue.locationFragment_choice _ _).trans ?_
  refine (EbnfValue.locationFragment_sequence _ _).trans ?_
  rw [EbnfValues.locationFragment_cons]
  rw [EbnfValues.locationFragment_cons]
  rw [EbnfValues.locationFragment_cons]
  rw [EbnfValues.locationFragment_nil]
  rw [EbnfValue.locationFragment_list0]
  rw [expressionRuleAtom_locationFragments arguments]
  apply LocationFragment.eq_of_fields <;>
    simp [RuleLocationView.ofRuleValue,
      RuleLocationView.ofPostfixPartValue,
      MatchedTerminal.locationFragment] <;>
    rfl

private theorem postfixPartSelect_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (field : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier)
    (projects : IdentifierProjects field spelling parsed) :
    PreservesExactLocationFragment
      (RuleReduction.postfixPartSelect
        origin finish dot field spelling parsed projects) := by
  unfold PreservesExactLocationFragment
  refine (EbnfValue.locationFragment_choice _ _).trans ?_
  refine (EbnfValue.locationFragment_sequence _ _).trans ?_
  apply LocationFragment.eq_of_fields <;>
    simp [RuleLocationView.ofRuleValue,
      RuleLocationView.ofPostfixPartValue,
      RuleReduction.terminalLoc, MatchedTerminal.locationFragment] <;>
    rfl

private theorem postfixPartIndex_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openBracket : MatchedTerminal file tokens (.symbol .leftBracket))
    (index : Expression)
    (closeBracket : MatchedTerminal file tokens (.symbol .rightBracket)) :
    PreservesExactLocationFragment
      (RuleReduction.postfixPartIndex
        origin finish openBracket index closeBracket) := by
  unfold PreservesExactLocationFragment
  refine (EbnfValue.locationFragment_choice _ _).trans ?_
  refine (EbnfValue.locationFragment_sequence _ _).trans ?_
  apply LocationFragment.eq_of_fields <;>
    simp [RuleLocationView.ofRuleValue,
      RuleLocationView.ofPostfixPartValue,
      MatchedTerminal.locationFragment]

private theorem literalDecimal_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (terminal : MatchedTerminal file tokens (.category .decimalLiteral))
    (payload : LiteralPayload)
    (projects : LiteralProjects terminal payload) :
    PreservesExactLocationFragment
      (RuleReduction.literalDecimal
        origin finish terminal payload projects) := by
  unfold PreservesExactLocationFragment
  calc
    _ = (EbnfValue.terminalAtom
          (.category .decimalLiteral) terminal).locationFragment :=
      EbnfValue.locationFragment_choice _ _
    _ = terminal.locationFragment :=
      EbnfValue.locationFragment_terminalAtom _ _
    _ = _ := by
      apply LocationFragment.eq_of_fields <;>
        simp [RuleLocationView.ofRuleValue, RuleReduction.terminalLoc,
          MatchedTerminal.locationFragment]

private theorem literalHexadecimal_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (terminal : MatchedTerminal file tokens (.category .hexadecimalLiteral))
    (payload : LiteralPayload)
    (projects : LiteralProjects terminal payload) :
    PreservesExactLocationFragment
      (RuleReduction.literalHexadecimal
        origin finish terminal payload projects) := by
  unfold PreservesExactLocationFragment
  calc
    _ = (EbnfValue.terminalAtom
          (.category .hexadecimalLiteral) terminal).locationFragment :=
      EbnfValue.locationFragment_choice _ _
    _ = terminal.locationFragment :=
      EbnfValue.locationFragment_terminalAtom _ _
    _ = _ := by
      apply LocationFragment.eq_of_fields <;>
        simp [RuleLocationView.ofRuleValue, RuleReduction.terminalLoc,
          MatchedTerminal.locationFragment]

private theorem literalString_fragment
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (terminal : MatchedTerminal file tokens (.category .stringLiteral))
    (payload : LiteralPayload)
    (projects : LiteralProjects terminal payload) :
    PreservesExactLocationFragment
      (RuleReduction.literalString
        origin finish terminal payload projects) := by
  unfold PreservesExactLocationFragment
  calc
    _ = (EbnfValue.terminalAtom
          (.category .stringLiteral) terminal).locationFragment :=
      EbnfValue.locationFragment_choice _ _
    _ = terminal.locationFragment :=
      EbnfValue.locationFragment_terminalAtom _ _
    _ = _ := by
      apply LocationFragment.eq_of_fields <;>
        simp [RuleLocationView.ofRuleValue, RuleReduction.terminalLoc,
          MatchedTerminal.locationFragment]

namespace ExactResult

/-- Every exact-result constructor exposes the same complete semantic fragment
before and after its source-rule action. -/
theorem fragment_eq
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (exact : RuleReduction.ExactResult reduces) :
    input.locationFragment = RuleLocationView.ofRuleValue rule output := by
  cases exact with
  | optionalCommaAbsent origin finish =>
      exact optionalCommaAbsent_preservesExactLocationFragment origin finish
  | optionalCommaPresent origin finish comma =>
      exact optionalCommaPresent_preservesExactLocationFragment
        origin finish comma
  | predicateList origin finish predicates =>
      exact predicateList_preservesExactLocationFragment
        origin finish predicates
  | assignmentOperatorEqual origin finish terminal =>
      exact assignmentOperatorEqual_fragment origin finish terminal
  | assignmentOperatorAddEqual origin finish terminal =>
      exact assignmentOperatorAddEqual_fragment origin finish terminal
  | assignmentOperatorSubtractEqual origin finish terminal =>
      exact assignmentOperatorSubtractEqual_fragment origin finish terminal
  | assignmentOperatorBitXorEqual origin finish terminal =>
      exact assignmentOperatorBitXorEqual_fragment origin finish terminal
  | assignmentOperatorBitAndEqual origin finish terminal =>
      exact assignmentOperatorBitAndEqual_fragment origin finish terminal
  | assignmentOperatorBitOrEqual origin finish terminal =>
      exact assignmentOperatorBitOrEqual_fragment origin finish terminal
  | assignmentOperatorModuloEqual origin finish terminal =>
      exact assignmentOperatorModuloEqual_fragment origin finish terminal
  | postfixPartCall origin finish openParen arguments closeParen =>
      exact postfixPartCall_fragment
        origin finish openParen arguments closeParen
  | postfixPartSelect origin finish dot field spelling parsed projects =>
      exact postfixPartSelect_fragment
        origin finish dot field spelling parsed projects
  | postfixPartIndex origin finish openBracket index closeBracket =>
      exact postfixPartIndex_fragment
        origin finish openBracket index closeBracket
  | literalDecimal origin finish terminal payload projects =>
      exact literalDecimal_fragment
        origin finish terminal payload projects
  | literalHexadecimal origin finish terminal payload projects =>
      exact literalHexadecimal_fragment
        origin finish terminal payload projects
  | literalString origin finish terminal payload projects =>
      exact literalString_fragment
        origin finish terminal payload projects

/-- Every one of the 16 exact-result constructors preserves interval evidence
and the complete physical trace. -/
theorem locationSound
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (exact : RuleReduction.ExactResult reduces) :
    RuleReduction.LocationSound reduces := by
  intro trace evidence
  exact IntervalLocationEvidence.replaceFragment exact.fragment_eq evidence

end ExactResult

namespace ExactLocation

/-- Every classified exact source-rule reduction preserves interval evidence
and its complete physical trace. -/
theorem locationSound
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (exact : RuleReduction.ExactLocation reduces) :
    RuleReduction.LocationSound reduces := by
  intro trace evidence
  cases exact with
  | semanticPassThrough passThrough =>
      exact passThrough.locationSound trace evidence
  | exactResult result =>
      exact result.locationSound trace evidence

end ExactLocation

end RuleReduction

end Solcore.Surface.Multi
