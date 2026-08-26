import Solcore.Surface.Multi.RuleIntervalLocationWrapped
import Solcore.Surface.Multi.EbnfLocationSubfragment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

namespace RuleReduction.WrappedLocation

/-! Concrete projected-wrapper proofs for statement, pattern, and expression
reductions.  Each proof names the semantic payload retained below the new
source wrapper and derives its inclusion from a structural EBNF occurrence. -/

private theorem projectedInput_of_shape
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (witness : ConsumedSpanWitness file tokens origin finish)
    (core : LocationFragment)
    (outputShape : RuleLocationView.ofRuleValue rule output =
      LocationFragment.located witness.span [core])
    (coreFromInput : core.IsSubfragmentOf input.locationFragment)
    (coreOccupied : core.roots ≠ []) :
    WrappedLocation reduces := by
  apply WrappedLocation.projectedInput witness core outputShape coreFromInput
  exact LocationFragment.IsSubfragmentOf.roots_ne_nil
    coreFromInput coreOccupied

private theorem raw_of_terminal_occurrence
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    (notEof : terminal ≠ .endOfFile)
    (inside : EbnfValue.ContainsLocationFragment
      file tokens input matched.locationFragment) :
    (LocationFragment.raw matched.span).IsSubfragmentOf
      input.locationFragment := by
  simpa [MatchedTerminal.locationFragment, notEof] using
    inside.locationFragment_isSubfragment

private theorem leaf_of_terminal_occurrence
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    (notEof : terminal ≠ .endOfFile)
    (inside : EbnfValue.ContainsLocationFragment
      file tokens input matched.locationFragment) :
    (LocationFragment.leaf matched.span).IsSubfragmentOf
      input.locationFragment := by
  change (LocationFragment.located matched.span []).IsSubfragmentOf _
  rw [LocationFragment.leaf_eq_raw]
  exact raw_of_terminal_occurrence matched notEof inside

private theorem identifier_of_terminal_occurrence
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} {input : EbnfValue file tokens expression}
    (matched : MatchedTerminal file tokens (.category .identifier))
    (parsed : Identifier)
    (inside : EbnfValue.ContainsLocationFragment
      file tokens input matched.locationFragment) :
    (LocationFragment.ofIdentifier
      (RuleReduction.terminalLoc matched parsed)).IsSubfragmentOf
        input.locationFragment := by
  change (LocationFragment.located matched.span []).IsSubfragmentOf _
  exact leaf_of_terminal_occurrence matched (by decide) inside

private theorem ofPatternList_eq_ofList (values : List Pattern) :
    LocationFragment.ofPatternList values =
      LocationFragment.ofList LocationFragment.ofPattern values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [LocationFragment.ofPatternList, inductionHypothesis]
      apply LocationFragment.eq_of_fields <;>
        simp [LocationFragment.ofList]

private theorem ofExpressionList_eq_ofList (values : List Expression) :
    LocationFragment.ofExpressionList values =
      LocationFragment.ofList LocationFragment.ofExpression values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [LocationFragment.ofExpressionList, inductionHypothesis]
      apply LocationFragment.eq_of_fields <;>
        simp [LocationFragment.ofList]

private theorem ofForInitItemList_eq_ofList (values : List ForInitItem) :
    LocationFragment.ofForInitItemList values =
      LocationFragment.ofList LocationFragment.ofForInitItem values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [LocationFragment.ofForInitItemList, inductionHypothesis]
      apply LocationFragment.eq_of_fields <;>
        simp [LocationFragment.ofList]

private theorem ofForPostItemList_eq_ofList (values : List ForPostItem) :
    LocationFragment.ofForPostItemList values =
      LocationFragment.ofList LocationFragment.ofForPostItem values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [LocationFragment.ofForPostItemList, inductionHypothesis]
      apply LocationFragment.eq_of_fields <;>
        simp [LocationFragment.ofList]

private theorem ofMatchArmList_eq_ofList (values : List MatchArm) :
    LocationFragment.ofMatchArmList values =
      LocationFragment.ofList LocationFragment.ofMatchArm values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [LocationFragment.ofMatchArmList, inductionHypothesis]
      apply LocationFragment.eq_of_fields <;>
        simp [LocationFragment.ofList]

private theorem projectedThreeExpressions_of_occurrences
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (witness : ConsumedSpanWitness file tokens origin finish)
    (first second third : Expression)
    (outputShape : RuleLocationView.ofRuleValue rule output =
      LocationFragment.located witness.span [LocationFragment.merge
        [LocationFragment.ofExpression first,
          LocationFragment.ofExpression second,
          LocationFragment.ofExpression third]])
    (firstInside : EbnfValue.ContainsLocationFragment file tokens input
      (LocationFragment.ofExpression first))
    (secondInside : EbnfValue.ContainsLocationFragment file tokens input
      (LocationFragment.ofExpression second))
    (thirdInside : EbnfValue.ContainsLocationFragment file tokens input
      (LocationFragment.ofExpression third)) :
    WrappedLocation reduces := by
  apply projectedInput_of_shape witness (LocationFragment.merge
    [LocationFragment.ofExpression first,
      LocationFragment.ofExpression second,
      LocationFragment.ofExpression third]) outputShape
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact firstInside.locationFragment_isSubfragment
    · exact secondInside.locationFragment_isSubfragment
    · exact thirdInside.locationFragment_isSubfragment
  · simp

private theorem projectedInfix_of_occurrences
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    {terminal : TerminalSymbol}
    (witness : ConsumedSpanWitness file tokens origin finish)
    (operator : MatchedTerminal file tokens terminal)
    (notEof : terminal ≠ .endOfFile)
    (left right : Expression)
    (outputShape : RuleLocationView.ofRuleValue rule output =
      LocationFragment.located witness.span [LocationFragment.merge
        [LocationFragment.leaf operator.span,
          LocationFragment.ofExpression left,
          LocationFragment.ofExpression right]])
    (operatorInside : EbnfValue.ContainsLocationFragment file tokens input
      operator.locationFragment)
    (leftInside : EbnfValue.ContainsLocationFragment file tokens input
      (LocationFragment.ofExpression left))
    (rightInside : EbnfValue.ContainsLocationFragment file tokens input
      (LocationFragment.ofExpression right)) :
    WrappedLocation reduces := by
  apply projectedInput_of_shape witness (LocationFragment.merge
    [LocationFragment.leaf operator.span,
      LocationFragment.ofExpression left,
      LocationFragment.ofExpression right]) outputShape
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact leaf_of_terminal_occurrence operator notEof operatorInside
    · exact leftInside.locationFragment_isSubfragment
    · exact rightInside.locationFragment_isSubfragment
  · simp

theorem letStatement_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (binding : LetBinding)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.letStatement origin finish binding semicolon witness) := by
  apply projectedInput_of_shape witness (LocationFragment.ofLetBinding binding)
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofStatementPayload]
  · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp

theorem letBindingUntyped_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (letKeyword : MatchedTerminal file tokens (.hardKeyword .letKw))
    (name : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier)
    (nameProjects : IdentifierProjects name spelling parsed)
    (initializer : Option
      (MatchedTerminal file tokens (.symbol .equal) × Expression))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.letBindingUntyped origin finish letKeyword name spelling
        parsed nameProjects initializer witness) := by
  let core := LocationFragment.ofLetBindingPayload {
    comptime := none
    name := RuleReduction.terminalLoc name parsed
    type := none
    initializer := initializer.map Prod.snd
  }
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc]
  · unfold core LocationFragment.ofLetBindingPayload
    apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact LocationFragment.IsSubfragmentOf.empty _
    · apply identifier_of_terminal_occurrence name parsed
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ name
    · exact LocationFragment.IsSubfragmentOf.empty _
    · cases initializer with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some initializer =>
          rcases initializer with ⟨equal, expression⟩
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core, LocationFragment.ofLetBindingPayload]

theorem letBindingTyped_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (letKeyword : MatchedTerminal file tokens (.hardKeyword .letKw))
    (name : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier)
    (nameProjects : IdentifierProjects name spelling parsed)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (typeValue : TypeExpr)
    (initializer : Option
      (MatchedTerminal file tokens (.symbol .equal) × Expression))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.letBindingTyped origin finish letKeyword name spelling
        parsed nameProjects colon typeValue initializer witness) := by
  let core := LocationFragment.ofLetBindingPayload {
    comptime := none
    name := RuleReduction.terminalLoc name parsed
    type := some typeValue
    initializer := initializer.map Prod.snd
  }
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc]
  · unfold core LocationFragment.ofLetBindingPayload
    apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact LocationFragment.IsSubfragmentOf.empty _
    · apply identifier_of_terminal_occurrence name parsed
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ name
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.optional
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · cases initializer with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some initializer =>
          rcases initializer with ⟨equal, expression⟩
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core, LocationFragment.ofLetBindingPayload]

theorem letBindingComptime_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (letKeyword : MatchedTerminal file tokens (.hardKeyword .letKw))
    (name : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier)
    (nameProjects : IdentifierProjects name spelling parsed)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (comptime : MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw))
    (typeValue : TypeExpr)
    (initializer : Option
      (MatchedTerminal file tokens (.symbol .equal) × Expression))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.letBindingComptime origin finish letKeyword name spelling
        parsed nameProjects colon comptime typeValue initializer witness) := by
  let core := LocationFragment.ofLetBindingPayload {
    comptime := some
      (RuleReduction.marker comptime (.comptimeModifier comptime))
    name := RuleReduction.terminalLoc name parsed
    type := some typeValue
    initializer := initializer.map Prod.snd
  }
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      RuleReduction.marker, RuleReduction.terminalLoc]
  · unfold core LocationFragment.ofLetBindingPayload
    apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · apply leaf_of_terminal_occurrence comptime (by decide)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.optional
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.optional
      exact EbnfValue.ContainsLocationFragment.terminal _ comptime
    · apply identifier_of_terminal_occurrence name parsed
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ name
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.optional
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · cases initializer with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some initializer =>
          rcases initializer with ⟨equal, expression⟩
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core, LocationFragment.ofLetBindingPayload]

theorem returnStatement_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (returnKeyword : MatchedTerminal file tokens (.hardKeyword .returnKw))
    (value : Option Expression)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.returnStatement origin finish returnKeyword value semicolon
        witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofOption LocationFragment.ofExpression value,
      LocationFragment.raw semicolon.span]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofStatementPayload]
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · cases value with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some expression =>
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply raw_of_terminal_occurrence semicolon (by decide)
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ semicolon
  · simp [core]

theorem ifStatementWithoutElse_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ifKeyword : MatchedTerminal file tokens (.hardKeyword .ifKw))
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (condition : Expression)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (thenBody : Body)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.ifStatementWithoutElse origin finish ifKeyword openParen
        condition closeParen thenBody witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofExpression condition,
      LocationFragment.ofBody thenBody,
      LocationFragment.ofOption LocationFragment.ofBody none]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofStatementPayload]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · exact LocationFragment.IsSubfragmentOf.empty _
  · simp [core]

theorem ifStatementWithElse_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ifKeyword : MatchedTerminal file tokens (.hardKeyword .ifKw))
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (condition : Expression)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (thenBody : Body)
    (elseKeyword : MatchedTerminal file tokens (.hardKeyword .elseKw))
    (elseBody : Body)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.ifStatementWithElse origin finish ifKeyword openParen
        condition closeParen thenBody elseKeyword elseBody witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofExpression condition,
      LocationFragment.ofBody thenBody,
      LocationFragment.ofOption LocationFragment.ofBody (some elseBody)]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofStatementPayload]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.optional
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core]

theorem forStatement_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (forKeyword : MatchedTerminal file tokens (.hardKeyword .forKw))
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (initializers : List ForInitItem)
    (firstSemicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (condition : Expression)
    (secondSemicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (post : List ForPostItem)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (body : Body)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.forStatement origin finish forKeyword openParen
        initializers firstSemicolon condition secondSemicolon post closeParen
        body witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofForInitItemList initializers,
      LocationFragment.ofExpression condition,
      LocationFragment.ofForPostItemList post,
      LocationFragment.ofBody body]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofStatementPayload]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · rw [ofForInitItemList_eq_ofList]
      unfold LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro item itemMember
      apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.list0
      · exact List.mem_map_of_mem itemMember
      · exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · rw [ofForPostItemList_eq_ofList]
      unfold LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro item itemMember
      apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.list0
      · exact List.mem_map_of_mem itemMember
      · exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core]

theorem matchStatement_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (matchKeyword : MatchedTerminal file tokens (.hardKeyword .matchKw))
    (scrutinees : NonemptyList Expression)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (arms : NonemptyList MatchArm)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (terminator : Option
      (MatchedTerminal file tokens (.symbol .semicolon)))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.matchStatement origin finish matchKeyword scrutinees
        openBrace arms closeBrace terminator witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofExpressionNonempty scrutinees,
      LocationFragment.ofMatchArmNonempty arms,
      LocationFragment.ofOption LocationFragment.raw
        (terminator.map MatchedTerminal.span)]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofStatementPayload]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · unfold LocationFragment.ofExpressionNonempty
      apply LocationFragment.IsSubfragmentOf.merge_pair
      · apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Head
        exact EbnfValue.ContainsLocationFragment.rule _ _
      · rw [ofExpressionList_eq_ofList]
        unfold LocationFragment.ofList
        apply LocationFragment.IsSubfragmentOf.merge_map
        intro expression expressionMember
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Tail
        · exact List.mem_map_of_mem expressionMember
        · exact EbnfValue.ContainsLocationFragment.rule _ _
    · unfold LocationFragment.ofMatchArmNonempty
      apply LocationFragment.IsSubfragmentOf.merge_pair
      · apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.plusHead
        exact EbnfValue.ContainsLocationFragment.rule _ _
      · rw [ofMatchArmList_eq_ofList]
        unfold LocationFragment.ofList
        apply LocationFragment.IsSubfragmentOf.merge_map
        intro arm armMember
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.plusTail
        · exact List.mem_map_of_mem armMember
        · exact EbnfValue.ContainsLocationFragment.rule _ _
    · cases terminator with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some semicolon =>
          apply raw_of_terminal_occurrence semicolon (by decide)
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          exact EbnfValue.ContainsLocationFragment.terminal _ semicolon
  · simp [core, LocationFragment.ofExpressionNonempty]

theorem forInitItemAssignment_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (left : Expression)
    (operator : Located AssignmentOperator) (right : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.forInitItemAssignment origin finish left operator right
        witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofAssignmentOperator operator,
      LocationFragment.ofExpression left,
      LocationFragment.ofExpression right]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofForInitItemPayload]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core]

theorem forPostItemAssignment_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (left : Expression)
    (operator : Located AssignmentOperator) (right : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.forPostItemAssignment origin finish left operator right
        witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofAssignmentOperator operator,
      LocationFragment.ofExpression left,
      LocationFragment.ofExpression right]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofForPostItemPayload]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core]

theorem assignmentStatement_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (left : Expression)
    (operator : Located AssignmentOperator) (right : Expression)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.assignmentStatement origin finish left operator right
        semicolon witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofAssignmentOperator operator,
      LocationFragment.ofExpression left,
      LocationFragment.ofExpression right]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofStatementPayload]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core]

theorem breakStatement_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (breakKeyword : MatchedTerminal file tokens (.hardKeyword .breakKw))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.breakStatement origin finish breakKeyword semicolon
        witness) := by
  apply projectedInput_of_shape witness (LocationFragment.raw semicolon.span)
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofStatementPayload]
  · have fragmentShape : semicolon.locationFragment =
        LocationFragment.raw semicolon.span := by
      simp [MatchedTerminal.locationFragment]
    rw [← fragmentShape]
    apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.terminal _ semicolon
  · change [semicolon.span] ≠ []
    simp

theorem continueStatement_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (continueKeyword : MatchedTerminal file tokens
      (.hardKeyword .continueKw))
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.continueStatement origin finish continueKeyword semicolon
        witness) := by
  apply projectedInput_of_shape witness (LocationFragment.raw semicolon.span)
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofStatementPayload]
  · have fragmentShape : semicolon.locationFragment =
        LocationFragment.raw semicolon.span := by
      simp [MatchedTerminal.locationFragment]
    rw [← fragmentShape]
    apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.terminal _ semicolon
  · change [semicolon.span] ≠ []
    simp

theorem patternGroup_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (inner : Pattern)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.patternGroup origin finish openParen inner closeParen
        witness) := by
  apply projectedInput_of_shape witness (LocationFragment.ofPattern inner)
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofPatternPayload]
  · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
    apply EbnfValue.ContainsLocationFragment.choice ⟨6, by decide⟩
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp

theorem patternDotConstructorWithArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (name : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier)
    (projects : IdentifierProjects name spelling parsed)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (arguments : NonemptyList Pattern)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.patternDotConstructorWithArguments origin finish dot name
        spelling parsed projects openParen arguments closeParen witness) := by
  let core := LocationFragment.merge
    [LocationFragment.leaf dot.span,
      LocationFragment.ofIdentifier (RuleReduction.terminalLoc name parsed),
      LocationFragment.ofPatternArguments (some arguments)]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofPatternPayload, RuleReduction.terminalLoc]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · apply leaf_of_terminal_occurrence dot (by decide)
      apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ dot
    · apply identifier_of_terminal_occurrence name parsed
      apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ name
    · unfold LocationFragment.ofPatternArguments
      apply LocationFragment.IsSubfragmentOf.merge_pair
      · apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.optional
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Head
        exact EbnfValue.ContainsLocationFragment.rule _ _
      · rw [ofPatternList_eq_ofList]
        unfold LocationFragment.ofList
        apply LocationFragment.IsSubfragmentOf.merge_map
        intro argument argumentMember
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.optional
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Tail
        · exact List.mem_map_of_mem argumentMember
        · exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core, LocationFragment.ofPatternArguments]

theorem patternNamedWithArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (name : QualifiedName)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (arguments : NonemptyList Pattern)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.patternNamedWithArguments origin finish name openParen
        arguments closeParen witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofQualifiedName name,
      LocationFragment.ofPatternArguments (some arguments)]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofPatternPayload]
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.choice ⟨4, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · unfold LocationFragment.ofPatternArguments
      apply LocationFragment.IsSubfragmentOf.merge_pair
      · apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.choice ⟨4, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.optional
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Head
        exact EbnfValue.ContainsLocationFragment.rule _ _
      · rw [ofPatternList_eq_ofList]
        unfold LocationFragment.ofList
        apply LocationFragment.IsSubfragmentOf.merge_map
        intro argument argumentMember
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.choice ⟨4, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.optional
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.list1Tail
        · exact List.mem_map_of_mem argumentMember
        · exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core, LocationFragment.ofPatternArguments]

theorem patternTuple_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (first : Pattern)
    (comma : MatchedTerminal file tokens (.symbol .comma))
    (second : Pattern)
    (rest : List
      (MatchedTerminal file tokens (.symbol .comma) × Pattern))
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.patternTuple origin finish openParen first comma second
        rest closeParen witness) := by
  let core := LocationFragment.ofPatternList
    (first :: second :: rest.map Prod.snd)
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofPatternPayload]
  · unfold core
    rw [LocationFragment.ofPatternList]
    apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.choice ⟨7, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · rw [LocationFragment.ofPatternList]
      apply LocationFragment.IsSubfragmentOf.merge_pair
      · apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.choice ⟨7, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        exact EbnfValue.ContainsLocationFragment.rule _ _
      · rw [ofPatternList_eq_ofList]
        unfold LocationFragment.ofList
        apply LocationFragment.IsSubfragmentOf.merge_map
        intro pattern patternMember
        rw [List.mem_map] at patternMember
        rcases patternMember with ⟨entry, entryMember, rfl⟩
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.choice ⟨7, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.star
        · exact List.mem_map_of_mem entryMember
        · apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core, LocationFragment.ofPatternList]

theorem annotationSome_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (expression : Expression)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (typeValue : TypeExpr)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.annotationSome origin finish expression colon typeValue
        witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofExpression expression,
      LocationFragment.ofTypeExpr typeValue]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload]
  · apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.optional
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core]

theorem conditionalKeyword_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ifKeyword : MatchedTerminal file tokens (.hardKeyword .ifKw))
    (condition : Expression)
    (thenKeyword : MatchedTerminal file tokens
      (.contextualKeyword .thenKw))
    (thenBranch : Expression)
    (elseKeyword : MatchedTerminal file tokens (.hardKeyword .elseKw))
    (elseBranch : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.conditionalKeyword origin finish ifKeyword condition
        thenKeyword thenBranch elseKeyword elseBranch witness) := by
  apply projectedThreeExpressions_of_occurrences witness condition thenBranch
    elseBranch
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload]
  · apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _

theorem conditionalTernary_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (condition : Expression)
    (question : MatchedTerminal file tokens (.symbol .question))
    (thenBranch : Expression)
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (elseBranch : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.conditionalTernary origin finish condition question
        thenBranch colon elseBranch witness) := by
  apply projectedThreeExpressions_of_occurrences witness condition thenBranch
    elseBranch
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload]
  · apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _

theorem equalityEqual_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (left : Expression)
    (operator : MatchedTerminal file tokens (.symbol .equalEqual))
    (right : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.equalityEqual origin finish left operator right
        witness) := by
  apply projectedInfix_of_occurrences witness operator (by decide) left right
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload, RuleReduction.infixOperator,
      RuleReduction.terminalLoc]
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.group
    apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
    exact EbnfValue.ContainsLocationFragment.terminal _ operator
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _

theorem equalityNotEqual_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (left : Expression)
    (operator : MatchedTerminal file tokens (.symbol .notEqual))
    (right : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.equalityNotEqual origin finish left operator right
        witness) := by
  apply projectedInfix_of_occurrences witness operator (by decide) left right
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload, RuleReduction.infixOperator,
      RuleReduction.terminalLoc]
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.group
    apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
    exact EbnfValue.ContainsLocationFragment.terminal _ operator
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _

theorem relationalLess_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (left : Expression)
    (operator : MatchedTerminal file tokens (.symbol .less))
    (right : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.relationalLess origin finish left operator right
        witness) := by
  apply projectedInfix_of_occurrences witness operator (by decide) left right
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload, RuleReduction.infixOperator,
      RuleReduction.terminalLoc]
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.group
    apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
    exact EbnfValue.ContainsLocationFragment.terminal _ operator
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _

theorem relationalGreater_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (left : Expression)
    (operator : MatchedTerminal file tokens (.symbol .greater))
    (right : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.relationalGreater origin finish left operator right
        witness) := by
  apply projectedInfix_of_occurrences witness operator (by decide) left right
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload, RuleReduction.infixOperator,
      RuleReduction.terminalLoc]
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.group
    apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
    exact EbnfValue.ContainsLocationFragment.terminal _ operator
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _

theorem relationalLessEqual_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (left : Expression)
    (operator : MatchedTerminal file tokens (.symbol .lessEqual))
    (right : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.relationalLessEqual origin finish left operator right
        witness) := by
  apply projectedInfix_of_occurrences witness operator (by decide) left right
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload, RuleReduction.infixOperator,
      RuleReduction.terminalLoc]
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.group
    apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
    exact EbnfValue.ContainsLocationFragment.terminal _ operator
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _

theorem relationalGreaterEqual_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (left : Expression)
    (operator : MatchedTerminal file tokens (.symbol .greaterEqual))
    (right : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.relationalGreaterEqual origin finish left operator right
        witness) := by
  apply projectedInfix_of_occurrences witness operator (by decide) left right
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload, RuleReduction.infixOperator,
      RuleReduction.terminalLoc]
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.group
    apply EbnfValue.ContainsLocationFragment.choice ⟨3, by decide⟩
    exact EbnfValue.ContainsLocationFragment.terminal _ operator
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.optional
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _

theorem atomGroup_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (inner : Expression)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.atomGroup origin finish openParen inner closeParen
        witness) := by
  apply projectedInput_of_shape witness (LocationFragment.ofExpression inner)
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload]
  · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
    apply EbnfValue.ContainsLocationFragment.choice ⟨6, by decide⟩
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp

theorem atomDotConstructorWithArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (name : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier)
    (projects : IdentifierProjects name spelling parsed)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (arguments : List Expression)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.atomDotConstructorWithArguments origin finish dot name
        spelling parsed projects openParen arguments closeParen witness) := by
  let core := LocationFragment.merge
    [LocationFragment.leaf dot.span,
      LocationFragment.ofIdentifier (RuleReduction.terminalLoc name parsed),
      LocationFragment.ofExpressionListOption (some arguments)]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload, RuleReduction.terminalLoc]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · apply leaf_of_terminal_occurrence dot (by decide)
      apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ dot
    · apply identifier_of_terminal_occurrence name parsed
      apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ name
    · unfold LocationFragment.ofExpressionListOption
      change (LocationFragment.ofExpressionList arguments).IsSubfragmentOf _
      rw [ofExpressionList_eq_ofList]
      unfold LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro argument argumentMember
      apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.optional
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.list0
      · exact List.mem_map_of_mem argumentMember
      · exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core]

theorem atomTuple_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (first : Expression)
    (comma : MatchedTerminal file tokens (.symbol .comma))
    (second : Expression)
    (rest : List
      (MatchedTerminal file tokens (.symbol .comma) × Expression))
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.atomTuple origin finish openParen first comma second rest
        closeParen witness) := by
  let core := LocationFragment.ofExpressionList
    (first :: second :: rest.map Prod.snd)
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload]
  · unfold core
    rw [LocationFragment.ofExpressionList]
    apply LocationFragment.IsSubfragmentOf.merge_pair
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.choice ⟨7, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
    · rw [LocationFragment.ofExpressionList]
      apply LocationFragment.IsSubfragmentOf.merge_pair
      · apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.choice ⟨7, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        exact EbnfValue.ContainsLocationFragment.rule _ _
      · rw [ofExpressionList_eq_ofList]
        unfold LocationFragment.ofList
        apply LocationFragment.IsSubfragmentOf.merge_map
        intro expression expressionMember
        rw [List.mem_map] at expressionMember
        rcases expressionMember with ⟨entry, entryMember, rfl⟩
        apply
          EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
        apply EbnfValue.ContainsLocationFragment.choice ⟨7, by decide⟩
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.star
        · exact List.mem_map_of_mem entryMember
        · apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.rule _ _
  · simp [core, LocationFragment.ofExpressionList]

theorem lambda_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (lambdaKeyword : MatchedTerminal file tokens (.hardKeyword .lamKw))
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (parameters : List Parameter)
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (returnType : Option
      (MatchedTerminal file tokens (.symbol .arrow) × TypeExpr))
    (body : Body)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.lambda origin finish lambdaKeyword openParen parameters
        closeParen returnType body witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofList LocationFragment.ofParameter parameters,
      LocationFragment.ofOption LocationFragment.ofTypeExpr
        (returnType.map Prod.snd),
      LocationFragment.ofBody body]
  apply projectedInput_of_shape witness core
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload]
  · apply LocationFragment.IsSubfragmentOf.merge
    intro fragment member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · unfold LocationFragment.ofList
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro parameter parameterMember
      apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.list0
      · exact List.mem_map_of_mem parameterMember
      · exact EbnfValue.ContainsLocationFragment.rule _ _
    · cases returnType with
      | none => exact LocationFragment.IsSubfragmentOf.empty _
      | some returnType =>
          rcases returnType with ⟨arrow, typeValue⟩
          apply
            EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.optional
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          exact EbnfValue.ContainsLocationFragment.rule _ _
    · apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule _ _
  · rcases body with ⟨span, origin, statements⟩
    cases origin <;> simp [core]

end RuleReduction.WrappedLocation

end Solcore.Surface.Multi
