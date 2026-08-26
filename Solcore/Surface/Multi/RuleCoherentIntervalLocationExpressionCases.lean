import Solcore.Surface.Multi.RuleCoherentIntervalLocation
import Solcore.Surface.Multi.SourceRuleIntervalLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

namespace RuleReduction

/-! Coherent interval proofs for the left-folding expression reductions. -/

/-- The source spans that a coherent focused trace must retain for one infix
fold: the first operand, followed by every operator and right operand. -/
def infixFoldFocusedSpans (left : Expression)
    (rest : List (Located InfixOperator × Expression)) : List SourceSpan :=
  left.span :: rest.flatMap fun pair => [pair.1.span, pair.2.span]

/-- The span calculation performed by an infix fold, with operator payloads
erased because they do not affect either endpoint. -/
def infixFoldSpan (file : WorkspaceFile) :
    SourceSpan → List Expression → SourceSpan
  | left, [] => left
  | left, right :: rest =>
      infixFoldSpan file
        (RuleReduction.between file left right.span ()).span rest

@[simp] theorem foldInfixLeft_span
    (file : WorkspaceFile) (left : Expression)
    (rest : List (Located InfixOperator × Expression)) :
    (RuleReduction.foldInfixLeft file left rest).span =
      infixFoldSpan file left.span (rest.map Prod.snd) := by
  induction rest generalizing left with
  | nil => rfl
  | cons pair tail inductionHypothesis =>
      rcases pair with ⟨operator, right⟩
      simp [RuleReduction.foldInfixLeft, infixFoldSpan,
        inductionHypothesis, RuleReduction.between]

@[simp] theorem infixFoldFocusedSpans_nil (left : Expression) :
    infixFoldFocusedSpans left [] = [left.span] := by
  rfl

@[simp] theorem infixFoldFocusedSpans_cons
    (left : Expression) (operator : Located InfixOperator)
    (right : Expression)
    (rest : List (Located InfixOperator × Expression)) :
    infixFoldFocusedSpans left ((operator, right) :: rest) =
      left.span :: operator.span :: right.span ::
        rest.flatMap fun pair => [pair.1.span, pair.2.span] := by
  rfl

private theorem infixStep_fragment
    {file : WorkspaceFile}
    (left : Expression) (operator : Located InfixOperator)
    (right : Expression) :
    LocationFragment.ofExpression
        (RuleReduction.between file left.span right.span
          (.infix operator left right)) =
      LocationFragment.located
        (RuleReduction.between file left.span right.span ()).span
        [LocationFragment.merge [
          LocationFragment.leaf operator.span,
          LocationFragment.ofExpression left,
          LocationFragment.ofExpression right]] := by
  simp [RuleReduction.between, LocationFragment.ofExpressionPayload]

/-- Replacing the first three anchors of an ordered infix focus by their
synthetic first-to-third interval preserves source order. -/
private theorem ordered_between_cons
    {file : WorkspaceFile} {tokens : List Token}
    (left operator right : SourceAnchor file tokens)
    (tail : SourceAnchorTrace file tokens)
    (ordered : SourceAnchorTrace.Ordered
      (left :: operator :: right :: tail)) :
    let originsOrdered : left.origin.val ≤ right.origin.val :=
      Nat.le_trans left.occupied.1.2.1
        (by
          have := ordered
          simp only [SourceAnchorTrace.Ordered, List.pairwise_cons] at this
          exact this.1 right (by simp))
    SourceAnchorTrace.Ordered
      (SourceAnchor.between left right originsOrdered :: tail) := by
  simp only [SourceAnchorTrace.Ordered, List.pairwise_cons] at ordered ⊢
  rcases ordered with
    ⟨_leftBefore, _operatorBefore, rightBefore, tailOrdered⟩
  refine ⟨?_, tailOrdered⟩
  intro later member
  change right.finish.val ≤ later.origin.val
  exact rightBefore later member

/-- Replacing the first three anchors of an infix focus by their synthetic
first-to-third interval preserves containment in the enclosing rule. -/
private theorem within_between_cons
    {file : WorkspaceFile} {tokens : List Token}
    (left operator right : SourceAnchor file tokens)
    (tail : SourceAnchorTrace file tokens)
    (origin finish : Boundary tokens)
    (inside : SourceAnchorTrace.Within
      (left :: operator :: right :: tail) origin finish)
    (originsOrdered : left.origin.val ≤ right.origin.val) :
    SourceAnchorTrace.Within
      (SourceAnchor.between left right originsOrdered :: tail)
      origin finish := by
  simp only [SourceAnchorTrace.within_cons] at inside ⊢
  exact ⟨⟨inside.1.1, inside.2.2.1.2⟩, inside.2.2.2⟩

/-- The three direct children introduced by one infix step fit inside the
synthetic first-to-third source anchor. -/
private theorem infixStep_children_contained
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (left operator right : SourceAnchor file tokens)
    (ordered : SourceAnchorTrace.Ordered [left, operator, right]) :
    let originsOrdered : left.origin.val ≤ right.origin.val :=
      Nat.le_trans left.occupied.1.2.1
        (by
          have := ordered
          simp only [SourceAnchorTrace.Ordered, List.pairwise_cons] at this
          exact this.1 right (by simp))
    (LocationFragment.merge [
      LocationFragment.leaf operator.span,
      LocationFragment.raw left.span,
      LocationFragment.raw right.span]).RootsContainedBy
        (SourceAnchor.between left right originsOrdered).span := by
  dsimp
  have viewed := ordered
  simp only [SourceAnchorTrace.Ordered, List.pairwise_cons] at viewed
  rcases viewed with ⟨leftBefore, operatorBefore, _rightBefore⟩
  have leftToRight : left.origin.val ≤ right.origin.val :=
    Nat.le_trans left.occupied.1.2.1 (leftBefore right (by simp))
  let outer := SourceAnchor.between left right leftToRight
  have rightOrdered : right.origin.val ≤ right.finish.val :=
    right.occupied.1.2.1
  have leftInside : left.Within outer.origin outer.finish :=
    ⟨Nat.le_refl _,
      Nat.le_trans (leftBefore right (by simp)) rightOrdered⟩
  have operatorInside : operator.Within outer.origin outer.finish :=
    ⟨Nat.le_trans left.occupied.1.2.1
        (leftBefore operator (by simp)),
      Nat.le_trans (operatorBefore right (by simp)) rightOrdered⟩
  have rightInside : right.Within outer.origin outer.finish :=
    ⟨leftToRight, Nat.le_refl _⟩
  intro span member
  simp [LocationFragment.leaf] at member
  rcases member with rfl | rfl | rfl
  · exact operator.containedBy tokensOrdered outer.occupied.1 operatorInside
  · exact left.containedBy tokensOrdered outer.occupied.1 leftInside
  · exact right.containedBy tokensOrdered outer.occupied.1 rightInside

/-- Fold one focused infix trace while preserving the enclosing physical
trace.  Occurrence hypotheses only identify fragments already present in the
original rule input; the focused anchors supply their source order. -/
private theorem foldInfixLeft_locationEvidence
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {origin finish : Boundary tokens}
    {inputFragment : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      inputFragment trace)
    (left : Expression)
    (rest : List (Located InfixOperator × Expression))
    (leftEvidence : IntervalLocationEvidence file tokens origin finish
      (LocationFragment.ofExpression left) trace)
    (operatorFromInput : ∀ pair, pair ∈ rest →
      (LocationFragment.leaf pair.1.span).IsSubfragmentOf inputFragment)
    (rightFromInput : ∀ pair, pair ∈ rest →
      (LocationFragment.ofExpression pair.2).IsSubfragmentOf inputFragment)
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans = infixFoldFocusedSpans left rest)
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered) :
    IntervalLocationEvidence file tokens origin finish
      (LocationFragment.ofExpression
        (RuleReduction.foldInfixLeft file left rest)) trace := by
  induction rest generalizing left anchors with
  | nil =>
      simpa [RuleReduction.foldInfixLeft] using leftEvidence
  | cons pair tail inductionHypothesis =>
      rcases pair with ⟨operator, right⟩
      cases anchors with
      | nil =>
          simp [infixFoldFocusedSpans] at anchorSpans
      | cons leftAnchor remaining =>
          cases remaining with
          | nil =>
              simp [infixFoldFocusedSpans] at anchorSpans
          | cons operatorAnchor remaining =>
              cases remaining with
              | nil =>
                  simp [infixFoldFocusedSpans] at anchorSpans
              | cons rightAnchor tailAnchors =>
                  simp only [SourceAnchorTrace.spans_cons,
                    infixFoldFocusedSpans_cons, List.cons.injEq] at anchorSpans
                  rcases anchorSpans with
                    ⟨leftSpan, operatorSpan, rightSpan, tailSpans⟩
                  have headOrdered : SourceAnchorTrace.Ordered
                      [leftAnchor, operatorAnchor, rightAnchor] :=
                    List.Pairwise.sublist (by simp) anchorsOrdered
                  have leftToRight :
                      leftAnchor.origin.val ≤ rightAnchor.origin.val :=
                    Nat.le_trans leftAnchor.occupied.1.2.1 (by
                      have viewed := headOrdered
                      simp only [SourceAnchorTrace.Ordered,
                        List.pairwise_cons] at viewed
                      exact viewed.1 rightAnchor (by simp))
                  let nextAnchor := SourceAnchor.between leftAnchor rightAnchor
                    leftToRight
                  let nextExpression := RuleReduction.between file left.span
                    right.span (ExpressionPayload.infix operator left right)
                  have nextSpan : nextAnchor.span = nextExpression.span := by
                    simp [nextAnchor, nextExpression, RuleReduction.between,
                      leftSpan, rightSpan]
                  have operatorEvidence := IntervalLocationEvidence.restrict
                    (operatorFromInput (operator, right) (by simp))
                      inputEvidence
                  have rightEvidence := IntervalLocationEvidence.restrict
                    (rightFromInput (operator, right) (by simp)) inputEvidence
                  have leftRightEvidence :=
                    IntervalLocationEvidence.mergeSameInterval
                      leftEvidence rightEvidence
                  have stepChildrenRaw :=
                    IntervalLocationEvidence.mergeSameInterval
                      operatorEvidence leftRightEvidence
                  have stepChildren : IntervalLocationEvidence file tokens
                      origin finish
                      (LocationFragment.merge [
                        LocationFragment.leaf operator.span,
                        LocationFragment.ofExpression left,
                        LocationFragment.ofExpression right]) trace := by
                    apply IntervalLocationEvidence.replaceFragment _
                      stepChildrenRaw
                    apply LocationFragment.eq_of_fields <;> simp
                  have childrenContained :
                      (LocationFragment.merge [
                        LocationFragment.leaf operator.span,
                        LocationFragment.ofExpression left,
                        LocationFragment.ofExpression right]).RootsContainedBy
                          nextAnchor.span := by
                    have basic := infixStep_children_contained tokensOrdered
                      leftAnchor operatorAnchor rightAnchor headOrdered
                    intro span member
                    simp [LocationFragment.leaf] at member
                    rcases member with rfl | rfl | rfl
                    · simpa [nextAnchor, operatorSpan] using
                        basic operatorAnchor.span (by
                          simp [LocationFragment.leaf])
                    · simpa [nextAnchor, leftSpan] using
                        basic leftAnchor.span (by
                          simp [LocationFragment.leaf])
                    · simpa [nextAnchor, rightSpan] using
                        basic rightAnchor.span (by
                          simp [LocationFragment.leaf])
                  have nextInside : nextAnchor.Within origin finish := by
                    have replaced := within_between_cons leftAnchor
                      operatorAnchor rightAnchor tailAnchors origin finish
                        anchorsWithin leftToRight
                    exact replaced nextAnchor (by simp [nextAnchor])
                  have wrapped := IntervalLocationEvidence.locatedInside
                    tokensOrdered nextAnchor stepChildren nextInside
                      childrenContained
                  have nextEvidence : IntervalLocationEvidence file tokens
                      origin finish
                      (LocationFragment.ofExpression nextExpression) trace := by
                    apply IntervalLocationEvidence.replaceFragment _ wrapped
                    calc
                      LocationFragment.located nextAnchor.span
                          [LocationFragment.merge [
                            LocationFragment.leaf operator.span,
                            LocationFragment.ofExpression left,
                            LocationFragment.ofExpression right]] =
                        LocationFragment.located nextExpression.span
                          [LocationFragment.merge [
                            LocationFragment.leaf operator.span,
                            LocationFragment.ofExpression left,
                            LocationFragment.ofExpression right]] := by
                              rw [nextSpan]
                      _ = LocationFragment.ofExpression nextExpression :=
                        (infixStep_fragment left operator right).symm
                  have nextAnchorSpans :
                      SourceAnchorTrace.spans (nextAnchor :: tailAnchors) =
                        infixFoldFocusedSpans nextExpression tail := by
                    rw [SourceAnchorTrace.spans_cons,
                      infixFoldFocusedSpans, nextSpan, tailSpans]
                  have nextWithin : SourceAnchorTrace.Within
                      (nextAnchor :: tailAnchors) origin finish :=
                    within_between_cons leftAnchor operatorAnchor rightAnchor
                      tailAnchors origin finish anchorsWithin leftToRight
                  have nextOrdered : SourceAnchorTrace.Ordered
                      (nextAnchor :: tailAnchors) := by
                    simpa [nextAnchor] using
                      (ordered_between_cons leftAnchor operatorAnchor
                        rightAnchor tailAnchors anchorsOrdered)
                  have tailOperatorFromInput : ∀ pair, pair ∈ tail →
                      (LocationFragment.leaf pair.1.span).IsSubfragmentOf
                        inputFragment := by
                    intro candidate member
                    exact operatorFromInput candidate (by simp [member])
                  have tailRightFromInput : ∀ pair, pair ∈ tail →
                      (LocationFragment.ofExpression pair.2).IsSubfragmentOf
                        inputFragment := by
                    intro candidate member
                    exact rightFromInput candidate (by simp [member])
                  simpa [RuleReduction.foldInfixLeft, nextExpression] using
                    inductionHypothesis nextExpression nextEvidence
                      tailOperatorFromInput tailRightFromInput
                      (nextAnchor :: tailAnchors) nextAnchorSpans nextWithin
                        nextOrdered

/-- The same focused infix trace determines one occupied anchor for the
eventual folded expression.  This is the action-facing half of the fold
proof: it lets a coherent focus retain the result as a principal child of a
later expression reduction. -/
theorem foldInfixLeft_principalFocusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (left : Expression)
    (rest : List (Located InfixOperator × Expression))
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans = infixFoldFocusedSpans left rest)
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered) :
    ∃ principal : SourceAnchorTrace file tokens,
      principal.spans =
          [(RuleReduction.foldInfixLeft file left rest).span] ∧
        principal.Within origin finish ∧ principal.Ordered := by
  induction rest generalizing left anchors with
  | nil =>
      cases anchors with
      | nil =>
          simp [infixFoldFocusedSpans] at anchorSpans
      | cons leftAnchor tailAnchors =>
          cases tailAnchors with
          | nil =>
              have leftSpan : leftAnchor.span = left.span := by
                simpa [infixFoldFocusedSpans] using anchorSpans
              refine ⟨[leftAnchor], ?_, ?_,
                SourceAnchorTrace.ordered_singleton leftAnchor⟩
              · simp [RuleReduction.foldInfixLeft, leftSpan]
              · intro anchor member
                exact anchorsWithin anchor member
          | cons nextAnchor tail =>
              simp [infixFoldFocusedSpans] at anchorSpans
  | cons pair tail inductionHypothesis =>
      rcases pair with ⟨operator, right⟩
      cases anchors with
      | nil =>
          simp [infixFoldFocusedSpans] at anchorSpans
      | cons leftAnchor remaining =>
          cases remaining with
          | nil =>
              simp [infixFoldFocusedSpans] at anchorSpans
          | cons operatorAnchor remaining =>
              cases remaining with
              | nil =>
                  simp [infixFoldFocusedSpans] at anchorSpans
              | cons rightAnchor tailAnchors =>
                  simp only [SourceAnchorTrace.spans_cons,
                    infixFoldFocusedSpans_cons, List.cons.injEq]
                      at anchorSpans
                  rcases anchorSpans with
                    ⟨leftSpan, _operatorSpan, rightSpan, tailSpans⟩
                  have headOrdered : SourceAnchorTrace.Ordered
                      [leftAnchor, operatorAnchor, rightAnchor] :=
                    List.Pairwise.sublist (by simp) anchorsOrdered
                  have leftToRight :
                      leftAnchor.origin.val ≤ rightAnchor.origin.val :=
                    Nat.le_trans leftAnchor.occupied.1.2.1 (by
                      have viewed := headOrdered
                      simp only [SourceAnchorTrace.Ordered,
                        List.pairwise_cons] at viewed
                      exact viewed.1 rightAnchor (by simp))
                  let nextAnchor := SourceAnchor.between leftAnchor
                    rightAnchor leftToRight
                  let nextExpression := RuleReduction.between file left.span
                    right.span (ExpressionPayload.infix operator left right)
                  have nextSpan : nextAnchor.span = nextExpression.span := by
                    simp [nextAnchor, nextExpression, RuleReduction.between,
                      leftSpan, rightSpan]
                  have nextAnchorSpans : SourceAnchorTrace.spans
                      (nextAnchor :: tailAnchors) =
                        infixFoldFocusedSpans nextExpression tail := by
                    rw [SourceAnchorTrace.spans_cons,
                      infixFoldFocusedSpans, nextSpan, tailSpans]
                  have nextWithin : SourceAnchorTrace.Within
                      (nextAnchor :: tailAnchors) origin finish :=
                    within_between_cons leftAnchor operatorAnchor rightAnchor
                      tailAnchors origin finish anchorsWithin leftToRight
                  have nextOrdered : SourceAnchorTrace.Ordered
                      (nextAnchor :: tailAnchors) := by
                    simpa [nextAnchor] using
                      (ordered_between_cons leftAnchor operatorAnchor
                        rightAnchor tailAnchors anchorsOrdered)
                  simpa [RuleReduction.foldInfixLeft, nextExpression] using
                    inductionHypothesis nextExpression
                      (nextAnchor :: tailAnchors) nextAnchorSpans nextWithin
                        nextOrdered

private theorem mappedInfix_locationSound_of_focusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {origin finish : Boundary tokens}
    {expression : EbnfExpr}
    {input : EbnfValue file tokens expression}
    {inputFragment : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    {sourcePart : Type}
    (left : Expression) (rest : List sourcePart)
    (toFold : sourcePart → Located InfixOperator × Expression)
    (leftInside : EbnfValue.ContainsLocationFragment file tokens input
      (LocationFragment.ofExpression left))
    (operatorInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens input
        (LocationFragment.leaf (toFold part).1.span))
    (rightInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens input
        (LocationFragment.ofExpression (toFold part).2))
    (inputFragmentShape : input.locationFragment = inputFragment)
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      inputFragment trace)
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans =
      infixFoldFocusedSpans left (rest.map toFold))
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered) :
    IntervalLocationEvidence file tokens origin finish
      (LocationFragment.ofExpression
        (RuleReduction.foldInfixLeft file left (rest.map toFold))) trace := by
  have normalizedInput : IntervalLocationEvidence file tokens origin finish
      input.locationFragment trace :=
    IntervalLocationEvidence.replaceFragment inputFragmentShape.symm
      inputEvidence
  have leftEvidence := IntervalLocationEvidence.restrict
    leftInside.locationFragment_isSubfragment normalizedInput
  have operatorFromInput : ∀ pair, pair ∈ rest.map toFold →
      (LocationFragment.leaf pair.1.span).IsSubfragmentOf
        input.locationFragment := by
    intro pair member
    rcases List.mem_map.mp member with ⟨part, partMember, rfl⟩
    exact (operatorInside part partMember).locationFragment_isSubfragment
  have rightFromInput : ∀ pair, pair ∈ rest.map toFold →
      (LocationFragment.ofExpression pair.2).IsSubfragmentOf
        input.locationFragment := by
    intro pair member
    rcases List.mem_map.mp member with ⟨part, partMember, rfl⟩
    exact (rightInside part partMember).locationFragment_isSubfragment
  exact foldInfixLeft_locationEvidence tokensOrdered normalizedInput left
    (rest.map toFold) leftEvidence operatorFromInput rightFromInput anchors
      anchorSpans anchorsWithin anchorsOrdered

/-- Source-level interval transformation for the logical-or fold once its
focused coherent anchors have been exposed. -/
theorem logicalOr_locationSound_of_focusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (left : Expression)
    (rest : List
      (MatchedTerminal file tokens (.symbol .logicalOr) × Expression))
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans =
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.logicalOr value.1),
            value.2)))
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered)
    {trace : SourceAnchorTrace file tokens}
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.logicalOr origin finish left rest)) trace) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .logicalOr
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.logicalOr value.1),
              value.2))))
      trace := by
  let reduction := RuleReduction.logicalOr origin finish left rest
  let foldedRest := rest.map fun value =>
    (RuleReduction.infixOperator value.1 (.logicalOr value.1), value.2)
  have leftInside : EbnfValue.ContainsLocationFragment file tokens
      (inputValue reduction) (LocationFragment.ofExpression left) := by
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .logicalAnd left
  have leftEvidence := IntervalLocationEvidence.restrict
    leftInside.locationFragment_isSubfragment inputEvidence
  have operatorFromInput : ∀ pair, pair ∈ foldedRest →
      (LocationFragment.leaf pair.1.span).IsSubfragmentOf
        (inputLocationFragment reduction) := by
    intro pair member
    rcases List.mem_map.mp member with ⟨sourcePair, sourceMember, rfl⟩
    have inside : EbnfValue.ContainsLocationFragment file tokens
        (inputValue reduction) sourcePair.1.locationFragment := by
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
        (List.mem_map_of_mem sourceMember)
      apply EbnfValue.ContainsLocationFragment.group
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ sourcePair.1
    simpa [RuleReduction.infixOperator, RuleReduction.terminalLoc,
      LocationFragment.leaf, MatchedTerminal.locationFragment] using
        inside.locationFragment_isSubfragment
  have rightFromInput : ∀ pair, pair ∈ foldedRest →
      (LocationFragment.ofExpression pair.2).IsSubfragmentOf
        (inputLocationFragment reduction) := by
    intro pair member
    rcases List.mem_map.mp member with ⟨sourcePair, sourceMember, rfl⟩
    have inside : EbnfValue.ContainsLocationFragment file tokens
        (inputValue reduction)
        (LocationFragment.ofExpression sourcePair.2) := by
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
        (List.mem_map_of_mem sourceMember)
      apply EbnfValue.ContainsLocationFragment.group
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.rule .logicalAnd sourcePair.2
    exact inside.locationFragment_isSubfragment
  simpa [reduction, foldedRest, RuleLocationView.ofRuleValue] using
    foldInfixLeft_locationEvidence tokensOrdered inputEvidence left foldedRest
      leftEvidence operatorFromInput rightFromInput anchors anchorSpans
        anchorsWithin anchorsOrdered

/-- Source-level interval transformation for the logical-and fold. -/
theorem logicalAnd_locationSound_of_focusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens) (left : Expression)
    (rest : List
      (MatchedTerminal file tokens (.symbol .logicalAnd) × Expression))
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans =
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.logicalAnd value.1),
            value.2)))
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered)
    {trace : SourceAnchorTrace file tokens}
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.logicalAnd origin finish left rest)) trace) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .logicalAnd
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.logicalAnd value.1),
              value.2)))) trace := by
  let reduction := RuleReduction.logicalAnd origin finish left rest
  let toFold := fun value :
      MatchedTerminal file tokens (.symbol .logicalAnd) × Expression =>
    (RuleReduction.infixOperator value.1 (.logicalAnd value.1), value.2)
  have leftInside : EbnfValue.ContainsLocationFragment file tokens
      (inputValue reduction) (LocationFragment.ofExpression left) := by
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .equality left
  have operatorInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens (inputValue reduction)
        (LocationFragment.leaf (toFold part).1.span) := by
    intro part member
    have inside : EbnfValue.ContainsLocationFragment file tokens
        (inputValue reduction) part.1.locationFragment := by
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
        (List.mem_map_of_mem member)
      apply EbnfValue.ContainsLocationFragment.group
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ part.1
    simpa [toFold, RuleReduction.infixOperator,
      RuleReduction.terminalLoc, LocationFragment.leaf,
      MatchedTerminal.locationFragment] using inside
  have rightInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens (inputValue reduction)
        (LocationFragment.ofExpression (toFold part).2) := by
    intro part member
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.star
      (List.mem_map_of_mem member)
    apply EbnfValue.ContainsLocationFragment.group
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .equality part.2
  simpa [reduction, toFold, RuleLocationView.ofRuleValue] using
    mappedInfix_locationSound_of_focusedAnchors tokensOrdered left rest toFold
      leftInside operatorInside rightInside rfl inputEvidence anchors
        anchorSpans anchorsWithin anchorsOrdered

/-- Source-level interval transformation for the bitwise-or fold. -/
theorem bitOr_locationSound_of_focusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens) (left : Expression)
    (rest : List
      (MatchedTerminal file tokens (.symbol .pipe) × Expression))
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans =
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.bitOr value.1), value.2)))
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered)
    {trace : SourceAnchorTrace file tokens}
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.bitOr origin finish left rest)) trace) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .bitOr
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.bitOr value.1),
              value.2)))) trace := by
  let reduction := RuleReduction.bitOr origin finish left rest
  let toFold := fun value :
      MatchedTerminal file tokens (.symbol .pipe) × Expression =>
    (RuleReduction.infixOperator value.1 (.bitOr value.1), value.2)
  have leftInside : EbnfValue.ContainsLocationFragment file tokens
      (inputValue reduction) (LocationFragment.ofExpression left) := by
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .bitXor left
  have operatorInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens (inputValue reduction)
        (LocationFragment.leaf (toFold part).1.span) := by
    intro part member
    have inside : EbnfValue.ContainsLocationFragment file tokens
        (inputValue reduction) part.1.locationFragment := by
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
        (List.mem_map_of_mem member)
      apply EbnfValue.ContainsLocationFragment.group
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ part.1
    simpa [toFold, RuleReduction.infixOperator,
      RuleReduction.terminalLoc, LocationFragment.leaf,
      MatchedTerminal.locationFragment] using inside
  have rightInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens (inputValue reduction)
        (LocationFragment.ofExpression (toFold part).2) := by
    intro part member
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.star
      (List.mem_map_of_mem member)
    apply EbnfValue.ContainsLocationFragment.group
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .bitXor part.2
  simpa [reduction, toFold, RuleLocationView.ofRuleValue] using
    mappedInfix_locationSound_of_focusedAnchors tokensOrdered left rest toFold
      leftInside operatorInside rightInside rfl inputEvidence anchors
        anchorSpans anchorsWithin anchorsOrdered

/-- Source-level interval transformation for the bitwise-xor fold. -/
theorem bitXor_locationSound_of_focusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens) (left : Expression)
    (rest : List
      (MatchedTerminal file tokens (.symbol .caret) × Expression))
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans =
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.bitXor value.1), value.2)))
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered)
    {trace : SourceAnchorTrace file tokens}
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.bitXor origin finish left rest)) trace) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .bitXor
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.bitXor value.1),
              value.2)))) trace := by
  let reduction := RuleReduction.bitXor origin finish left rest
  let toFold := fun value :
      MatchedTerminal file tokens (.symbol .caret) × Expression =>
    (RuleReduction.infixOperator value.1 (.bitXor value.1), value.2)
  have leftInside : EbnfValue.ContainsLocationFragment file tokens
      (inputValue reduction) (LocationFragment.ofExpression left) := by
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .bitAnd left
  have operatorInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens (inputValue reduction)
        (LocationFragment.leaf (toFold part).1.span) := by
    intro part member
    have inside : EbnfValue.ContainsLocationFragment file tokens
        (inputValue reduction) part.1.locationFragment := by
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
        (List.mem_map_of_mem member)
      apply EbnfValue.ContainsLocationFragment.group
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ part.1
    simpa [toFold, RuleReduction.infixOperator,
      RuleReduction.terminalLoc, LocationFragment.leaf,
      MatchedTerminal.locationFragment] using inside
  have rightInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens (inputValue reduction)
        (LocationFragment.ofExpression (toFold part).2) := by
    intro part member
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.star
      (List.mem_map_of_mem member)
    apply EbnfValue.ContainsLocationFragment.group
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .bitAnd part.2
  simpa [reduction, toFold, RuleLocationView.ofRuleValue] using
    mappedInfix_locationSound_of_focusedAnchors tokensOrdered left rest toFold
      leftInside operatorInside rightInside rfl inputEvidence anchors
        anchorSpans anchorsWithin anchorsOrdered

/-- Source-level interval transformation for the bitwise-and fold. -/
theorem bitAnd_locationSound_of_focusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens) (left : Expression)
    (rest : List
      (MatchedTerminal file tokens (.symbol .amp) × Expression))
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans =
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.bitAnd value.1), value.2)))
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered)
    {trace : SourceAnchorTrace file tokens}
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.bitAnd origin finish left rest)) trace) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .bitAnd
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.bitAnd value.1),
              value.2)))) trace := by
  let reduction := RuleReduction.bitAnd origin finish left rest
  let toFold := fun value :
      MatchedTerminal file tokens (.symbol .amp) × Expression =>
    (RuleReduction.infixOperator value.1 (.bitAnd value.1), value.2)
  have leftInside : EbnfValue.ContainsLocationFragment file tokens
      (inputValue reduction) (LocationFragment.ofExpression left) := by
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .additive left
  have operatorInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens (inputValue reduction)
        (LocationFragment.leaf (toFold part).1.span) := by
    intro part member
    have inside : EbnfValue.ContainsLocationFragment file tokens
        (inputValue reduction) part.1.locationFragment := by
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
        (List.mem_map_of_mem member)
      apply EbnfValue.ContainsLocationFragment.group
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ part.1
    simpa [toFold, RuleReduction.infixOperator,
      RuleReduction.terminalLoc, LocationFragment.leaf,
      MatchedTerminal.locationFragment] using inside
  have rightInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens (inputValue reduction)
        (LocationFragment.ofExpression (toFold part).2) := by
    intro part member
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.star
      (List.mem_map_of_mem member)
    apply EbnfValue.ContainsLocationFragment.group
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .additive part.2
  simpa [reduction, toFold, RuleLocationView.ofRuleValue] using
    mappedInfix_locationSound_of_focusedAnchors tokensOrdered left rest toFold
      leftInside operatorInside rightInside rfl inputEvidence anchors
        anchorSpans anchorsWithin anchorsOrdered

/-- Source-level interval transformation for the additive fold. -/
theorem additive_locationSound_of_focusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens) (left : Expression)
    (rest : List
      (Sum
        (MatchedTerminal file tokens (.symbol .plus))
        (MatchedTerminal file tokens (.symbol .minus)) × Expression))
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans =
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (match value.1 with
            | .inl plus =>
                RuleReduction.infixOperator plus (.add plus)
            | .inr minus =>
                RuleReduction.infixOperator minus (.subtract minus),
            value.2)))
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered)
    {trace : SourceAnchorTrace file tokens}
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.additive origin finish left rest)) trace) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .additive
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (match value.1 with
              | .inl plus =>
                  RuleReduction.infixOperator plus (.add plus)
              | .inr minus =>
                  RuleReduction.infixOperator minus (.subtract minus),
              value.2)))) trace := by
  let reduction := RuleReduction.additive origin finish left rest
  let toFold := fun value :
      Sum
        (MatchedTerminal file tokens (.symbol .plus))
        (MatchedTerminal file tokens (.symbol .minus)) × Expression =>
    (match value.1 with
      | .inl plus => RuleReduction.infixOperator plus (.add plus)
      | .inr minus => RuleReduction.infixOperator minus (.subtract minus),
      value.2)
  have leftInside : EbnfValue.ContainsLocationFragment file tokens
      (inputValue reduction) (LocationFragment.ofExpression left) := by
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .multiplicative left
  have operatorInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens (inputValue reduction)
        (LocationFragment.leaf (toFold part).1.span) := by
    intro part member
    rcases part with ⟨operator, right⟩
    cases operator with
    | inl plus =>
        have inside : EbnfValue.ContainsLocationFragment file tokens
            (inputValue reduction) plus.locationFragment := by
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.star
            (List.mem_map_of_mem member)
          apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
          exact EbnfValue.ContainsLocationFragment.terminal _ plus
        simpa [toFold, RuleReduction.infixOperator,
          RuleReduction.terminalLoc, LocationFragment.leaf,
          MatchedTerminal.locationFragment] using inside
    | inr minus =>
        have inside : EbnfValue.ContainsLocationFragment file tokens
            (inputValue reduction) minus.locationFragment := by
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.star
            (List.mem_map_of_mem member)
          apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
          exact EbnfValue.ContainsLocationFragment.terminal _ minus
        simpa [toFold, RuleReduction.infixOperator,
          RuleReduction.terminalLoc, LocationFragment.leaf,
          MatchedTerminal.locationFragment] using inside
  have rightInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens (inputValue reduction)
        (LocationFragment.ofExpression (toFold part).2) := by
    intro part member
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.star
      (List.mem_map_of_mem member)
    apply EbnfValue.ContainsLocationFragment.group
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .multiplicative part.2
  simpa [reduction, toFold, RuleLocationView.ofRuleValue] using
    mappedInfix_locationSound_of_focusedAnchors tokensOrdered left rest toFold
      leftInside operatorInside rightInside rfl inputEvidence anchors
        anchorSpans anchorsWithin anchorsOrdered

/-- Source-level interval transformation for the multiplicative fold. -/
theorem multiplicative_locationSound_of_focusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens) (left : Expression)
    (rest : List
      (Sum
        (MatchedTerminal file tokens (.symbol .star))
        (Sum
          (MatchedTerminal file tokens (.symbol .slash))
          (MatchedTerminal file tokens (.symbol .percent))) × Expression))
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans =
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (match value.1 with
            | .inl star =>
                RuleReduction.infixOperator star (.multiply star)
            | .inr (.inl slash) =>
                RuleReduction.infixOperator slash (.divide slash)
            | .inr (.inr percent) =>
                RuleReduction.infixOperator percent (.modulo percent),
            value.2)))
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered)
    {trace : SourceAnchorTrace file tokens}
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.multiplicative origin finish left rest)) trace) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .multiplicative
        (RuleReduction.foldInfixLeft file left
          (rest.map fun value =>
            (match value.1 with
              | .inl star =>
                  RuleReduction.infixOperator star (.multiply star)
              | .inr (.inl slash) =>
                  RuleReduction.infixOperator slash (.divide slash)
              | .inr (.inr percent) =>
                  RuleReduction.infixOperator percent (.modulo percent),
              value.2)))) trace := by
  let reduction := RuleReduction.multiplicative origin finish left rest
  let toFold := fun value :
      Sum
        (MatchedTerminal file tokens (.symbol .star))
        (Sum
          (MatchedTerminal file tokens (.symbol .slash))
          (MatchedTerminal file tokens (.symbol .percent))) × Expression =>
    (match value.1 with
      | .inl star => RuleReduction.infixOperator star (.multiply star)
      | .inr (.inl slash) =>
          RuleReduction.infixOperator slash (.divide slash)
      | .inr (.inr percent) =>
          RuleReduction.infixOperator percent (.modulo percent),
      value.2)
  have leftInside : EbnfValue.ContainsLocationFragment file tokens
      (inputValue reduction) (LocationFragment.ofExpression left) := by
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .prefix left
  have operatorInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens (inputValue reduction)
        (LocationFragment.leaf (toFold part).1.span) := by
    intro part member
    rcases part with ⟨operator, right⟩
    rcases operator with star | operator
    · have inside : EbnfValue.ContainsLocationFragment file tokens
          (inputValue reduction) star.locationFragment := by
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.tail
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.star
          (List.mem_map_of_mem member)
        apply EbnfValue.ContainsLocationFragment.group
        apply EbnfValue.ContainsLocationFragment.sequence
        apply EbnfValues.ContainsLocationFragment.head
        apply EbnfValue.ContainsLocationFragment.group
        apply EbnfValue.ContainsLocationFragment.choice ⟨0, by decide⟩
        exact EbnfValue.ContainsLocationFragment.terminal _ star
      simpa [toFold, RuleReduction.infixOperator,
        RuleReduction.terminalLoc, LocationFragment.leaf,
        MatchedTerminal.locationFragment] using inside
    · rcases operator with slash | percent
      · have inside : EbnfValue.ContainsLocationFragment file tokens
            (inputValue reduction) slash.locationFragment := by
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.star
            (List.mem_map_of_mem member)
          apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.choice ⟨1, by decide⟩
          exact EbnfValue.ContainsLocationFragment.terminal _ slash
        simpa [toFold, RuleReduction.infixOperator,
          RuleReduction.terminalLoc, LocationFragment.leaf,
          MatchedTerminal.locationFragment] using inside
      · have inside : EbnfValue.ContainsLocationFragment file tokens
            (inputValue reduction) percent.locationFragment := by
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.tail
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.star
            (List.mem_map_of_mem member)
          apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.sequence
          apply EbnfValues.ContainsLocationFragment.head
          apply EbnfValue.ContainsLocationFragment.group
          apply EbnfValue.ContainsLocationFragment.choice ⟨2, by decide⟩
          exact EbnfValue.ContainsLocationFragment.terminal _ percent
        simpa [toFold, RuleReduction.infixOperator,
          RuleReduction.terminalLoc, LocationFragment.leaf,
          MatchedTerminal.locationFragment] using inside
  have rightInside : ∀ part, part ∈ rest →
      EbnfValue.ContainsLocationFragment file tokens (inputValue reduction)
        (LocationFragment.ofExpression (toFold part).2) := by
    intro part member
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.star
      (List.mem_map_of_mem member)
    apply EbnfValue.ContainsLocationFragment.group
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .prefix part.2
  simpa [reduction, toFold, RuleLocationView.ofRuleValue] using
    mappedInfix_locationSound_of_focusedAnchors tokensOrdered left rest toFold
      leftInside operatorInside rightInside rfl inputEvidence anchors
        anchorSpans anchorsWithin anchorsOrdered

/-- Semantic locations retained below one folded postfix wrapper. -/
def postfixPartCore : PostfixPartValue → LocationFragment
  | .call _ arguments _ => LocationFragment.ofExpressionList arguments
  | .select _ field => LocationFragment.ofIdentifier field
  | .index _ index _ => LocationFragment.ofExpression index

/-- Focused spans before the final endpoint of one postfix part. -/
def postfixPartInitialFocusedSpans : PostfixPartValue → List SourceSpan
  | .call openParen arguments _ =>
      openParen :: arguments.map (fun argument => argument.span)
  | .select dot _ => [dot]
  | .index openBracket index _ => [openBracket, index.span]

/-- The final source endpoint used to extend a postfix receiver. -/
def postfixPartEndpointSpan : PostfixPartValue → SourceSpan
  | .call _ _ closeParen => closeParen
  | .select _ field => field.span
  | .index _ _ closeBracket => closeBracket

/-- Interleaved receiver, punctuation, semantic children, and final endpoints
for a complete postfix fold. -/
def postfixFoldFocusedSpans (receiver : Expression)
    (parts : List PostfixPartValue) : List SourceSpan :=
  receiver.span :: parts.flatMap fun part =>
    postfixPartInitialFocusedSpans part ++ [postfixPartEndpointSpan part]

@[simp] theorem postfixFoldFocusedSpans_nil (receiver : Expression) :
    postfixFoldFocusedSpans receiver [] = [receiver.span] := by
  rfl

@[simp] theorem postfixFoldFocusedSpans_cons
    (receiver : Expression) (part : PostfixPartValue)
    (rest : List PostfixPartValue) :
    postfixFoldFocusedSpans receiver (part :: rest) =
      receiver.span ::
        (postfixPartInitialFocusedSpans part ++
          postfixPartEndpointSpan part ::
            rest.flatMap fun remaining =>
              postfixPartInitialFocusedSpans remaining ++
                [postfixPartEndpointSpan remaining]) := by
  simp [postfixFoldFocusedSpans]

/-- Apply one postfix part without processing the remaining suffix. -/
def applyPostfixPart (file : WorkspaceFile)
    (receiver : Expression) : PostfixPartValue → Expression
  | .call _ arguments closeParen =>
      RuleReduction.between file receiver.span closeParen
        (.call receiver arguments)
  | .select _ field =>
      RuleReduction.between file receiver.span field.span
        (.select receiver field)
  | .index _ index closeBracket =>
      RuleReduction.between file receiver.span closeBracket
        (.index receiver index)

@[simp] private theorem foldPostfix_cons
    (file : WorkspaceFile) (receiver : Expression)
    (part : PostfixPartValue) (rest : List PostfixPartValue) :
    RuleReduction.foldPostfix file receiver (part :: rest) =
      RuleReduction.foldPostfix file (applyPostfixPart file receiver part)
        rest := by
  cases part <;> rfl

private theorem postfixStep_fragment
    (file : WorkspaceFile) (receiver : Expression)
    (part : PostfixPartValue) :
    LocationFragment.ofExpression (applyPostfixPart file receiver part) =
      LocationFragment.located
        (RuleReduction.between file receiver.span
          (postfixPartEndpointSpan part) ()).span
        [LocationFragment.merge [
          LocationFragment.ofExpression receiver,
          postfixPartCore part]] := by
  cases part <;>
    simp [applyPostfixPart, postfixPartCore, postfixPartEndpointSpan,
      RuleReduction.between, LocationFragment.ofExpressionPayload]

@[simp] private theorem ofExpressionList_roots
    (expressions : List Expression) :
    (LocationFragment.ofExpressionList expressions).roots =
      expressions.map (fun expression => expression.span) := by
  induction expressions with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [LocationFragment.ofExpressionList, inductionHypothesis]

private theorem ofExpressionList_eq_merge_map
    (expressions : List Expression) :
    LocationFragment.ofExpressionList expressions =
      LocationFragment.merge
        (expressions.map LocationFragment.ofExpression) := by
  induction expressions with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [LocationFragment.ofExpressionList, inductionHypothesis]
      apply LocationFragment.eq_of_fields <;> simp

private theorem postfixPartCore_subfragment
    (part : PostfixPartValue) :
    (postfixPartCore part).IsSubfragmentOf
      (RuleLocationView.ofPostfixPartValue part) := by
  cases part with
  | call openParen arguments closeParen =>
      rw [postfixPartCore, ofExpressionList_eq_merge_map]
      apply LocationFragment.IsSubfragmentOf.merge_map
      intro argument member
      apply LocationFragment.IsSubfragmentOf.of_mem_merge
      apply List.mem_append.mpr
      apply Or.inl
      apply List.mem_append.mpr
      apply Or.inr
      exact List.mem_map_of_mem member
  | select dot field =>
      apply LocationFragment.IsSubfragmentOf.of_mem_merge
      simp [postfixPartCore]
  | index openBracket index closeBracket =>
      apply LocationFragment.IsSubfragmentOf.of_mem_merge
      simp [postfixPartCore]

/-- Split an anchor trace at any prescribed split of its span list. -/
private theorem splitAnchors_of_spans_append
    {file : WorkspaceFile} {tokens : List Token}
    (anchors : SourceAnchorTrace file tokens)
    (leadingSpans trailingSpans : List SourceSpan)
    (shape : anchors.spans = leadingSpans ++ trailingSpans) :
    ∃ prefixAnchors suffixAnchors : SourceAnchorTrace file tokens,
      anchors = prefixAnchors ++ suffixAnchors ∧
        prefixAnchors.spans = leadingSpans ∧
          suffixAnchors.spans = trailingSpans := by
  induction leadingSpans generalizing anchors with
  | nil =>
      exact ⟨[], anchors, rfl, rfl, by simpa using shape⟩
  | cons span rest inductionHypothesis =>
      cases anchors with
      | nil => simp at shape
      | cons anchor tail =>
          simp only [SourceAnchorTrace.spans_cons, List.cons_append,
            List.cons.injEq] at shape
          rcases shape with ⟨headSpan, tailShape⟩
          rcases inductionHypothesis tail tailShape with
            ⟨prefixAnchors, suffixAnchors, anchorsShape, prefixShape,
              suffixShape⟩
          refine ⟨anchor :: prefixAnchors, suffixAnchors, ?_, ?_,
            suffixShape⟩
          · simp [anchorsShape]
          · simp [headSpan, prefixShape]

/-- Every anchor from an ordered first/middle/last trace is contained by the
synthetic source interval joining its endpoints. -/
private theorem anchors_contained_between
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (left right : SourceAnchor file tokens)
    (middle : SourceAnchorTrace file tokens)
    (ordered : SourceAnchorTrace.Ordered
      (left :: middle ++ [right])) :
    let originsOrdered : left.origin.val ≤ right.origin.val :=
      Nat.le_trans left.occupied.1.2.1 (by
        have split := (SourceAnchorTrace.ordered_append_iff
          [left] (middle ++ [right])).mp (by simpa using ordered)
        exact split.2.2 left (by simp) right (by simp))
    ∀ anchor ∈ left :: middle ++ [right],
      (SourceAnchor.between left right originsOrdered).span.Contains
        anchor.span := by
  dsimp
  have startSplit := (SourceAnchorTrace.ordered_append_iff
    [left] (middle ++ [right])).mp (by simpa using ordered)
  have finishSplit := (SourceAnchorTrace.ordered_append_iff
    (left :: middle) [right]).mp (by simpa using ordered)
  have leftToRight : left.origin.val ≤ right.origin.val :=
    Nat.le_trans left.occupied.1.2.1
      (startSplit.2.2 left (by simp) right (by simp))
  let outer := SourceAnchor.between left right leftToRight
  intro anchor member
  have startsInside : left.origin.val ≤ anchor.origin.val := by
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.le_refl _
    · exact Nat.le_trans left.occupied.1.2.1
        (startSplit.2.2 left (by simp) anchor later)
  have finishesInside : anchor.finish.val ≤ right.finish.val := by
    have viewed : anchor ∈ left :: middle ∨ anchor = right := by
      have reshaped : anchor ∈ (left :: middle) ++ [right] := by
        simpa only [List.cons_append] using member
      simpa only [List.mem_append, List.mem_singleton] using reshaped
    rcases viewed with earlier | rfl
    · exact Nat.le_trans
        (finishSplit.2.2 anchor earlier right (by simp))
        right.occupied.1.2.1
    · exact Nat.le_refl _
  exact anchor.containedBy tokensOrdered outer.occupied.1
    ⟨startsInside, finishesInside⟩

/-- Fold a postfix anchor trace while preserving the enclosing physical trace
and reusing only semantic children present in the original rule input. -/
private theorem foldPostfix_locationEvidence
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {origin finish : Boundary tokens}
    {inputFragment : LocationFragment}
    {trace : SourceAnchorTrace file tokens}
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      inputFragment trace)
    (receiver : Expression) (parts : List PostfixPartValue)
    (receiverEvidence : IntervalLocationEvidence file tokens origin finish
      (LocationFragment.ofExpression receiver) trace)
    (coreFromInput : ∀ part, part ∈ parts →
      (postfixPartCore part).IsSubfragmentOf inputFragment)
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans = postfixFoldFocusedSpans receiver parts)
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered) :
    IntervalLocationEvidence file tokens origin finish
      (LocationFragment.ofExpression
        (RuleReduction.foldPostfix file receiver parts)) trace := by
  induction parts generalizing receiver anchors with
  | nil =>
      simpa [RuleReduction.foldPostfix] using receiverEvidence
  | cons part tail inductionHypothesis =>
      cases anchors with
      | nil => simp [postfixFoldFocusedSpans] at anchorSpans
      | cons receiverAnchor remainingAnchors =>
          simp only [SourceAnchorTrace.spans_cons,
            postfixFoldFocusedSpans_cons, List.cons.injEq] at anchorSpans
          rcases anchorSpans with ⟨receiverSpan, remainingSpans⟩
          rcases splitAnchors_of_spans_append remainingAnchors
              (postfixPartInitialFocusedSpans part)
              (postfixPartEndpointSpan part ::
                tail.flatMap fun remaining =>
                  postfixPartInitialFocusedSpans remaining ++
                    [postfixPartEndpointSpan remaining]) remainingSpans with
            ⟨initialAnchors, endpointAndTail, remainingShape,
              initialSpans, endpointAndTailSpans⟩
          cases endpointAndTail with
          | nil => simp at endpointAndTailSpans
          | cons endpointAnchor tailAnchors =>
              simp only [SourceAnchorTrace.spans_cons, List.cons.injEq]
                at endpointAndTailSpans
              rcases endpointAndTailSpans with ⟨endpointSpan, tailSpans⟩
              subst remainingAnchors
              have endpointPairOrdered :
                  SourceAnchorTrace.Ordered [receiverAnchor, endpointAnchor] :=
                List.Pairwise.sublist (by simp) anchorsOrdered
              have receiverToEndpoint :
                  receiverAnchor.origin.val ≤ endpointAnchor.origin.val :=
                Nat.le_trans receiverAnchor.occupied.1.2.1 (by
                  have viewed := endpointPairOrdered
                  simp only [SourceAnchorTrace.Ordered,
                    List.pairwise_cons] at viewed
                  exact viewed.1 endpointAnchor (by simp))
              let nextAnchor := SourceAnchor.between receiverAnchor
                endpointAnchor receiverToEndpoint
              let nextExpression := applyPostfixPart file receiver part
              have nextSpan : nextAnchor.span = nextExpression.span := by
                cases part <;>
                  simp [nextAnchor, nextExpression, applyPostfixPart,
                    RuleReduction.between, receiverSpan, endpointSpan,
                    postfixPartEndpointSpan]
              have coreEvidence := IntervalLocationEvidence.restrict
                (coreFromInput part (by simp)) inputEvidence
              have stepChildren := IntervalLocationEvidence.mergeSameInterval
                receiverEvidence coreEvidence
              have focusedPrefixOrdered : SourceAnchorTrace.Ordered
                  (receiverAnchor :: initialAnchors ++ [endpointAnchor]) :=
                List.Pairwise.sublist (by simp) anchorsOrdered
              have focusedContained := anchors_contained_between tokensOrdered
                receiverAnchor endpointAnchor initialAnchors
                  focusedPrefixOrdered
              have childrenContained :
                  (LocationFragment.merge [
                    LocationFragment.ofExpression receiver,
                    postfixPartCore part]).RootsContainedBy
                      nextAnchor.span := by
                intro span member
                have spanMember : span ∈ SourceAnchorTrace.spans
                    (receiverAnchor :: initialAnchors ++
                      [endpointAnchor]) := by
                  simp only [SourceAnchorTrace.spans, List.map_cons,
                    List.map_append]
                  change span ∈ receiverAnchor.span ::
                    SourceAnchorTrace.spans initialAnchors ++
                      [endpointAnchor.span]
                  rw [initialSpans, receiverSpan, endpointSpan]
                  cases part with
                  | call openParen arguments closeParen =>
                      simp [postfixPartCore,
                        postfixPartInitialFocusedSpans,
                        postfixPartEndpointSpan] at member ⊢
                      rcases member with receiverMember | argumentMember
                      · exact Or.inl receiverMember
                      · exact Or.inr (Or.inr (Or.inl argumentMember))
                  | select dot field =>
                      simp [postfixPartCore,
                        postfixPartInitialFocusedSpans,
                        postfixPartEndpointSpan] at member ⊢
                      rcases member with receiverMember | fieldMember
                      · exact Or.inl receiverMember
                      · exact Or.inr (Or.inr fieldMember)
                  | index openBracket index closeBracket =>
                      simp [postfixPartCore,
                        postfixPartInitialFocusedSpans,
                        postfixPartEndpointSpan] at member ⊢
                      rcases member with receiverMember | indexMember
                      · exact Or.inl receiverMember
                      · exact Or.inr (Or.inr (Or.inl indexMember))
                rw [SourceAnchorTrace.spans, List.mem_map] at spanMember
                rcases spanMember with ⟨anchor, anchorMember, rfl⟩
                simpa [nextAnchor] using
                  focusedContained anchor anchorMember
              have nextInside : nextAnchor.Within origin finish := by
                refine ⟨?_, ?_⟩
                · exact (anchorsWithin receiverAnchor (by simp)).1
                · exact (anchorsWithin endpointAnchor (by simp)).2
              have wrapped := IntervalLocationEvidence.locatedInside
                tokensOrdered nextAnchor stepChildren nextInside
                  childrenContained
              have nextEvidence : IntervalLocationEvidence file tokens
                  origin finish
                  (LocationFragment.ofExpression nextExpression) trace := by
                apply IntervalLocationEvidence.replaceFragment _ wrapped
                calc
                  LocationFragment.located nextAnchor.span
                      [LocationFragment.merge [
                        LocationFragment.ofExpression receiver,
                        postfixPartCore part]] =
                    LocationFragment.located nextExpression.span
                      [LocationFragment.merge [
                        LocationFragment.ofExpression receiver,
                        postfixPartCore part]] := by rw [nextSpan]
                  _ = LocationFragment.ofExpression nextExpression :=
                    by
                      have expressionSpanShape : nextExpression.span =
                          (RuleReduction.between file receiver.span
                            (postfixPartEndpointSpan part) ()).span := by
                        cases part <;>
                          rfl
                      rw [expressionSpanShape]
                      exact (postfixStep_fragment file receiver part).symm
              have nextAnchorSpans : SourceAnchorTrace.spans
                    (nextAnchor :: tailAnchors) =
                  postfixFoldFocusedSpans nextExpression tail := by
                rw [SourceAnchorTrace.spans_cons,
                  postfixFoldFocusedSpans, nextSpan, tailSpans]
              have nextWithin : SourceAnchorTrace.Within
                  (nextAnchor :: tailAnchors) origin finish := by
                intro anchor member
                simp only [List.mem_cons] at member
                rcases member with rfl | tailMember
                · exact nextInside
                · exact anchorsWithin anchor (by simp [tailMember])
              have nextOrdered : SourceAnchorTrace.Ordered
                  (nextAnchor :: tailAnchors) := by
                have endpointTailOrdered : SourceAnchorTrace.Ordered
                    (endpointAnchor :: tailAnchors) :=
                  List.Pairwise.sublist (by simp) anchorsOrdered
                simp only [SourceAnchorTrace.Ordered,
                  List.pairwise_cons] at endpointTailOrdered ⊢
                exact endpointTailOrdered
              have tailCoreFromInput : ∀ candidate, candidate ∈ tail →
                  (postfixPartCore candidate).IsSubfragmentOf
                    inputFragment := by
                intro candidate member
                exact coreFromInput candidate (by simp [member])
              rw [foldPostfix_cons]
              exact inductionHypothesis nextExpression nextEvidence
                tailCoreFromInput (nextAnchor :: tailAnchors)
                  nextAnchorSpans nextWithin nextOrdered

/-- An interleaved postfix focus also determines one occupied anchor for the
eventual folded receiver. -/
theorem foldPostfix_principalFocusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (receiver : Expression) (parts : List PostfixPartValue)
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans = postfixFoldFocusedSpans receiver parts)
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered) :
    ∃ principal : SourceAnchorTrace file tokens,
      principal.spans =
          [(RuleReduction.foldPostfix file receiver parts).span] ∧
        principal.Within origin finish ∧ principal.Ordered := by
  induction parts generalizing receiver anchors with
  | nil =>
      cases anchors with
      | nil =>
          simp [postfixFoldFocusedSpans] at anchorSpans
      | cons receiverAnchor tailAnchors =>
          cases tailAnchors with
          | nil =>
              have receiverSpan : receiverAnchor.span = receiver.span := by
                simpa [postfixFoldFocusedSpans] using anchorSpans
              refine ⟨[receiverAnchor], ?_, ?_,
                SourceAnchorTrace.ordered_singleton receiverAnchor⟩
              · simp [RuleReduction.foldPostfix, receiverSpan]
              · intro anchor member
                exact anchorsWithin anchor member
          | cons nextAnchor tail =>
              simp [postfixFoldFocusedSpans] at anchorSpans
  | cons part tail inductionHypothesis =>
      cases anchors with
      | nil =>
          simp [postfixFoldFocusedSpans] at anchorSpans
      | cons receiverAnchor remainingAnchors =>
          simp only [SourceAnchorTrace.spans_cons,
            postfixFoldFocusedSpans_cons, List.cons.injEq] at anchorSpans
          rcases anchorSpans with ⟨receiverSpan, remainingSpans⟩
          rcases splitAnchors_of_spans_append remainingAnchors
              (postfixPartInitialFocusedSpans part)
              (postfixPartEndpointSpan part ::
                tail.flatMap fun remaining =>
                  postfixPartInitialFocusedSpans remaining ++
                    [postfixPartEndpointSpan remaining]) remainingSpans with
            ⟨initialAnchors, endpointAndTail, remainingShape,
              _initialSpans, endpointAndTailSpans⟩
          cases endpointAndTail with
          | nil =>
              simp at endpointAndTailSpans
          | cons endpointAnchor tailAnchors =>
              simp only [SourceAnchorTrace.spans_cons, List.cons.injEq]
                at endpointAndTailSpans
              rcases endpointAndTailSpans with ⟨endpointSpan, tailSpans⟩
              subst remainingAnchors
              have endpointPairOrdered : SourceAnchorTrace.Ordered
                  [receiverAnchor, endpointAnchor] :=
                List.Pairwise.sublist (by simp) anchorsOrdered
              have receiverToEndpoint :
                  receiverAnchor.origin.val ≤ endpointAnchor.origin.val :=
                Nat.le_trans receiverAnchor.occupied.1.2.1 (by
                  have viewed := endpointPairOrdered
                  simp only [SourceAnchorTrace.Ordered,
                    List.pairwise_cons] at viewed
                  exact viewed.1 endpointAnchor (by simp))
              let nextAnchor := SourceAnchor.between receiverAnchor
                endpointAnchor receiverToEndpoint
              let nextExpression := applyPostfixPart file receiver part
              have nextSpan : nextAnchor.span = nextExpression.span := by
                cases part <;>
                  simp [nextAnchor, nextExpression, applyPostfixPart,
                    RuleReduction.between, receiverSpan, endpointSpan,
                    postfixPartEndpointSpan]
              have nextAnchorSpans : SourceAnchorTrace.spans
                    (nextAnchor :: tailAnchors) =
                  postfixFoldFocusedSpans nextExpression tail := by
                rw [SourceAnchorTrace.spans_cons,
                  postfixFoldFocusedSpans, nextSpan, tailSpans]
              have nextWithin : SourceAnchorTrace.Within
                  (nextAnchor :: tailAnchors) origin finish := by
                intro anchor member
                simp only [List.mem_cons] at member
                rcases member with rfl | tailMember
                · exact ⟨(anchorsWithin receiverAnchor (by simp)).1,
                    (anchorsWithin endpointAnchor (by simp)).2⟩
                · exact anchorsWithin anchor (by simp [tailMember])
              have nextOrdered : SourceAnchorTrace.Ordered
                  (nextAnchor :: tailAnchors) := by
                have endpointTailOrdered : SourceAnchorTrace.Ordered
                    (endpointAnchor :: tailAnchors) :=
                  List.Pairwise.sublist (by simp) anchorsOrdered
                simp only [SourceAnchorTrace.Ordered,
                  List.pairwise_cons] at endpointTailOrdered ⊢
                exact endpointTailOrdered
              rw [foldPostfix_cons]
              exact inductionHypothesis nextExpression
                (nextAnchor :: tailAnchors) nextAnchorSpans nextWithin
                  nextOrdered

/-- Source-level interval transformation for the postfix fold once its
interleaved coherent focus anchors have been exposed. -/
theorem postfix_locationSound_of_focusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (origin finish : Boundary tokens)
    (atom : Expression) (parts : List PostfixPartValue)
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans = postfixFoldFocusedSpans atom parts)
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered)
    {trace : SourceAnchorTrace file tokens}
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      (inputLocationFragment
        (RuleReduction.postfix (file := file) (tokens := tokens)
          origin finish atom parts)) trace) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue .postfix
        (RuleReduction.foldPostfix file atom parts)) trace := by
  let reduction := RuleReduction.postfix (file := file) (tokens := tokens)
    origin finish atom parts
  have atomInside : EbnfValue.ContainsLocationFragment file tokens
      (inputValue reduction) (LocationFragment.ofExpression atom) := by
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.head
    exact EbnfValue.ContainsLocationFragment.rule .atom atom
  have atomEvidence := IntervalLocationEvidence.restrict
    atomInside.locationFragment_isSubfragment inputEvidence
  have coreFromInput : ∀ part, part ∈ parts →
      (postfixPartCore part).IsSubfragmentOf
        (inputLocationFragment reduction) := by
    intro part member
    have inside : EbnfValue.ContainsLocationFragment file tokens
        (inputValue reduction) (RuleLocationView.ofPostfixPartValue part) := by
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.tail
      apply EbnfValues.ContainsLocationFragment.head
      apply EbnfValue.ContainsLocationFragment.star
        (List.mem_map_of_mem member)
      exact EbnfValue.ContainsLocationFragment.rule .postfixPart part
    exact (postfixPartCore_subfragment part).trans
      inside.locationFragment_isSubfragment
  simpa [reduction, RuleLocationView.ofRuleValue] using
    foldPostfix_locationEvidence tokensOrdered inputEvidence atom parts
      atomEvidence coreFromInput anchors anchorSpans anchorsWithin
        anchorsOrdered

/-- Exact constructor classification for the eight endpoint-sensitive
left-folding expression rules. -/
inductive ExpressionFoldLocationCase
    {file : WorkspaceFile} {tokens : List Token} :
    {rule : GrammarRuleId} → {origin finish : Boundary tokens} →
      {input : EbnfValue file tokens (m2cV1.rhs rule)} →
      {output : RuleValue rule} →
      RuleReduction file tokens rule origin finish input output → Type where
  | logicalOr
      (origin finish : Boundary tokens) (left : Expression)
      (rest : List
        (MatchedTerminal file tokens (.symbol .logicalOr) × Expression)) :
      ExpressionFoldLocationCase
        (RuleReduction.logicalOr origin finish left rest)
  | logicalAnd
      (origin finish : Boundary tokens) (left : Expression)
      (rest : List
        (MatchedTerminal file tokens (.symbol .logicalAnd) × Expression)) :
      ExpressionFoldLocationCase
        (RuleReduction.logicalAnd origin finish left rest)
  | bitOr
      (origin finish : Boundary tokens) (left : Expression)
      (rest : List
        (MatchedTerminal file tokens (.symbol .pipe) × Expression)) :
      ExpressionFoldLocationCase
        (RuleReduction.bitOr origin finish left rest)
  | bitXor
      (origin finish : Boundary tokens) (left : Expression)
      (rest : List
        (MatchedTerminal file tokens (.symbol .caret) × Expression)) :
      ExpressionFoldLocationCase
        (RuleReduction.bitXor origin finish left rest)
  | bitAnd
      (origin finish : Boundary tokens) (left : Expression)
      (rest : List
        (MatchedTerminal file tokens (.symbol .amp) × Expression)) :
      ExpressionFoldLocationCase
        (RuleReduction.bitAnd origin finish left rest)
  | additive
      (origin finish : Boundary tokens) (left : Expression)
      (rest : List
        (Sum
          (MatchedTerminal file tokens (.symbol .plus))
          (MatchedTerminal file tokens (.symbol .minus)) × Expression)) :
      ExpressionFoldLocationCase
        (RuleReduction.additive origin finish left rest)
  | multiplicative
      (origin finish : Boundary tokens) (left : Expression)
      (rest : List
        (Sum
          (MatchedTerminal file tokens (.symbol .star))
          (Sum
            (MatchedTerminal file tokens (.symbol .slash))
            (MatchedTerminal file tokens (.symbol .percent))) × Expression)) :
      ExpressionFoldLocationCase
        (RuleReduction.multiplicative origin finish left rest)
  | postfix
      (origin finish : Boundary tokens) (atom : Expression)
      (parts : List PostfixPartValue) :
      ExpressionFoldLocationCase
        (RuleReduction.postfix (file := file) (tokens := tokens)
          origin finish atom parts)

namespace ExpressionFoldLocationCase

/-- The grammar-ordered source spans needed by the classified fold. -/
def focusedSpans
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output} :
    ExpressionFoldLocationCase reduces → List SourceSpan
  | .logicalOr _ _ left rest =>
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.logicalOr value.1),
            value.2))
  | .logicalAnd _ _ left rest =>
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.logicalAnd value.1),
            value.2))
  | .bitOr _ _ left rest =>
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.bitOr value.1), value.2))
  | .bitXor _ _ left rest =>
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.bitXor value.1), value.2))
  | .bitAnd _ _ left rest =>
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.bitAnd value.1), value.2))
  | .additive _ _ left rest =>
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (match value.1 with
            | .inl plus =>
                RuleReduction.infixOperator plus (.add plus)
            | .inr minus =>
                RuleReduction.infixOperator minus (.subtract minus),
            value.2))
  | .multiplicative _ _ left rest =>
      infixFoldFocusedSpans left
        (rest.map fun value =>
          (match value.1 with
            | .inl star =>
                RuleReduction.infixOperator star (.multiply star)
            | .inr (.inl slash) =>
                RuleReduction.infixOperator slash (.divide slash)
            | .inr (.inr percent) =>
                RuleReduction.infixOperator percent (.modulo percent),
            value.2))
  | .«postfix» _ _ atom parts => postfixFoldFocusedSpans atom parts

/-- Every exact fold classification belongs to the endpoint partition. -/
theorem endpointSensitive
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (classified : ExpressionFoldLocationCase reduces) :
    EndpointSensitiveRuleCase reduces := by
  cases classified with
  | logicalOr => exact .logicalOr _
  | logicalAnd => exact .logicalAnd _
  | bitOr => exact .bitOr _
  | bitXor => exact .bitXor _
  | bitAnd => exact .bitAnd _
  | additive => exact .additive _
  | multiplicative => exact .multiplicative _
  | «postfix» => exact .postfix _

/-- Uniform source-level interval theorem for all eight classified folds. -/
theorem locationSound_of_focusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (reduces : RuleReduction file tokens rule origin finish input output)
    (classified : ExpressionFoldLocationCase reduces)
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans = classified.focusedSpans)
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered)
    {trace : SourceAnchorTrace file tokens}
    (inputEvidence : IntervalLocationEvidence file tokens origin finish
      input.locationFragment trace) :
    IntervalLocationEvidence file tokens origin finish
      (RuleLocationView.ofRuleValue rule output) trace := by
  cases classified with
  | logicalOr origin finish left rest =>
      exact logicalOr_locationSound_of_focusedAnchors tokensOrdered origin
        finish left rest anchors (by simpa [focusedSpans] using anchorSpans)
          anchorsWithin anchorsOrdered inputEvidence
  | logicalAnd origin finish left rest =>
      exact logicalAnd_locationSound_of_focusedAnchors tokensOrdered origin
        finish left rest anchors (by simpa [focusedSpans] using anchorSpans)
          anchorsWithin anchorsOrdered inputEvidence
  | bitOr origin finish left rest =>
      exact bitOr_locationSound_of_focusedAnchors tokensOrdered origin finish
        left rest anchors (by simpa [focusedSpans] using anchorSpans)
          anchorsWithin anchorsOrdered inputEvidence
  | bitXor origin finish left rest =>
      exact bitXor_locationSound_of_focusedAnchors tokensOrdered origin finish
        left rest anchors (by simpa [focusedSpans] using anchorSpans)
          anchorsWithin anchorsOrdered inputEvidence
  | bitAnd origin finish left rest =>
      exact bitAnd_locationSound_of_focusedAnchors tokensOrdered origin finish
        left rest anchors (by simpa [focusedSpans] using anchorSpans)
          anchorsWithin anchorsOrdered inputEvidence
  | additive origin finish left rest =>
      exact additive_locationSound_of_focusedAnchors tokensOrdered origin
        finish left rest anchors (by simpa [focusedSpans] using anchorSpans)
          anchorsWithin anchorsOrdered inputEvidence
  | multiplicative origin finish left rest =>
      exact multiplicative_locationSound_of_focusedAnchors tokensOrdered
        origin finish left rest anchors
          (by simpa [focusedSpans] using anchorSpans) anchorsWithin
            anchorsOrdered inputEvidence
  | «postfix» origin finish atom parts =>
      exact postfix_locationSound_of_focusedAnchors tokensOrdered origin finish
        atom parts anchors (by simpa [focusedSpans] using anchorSpans)
          anchorsWithin anchorsOrdered inputEvidence

/-- Uniform action-facing principal-anchor theorem for all eight folds. -/
theorem principalFocusedAnchors
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (reduces : RuleReduction file tokens rule origin finish input output)
    (classified : ExpressionFoldLocationCase reduces)
    (anchors : SourceAnchorTrace file tokens)
    (anchorSpans : anchors.spans = classified.focusedSpans)
    (anchorsWithin : anchors.Within origin finish)
    (anchorsOrdered : anchors.Ordered) :
    ∃ principal : SourceAnchorTrace file tokens,
      principal.spans = RuleLocationView.exposedSpans rule output ∧
        principal.Within origin finish ∧ principal.Ordered := by
  cases classified with
  | logicalOr origin finish left rest =>
      simpa [RuleLocationView.exposedSpans, RuleLocationView.ofRuleValue] using
        foldInfixLeft_principalFocusedAnchors left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.logicalOr value.1),
              value.2)) anchors
          (by simpa [focusedSpans] using anchorSpans) anchorsWithin
            anchorsOrdered
  | logicalAnd origin finish left rest =>
      simpa [RuleLocationView.exposedSpans, RuleLocationView.ofRuleValue] using
        foldInfixLeft_principalFocusedAnchors left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.logicalAnd value.1),
              value.2)) anchors
          (by simpa [focusedSpans] using anchorSpans) anchorsWithin
            anchorsOrdered
  | bitOr origin finish left rest =>
      simpa [RuleLocationView.exposedSpans, RuleLocationView.ofRuleValue] using
        foldInfixLeft_principalFocusedAnchors left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.bitOr value.1), value.2))
          anchors (by simpa [focusedSpans] using anchorSpans) anchorsWithin
            anchorsOrdered
  | bitXor origin finish left rest =>
      simpa [RuleLocationView.exposedSpans, RuleLocationView.ofRuleValue] using
        foldInfixLeft_principalFocusedAnchors left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.bitXor value.1), value.2))
          anchors (by simpa [focusedSpans] using anchorSpans) anchorsWithin
            anchorsOrdered
  | bitAnd origin finish left rest =>
      simpa [RuleLocationView.exposedSpans, RuleLocationView.ofRuleValue] using
        foldInfixLeft_principalFocusedAnchors left
          (rest.map fun value =>
            (RuleReduction.infixOperator value.1 (.bitAnd value.1), value.2))
          anchors (by simpa [focusedSpans] using anchorSpans) anchorsWithin
            anchorsOrdered
  | additive origin finish left rest =>
      simpa only [RuleLocationView.exposedSpans,
        RuleLocationView.ofRuleValue, LocationFragment.ofExpression_roots,
        foldInfixLeft_span, List.map_map, Function.comp_def] using
        foldInfixLeft_principalFocusedAnchors left
          (rest.map fun value =>
            (match value.1 with
              | .inl plus =>
                  RuleReduction.infixOperator plus (.add plus)
              | .inr minus =>
                  RuleReduction.infixOperator minus (.subtract minus),
              value.2)) anchors
          (by simpa [focusedSpans] using anchorSpans) anchorsWithin
            anchorsOrdered
  | multiplicative origin finish left rest =>
      simpa only [RuleLocationView.exposedSpans,
        RuleLocationView.ofRuleValue, LocationFragment.ofExpression_roots,
        foldInfixLeft_span, List.map_map, Function.comp_def] using
        foldInfixLeft_principalFocusedAnchors left
          (rest.map fun value =>
            (match value.1 with
              | .inl star =>
                  RuleReduction.infixOperator star (.multiply star)
              | .inr (.inl slash) =>
                  RuleReduction.infixOperator slash (.divide slash)
              | .inr (.inr percent) =>
                  RuleReduction.infixOperator percent (.modulo percent),
              value.2)) anchors
          (by simpa [focusedSpans] using anchorSpans) anchorsWithin
            anchorsOrdered
  | «postfix» origin finish atom parts =>
      simpa [RuleLocationView.exposedSpans, RuleLocationView.ofRuleValue] using
        foldPostfix_principalFocusedAnchors atom parts anchors
          (by simpa [focusedSpans] using anchorSpans) anchorsWithin
            anchorsOrdered

end ExpressionFoldLocationCase

/-- Lift any focused-anchor source transformation through the canonical root
action wrapper used by coherent parser reductions. -/
private theorem coherentRootLocationSound_of_focusedAnchors
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
      (CanonicalRootLocationItem tokens rule origin finish context)
        priorValues}
    {ruleInput : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (reduces : RuleReduction file tokens rule origin finish ruleInput output)
    (inputEq : ruleInput = RootAction.unpack rule
      (PrefixValues.fullValue
        (CanonicalRootLocationItem tokens rule origin finish context)
        complete priorValues))
    {focusedSpans : List SourceSpan}
    (focusedEvidence : ∃ anchors : SourceAnchorTrace file tokens,
      anchors.spans = focusedSpans ∧ anchors.Within origin finish ∧
        anchors.Ordered)
    (sourceSound : ∀ anchors : SourceAnchorTrace file tokens,
      anchors.spans = focusedSpans → anchors.Within origin finish →
        anchors.Ordered →
          ∀ trace : SourceAnchorTrace file tokens,
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
  have ruleInputEvidence : IntervalLocationEvidence file tokens origin finish
      ruleInput.locationFragment trace := by
    have unpackEvidence := IntervalLocationEvidence.replaceFragment
      (RootAction.unpack_locationFragment rule rootInput).symm inputEvidence
    rw [← inputEq] at unpackEvidence
    exact unpackEvidence
  rcases focusedEvidence with
    ⟨anchors, anchorSpans, anchorsWithin, anchorsOrdered⟩
  exact sourceSound anchors anchorSpans anchorsWithin anchorsOrdered trace
    ruleInputEvidence

end RuleReduction

end Solcore.Surface.Multi
