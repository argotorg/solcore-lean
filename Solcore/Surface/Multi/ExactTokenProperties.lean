import Solcore.Surface.Multi.ExactToken

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- Pointwise exact source evidence for one retained token sequence. -/
def TokensSourceExact (file : WorkspaceFile) (tokens : List Token) : Prop :=
  ∀ token ∈ tokens, TokenSourceExact file token

/-- A complete lexical derivation supplies pointwise exact source evidence. -/
theorem Lexes.tokensSourceExact
    {file : WorkspaceFile} {tokens : List Token}
    {comments : List Comment} (lexical : Lexes file tokens comments) :
    TokensSourceExact file tokens := by
  intro token member
  exact lexical.tokenSourceExact member

namespace ExpectedToken

/-- Forgetting endpoint constraints preserves a successful token-kind match. -/
theorem Matches.toPlain
    {expected : ExpectedToken} {actual : Token}
    (relation : expected.Matches actual) :
    (ExpectedToken.plain expected.kind).Matches actual := by
  exact ⟨relation.1, by intro constraint member; cases member⟩

end ExpectedToken

namespace TokenSlot

def FirstSatisfies
    (constraint : TokenSpanConstraint) : List Token → Prop
  | [] => False
  | first :: _ => constraint.Holds first

def LastSatisfies
    (constraint : TokenSpanConstraint) : List Token → Prop
  | [] => False
  | [last] => constraint.Holds last
  | _ :: second :: rest => LastSatisfies constraint (second :: rest)

theorem FirstSatisfies.holds_of_eq_cons
    {constraint : TokenSpanConstraint} {actual : List Token}
    (satisfies : FirstSatisfies constraint actual)
    {first : Token} {rest : List Token}
    (equation : actual = first :: rest) :
    constraint.Holds first := by
  rw [equation] at satisfies
  exact satisfies

private theorem lastSatisfies_append_singleton
    (constraint : TokenSpanConstraint) (initial : List Token)
    (last : Token) :
    LastSatisfies constraint (initial ++ [last]) ↔
      constraint.Holds last := by
  induction initial with
  | nil => rfl
  | cons head tail induction =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          change LastSatisfies constraint
            (next :: rest ++ [last]) ↔ constraint.Holds last
          exact induction

theorem LastSatisfies.holds_of_eq_append_singleton
    {constraint : TokenSpanConstraint} {actual : List Token}
    (satisfies : LastSatisfies constraint actual)
    {initial : List Token} {last : Token}
    (equation : actual = initial ++ [last]) :
    constraint.Holds last := by
  rw [equation] at satisfies
  exact (lastSatisfies_append_singleton constraint initial last).mp satisfies

namespace ListMatches

theorem append
    {firstSlots secondSlots : List TokenSlot}
    {firstActual secondActual : List Token}
    (first : ListMatches firstSlots firstActual)
    (second : ListMatches secondSlots secondActual) :
    ListMatches (firstSlots ++ secondSlots)
      (firstActual ++ secondActual) := by
  induction first with
  | nil => exact second
  | required head tail ih =>
      exact .required head ih
  | optionalAbsent tail ih =>
      exact .optionalAbsent ih
  | optionalPresent head tail ih =>
      exact .optionalPresent head ih

theorem required_singleton
    {expected : ExpectedToken} {actual : Token}
    (head : expected.Matches actual) :
    ListMatches [.required expected] [actual] :=
  .required head .nil

theorem optional_absent (expected : ExpectedToken) :
    ListMatches [.optional expected] [] :=
  .optionalAbsent .nil

theorem optional_present
    {expected : ExpectedToken} {actual : Token}
    (head : expected.Matches actual) :
    ListMatches [.optional expected] [actual] :=
  .optionalPresent head .nil

/-- A mandatory singleton plan consumes exactly one matching token. -/
theorem required_singleton_iff
    {expected : ExpectedToken} {actual : List Token} :
    ListMatches [.required expected] actual ↔
      ∃ token, actual = [token] ∧ expected.Matches token := by
  constructor
  · intro relation
    cases relation with
    | required head tail =>
        cases tail
        exact ⟨_, rfl, head⟩
  · rintro ⟨token, rfl, head⟩
    exact .required head .nil

/-- Matching a concatenated slot language determines matching physical
prefix and suffix slices. The split need not be unique when optional slots
are present, so the result is deliberately existential. -/
theorem split_append
    {leftSlots rightSlots : List TokenSlot} {actual : List Token}
    (relation : ListMatches (leftSlots ++ rightSlots) actual) :
    ∃ leftActual rightActual,
      actual = leftActual ++ rightActual ∧
        ListMatches leftSlots leftActual ∧
        ListMatches rightSlots rightActual := by
  induction leftSlots generalizing actual with
  | nil =>
      exact ⟨[], actual, rfl, .nil, relation⟩
  | cons slot leftSlots induction =>
      cases slot with
      | required expected =>
          cases relation with
          | required head tail =>
              rcases induction tail with
                ⟨leftActual, rightActual, equation,
                  leftRelation, rightRelation⟩
              exact ⟨_ :: leftActual, rightActual, by simp [equation],
                .required head leftRelation, rightRelation⟩
      | optional expected =>
          cases relation with
          | optionalAbsent tail =>
              rcases induction tail with
                ⟨leftActual, rightActual, equation,
                  leftRelation, rightRelation⟩
              exact ⟨leftActual, rightActual, equation,
                .optionalAbsent leftRelation, rightRelation⟩
          | optionalPresent head tail =>
              rcases induction tail with
                ⟨leftActual, rightActual, equation,
                  leftRelation, rightRelation⟩
              exact ⟨_ :: leftActual, rightActual, by simp [equation],
                .optionalPresent head leftRelation, rightRelation⟩

/-- An enclosing span is sound when the generated plan has mandatory physical
endpoints and the actual first and last tokens realize those endpoints. -/
theorem enclose
    {span : SourceSpan} {plan : TokenPlan} {actual : List Token}
    (relation : ListMatches plan.slots actual)
    (anchored : plan.WellAnchored)
    (starts : FirstSatisfies (.starts span) actual)
    (ends : LastSatisfies (.ends span) actual) :
    ListMatches (plan.enclose span).slots actual := by
  apply TokenPlan.enclose_listMatches relation anchored
  · intro first rest equation
    exact starts.holds_of_eq_cons equation
  · intro initial last equation
    exact ends.holds_of_eq_append_singleton equation

end ListMatches

end TokenSlot

namespace TokenPlan

private def lastRequiredShape : Bool → List Bool → Bool
  | last, [] => last
  | _, next :: rest => lastRequiredShape next rest

private def slotsWellAnchored : List TokenSlot → Bool
  | [] => true
  | first :: rest =>
      first.isRequired &&
        lastRequiredShape first.isRequired (rest.map TokenSlot.isRequired)

private def requiredSentinel : TokenSlot :=
  .required (.plain (.symbol .comma))

private theorem exposedLastRequired_eq
    (first : TokenSlot) (rest : List TokenSlot) :
    ({ slots := requiredSentinel :: first :: rest } : TokenPlan).wellAnchored =
      lastRequiredShape first.isRequired
        (rest.map TokenSlot.isRequired) := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest induction =>
      exact induction next

private theorem wellAnchored_eq_slotsWellAnchored (plan : TokenPlan) :
    plan.wellAnchored = slotsWellAnchored plan.slots := by
  cases plan with
  | mk slots =>
      cases slots with
      | nil => rfl
      | cons first rest =>
          change (first.isRequired &&
              ({ slots := requiredSentinel :: first :: rest } :
                TokenPlan).wellAnchored) =
            (first.isRequired && lastRequiredShape first.isRequired
              (rest.map TokenSlot.isRequired))
          rw [exposedLastRequired_eq]

private def addConstraintView
    (constraint : TokenSpanConstraint) : TokenSlot → TokenSlot
  | .required expected => .required {
      expected with constraints := constraint :: expected.constraints }
  | .optional expected => .optional {
      expected with constraints := constraint :: expected.constraints }

private def addFirstView
    (constraint : TokenSpanConstraint) : List TokenSlot → List TokenSlot
  | [] => []
  | first :: rest => addConstraintView constraint first :: rest

private def addLastView (constraint : TokenSpanConstraint)
    (slots : List TokenSlot) : List TokenSlot :=
  (addFirstView constraint slots.reverse).reverse

private theorem enclose_eq_view (span : SourceSpan)
    (slots : List TokenSlot) :
    TokenSlot.enclose span slots =
      addLastView (.ends span) (addFirstView (.starts span) slots) := by
  rfl

@[simp] private theorem isRequired_addConstraintView
    (constraint : TokenSpanConstraint) (slot : TokenSlot) :
    (addConstraintView constraint slot).isRequired = slot.isRequired := by
  cases slot <;> rfl

@[simp] private theorem requiredShape_addFirstView
    (constraint : TokenSpanConstraint) (slots : List TokenSlot) :
    (addFirstView constraint slots).map TokenSlot.isRequired =
      slots.map TokenSlot.isRequired := by
  cases slots with
  | nil => rfl
  | cons first rest => simp [addFirstView]

@[simp] private theorem requiredShape_addLastView
    (constraint : TokenSpanConstraint) (slots : List TokenSlot) :
    (addLastView constraint slots).map TokenSlot.isRequired =
      slots.map TokenSlot.isRequired := by
  simp [addLastView, List.map_reverse]

private theorem slotsWellAnchored_of_shape_eq
    {left right : List TokenSlot}
    (shapeEq : left.map TokenSlot.isRequired =
      right.map TokenSlot.isRequired) :
    slotsWellAnchored left = slotsWellAnchored right := by
  cases left with
  | nil =>
      cases right with
      | nil => rfl
      | cons first rest => simp at shapeEq
  | cons leftFirst leftRest =>
      cases right with
      | nil => simp at shapeEq
      | cons rightFirst rightRest =>
          simp only [List.map_cons, List.cons.injEq] at shapeEq
          rcases shapeEq with ⟨firstEq, restEq⟩
          simp only [slotsWellAnchored]
          rw [firstEq, restEq]

private theorem slotsWellAnchored_enclose
    (span : SourceSpan) (slots : List TokenSlot) :
    slotsWellAnchored (TokenSlot.enclose span slots) =
      slotsWellAnchored slots := by
  apply slotsWellAnchored_of_shape_eq
  rw [enclose_eq_view]
  simp

private theorem lastRequiredShape_append_nonempty
    (first : Bool) (rest : List Bool) (next : Bool) (tail : List Bool) :
    lastRequiredShape first (rest ++ next :: tail) =
      lastRequiredShape next tail := by
  induction rest generalizing first with
  | nil => rfl
  | cons head rest induction =>
      exact induction head

private theorem slotsWellAnchored_append
    (left right : List TokenSlot)
    (leftAnchored : slotsWellAnchored left = true)
    (rightAnchored : slotsWellAnchored right = true) :
    slotsWellAnchored (left ++ right) = true := by
  cases left with
  | nil => simpa using rightAnchored
  | cons leftFirst leftRest =>
      cases right with
      | nil => simpa using leftAnchored
      | cons rightFirst rightRest =>
          change (leftFirst.isRequired && lastRequiredShape leftFirst.isRequired
            (leftRest.map TokenSlot.isRequired)) = true at leftAnchored
          change (rightFirst.isRequired &&
            lastRequiredShape rightFirst.isRequired
              (rightRest.map TokenSlot.isRequired)) = true at rightAnchored
          change (leftFirst.isRequired && lastRequiredShape
            leftFirst.isRequired
              ((leftRest ++ rightFirst :: rightRest).map
                TokenSlot.isRequired)) = true
          rw [Bool.and_eq_true] at leftAnchored rightAnchored ⊢
          exact ⟨leftAnchored.1, by
            rw [List.map_append, List.map_cons,
              lastRequiredShape_append_nonempty]
            exact rightAnchored.2⟩

private theorem slotsWellAnchored_required_bookends
    (first last : ExpectedToken) (middle : List TokenSlot) :
    slotsWellAnchored
      ([.required first] ++ middle ++ [.required last]) = true := by
  simp only [List.cons_append, slotsWellAnchored,
    TokenSlot.isRequired, Bool.true_and, List.map_append,
    List.map_singleton]
  rw [lastRequiredShape_append_nonempty]
  rfl

namespace WellAnchored

/-- The empty token plan has no unguarded physical endpoint. -/
theorem empty : TokenPlan.empty.WellAnchored := by
  rfl

/-- A single mandatory token is endpoint-anchored. -/
theorem plain (kind : TokenKind) :
    (TokenPlan.plain kind).WellAnchored := by
  rfl

/-- A single mandatory exact token is endpoint-anchored. -/
theorem exact (kind : TokenKind) (span : SourceSpan) :
    (TokenPlan.exact kind span).WellAnchored := by
  rfl

/-- Adding source-span constraints preserves mandatory physical endpoints. -/
theorem enclose {plan : TokenPlan} (anchored : plan.WellAnchored)
    (span : SourceSpan) :
    (plan.enclose span).WellAnchored := by
  unfold TokenPlan.WellAnchored at anchored ⊢
  rw [wellAnchored_eq_slotsWellAnchored] at anchored ⊢
  change slotsWellAnchored (TokenSlot.enclose span plan.slots) = true
  rw [slotsWellAnchored_enclose]
  exact anchored

/-- Appending endpoint-anchored plans preserves endpoint anchoring. -/
theorem append {left right : TokenPlan}
    (leftAnchored : left.WellAnchored)
    (rightAnchored : right.WellAnchored) :
    (left.append right).WellAnchored := by
  unfold TokenPlan.WellAnchored at leftAnchored rightAnchored ⊢
  rw [wellAnchored_eq_slotsWellAnchored] at leftAnchored rightAnchored ⊢
  apply slotsWellAnchored_append left.slots right.slots
  · exact leftAnchored
  · exact rightAnchored

/-- Concatenating pointwise endpoint-anchored plans preserves anchoring. -/
theorem concat (plans : List TokenPlan)
    (anchored : ∀ plan ∈ plans, plan.WellAnchored) :
    (TokenPlan.concat plans).WellAnchored := by
  induction plans with
  | nil => exact empty
  | cons plan rest induction =>
      have headAnchored := anchored plan (by simp)
      have tailAnchored := induction (by
        intro candidate member
        exact anchored candidate (by simp [member]))
      simpa [TokenPlan.concat, TokenPlan.append] using
        append headAnchored tailAnchored

/-- Inserting required commas between anchored elements preserves anchoring. -/
theorem commaSeparated (plans : List TokenPlan)
    (anchored : ∀ plan ∈ plans, plan.WellAnchored) :
    (TokenPlan.commaSeparated plans).WellAnchored := by
  cases plans with
  | nil => exact empty
  | cons first rest =>
      apply append (anchored first (by simp))
      apply concat
      intro combined member
      simp only [List.mem_map] at member
      rcases member with ⟨plan, planMember, rfl⟩
      exact append (plain (.symbol .comma))
        (anchored plan (by simp [planMember]))

/-- Required parentheses anchor the result independently of the inner plan. -/
theorem parens (inner : TokenPlan) :
    (TokenPlan.parens inner).WellAnchored := by
  unfold TokenPlan.WellAnchored
  rw [wellAnchored_eq_slotsWellAnchored]
  change slotsWellAnchored
    (.required (ExpectedToken.plain (.symbol .leftParen)) ::
      inner.slots ++
      [.required (ExpectedToken.plain (.symbol .rightParen))]) = true
  exact slotsWellAnchored_required_bookends _ _ _

end WellAnchored

end TokenPlan

end Solcore.Surface.Multi
