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

end Solcore.Surface.Multi
