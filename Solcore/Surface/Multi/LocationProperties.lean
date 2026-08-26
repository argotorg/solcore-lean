import Solcore.Surface.Multi.Location
import Solcore.Surface.Multi.Properties

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

namespace TokenSpansOrdered

/-- Earlier retained tokens end no later than a later token starts. -/
theorem getElem_end_le_start
    {tokens : List Token}
    (ordered : TokenSpansOrdered tokens)
    {earlier later : Nat}
    (earlierBound : earlier < tokens.length)
    (laterBound : later < tokens.length)
    (before : earlier < later) :
    tokens[earlier].span.endByte ≤ tokens[later].span.startByte := by
  rw [TokenSpansOrdered, List.pairwise_iff_getElem] at ordered
  exact ordered earlier later earlierBound laterBound before

end TokenSpansOrdered

namespace TokensOwnedBy

/-- Every indexed retained token has a source-valid span. -/
theorem getElem_valid
    {file : WorkspaceFile}
    {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (index : Nat)
    (bound : index < tokens.length) :
    tokens[index].span.ValidFor file := by
  exact owned tokens[index] (List.getElem_mem bound)

end TokensOwnedBy

namespace ConsumedSpan

/-- A consumed chart interval is source-valid when its retained token stream is
physically ordered. -/
theorem validFor
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {span : SourceSpan}
    (tokensOrdered : TokenSpansOrdered tokens)
    (consumed : ConsumedSpan file tokens origin finish span) :
    span.ValidFor file := by
  unfold ConsumedSpan at consumed
  rcases consumed with ⟨owned, intervalOrdered, shape⟩
  split at shape
  · rename_i occupied
    subst span
    have firstBound : origin.val < tokens.length :=
      Nat.lt_of_lt_of_le occupied (Nat.min_le_right _ _)
    have capPositive : 0 < Nat.min finish.val tokens.length :=
      Nat.zero_lt_of_lt occupied
    have lastBound : Nat.min finish.val tokens.length - 1 < tokens.length :=
      Nat.lt_of_lt_of_le
        (Nat.sub_lt capPositive Nat.zero_lt_one)
        (Nat.min_le_right _ _)
    have firstValid := owned.getElem_valid origin.val firstBound
    have lastValid := owned.getElem_valid
      (Nat.min finish.val tokens.length - 1) lastBound
    have firstIndexLeLast :
        origin.val ≤ Nat.min finish.val tokens.length - 1 := by
      omega
    have endpointsOrdered :
        tokens[origin.val].span.startByte ≤
          tokens[Nat.min finish.val tokens.length - 1].span.endByte := by
      by_cases same :
          origin.val = Nat.min finish.val tokens.length - 1
      · simpa only [same] using lastValid.2.1
      · have before :
            origin.val < Nat.min finish.val tokens.length - 1 := by
          omega
        exact Nat.le_trans firstValid.2.1
          (Nat.le_trans
            (tokensOrdered.getElem_end_le_start
              firstBound lastBound before)
            lastValid.2.1)
    exact ⟨rfl, endpointsOrdered, lastValid.2.2.1,
      firstValid.2.2.2.1, lastValid.2.2.2.2⟩
  · rename_i vacant
    rcases shape with ⟨byte, boundary, rfl⟩
    unfold BoundaryByte at boundary
    rcases boundary with ⟨_boundaryOwned, byteEq⟩
    split at byteEq
    · rename_i inRange
      subst byte
      have valid := owned.getElem_valid origin.val inRange
      exact ⟨rfl, Nat.le_refl _,
        Nat.le_trans valid.2.1 valid.2.2.1,
        valid.2.2.2.1, valid.2.2.2.1⟩
    · subst byte
      exact ⟨rfl, Nat.le_refl _, Nat.le_refl _,
        isUtf8Boundary_end file.content,
        isUtf8Boundary_end file.content⟩

end ConsumedSpan

/-- A consumed chart interval that retains at least one physical token. -/
def OccupiedConsumedSpan
    (file : WorkspaceFile)
    (tokens : List Token)
    (origin finish : Boundary tokens)
    (span : SourceSpan) : Prop :=
  ConsumedSpan file tokens origin finish span ∧
    origin.val < Nat.min finish.val tokens.length

namespace OccupiedConsumedSpan

/-- An occupied consumed interval is source-valid. -/
theorem validFor
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {span : SourceSpan}
    (tokensOrdered : TokenSpansOrdered tokens)
    (occupied : OccupiedConsumedSpan file tokens origin finish span) :
    span.ValidFor file :=
  ConsumedSpan.validFor tokensOrdered occupied.1

/-- A physically occupied inner chart interval is contained by any enclosing
consumed interval. Empty intervals deliberately use a separate theorem because
trivia can separate a boundary byte from the preceding token end. -/
theorem containedBy
    {file : WorkspaceFile}
    {tokens : List Token}
    {outerOrigin outerFinish innerOrigin innerFinish : Boundary tokens}
    {outerSpan innerSpan : SourceSpan}
    (tokensOrdered : TokenSpansOrdered tokens)
    (outer : ConsumedSpan file tokens outerOrigin outerFinish outerSpan)
    (inner : OccupiedConsumedSpan file tokens innerOrigin innerFinish innerSpan)
    (startsInside : outerOrigin.val ≤ innerOrigin.val)
    (finishesInside : innerFinish.val ≤ outerFinish.val) :
    outerSpan.Contains innerSpan := by
  have innerValid := inner.validFor tokensOrdered
  have innerOccupied := inner.2
  have innerBounds := Nat.lt_min.mp innerOccupied
  have outerOccupied :
      outerOrigin.val < Nat.min outerFinish.val tokens.length := by
    apply Nat.lt_min.mpr
    constructor <;> omega
  unfold ConsumedSpan at outer
  rcases outer with ⟨outerOwned, _outerOrdered, outerShape⟩
  simp only [outerOccupied, ↓reduceDIte] at outerShape
  unfold OccupiedConsumedSpan ConsumedSpan at inner
  rcases inner with ⟨⟨innerOwned, _innerOrdered, innerShape⟩,
    _occupiedAgain⟩
  simp only [innerOccupied, ↓reduceDIte] at innerShape
  subst outerSpan
  subst innerSpan
  have outerFirstBound : outerOrigin.val < tokens.length :=
    Nat.lt_of_lt_of_le outerOccupied (Nat.min_le_right _ _)
  have innerFirstBound : innerOrigin.val < tokens.length :=
    innerBounds.2
  have outerCapPositive :
      0 < Nat.min outerFinish.val tokens.length :=
    Nat.zero_lt_of_lt outerOccupied
  have innerCapPositive :
      0 < Nat.min innerFinish.val tokens.length :=
    Nat.zero_lt_of_lt innerOccupied
  have outerLastBound :
      Nat.min outerFinish.val tokens.length - 1 < tokens.length :=
    Nat.lt_of_lt_of_le
      (Nat.sub_lt outerCapPositive Nat.zero_lt_one)
      (Nat.min_le_right _ _)
  have innerLastBound :
      Nat.min innerFinish.val tokens.length - 1 < tokens.length :=
    Nat.lt_of_lt_of_le
      (Nat.sub_lt innerCapPositive Nat.zero_lt_one)
      (Nat.min_le_right _ _)
  have startsOrdered :
      tokens[outerOrigin.val].span.startByte ≤
        tokens[innerOrigin.val].span.startByte := by
    by_cases same : outerOrigin.val = innerOrigin.val
    · simpa only [same] using
        Nat.le_refl tokens[innerOrigin.val].span.startByte
    · have before : outerOrigin.val < innerOrigin.val := by omega
      have outerFirstValid :=
        outerOwned.getElem_valid outerOrigin.val outerFirstBound
      exact Nat.le_trans outerFirstValid.2.1
        (tokensOrdered.getElem_end_le_start
          outerFirstBound innerFirstBound before)
  have cappedFinishesOrdered :
      Nat.min innerFinish.val tokens.length ≤
        Nat.min outerFinish.val tokens.length := by
    simp only [Nat.min_def]
    split <;> split <;> omega
  have lastIndicesOrdered :
      Nat.min innerFinish.val tokens.length - 1 ≤
        Nat.min outerFinish.val tokens.length - 1 := by
    exact Nat.sub_le_sub_right cappedFinishesOrdered 1
  have finishesOrdered :
      tokens[Nat.min innerFinish.val tokens.length - 1].span.endByte ≤
        tokens[Nat.min outerFinish.val tokens.length - 1].span.endByte := by
    by_cases same :
        Nat.min innerFinish.val tokens.length - 1 =
          Nat.min outerFinish.val tokens.length - 1
    · simpa only [same] using Nat.le_refl
        tokens[Nat.min outerFinish.val tokens.length - 1].span.endByte
    · have before :
          Nat.min innerFinish.val tokens.length - 1 <
            Nat.min outerFinish.val tokens.length - 1 := by
        omega
      have outerLastValid := outerOwned.getElem_valid
        (Nat.min outerFinish.val tokens.length - 1) outerLastBound
      exact Nat.le_trans
        (tokensOrdered.getElem_end_le_start
          innerLastBound outerLastBound before)
        outerLastValid.2.1
  exact ⟨rfl, startsOrdered, innerValid.2.1, finishesOrdered⟩

end OccupiedConsumedSpan

/-- One nonempty physical parser interval together with its exact source span. -/
structure SourceAnchor (file : WorkspaceFile) (tokens : List Token) where
  origin : Boundary tokens
  finish : Boundary tokens
  span : SourceSpan
  occupied : OccupiedConsumedSpan file tokens origin finish span

namespace SourceAnchor

/-- One anchor interval lies inside an enclosing parser interval. -/
def Within {file : WorkspaceFile} {tokens : List Token}
    (anchor : SourceAnchor file tokens)
    (outerOrigin outerFinish : Boundary tokens) : Prop :=
  outerOrigin.val ≤ anchor.origin.val ∧
    anchor.finish.val ≤ outerFinish.val

/-- Every anchored source span is valid when retained tokens are ordered. -/
theorem span_validFor
    {file : WorkspaceFile}
    {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    (anchor : SourceAnchor file tokens) :
    anchor.span.ValidFor file :=
  anchor.occupied.validFor tokensOrdered

/-- An anchor inside a consumed interval is contained by that interval's span. -/
theorem containedBy
    {file : WorkspaceFile}
    {tokens : List Token}
    {outerOrigin outerFinish : Boundary tokens}
    {outerSpan : SourceSpan}
    (tokensOrdered : TokenSpansOrdered tokens)
    (outer : ConsumedSpan file tokens outerOrigin outerFinish outerSpan)
    (anchor : SourceAnchor file tokens)
    (inside : anchor.Within outerOrigin outerFinish) :
    outerSpan.Contains anchor.span :=
  anchor.occupied.containedBy tokensOrdered outer inside.1 inside.2

end SourceAnchor

/-- A ghost trace of physical source anchors retained while EBNF actions
reshape their semantic values. -/
abbrev SourceAnchorTrace (file : WorkspaceFile) (tokens : List Token) :=
  List (SourceAnchor file tokens)

namespace SourceAnchorTrace

/-- The exact source spans carried by an anchor trace, in trace order. -/
def spans {file : WorkspaceFile} {tokens : List Token}
    (trace : SourceAnchorTrace file tokens) : List SourceSpan :=
  trace.map SourceAnchor.span

/-- Every trace interval lies inside one enclosing parser interval. -/
def Within {file : WorkspaceFile} {tokens : List Token}
    (trace : SourceAnchorTrace file tokens)
    (outerOrigin outerFinish : Boundary tokens) : Prop :=
  ∀ anchor ∈ trace, anchor.Within outerOrigin outerFinish

/-- Earlier physical anchors finish no later than later anchors begin. -/
def Ordered {file : WorkspaceFile} {tokens : List Token}
    (trace : SourceAnchorTrace file tokens) : Prop :=
  trace.Pairwise fun earlier later =>
    earlier.finish.val ≤ later.origin.val

@[simp] theorem spans_nil {file : WorkspaceFile} {tokens : List Token} :
    spans ([] : SourceAnchorTrace file tokens) = [] := by
  rfl

@[simp] theorem spans_cons
    {file : WorkspaceFile} {tokens : List Token}
    (head : SourceAnchor file tokens)
    (tail : SourceAnchorTrace file tokens) :
    spans (head :: tail) = head.span :: spans tail := by
  rfl

@[simp] theorem spans_append
    {file : WorkspaceFile} {tokens : List Token}
    (left right : SourceAnchorTrace file tokens) :
    spans (left ++ right) = spans left ++ spans right := by
  simp [spans]

@[simp] theorem within_nil
    {file : WorkspaceFile} {tokens : List Token}
    {outerOrigin outerFinish : Boundary tokens} :
    Within ([] : SourceAnchorTrace file tokens) outerOrigin outerFinish := by
  simp [Within]

@[simp] theorem within_cons
    {file : WorkspaceFile} {tokens : List Token}
    (head : SourceAnchor file tokens)
    (tail : SourceAnchorTrace file tokens)
    (outerOrigin outerFinish : Boundary tokens) :
    Within (head :: tail) outerOrigin outerFinish ↔
      head.Within outerOrigin outerFinish ∧
        Within tail outerOrigin outerFinish := by
  simp [Within]

@[simp] theorem within_append
    {file : WorkspaceFile} {tokens : List Token}
    (left right : SourceAnchorTrace file tokens)
    (outerOrigin outerFinish : Boundary tokens) :
    Within (left ++ right) outerOrigin outerFinish ↔
      Within left outerOrigin outerFinish ∧
        Within right outerOrigin outerFinish := by
  constructor
  · intro allInside
    constructor
    · intro anchor member
      exact allInside anchor (List.mem_append.mpr (Or.inl member))
    · intro anchor member
      exact allInside anchor (List.mem_append.mpr (Or.inr member))
  · rintro ⟨leftInside, rightInside⟩ anchor member
    rcases List.mem_append.mp member with member | member
    · exact leftInside anchor member
    · exact rightInside anchor member

@[simp] theorem ordered_nil
    {file : WorkspaceFile} {tokens : List Token} :
    Ordered ([] : SourceAnchorTrace file tokens) := by
  simp [Ordered]

@[simp] theorem ordered_singleton
    {file : WorkspaceFile} {tokens : List Token}
    (anchor : SourceAnchor file tokens) :
    Ordered [anchor] := by
  simp [Ordered]

/-- Appending traces preserves order exactly when both sides are ordered and
every anchor on the left precedes every anchor on the right. -/
theorem ordered_append_iff
    {file : WorkspaceFile} {tokens : List Token}
    (left right : SourceAnchorTrace file tokens) :
    Ordered (left ++ right) ↔
      Ordered left ∧ Ordered right ∧
        ∀ earlier ∈ left, ∀ later ∈ right,
          earlier.finish.val ≤ later.origin.val := by
  simp [Ordered, List.pairwise_append]

end SourceAnchorTrace

namespace ConsumedSpanWitness

/-- Every checked chart-span witness is valid for its source file when the
retained tokens are physically ordered. -/
theorem span_validFor
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    (tokensOrdered : TokenSpansOrdered tokens)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    witness.span.ValidFor file :=
  ConsumedSpan.validFor tokensOrdered witness.consumed

end ConsumedSpanWitness

namespace SourceLocates

/-- A value located by a checked chart interval has a source-valid wrapper. -/
theorem span_validFor
    {alpha : Type}
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {payload : alpha}
    {located : Located alpha}
    (tokensOrdered : TokenSpansOrdered tokens)
    (locates : SourceLocates file tokens origin finish payload located) :
    located.span.ValidFor file := by
  rcases locates with ⟨witness, rfl⟩
  exact witness.span_validFor tokensOrdered

end SourceLocates

namespace Lexes

/-- Successful lexing makes every consumed chart interval source-valid. -/
theorem consumedSpan_validFor
    {file : WorkspaceFile}
    {tokens : List Token}
    {comments : List Comment}
    {origin finish : Boundary tokens}
    {span : SourceSpan}
    (lexical : Lexes file tokens comments)
    (consumed : ConsumedSpan file tokens origin finish span) :
    span.ValidFor file :=
  ConsumedSpan.validFor lexical.tokenSpansOrdered consumed

/-- Successful lexing makes every checked source-located wrapper valid. -/
theorem sourceLocates_span_validFor
    {alpha : Type}
    {file : WorkspaceFile}
    {tokens : List Token}
    {comments : List Comment}
    {origin finish : Boundary tokens}
    {payload : alpha}
    {located : Located alpha}
    (lexical : Lexes file tokens comments)
    (locates : SourceLocates file tokens origin finish payload located) :
    located.span.ValidFor file :=
  SourceLocates.span_validFor lexical.tokenSpansOrdered locates

end Lexes

namespace MatchedTerminal

/-- Every checked terminal observation has a source-valid span. -/
theorem span_validFor
    {file : WorkspaceFile}
    {tokens : List Token}
    {terminal : Grammar.TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal) :
    matched.span.ValidFor file := by
  rcases matched with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  dsimp only
  cases terminalAt with
  | retained _token _inRange _lookup valid =>
      exact valid
  | endOfFile _atEnd =>
      exact ⟨rfl, Nat.le_refl _, Nat.le_refl _,
        isUtf8Boundary_end file.content,
        isUtf8Boundary_end file.content⟩

/-- A non-EOF terminal is exactly one occupied retained-token interval. -/
theorem occupiedConsumedSpan
    {file : WorkspaceFile}
    {tokens : List Token}
    {terminal : Grammar.TerminalSymbol}
    (owned : TokensOwnedBy file tokens)
    (matched : MatchedTerminal file tokens terminal)
    (notEof : terminal ≠ .endOfFile) :
    OccupiedConsumedSpan file tokens matched.cursor.beforeBoundary
      matched.cursor.afterBoundary matched.span := by
  rcases matched with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  dsimp only
  cases terminalAt with
  | retained token inRange lookup valid =>
      have occupied :
          cursor.val < Nat.min (cursor.val + 1) tokens.length :=
        Nat.lt_min.mpr ⟨Nat.lt_succ_self _, inRange⟩
      have boundaries := terminalCursor_boundary_coercions_exact cursor
      have occupiedAtBoundaries :
          cursor.beforeBoundary.val <
            Nat.min cursor.afterBoundary.val tokens.length := by
        rw [boundaries.1, boundaries.2]
        exact occupied
      constructor
      · unfold ConsumedSpan
        refine ⟨owned, ?_, ?_⟩
        · rw [boundaries.1, boundaries.2]
          exact Nat.le_succ _
        · simp only [occupiedAtBoundaries, ↓reduceDIte]
          have lookupEq : tokens[cursor.val] = token :=
            Option.some.inj
              ((List.getElem?_eq_getElem inRange).symm.trans lookup)
          have capped : Nat.min (cursor.val + 1) tokens.length =
              cursor.val + 1 :=
            Nat.min_eq_left (Nat.succ_le_iff.mpr inRange)
          simp only [boundaries.1, boundaries.2, capped,
            Nat.add_sub_cancel]
          rw [lookupEq]
          rcases token with ⟨⟨tokenSource, startByte, endByte⟩, payload⟩
          simp only [SourceSpan.ValidFor] at valid
          simp only
          rw [valid.1]
      · exact occupiedAtBoundaries
  | endOfFile atEnd =>
      have terminalEq : terminal = .endOfFile := by
        cases terminal <;>
          simp [TerminalMatches] at matchedEvidence ⊢
      exact (notEof terminalEq).elim

/-- Package one non-EOF matched terminal as a physical source anchor. -/
def sourceAnchor
    {file : WorkspaceFile}
    {tokens : List Token}
    {terminal : Grammar.TerminalSymbol}
    (owned : TokensOwnedBy file tokens)
    (matched : MatchedTerminal file tokens terminal)
    (notEof : terminal ≠ .endOfFile) : SourceAnchor file tokens := {
  origin := matched.cursor.beforeBoundary
  finish := matched.cursor.afterBoundary
  span := matched.span
  occupied := matched.occupiedConsumedSpan owned notEof
}

@[simp] theorem sourceAnchor_origin
    {file : WorkspaceFile}
    {tokens : List Token}
    {terminal : Grammar.TerminalSymbol}
    (owned : TokensOwnedBy file tokens)
    (matched : MatchedTerminal file tokens terminal)
    (notEof : terminal ≠ .endOfFile) :
    (matched.sourceAnchor owned notEof).origin =
      matched.cursor.beforeBoundary := by
  rfl

@[simp] theorem sourceAnchor_finish
    {file : WorkspaceFile}
    {tokens : List Token}
    {terminal : Grammar.TerminalSymbol}
    (owned : TokensOwnedBy file tokens)
    (matched : MatchedTerminal file tokens terminal)
    (notEof : terminal ≠ .endOfFile) :
    (matched.sourceAnchor owned notEof).finish =
      matched.cursor.afterBoundary := by
  rfl

@[simp] theorem sourceAnchor_span
    {file : WorkspaceFile}
    {tokens : List Token}
    {terminal : Grammar.TerminalSymbol}
    (owned : TokensOwnedBy file tokens)
    (matched : MatchedTerminal file tokens terminal)
    (notEof : terminal ≠ .endOfFile) :
    (matched.sourceAnchor owned notEof).span = matched.span := by
  rfl

/-- A retained terminal observation exposes both membership in the parser's
token stream and equality with that token's source span. -/
theorem retained_member_and_span
    {file : WorkspaceFile}
    {tokens : List Token}
    {terminal : Grammar.TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    {token : Token}
    (valueEq : matched.value = .retained token) :
    token ∈ tokens ∧ matched.span = token.span := by
  rcases matched with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  dsimp only at valueEq ⊢
  cases terminalAt with
  | retained retained inRange lookup valid =>
      simp only [TerminalStreamValue.retained.injEq] at valueEq
      subst token
      have retainedEq : tokens[cursor.val] = retained :=
        Option.some.inj
          ((List.getElem?_eq_getElem inRange).symm.trans lookup)
      have member : tokens[cursor.val] ∈ tokens :=
        List.getElem_mem inRange
      rw [retainedEq] at member
      exact ⟨member, rfl⟩
  | endOfFile atEnd =>
      simp at valueEq

end MatchedTerminal

namespace Lexes

/-- An assembly slice projected by the parser inherits every location fact
proved by the independent lexical partition. -/
theorem assemblySlice_locations_of_projects
    {file : WorkspaceFile}
    {tokens : List Token}
    {comments : List Comment}
    (lexical : Lexes file tokens comments)
    (terminal : MatchedTerminal file tokens (.category .assemblyBlock))
    {slice : AssemblySlice}
    (projects : AssemblySliceProjects terminal slice) :
    terminal.span = slice.span ∧ AssemblySliceLocationFacts file slice := by
  rcases projects with ⟨token, valueEq, payload⟩
  rcases terminal.retained_member_and_span valueEq with
    ⟨member, terminalSpan⟩
  rcases lexical.assemblySlice_locations member payload with
    ⟨tokenSpan, facts⟩
  exact ⟨terminalSpan.trans tokenSpan, facts⟩

end Lexes

end Solcore.Surface.Multi
