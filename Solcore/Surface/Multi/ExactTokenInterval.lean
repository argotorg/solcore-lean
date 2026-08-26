import Solcore.Surface.Multi.ExactTokenProperties

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- The retained-token slice covered by a parser interval. Logical EOF is
clamped away because it has no retained token. -/
def PhysicalTokens
    (tokens : List Token) (origin finish : Boundary tokens) : List Token :=
  let start := Nat.min origin.val tokens.length
  let stop := Nat.min finish.val tokens.length
  (tokens.drop start).take (stop - start)

/-- The complete module interval contains every retained token and excludes
the logical EOF observation. -/
@[simp] theorem PhysicalTokens.start_afterLogicalEOF
    (tokens : List Token) :
    PhysicalTokens tokens (Boundary.start tokens)
      (Boundary.afterLogicalEOF tokens) = tokens := by
  simp [PhysicalTokens, Boundary.start, Boundary.afterLogicalEOF]

/-- The plan contributed by one scan: an exact retained token, or no slot for
the logical EOF observation. -/
def MatchedTerminal.physicalTokenPlan
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal) : TokenPlan :=
  match matched.value with
  | .retained token => .exact token.payload matched.span
  | .endOfFile => .empty

/-- Grammar-normalized scan plan. Fixed terminals use their grammar spelling;
category terminals retain the exact payload and span selected by the lexer. -/
def MatchedTerminal.grammarTokenPlan
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) : TokenPlan :=
  match terminal with
  | .hardKeyword keyword => .plain (.hardKeyword keyword)
  | .contextualKeyword keyword => .plain (.identifier keyword.spelling)
  | .pragmaName kind => .plain (.pragmaName kind)
  | .symbol symbol => .plain (.symbol symbol)
  | .category _ =>
      match matched.value with
      | .retained token => .exact token.payload matched.span
      | .endOfFile => .empty
  | .endOfFile => .empty

/-- A checked terminal observation matches its scan-local token plan. -/
theorem MatchedTerminal.physicalTokenPlan_matches
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal) :
    TokenSlot.ListMatches matched.physicalTokenPlan.slots
      (match matched.value with
      | .retained token => [token]
      | .endOfFile => []) := by
  rcases matched with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases terminalAt with
  | retained token inRange lookup valid =>
      exact TokenSlot.ListMatches.required_singleton ⟨rfl, by simp
        [ExpectedToken.exact, TokenSpanConstraint.Holds]⟩
  | endOfFile atEnd =>
      exact TokenSlot.ListMatches.nil

/-- Every checked scan matches the grammar-normalized terminal plan. -/
theorem MatchedTerminal.grammarTokenPlan_matches
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    TokenSlot.ListMatches (matched.grammarTokenPlan terminal).slots
      (match matched.value with
      | .retained token => [token]
      | .endOfFile => []) := by
  rcases matched with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases terminal with
  | hardKeyword keyword =>
      cases terminalAt with
      | retained token inRange lookup valid =>
          exact TokenSlot.ListMatches.required_singleton
            ⟨matchedEvidence.symm, by intro constraint member; cases member⟩
      | endOfFile atEnd => simp [TerminalMatches] at matchedEvidence
  | contextualKeyword keyword =>
      cases terminalAt with
      | retained token inRange lookup valid =>
          exact TokenSlot.ListMatches.required_singleton
            ⟨matchedEvidence.symm, by intro constraint member; cases member⟩
      | endOfFile atEnd => simp [TerminalMatches] at matchedEvidence
  | pragmaName kind =>
      cases terminalAt with
      | retained token inRange lookup valid =>
          exact TokenSlot.ListMatches.required_singleton
            ⟨matchedEvidence.symm, by intro constraint member; cases member⟩
      | endOfFile atEnd => simp [TerminalMatches] at matchedEvidence
  | symbol symbol =>
      cases terminalAt with
      | retained token inRange lookup valid =>
          exact TokenSlot.ListMatches.required_singleton
            ⟨matchedEvidence.symm, by intro constraint member; cases member⟩
      | endOfFile atEnd => simp [TerminalMatches] at matchedEvidence
  | category category =>
      cases terminalAt with
      | retained token inRange lookup valid =>
          exact TokenSlot.ListMatches.required_singleton
            ⟨rfl, by simp [ExpectedToken.exact,
              TokenSpanConstraint.Holds]⟩
      | endOfFile atEnd => simp [TerminalMatches] at matchedEvidence
  | endOfFile =>
      cases terminalAt with
      | retained token inRange lookup valid =>
          simp [TerminalMatches] at matchedEvidence
      | endOfFile atEnd => exact .nil

/-- The scan-local parser interval is exactly the retained singleton, while
the logical EOF interval contains no retained token. -/
theorem MatchedTerminal.physicalTokens_before_after
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal) :
    PhysicalTokens tokens matched.cursor.beforeBoundary
        matched.cursor.afterBoundary =
      match matched.value with
      | .retained token => [token]
      | .endOfFile => [] := by
  rcases matched with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases terminalAt with
  | retained token inRange lookup valid =>
      have startEq : Nat.min cursor.val tokens.length = cursor.val :=
        Nat.min_eq_left (Nat.le_of_lt inRange)
      change (tokens.drop (Nat.min cursor.val tokens.length)).take
        (Nat.min (cursor.val + 1) tokens.length -
          Nat.min cursor.val tokens.length) = [token]
      rw [startEq]
      have lookupEq : tokens[cursor.val] = token := by
        exact Option.some.inj
          ((List.getElem?_eq_getElem inRange).symm.trans lookup)
      have minEq : Nat.min (cursor.val + 1) tokens.length =
          cursor.val + 1 := Nat.min_eq_left (by omega)
      rw [minEq]
      simp only [Nat.add_sub_cancel_left, List.take_one]
      rw [List.head?_drop, List.getElem?_eq_getElem inRange, lookupEq]
      rfl
  | endOfFile atEnd =>
      change (tokens.drop (Nat.min cursor.val tokens.length)).take
        (Nat.min (cursor.val + 1) tokens.length -
          Nat.min cursor.val tokens.length) = []
      simp [atEnd]

/-- Adjacent ordered parser intervals concatenate their retained-token slices,
including intervals whose finish crosses logical EOF. -/
theorem PhysicalTokens.append
    {tokens : List Token} {origin shared finish : Boundary tokens}
    (leftOrdered : origin.val ≤ shared.val)
    (rightOrdered : shared.val ≤ finish.val) :
    PhysicalTokens tokens origin finish =
      PhysicalTokens tokens origin shared ++
        PhysicalTokens tokens shared finish := by
  let start := Nat.min origin.val tokens.length
  let middle := Nat.min shared.val tokens.length
  let stop := Nat.min finish.val tokens.length
  have startMiddle : start ≤ middle := by
    simp only [start, middle, Nat.min_def]
    split <;> split <;> omega
  have middleStop : middle ≤ stop := by
    simp only [middle, stop, Nat.min_def]
    split <;> split <;> omega
  have split : stop - start = (middle - start) + (stop - middle) := by
    simpa [Nat.add_comm] using
      (Nat.sub_add_sub_cancel middleStop startMiddle).symm
  unfold PhysicalTokens
  change (tokens.drop start).take (stop - start) =
    (tokens.drop start).take (middle - start) ++
      (tokens.drop middle).take (stop - middle)
  rw [split, List.take_add, List.drop_drop]
  have startGap : start + (middle - start) = middle :=
    Nat.add_sub_of_le startMiddle
  rw [startGap]

/-- Scanning one checked terminal extends any ordered prefix by precisely its
retained token contribution. -/
theorem MatchedTerminal.physicalTokens_append
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    (origin : Boundary tokens)
    (ordered : origin.val ≤ matched.cursor.beforeBoundary.val) :
    PhysicalTokens tokens origin matched.cursor.afterBoundary =
      PhysicalTokens tokens origin matched.cursor.beforeBoundary ++
        match matched.value with
        | .retained token => [token]
        | .endOfFile => [] := by
  rw [PhysicalTokens.append ordered (by
    simp [TerminalCursor.beforeBoundary, TerminalCursor.afterBoundary])]
  rw [matched.physicalTokens_before_after]

/-- A non-occupied ordered interval has no retained token. -/
theorem PhysicalTokens.eq_nil_of_not_occupied
    {tokens : List Token} {origin finish : Boundary tokens}
    (vacant : ¬ origin.val < Nat.min finish.val tokens.length) :
    PhysicalTokens tokens origin finish = [] := by
  have stopStart :
      Nat.min finish.val tokens.length ≤
        Nat.min origin.val tokens.length := by
    by_cases originLe : origin.val ≤ tokens.length
    · calc
        Nat.min finish.val tokens.length ≤ origin.val :=
          Nat.le_of_not_gt vacant
        _ = Nat.min origin.val tokens.length :=
          (Nat.min_eq_left originLe).symm
    · calc
        Nat.min finish.val tokens.length ≤ tokens.length :=
          Nat.min_le_right _ _
        _ = Nat.min origin.val tokens.length :=
          (Nat.min_eq_right
            (Nat.le_of_lt (Nat.lt_of_not_ge originLe))).symm
  simp [PhysicalTokens, Nat.sub_eq_zero_of_le stopStart]

/-- The first token of an occupied interval is the token at its origin. -/
theorem PhysicalTokens.head?_eq_getElem
    {tokens : List Token} {origin finish : Boundary tokens}
    (occupied : origin.val < Nat.min finish.val tokens.length) :
    have originBound : origin.val < tokens.length :=
      Nat.lt_of_lt_of_le occupied (Nat.min_le_right _ _)
    (PhysicalTokens tokens origin finish).head? =
      some (tokens[origin.val]'originBound) := by
  have originBound : origin.val < tokens.length :=
    Nat.lt_of_lt_of_le occupied (Nat.min_le_right _ _)
  have startEq : Nat.min origin.val tokens.length = origin.val :=
    Nat.min_eq_left (Nat.le_of_lt originBound)
  have countNonzero :
      Nat.min finish.val tokens.length - origin.val ≠ 0 :=
    Nat.ne_of_gt (Nat.sub_pos_of_lt occupied)
  simp only [PhysicalTokens, startEq]
  rw [List.head?_take]
  simp only [countNonzero, ↓reduceIte, List.head?_drop,
    List.getElem?_eq_getElem originBound]

/-- The last token of an occupied interval is the token immediately before
its clamped finish boundary. -/
theorem PhysicalTokens.getLast?_eq_getElem
    {tokens : List Token} {origin finish : Boundary tokens}
    (occupied : origin.val < Nat.min finish.val tokens.length) :
    have capPositive : 0 < Nat.min finish.val tokens.length :=
      Nat.zero_lt_of_lt occupied
    have lastBound :
        Nat.min finish.val tokens.length - 1 < tokens.length :=
      Nat.lt_of_lt_of_le
        (Nat.sub_lt capPositive Nat.zero_lt_one)
        (Nat.min_le_right _ _)
    (PhysicalTokens tokens origin finish).getLast? =
      some (tokens[Nat.min finish.val tokens.length - 1]'lastBound) := by
  have originBound : origin.val < tokens.length :=
    Nat.lt_of_lt_of_le occupied (Nat.min_le_right _ _)
  have startEq : Nat.min origin.val tokens.length = origin.val :=
    Nat.min_eq_left (Nat.le_of_lt originBound)
  have countNonzero :
      Nat.min finish.val tokens.length - origin.val ≠ 0 :=
    Nat.ne_of_gt (Nat.sub_pos_of_lt occupied)
  have capPositive : 0 < Nat.min finish.val tokens.length :=
    Nat.zero_lt_of_lt occupied
  have lastBound :
      Nat.min finish.val tokens.length - 1 < tokens.length :=
    Nat.lt_of_lt_of_le
      (Nat.sub_lt capPositive Nat.zero_lt_one)
      (Nat.min_le_right _ _)
  have indexEq :
      origin.val +
          (Nat.min finish.val tokens.length - origin.val - 1) =
        Nat.min finish.val tokens.length - 1 := by
    omega
  simp only [PhysicalTokens, startEq]
  rw [List.getLast?_take]
  simp only [countNonzero, ↓reduceIte, List.getElem?_drop, indexEq,
    List.getElem?_eq_getElem lastBound, Option.some_or]

namespace ConsumedSpan

/-- If the physical interval has a first token, that token realizes the
consumed span's source and starting byte. -/
theorem startsPhysicalTokens
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens} {span : SourceSpan}
    (consumed : ConsumedSpan file tokens origin finish span) :
    ∀ first rest,
      PhysicalTokens tokens origin finish = first :: rest →
        (TokenSpanConstraint.starts span).Holds first := by
  intro first rest equation
  unfold ConsumedSpan at consumed
  rcases consumed with ⟨owned, ordered, shape⟩
  by_cases occupied : origin.val < Nat.min finish.val tokens.length
  · simp only [occupied, ↓reduceDIte] at shape
    have originBound : origin.val < tokens.length :=
      Nat.lt_of_lt_of_le occupied (Nat.min_le_right _ _)
    have headEq := PhysicalTokens.head?_eq_getElem occupied
    rw [equation] at headEq
    simp only [List.head?_cons, Option.some.injEq] at headEq
    subst first
    subst span
    exact ⟨(owned _ (List.getElem_mem originBound)).1, rfl⟩
  · have empty :=
      PhysicalTokens.eq_nil_of_not_occupied occupied
    rw [empty] at equation
    simp at equation

/-- If the physical interval has a last token, that token realizes the
consumed span's source and ending byte. -/
theorem endsPhysicalTokens
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens} {span : SourceSpan}
    (consumed : ConsumedSpan file tokens origin finish span) :
    ∀ initial last,
      PhysicalTokens tokens origin finish = initial ++ [last] →
        (TokenSpanConstraint.ends span).Holds last := by
  intro initial last equation
  unfold ConsumedSpan at consumed
  rcases consumed with ⟨owned, ordered, shape⟩
  by_cases occupied : origin.val < Nat.min finish.val tokens.length
  · simp only [occupied, ↓reduceDIte] at shape
    have capPositive : 0 < Nat.min finish.val tokens.length :=
      Nat.zero_lt_of_lt occupied
    have lastBound :
        Nat.min finish.val tokens.length - 1 < tokens.length :=
      Nat.lt_of_lt_of_le
        (Nat.sub_lt capPositive Nat.zero_lt_one)
        (Nat.min_le_right _ _)
    have lastEq := PhysicalTokens.getLast?_eq_getElem occupied
    rw [equation, List.getLast?_append] at lastEq
    simp only [List.getLast?_singleton, Option.some_or,
      Option.some.injEq] at lastEq
    subst last
    subst span
    exact ⟨(owned _ (List.getElem_mem lastBound)).1, rfl⟩
  · have empty :=
      PhysicalTokens.eq_nil_of_not_occupied occupied
    rw [empty] at equation
    simp at equation

end ConsumedSpan

namespace ConsumedSpanWitness

/-- Witness-level form of `ConsumedSpan.startsPhysicalTokens`. -/
theorem startsPhysicalTokens
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (witness : ConsumedSpanWitness file tokens origin finish) :
    ∀ first rest,
      PhysicalTokens tokens origin finish = first :: rest →
        (TokenSpanConstraint.starts witness.span).Holds first :=
  witness.consumed.startsPhysicalTokens

/-- Witness-level form of `ConsumedSpan.endsPhysicalTokens`. -/
theorem endsPhysicalTokens
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (witness : ConsumedSpanWitness file tokens origin finish) :
    ∀ initial last,
      PhysicalTokens tokens origin finish = initial ++ [last] →
        (TokenSpanConstraint.ends witness.span).Holds last :=
  witness.consumed.endsPhysicalTokens

end ConsumedSpanWitness

end Solcore.Surface.Multi
