import Solcore.Surface.Multi.Grammar

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- Every chart boundary, including the boundary after logical end of file. -/
abbrev Boundary (tokens : List Token) : Type := Fin (tokens.length + 2)

/-- Every terminal position: retained tokens followed by logical end of file. -/
abbrev TerminalCursor (tokens : List Token) : Type := Fin (tokens.length + 1)

namespace TerminalCursor

/-- Embed a terminal cursor as its boundary before the selected terminal. -/
def beforeBoundary {tokens : List Token}
    (cursor : TerminalCursor tokens) : Boundary tokens :=
  Fin.castLE (Nat.le_succ _) cursor

/-- Select the boundary immediately after one retained or logical terminal. -/
def afterBoundary {tokens : List Token}
    (cursor : TerminalCursor tokens) : Boundary tokens := {
  val := cursor.val + 1
  isLt := Nat.succ_lt_succ cursor.isLt
}

end TerminalCursor

/-- The two embeddings of a terminal cursor preserve its index and select
the immediately following chart boundary, respectively. -/
theorem terminalCursor_boundary_coercions_exact
    {tokens : List Token} (cursor : TerminalCursor tokens) :
    cursor.beforeBoundary.val = cursor.val ∧
      cursor.afterBoundary.val = cursor.val + 1 := by
  exact ⟨rfl, rfl⟩

namespace Boundary

/-- The first chart boundary. -/
def start (tokens : List Token) : Boundary tokens := {
  val := 0
  isLt := Nat.zero_lt_succ _
}

/-- The chart boundary after the one logical end-of-file terminal. -/
def afterLogicalEOF (tokens : List Token) : Boundary tokens := {
  val := tokens.length + 1
  isLt := Nat.lt_succ_self (tokens.length + 1)
}

end Boundary

/-- The nearest parser region relevant to guarded productions. -/
inductive GuardContext (tokens : List Token) where
  | plain
  | bracedBody (bodyStart : Boundary tokens)
  | armBody (armBodyStart : Boundary tokens)
  | postfixInvocation (postfixStart : Boundary tokens)
  deriving Repr, BEq, DecidableEq

/-- Exact finite cardinality certificate for contextual ancestry. -/
theorem guard_context_cardinality (tokens : List Token) :
    ∃ encode : GuardContext tokens → Fin (1 + 3 * (tokens.length + 2)),
      Function.Injective encode ∧ Function.Surjective encode := by
  let q := tokens.length + 2
  let encode : GuardContext tokens → Fin (1 + 3 * q)
    | .plain => ⟨0, by omega⟩
    | .bracedBody boundary => ⟨1 + boundary.val, by
        have := boundary.isLt
        omega⟩
    | .armBody boundary => ⟨1 + q + boundary.val, by
        have := boundary.isLt
        omega⟩
    | .postfixInvocation boundary => ⟨1 + 2 * q + boundary.val, by
        have := boundary.isLt
        omega⟩
  refine ⟨encode, ?_, ?_⟩
  · intro left right same
    cases left <;> cases right <;>
      simp only [encode, Fin.mk.injEq] at same ⊢ <;>
      try omega
    all_goals
      congr
      apply Fin.ext
      omega
  · intro value
    by_cases plain : value.val = 0
    · refine ⟨.plain, ?_⟩
      apply Fin.ext
      simp [encode, plain]
    · have positive : 0 < value.val := Nat.pos_of_ne_zero plain
      by_cases braced : value.val - 1 < q
      · let boundary : Boundary tokens := ⟨value.val - 1, by
          simpa [q] using braced⟩
        refine ⟨.bracedBody boundary, ?_⟩
        apply Fin.ext
        simp only [encode, boundary]
        omega
      · by_cases arm : value.val - 1 < 2 * q
        · have armLower : q ≤ value.val - 1 := Nat.le_of_not_gt braced
          let boundary : Boundary tokens := ⟨value.val - 1 - q, by
            simpa [q] using (show value.val - 1 - q < q by omega)⟩
          refine ⟨.armBody boundary, ?_⟩
          apply Fin.ext
          simp only [encode, boundary]
          omega
        · have postfixLower : 2 * q ≤ value.val - 1 :=
            Nat.le_of_not_gt arm
          have valueUpper : value.val < 1 + 3 * q := value.isLt
          let boundary : Boundary tokens := ⟨value.val - 1 - 2 * q, by
            simpa [q] using
              (show value.val - 1 - 2 * q < q by omega)⟩
          refine ⟨.postfixInvocation boundary, ?_⟩
          apply Fin.ext
          simp only [encode, boundary]
          omega

/-- One production predicted at an origin in its exact guard context. -/
structure ProductionInstanceKey (tokens : List Token) where
  production : ProductionId
  origin : Boundary tokens
  context : GuardContext tokens
  deriving Repr, BEq, DecidableEq

/-- One priority-guard query at an ordered pair of chart boundaries. -/
structure GuardInstanceKey (tokens : List Token) where
  guard : PriorityGuardId
  contextStart : Boundary tokens
  siteCursor : Boundary tokens
  ordered : contextStart.val ≤ siteCursor.val
  deriving Repr, BEq, DecidableEq

private def triangle (n : Nat) : Nat := (List.range' 1 n 1).sum

private theorem triangle_succ (n : Nat) :
    triangle (n + 1) = triangle n + (n + 1) := by
  simp [triangle, List.range'_concat, Nat.add_comm, Nat.add_left_comm]

private theorem triangle_mono {a b : Nat} (atMost : a ≤ b) :
    triangle a ≤ triangle b := by
  obtain ⟨offset, rfl⟩ := Nat.le.dest atMost
  clear atMost
  induction offset with
  | zero => simp
  | succ offset induction =>
      rw [show a + (offset + 1) = (a + offset) + 1 by omega]
      rw [triangle_succ]
      exact Nat.le_trans induction (Nat.le_add_right _ _)

private theorem twice_triangle (n : Nat) :
    2 * triangle n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n induction =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega]
      rw [triangle_succ, Nat.mul_add, induction]
      simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
      omega

private structure OrderedFinPair (q : Nat) where
  first : Fin q
  second : Fin q
  ordered : first.val ≤ second.val

private def OrderedFinPair.rank {q : Nat} (pair : OrderedFinPair q) : Nat :=
  triangle pair.second.val + pair.first.val

private theorem OrderedFinPair.rank_lt {q : Nat} (pair : OrderedFinPair q) :
    pair.rank < triangle q := by
  have firstBound : pair.first.val < pair.second.val + 1 := by
    exact Nat.lt_succ_of_le pair.ordered
  have rowBound :
      pair.rank < triangle (pair.second.val + 1) := by
    rw [triangle_succ]
    exact Nat.add_lt_add_left firstBound _
  exact Nat.lt_of_lt_of_le rowBound
    (triangle_mono (Nat.succ_le_of_lt pair.second.isLt))

private theorem OrderedFinPair.rank_injective {q : Nat} :
    Function.Injective (@OrderedFinPair.rank q) := by
  intro left right equality
  have sameSecond : left.second.val = right.second.val := by
    rcases Nat.lt_trichotomy left.second.val right.second.val with
      less | same | greater
    · have firstRowBound :
          left.rank < triangle (left.second.val + 1) := by
        rw [triangle_succ]
        simp only [OrderedFinPair.rank]
        exact Nat.add_lt_add_left (Nat.lt_succ_of_le left.ordered) _
      have rowsOrdered :
          triangle (left.second.val + 1) ≤ triangle right.second.val :=
        triangle_mono (by omega)
      have rightRowStart : triangle right.second.val ≤ right.rank := by
        simp [OrderedFinPair.rank]
      have rankLess : left.rank < right.rank :=
        Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le firstRowBound rowsOrdered) rightRowStart
      exact False.elim ((Nat.ne_of_lt rankLess) equality)
    · exact same
    · have rightRowBound :
          right.rank < triangle (right.second.val + 1) := by
        rw [triangle_succ]
        simp only [OrderedFinPair.rank]
        exact Nat.add_lt_add_left (Nat.lt_succ_of_le right.ordered) _
      have rowsOrdered :
          triangle (right.second.val + 1) ≤ triangle left.second.val :=
        triangle_mono (by omega)
      have leftRowStart : triangle left.second.val ≤ left.rank := by
        simp [OrderedFinPair.rank]
      have rankLess : right.rank < left.rank :=
        Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le rightRowBound rowsOrdered) leftRowStart
      exact False.elim ((Nat.ne_of_lt rankLess) equality.symm)
  have sameFirst : left.first.val = right.first.val := by
    simp only [OrderedFinPair.rank] at equality
    rw [sameSecond] at equality
    exact Nat.add_left_cancel equality
  have sameFirstFin : left.first = right.first := Fin.ext sameFirst
  have sameSecondFin : left.second = right.second := Fin.ext sameSecond
  cases left
  cases right
  cases sameFirstFin
  cases sameSecondFin
  rfl

private theorem OrderedFinPair.rank_surjective (q : Nat) :
    ∀ value : Fin (triangle q), ∃ pair : OrderedFinPair q, pair.rank = value.val := by
  induction q with
  | zero =>
      intro value
      exact Fin.elim0 (Fin.cast (by rfl) value)
  | succ q induction =>
      intro value
      by_cases earlier : value.val < triangle q
      · obtain ⟨pair, rankEq⟩ := induction ⟨value.val, earlier⟩
        let lifted : OrderedFinPair (q + 1) := {
          first := Fin.castLE (Nat.le_succ q) pair.first
          second := Fin.castLE (Nat.le_succ q) pair.second
          ordered := pair.ordered
        }
        exact ⟨lifted, by simpa [lifted, OrderedFinPair.rank] using rankEq⟩
      · have valueBound : value.val < triangle q + (q + 1) := by
          simpa [triangle_succ] using value.isLt
        let first : Fin (q + 1) := ⟨value.val - triangle q, by omega⟩
        let second : Fin (q + 1) := ⟨q, by omega⟩
        let pair : OrderedFinPair (q + 1) := {
          first := first
          second := second
          ordered := by
            simp only [first, second]
            omega
        }
        refine ⟨pair, ?_⟩
        simp only [pair, OrderedFinPair.rank, first, second]
        omega

private def guardRank : PriorityGuardId → Nat
  | .G01_statementIf => 0 | .G02_matchArmBoundary => 1
  | .G03_parameterComptime => 2 | .G04_letComptime => 3
  | .G05_typeComptime => 4 | .G06_patternComptime => 5
  | .G07_leadingDotArguments => 6 | .G08_terminalExpression => 7
  | .G09_genericContext => 8

private theorem guardRank_lt (guard : PriorityGuardId) :
    guardRank guard < allPriorityGuardIds.length := by
  cases guard <;> decide

private theorem guardRank_injective :
    Function.Injective guardRank := by
  intro left right equality
  cases left <;> cases right <;>
    simp only [guardRank] at equality ⊢ <;> omega

private theorem guardRank_surjective :
    ∀ value : Fin allPriorityGuardIds.length,
      ∃ guard : PriorityGuardId, guardRank guard = value.val := by
  intro value
  have bound : value.val < 9 := by
    change value.val < allPriorityGuardIds.length
    exact value.isLt
  have alternatives :
      value.val = 0 ∨ value.val = 1 ∨ value.val = 2 ∨
      value.val = 3 ∨ value.val = 4 ∨ value.val = 5 ∨
      value.val = 6 ∨ value.val = 7 ∨ value.val = 8 := by
    omega
  rcases alternatives with h | h | h | h | h | h | h | h | h
  · exact ⟨.G01_statementIf, by simp [guardRank, h]⟩
  · exact ⟨.G02_matchArmBoundary, by simp [guardRank, h]⟩
  · exact ⟨.G03_parameterComptime, by simp [guardRank, h]⟩
  · exact ⟨.G04_letComptime, by simp [guardRank, h]⟩
  · exact ⟨.G05_typeComptime, by simp [guardRank, h]⟩
  · exact ⟨.G06_patternComptime, by simp [guardRank, h]⟩
  · exact ⟨.G07_leadingDotArguments, by simp [guardRank, h]⟩
  · exact ⟨.G08_terminalExpression, by simp [guardRank, h]⟩
  · exact ⟨.G09_genericContext, by simp [guardRank, h]⟩

private theorem blockRank_injective {width : Nat}
    {leftBlock rightBlock leftOffset rightOffset : Nat}
    (leftOffsetBound : leftOffset < width)
    (rightOffsetBound : rightOffset < width)
    (equality :
      leftBlock * width + leftOffset =
        rightBlock * width + rightOffset) :
    leftBlock = rightBlock ∧ leftOffset = rightOffset := by
  have widthPositive : 0 < width := Nat.zero_lt_of_lt leftOffsetBound
  have quotient (block offset : Nat) (offsetBound : offset < width) :
      (block * width + offset) / width = block := by
    rw [Nat.add_comm, Nat.mul_comm block width,
      Nat.add_mul_div_left _ _ widthPositive, Nat.div_eq_of_lt offsetBound]
    exact Nat.zero_add block
  have sameBlock : leftBlock = rightBlock := by
    rw [← quotient leftBlock leftOffset leftOffsetBound,
      equality, quotient rightBlock rightOffset rightOffsetBound]
  constructor
  · exact sameBlock
  · rw [sameBlock] at equality
    exact Nat.add_left_cancel equality

/-- Exact finite cardinality of priority-guard queries over ordered chart
boundary pairs. -/
theorem guard_instance_cardinality (tokens : List Token) :
    ∃ encode : GuardInstanceKey tokens →
        Fin (allPriorityGuardIds.length * (tokens.length + 2) *
          (tokens.length + 2 + 1) / 2),
      Function.Injective encode ∧ Function.Surjective encode := by
  let q := tokens.length + 2
  let width := triangle q
  have widthPositive : 0 < width := by
    change 0 < triangle q
    rw [show q = (tokens.length + 1) + 1 by simp [q]]
    rw [triangle_succ]
    omega
  have cardinalityEq :
      allPriorityGuardIds.length * width =
        allPriorityGuardIds.length * q * (q + 1) / 2 := by
    have numeratorEq :
        2 * (allPriorityGuardIds.length * width) =
          allPriorityGuardIds.length * q * (q + 1) := by
      rw [show 2 * (allPriorityGuardIds.length * width) =
        allPriorityGuardIds.length * (2 * width) by
          simp [Nat.mul_left_comm]]
      rw [show 2 * width = q * (q + 1) by
        simpa [width] using twice_triangle q]
      simp [Nat.mul_assoc]
    calc
      allPriorityGuardIds.length * width =
          2 * (allPriorityGuardIds.length * width) / 2 := by
        exact (Nat.mul_div_cancel_left _ (by omega)).symm
      _ = allPriorityGuardIds.length * q * (q + 1) / 2 :=
        congrArg (fun value => value / 2) numeratorEq
  let pairOf (key : GuardInstanceKey tokens) : OrderedFinPair q := {
    first := key.contextStart
    second := key.siteCursor
    ordered := key.ordered
  }
  let rawEncode (key : GuardInstanceKey tokens) : Nat :=
    guardRank key.guard * width + (pairOf key).rank
  let encode (key : GuardInstanceKey tokens) :
      Fin (allPriorityGuardIds.length * (tokens.length + 2) *
        (tokens.length + 2 + 1) / 2) := ⟨rawEncode key, by
    have guardBound := guardRank_lt key.guard
    have pairBound := OrderedFinPair.rank_lt (pairOf key)
    have rowBound :
        rawEncode key < (guardRank key.guard + 1) * width := by
      change guardRank key.guard * width + (pairOf key).rank <
        (guardRank key.guard + 1) * width
      rw [Nat.add_mul]
      simpa only [Nat.one_mul, width] using
        Nat.add_lt_add_left pairBound (guardRank key.guard * width)
    have rowsBound :
        (guardRank key.guard + 1) * width ≤
          allPriorityGuardIds.length * width :=
      Nat.mul_le_mul_right width (Nat.succ_le_of_lt guardBound)
    have rawBound := Nat.lt_of_lt_of_le rowBound rowsBound
    have normalizedEq :
        allPriorityGuardIds.length * width =
          allPriorityGuardIds.length * (tokens.length + 2) *
            (tokens.length + 2 + 1) / 2 := by
      simpa [q] using cardinalityEq
    exact normalizedEq ▸ rawBound
  ⟩
  refine ⟨encode, ?_, ?_⟩
  · intro left right equality
    have rawEquality : rawEncode left = rawEncode right := by
      exact congrArg Fin.val equality
    have blocksEqual := blockRank_injective
      (OrderedFinPair.rank_lt (pairOf left))
      (OrderedFinPair.rank_lt (pairOf right)) rawEquality
    have guardEqual : left.guard = right.guard :=
      guardRank_injective blocksEqual.1
    have pairsEqual : pairOf left = pairOf right :=
      OrderedFinPair.rank_injective blocksEqual.2
    have contextEqual : left.contextStart = right.contextStart :=
      congrArg OrderedFinPair.first pairsEqual
    have siteEqual : left.siteCursor = right.siteCursor :=
      congrArg OrderedFinPair.second pairsEqual
    cases left
    cases right
    simp only [GuardInstanceKey.mk.injEq]
    exact ⟨guardEqual, contextEqual, siteEqual⟩
  · intro value
    let rawValue : Fin (allPriorityGuardIds.length * width) :=
      Fin.cast cardinalityEq.symm (Fin.cast (by simp [q]) value)
    let guardIndex : Fin allPriorityGuardIds.length :=
      ⟨rawValue.val / width, (Nat.div_lt_iff_lt_mul widthPositive).mpr
        rawValue.isLt⟩
    let pairIndex : Fin width :=
      ⟨rawValue.val % width, Nat.mod_lt _ widthPositive⟩
    obtain ⟨guard, guardEq⟩ := guardRank_surjective guardIndex
    obtain ⟨pair, pairEq⟩ := OrderedFinPair.rank_surjective q pairIndex
    let key : GuardInstanceKey tokens := {
      guard := guard
      contextStart := pair.first
      siteCursor := pair.second
      ordered := pair.ordered
    }
    refine ⟨key, ?_⟩
    apply Fin.ext
    simp only [encode, rawEncode, pairOf, key]
    rw [guardEq, pairEq]
    simpa [guardIndex, pairIndex, rawValue, Nat.add_comm, Nat.mul_comm] using
      Nat.mod_add_div rawValue.val width

/-- One expanded production at a dot position and chart interval. -/
structure DottedItem (tokens : List Token) where
  production : ProductionId
  dot : Fin (production.rhs.length + 1)
  origin : Boundary tokens
  current : Boundary tokens
  deriving Repr, BEq, DecidableEq

private theorem dependentEnumeration_nodup
    {α γ : Type} {β : α → Type}
    (values : List α) (items : (value : α) → List (β value))
    (make : (value : α) → β value → γ)
    (valuesUnique : values.Nodup)
    (itemsUnique : ∀ value, (items value).Nodup)
    (makeInjective : ∀ {left right} {leftItem : β left}
      {rightItem : β right},
      make left leftItem = make right rightItem →
        Sigma.mk left leftItem = Sigma.mk right rightItem) :
    (values.flatMap fun value =>
      (items value).map (make value)).Nodup := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at valuesUnique
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      have mappedUnique :
          ((items head).map (make head)).Nodup := by
        rw [List.nodup_iff_pairwise_ne]
        rw [List.pairwise_map]
        exact (itemsUnique head).imp fun different equal =>
          different (eq_of_heq
            (Sigma.ext_iff.mp (makeInjective equal)).2)
      refine ⟨mappedUnique, induction valuesUnique.2, ?_⟩
      intro left leftMember right rightMember equal
      rw [List.mem_map] at leftMember
      rcases leftMember with ⟨leftItem, _, rfl⟩
      rw [List.mem_flatMap] at rightMember
      rcases rightMember with ⟨owner, ownerMember, rightMember⟩
      rw [List.mem_map] at rightMember
      rcases rightMember with ⟨rightItem, _, rfl⟩
      have ownerEqual := congrArg Sigma.fst (makeInjective equal)
      change head = owner at ownerEqual
      exact valuesUnique.1 (ownerEqual.symm ▸ ownerMember)

private theorem allDottedRhs_nodup_for_chart : allDottedRhs.Nodup := by
  apply dependentEnumeration_nodup allProductionIds
    (fun production =>
      List.ofFn fun dot : Fin (production.rhs.length + 1) => dot)
    (fun production dot => ({ production, dot } : DottedRhs))
    allProductionIds_nodup
  · intro production
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro left right leftBound rightBound before equal
    have sameFin :
        (⟨left, by simpa using leftBound⟩ :
            Fin (production.rhs.length + 1)) =
          ⟨right, by simpa using rightBound⟩ := by
      simpa only [List.getElem_ofFn] using equal
    have sameValue : left = right := congrArg Fin.val sameFin
    omega
  · intro left right leftDot rightDot equal
    cases equal
    rfl

private def allBoundaries (tokens : List Token) : List (Boundary tokens) :=
  List.ofFn id

private theorem allBoundaries_complete {tokens : List Token}
    (boundary : Boundary tokens) : boundary ∈ allBoundaries tokens := by
  rw [allBoundaries, List.mem_ofFn]
  exact ⟨boundary, rfl⟩

private theorem allBoundaries_nodup (tokens : List Token) :
    (allBoundaries tokens).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro left right leftBound rightBound before equal
  have sameFin :
      (⟨left, by simpa [allBoundaries] using leftBound⟩ :
          Boundary tokens) =
        ⟨right, by simpa [allBoundaries] using rightBound⟩ := by
    simpa only [allBoundaries, List.getElem_ofFn, id_eq] using equal
  have sameValue : left = right := congrArg Fin.val sameFin
  omega

private theorem allBoundaries_length (tokens : List Token) :
    (allBoundaries tokens).length = tokens.length + 2 := by
  simp [allBoundaries]

private theorem dependentEnumeration_length
    {α γ : Type} {β : α → Type}
    (values : List α) (items : (value : α) → List (β value))
    (make : (value : α) → β value → γ)
    (size : Nat) (itemLength : ∀ value, (items value).length = size) :
    (values.flatMap fun value =>
      (items value).map (make value)).length = values.length * size := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons]
      rw [itemLength head, induction]
      rw [Nat.succ_mul]
      omega

private structure DottedOrigin (tokens : List Token) where
  dotted : DottedRhs
  origin : Boundary tokens

private def allDottedOrigins (tokens : List Token) :
    List (DottedOrigin tokens) :=
  allDottedRhs.flatMap fun dotted =>
    (allBoundaries tokens).map fun origin => { dotted, origin }

private theorem allDottedOrigins_complete {tokens : List Token}
    (value : DottedOrigin tokens) : value ∈ allDottedOrigins tokens := by
  rw [allDottedOrigins, List.mem_flatMap]
  refine ⟨value.dotted, allDottedRhs_complete value.dotted, ?_⟩
  rw [List.mem_map]
  exact ⟨value.origin, allBoundaries_complete value.origin, by
    cases value
    rfl⟩

private theorem allDottedOrigins_nodup (tokens : List Token) :
    (allDottedOrigins tokens).Nodup := by
  apply dependentEnumeration_nodup allDottedRhs
    (fun _ => allBoundaries tokens)
    (fun dotted origin => ({ dotted, origin } : DottedOrigin tokens))
    allDottedRhs_nodup_for_chart
    (fun _ => allBoundaries_nodup tokens)
  intro left right leftOrigin rightOrigin equal
  cases equal
  rfl

/-- Every dotted chart item in stable production, dot, and boundary order. -/
def allDottedItems (tokens : List Token) : List (DottedItem tokens) :=
  (allDottedOrigins tokens).flatMap fun value =>
    (allBoundaries tokens).map fun current => {
      production := value.dotted.production
      dot := value.dotted.dot
      origin := value.origin
      current := current
    }

/-- Every dotted chart item occurs in the stable finite enumeration. -/
theorem allDottedItems_complete {tokens : List Token}
    (item : DottedItem tokens) : item ∈ allDottedItems tokens := by
  let value : DottedOrigin tokens := {
    dotted := { production := item.production, dot := item.dot }
    origin := item.origin
  }
  rw [allDottedItems, List.mem_flatMap]
  refine ⟨value, allDottedOrigins_complete value, ?_⟩
  rw [List.mem_map]
  refine ⟨item.current, allBoundaries_complete item.current, ?_⟩
  cases item
  rfl

/-- The stable dotted-item enumeration contains no duplicate key. -/
theorem allDottedItems_nodup (tokens : List Token) :
    (allDottedItems tokens).Nodup := by
  apply dependentEnumeration_nodup (allDottedOrigins tokens)
    (fun _ => allBoundaries tokens)
    (fun value current => ({
      production := value.dotted.production
      dot := value.dotted.dot
      origin := value.origin
      current := current
    } : DottedItem tokens))
    (allDottedOrigins_nodup tokens)
    (fun _ => allBoundaries_nodup tokens)
  intro left right leftCurrent rightCurrent equal
  cases left with
  | mk leftDotted leftOrigin =>
      cases right with
      | mk rightDotted rightOrigin =>
          cases leftDotted
          cases rightDotted
          cases equal
          rfl

/-- The dotted-item enumeration has the displayed chart-item cardinality. -/
theorem allDottedItems_length (tokens : List Token) :
    (allDottedItems tokens).length =
      D * (tokens.length + 2) * (tokens.length + 2) := by
  rw [allDottedItems]
  rw [dependentEnumeration_length (allDottedOrigins tokens)
    (fun _ => allBoundaries tokens) _ (tokens.length + 2)
    (fun _ => allBoundaries_length tokens)]
  rw [allDottedOrigins]
  rw [dependentEnumeration_length allDottedRhs
    (fun _ => allBoundaries tokens) _ (tokens.length + 2)
    (fun _ => allBoundaries_length tokens)]
  rw [allDottedRhs_length]

/-- A proof-free unguarded scan or completion edge key. -/
inductive PackedEdgeKey (tokens : List Token) where
  | scanned
      (before after : DottedItem tokens)
      (terminalCursor : TerminalCursor tokens)
  | completed
      (waiting finished after : DottedItem tokens)
      (sharedCursor : Boundary tokens)
  deriving Repr, BEq, DecidableEq

/-- One dotted item paired with its exact guard context. -/
structure ContextualItemKey (tokens : List Token) where
  raw : DottedItem tokens
  context : GuardContext tokens
  deriving Repr, BEq, DecidableEq

private def allGuardContexts (tokens : List Token) :
    List (GuardContext tokens) :=
  .plain ::
    ((allBoundaries tokens).map .bracedBody ++
      (allBoundaries tokens).map .armBody ++
      (allBoundaries tokens).map .postfixInvocation)

private theorem allGuardContexts_complete {tokens : List Token}
    (context : GuardContext tokens) :
    context ∈ allGuardContexts tokens := by
  cases context with
  | plain => simp [allGuardContexts]
  | bracedBody bodyStart =>
      simp [allGuardContexts, allBoundaries_complete bodyStart]
  | armBody armBodyStart =>
      simp [allGuardContexts, allBoundaries_complete armBodyStart]
  | postfixInvocation postfixStart =>
      simp [allGuardContexts, allBoundaries_complete postfixStart]

private theorem allGuardContexts_map_nodup
    (tokens : List Token)
    (make : Boundary tokens → GuardContext tokens)
    (injective : Function.Injective make) :
    ((allBoundaries tokens).map make).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  have boundariesPairwise :
      (allBoundaries tokens).Pairwise (fun left right => left ≠ right) := by
    rw [← List.nodup_iff_pairwise_ne]
    exact allBoundaries_nodup tokens
  exact boundariesPairwise.imp fun different equal =>
    different (injective equal)

private theorem allGuardContexts_nodup (tokens : List Token) :
    (allGuardContexts tokens).Nodup := by
  have bracedUnique := allGuardContexts_map_nodup tokens
    GuardContext.bracedBody (by
      intro left right equal
      cases equal
      rfl)
  have armUnique := allGuardContexts_map_nodup tokens
    GuardContext.armBody (by
      intro left right equal
      cases equal
      rfl)
  have postfixUnique := allGuardContexts_map_nodup tokens
    GuardContext.postfixInvocation (by
      intro left right equal
      cases equal
      rfl)
  rw [allGuardContexts, List.nodup_cons]
  refine ⟨by simp, ?_⟩
  rw [List.nodup_append]
  refine ⟨?_, postfixUnique, ?_⟩
  rw [List.nodup_append]
  exact ⟨bracedUnique, armUnique, by simp⟩
  intro left leftMember right rightMember equal
  rw [List.mem_append] at leftMember
  rw [List.mem_map] at rightMember
  rcases rightMember with ⟨rightBoundary, _, rfl⟩
  cases leftMember with
  | inl bracedMember =>
      rw [List.mem_map] at bracedMember
      rcases bracedMember with ⟨leftBoundary, _, rfl⟩
      cases equal
  | inr armMember =>
      rw [List.mem_map] at armMember
      rcases armMember with ⟨leftBoundary, _, rfl⟩
      cases equal

private theorem allGuardContexts_length (tokens : List Token) :
    (allGuardContexts tokens).length =
      1 + 3 * (tokens.length + 2) := by
  simp [allGuardContexts, allBoundaries_length]
  omega

/-- Every contextual chart item in stable raw-item and context order. -/
def allContextualItems (tokens : List Token) :
    List (ContextualItemKey tokens) :=
  (allDottedItems tokens).flatMap fun raw =>
    (allGuardContexts tokens).map fun context => { raw, context }

/-- Every contextual chart item occurs in the stable finite enumeration. -/
theorem allContextualItems_complete {tokens : List Token}
    (item : ContextualItemKey tokens) :
    item ∈ allContextualItems tokens := by
  rw [allContextualItems, List.mem_flatMap]
  refine ⟨item.raw, allDottedItems_complete item.raw, ?_⟩
  rw [List.mem_map]
  exact ⟨item.context, allGuardContexts_complete item.context, by
    cases item
    rfl⟩

/-- The contextual-item enumeration contains no duplicate key. -/
theorem allContextualItems_nodup (tokens : List Token) :
    (allContextualItems tokens).Nodup := by
  apply dependentEnumeration_nodup (allDottedItems tokens)
    (fun _ => allGuardContexts tokens)
    (fun raw context => ({ raw, context } : ContextualItemKey tokens))
    (allDottedItems_nodup tokens)
    (fun _ => allGuardContexts_nodup tokens)
  intro left right leftContext rightContext equal
  cases left
  cases right
  cases equal
  rfl

/-- The contextual-item enumeration has the displayed Phase-C cardinality. -/
theorem allContextualItems_length (tokens : List Token) :
    (allContextualItems tokens).length =
      (1 + 3 * (tokens.length + 2)) * D *
        (tokens.length + 2) * (tokens.length + 2) := by
  rw [allContextualItems]
  rw [dependentEnumeration_length (allDottedItems tokens)
    (fun _ => allGuardContexts tokens) _
    (1 + 3 * (tokens.length + 2))
    (fun _ => allGuardContexts_length tokens)]
  rw [allDottedItems_length]
  simp only [Nat.mul_comm, Nat.mul_left_comm]

/-- A proof-free contextual scan or completion edge key. -/
inductive ContextualPackedEdgeKey (tokens : List Token) where
  | scanned
      (before after : ContextualItemKey tokens)
      (terminalCursor : TerminalCursor tokens)
  | completed
      (waiting finished after : ContextualItemKey tokens)
      (sharedCursor : Boundary tokens)
  deriving Repr, BEq, DecidableEq

/-- The definitionally complete contextual item for one root production. -/
def CanonicalCompleteRootItem
    (tokens : List Token)
    (rule : GrammarRuleId)
    (origin finish : Boundary tokens)
    (context : GuardContext tokens) :
    ContextualItemKey tokens := {
  raw := {
    production := ProductionId.root rule
    dot := {
      val := (ProductionId.root rule).rhs.length
      isLt := Nat.lt_succ_self _
    }
    origin := origin
    current := finish
  }
  context := context
}

/-- Select the exact guard context inherited by one predicted production. -/
def descendContext {tokens : List Token}
    (waiting : ContextualItemKey tokens)
    (predicted : ProductionId) : GuardContext tokens :=
  match predicted with
  | .root .postfix =>
      .postfixInvocation waiting.raw.current
  | _ =>
      match waiting.raw.production, predicted.lhs with
      | .seq waitingSite, .aux predictedSite =>
          if waitingSite.site.isAt .body [] &&
              waiting.raw.dot.val == 1 &&
              predictedSite.isAt .body [1] then
            .bracedBody waiting.raw.current
          else if waitingSite.site.isAt .matchArm [] &&
              waiting.raw.dot.val == 3 &&
              predictedSite.isAt .matchArm [3] then
            .armBody waiting.raw.current
          else
            waiting.context
      | _, _ => waiting.context

/-- Select the unique context start allowed by one closed priority guard. -/
private def guardAnchorContextStart?
    {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens)
    (guard : PriorityGuardId) : Option (Boundary tokens) :=
  match guard with
  | .G01_statementIf => some productionInstance.origin
  | .G02_matchArmBoundary =>
      match productionInstance.context with
      | .armBody armBodyStart => some armBodyStart
      | _ => none
  | .G03_parameterComptime => some productionInstance.origin
  | .G04_letComptime => some productionInstance.origin
  | .G05_typeComptime => some productionInstance.origin
  | .G06_patternComptime => some productionInstance.origin
  | .G07_leadingDotArguments =>
      match productionInstance.context with
      | .postfixInvocation postfixStart => some postfixStart
      | _ => none
  | .G08_terminalExpression =>
      match productionInstance.context with
      | .bracedBody bodyStart => some bodyStart
      | .armBody armBodyStart => some armBodyStart
      | _ => none
  | .G09_genericContext => some productionInstance.origin

/-- Constructive membership decision for the closed guard-cell lists. -/
private def decidableGuardCellMem
    (cell : PriorityGuardId × Polarity) :
    (cells : List (PriorityGuardId × Polarity)) → Decidable (cell ∈ cells)
  | [] => isFalse (by simp)
  | candidate :: rest =>
      if same : cell = candidate then
        isTrue (List.mem_cons.mpr (Or.inl same))
      else
        match decidableGuardCellMem cell rest with
        | isTrue member =>
            isTrue (List.mem_cons_of_mem candidate member)
        | isFalse absent =>
            isFalse (by
              intro member
              rcases List.mem_cons.mp member with equal | inRest
              · exact same equal
              · exact absent inRest)

/-- The exact structural anchor of one grammar-owned priority-guard cell. -/
def GuardAnchor
    {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens)
    (cell : PriorityGuardId × Polarity)
    (guardInstance : GuardInstanceKey tokens) : Prop :=
  cell ∈ guardOf productionInstance.production ∧
    guardInstance.guard = cell.1 ∧
    guardInstance.siteCursor = productionInstance.origin ∧
    guardAnchorContextStart? productionInstance cell.1 =
      some guardInstance.contextStart

namespace GuardAnchor

/-- A production cell determines at most one structural guard anchor. -/
theorem functional
    {tokens : List Token}
    {productionInstance : ProductionInstanceKey tokens}
    {cell : PriorityGuardId × Polarity}
    {left right : GuardInstanceKey tokens}
    (leftAnchor : GuardAnchor productionInstance cell left)
    (rightAnchor : GuardAnchor productionInstance cell right) :
    left = right := by
  rcases left with ⟨leftGuard, leftStart, leftSite, _leftOrdered⟩
  rcases right with ⟨rightGuard, rightStart, rightSite, _rightOrdered⟩
  rcases leftAnchor with
    ⟨_leftMember, leftGuardEq, leftSiteEq, leftStartEq⟩
  rcases rightAnchor with
    ⟨_rightMember, rightGuardEq, rightSiteEq, rightStartEq⟩
  have guardEq : leftGuard = rightGuard :=
    leftGuardEq.trans rightGuardEq.symm
  have startEq : leftStart = rightStart :=
    Option.some.inj (leftStartEq.symm.trans rightStartEq)
  have siteEq : leftSite = rightSite :=
    leftSiteEq.trans rightSiteEq.symm
  cases guardEq
  cases startEq
  cases siteEq
  rfl

/-- Compute the exact structural anchor of one grammar-owned guard cell. -/
def decide
    {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens)
    (cell : PriorityGuardId × Polarity) :
    Option (GuardInstanceKey tokens) :=
  letI : Decidable (cell ∈ guardOf productionInstance.production) :=
    decidableGuardCellMem cell (guardOf productionInstance.production)
  if _member : cell ∈ guardOf productionInstance.production then
    match guardAnchorContextStart? productionInstance cell.1 with
    | none => none
    | some contextStart =>
        if ordered : contextStart.val ≤ productionInstance.origin.val then
          some {
            guard := cell.1
            contextStart := contextStart
            siteCursor := productionInstance.origin
            ordered := ordered
          }
        else
          none
  else
    none

/-- The anchor computation succeeds exactly for the structural relation. -/
theorem decide_eq_some_iff
    {tokens : List Token}
    {productionInstance : ProductionInstanceKey tokens}
    {cell : PriorityGuardId × Polarity}
    {guardInstance : GuardInstanceKey tokens} :
    decide productionInstance cell = some guardInstance ↔
      GuardAnchor productionInstance cell guardInstance := by
  rcases guardInstance with
    ⟨guard, contextStart, siteCursor, instanceOrdered⟩
  unfold decide GuardAnchor
  by_cases member : cell ∈ guardOf productionInstance.production
  · cases startResult : guardAnchorContextStart? productionInstance cell.1 with
    | none =>
        simp [member]
    | some start =>
        by_cases ordered : start.val ≤ productionInstance.origin.val
        · simp [member]
          constructor
          · rintro ⟨guardEq, startEq, _startOrdered, siteEq⟩
            exact ⟨guardEq.symm, siteEq.symm, startEq⟩
          · rintro ⟨guardEq, siteEq, startEq⟩
            exact ⟨guardEq.symm, startEq, ordered, siteEq.symm⟩
        · simp [member]
          constructor
          · rintro ⟨_guardEq, _startEq, startOrdered, _siteEq⟩
            exact (ordered startOrdered).elim
          · rintro ⟨_guardEq, siteEq, startEq⟩
            apply (ordered ?_).elim
            have startValEq : start.val = contextStart.val :=
              congrArg Fin.val startEq
            have siteValEq : siteCursor.val =
                productionInstance.origin.val :=
              congrArg Fin.val siteEq
            omega
  · simp [member]

end GuardAnchor

/-- The unfinished or sealed state of one priority-guard computation. -/
inductive GuardMemoState where
  | undecided
  | final (decision : GuardDecision)
  deriving Repr, BEq, DecidableEq

/-- A table of priority-guard states indexed by their structural anchors. -/
abbrev GuardMemo (tokens : List Token) : Type :=
  GuardInstanceKey tokens → GuardMemoState

/-- Every structural guard query has reached a sealed decision. -/
def AllGuardsFinal
    {tokens : List Token}
    (memo : GuardMemo tokens) : Prop :=
  ∀ key : GuardInstanceKey tokens,
    ∃ decision : GuardDecision, memo key = .final decision

namespace GuardWitnessKey

/-- The proof-free production cell and structural anchor retained by a chart. -/
structure Raw (tokens : List Token) where
  productionInstance : ProductionInstanceKey tokens
  guardInstance : GuardInstanceKey tokens
  polarity : Polarity
  deriving Repr, BEq, DecidableEq

/-- A retained guard key names an exact guarded production-table cell. -/
def Valid
    {tokens : List Token}
    (raw : Raw tokens) : Prop :=
  (raw.guardInstance.guard, raw.polarity) ∈
      guardOf raw.productionInstance.production ∧
    GuardAnchor raw.productionInstance
      (raw.guardInstance.guard, raw.polarity) raw.guardInstance

end GuardWitnessKey

/-- The proof-irrelevant subtype of structurally valid retained guard keys. -/
abbrev GuardWitnessKey (tokens : List Token) : Type :=
  { raw : GuardWitnessKey.Raw tokens // GuardWitnessKey.Valid raw }

namespace GuardWitnessKey

/-- Project the guarded production instance through the checked subtype. -/
def productionInstance
    {tokens : List Token}
    (key : GuardWitnessKey tokens) : ProductionInstanceKey tokens :=
  key.val.productionInstance

/-- Project the structural guard instance through the checked subtype. -/
def guardInstance
    {tokens : List Token}
    (key : GuardWitnessKey tokens) : GuardInstanceKey tokens :=
  key.val.guardInstance

/-- Project the guarded production polarity through the checked subtype. -/
def polarity
    {tokens : List Token}
    (key : GuardWitnessKey tokens) : Polarity :=
  key.val.polarity

end GuardWitnessKey

namespace Grammar

/-- One cell of the executable guard table, retaining its full production. -/
private structure GuardTableCell where
  production : ProductionId
  guard : PriorityGuardId
  polarity : Polarity
  deriving Repr, DecidableEq

/-- All cells of the executable guard table in production order. -/
private def allGuardTableCells : List GuardTableCell :=
  allProductionIds.flatMap fun production =>
    (guardOf production).map fun cell => {
      production := production
      guard := cell.1
      polarity := cell.2
    }

private theorem allGuardTableCells_length :
    allGuardTableCells.length = H := by
  simp [H, allGuardTableCells]

private theorem allGuardTableCells_complete
    (production : ProductionId) (guard : PriorityGuardId)
    (polarity : Polarity)
    (member : (guard, polarity) ∈ guardOf production) :
    ({ production, guard, polarity } : GuardTableCell) ∈
      allGuardTableCells := by
  rw [allGuardTableCells, List.mem_flatMap]
  refine ⟨production, allProductionIds_complete production, ?_⟩
  rw [List.mem_map]
  exact ⟨(guard, polarity), member, rfl⟩

/-- Stable rank of a full cell in the executable guard table. -/
private def GuardTableCell.rank (cell : GuardTableCell) : Nat :=
  allGuardTableCells.findIdx fun candidate => decide (candidate = cell)

private theorem GuardTableCell.rank_lt
    (cell : GuardTableCell) (member : cell ∈ allGuardTableCells) :
    cell.rank < H := by
  rw [GuardTableCell.rank, ← allGuardTableCells_length,
    List.findIdx_lt_length]
  exact ⟨cell, member, by simp⟩

private theorem GuardTableCell.rank_injective_on_mem
    {left right : GuardTableCell}
    (leftMember : left ∈ allGuardTableCells)
    (rightMember : right ∈ allGuardTableCells)
    (same : left.rank = right.rank) :
    left = right := by
  have leftBound := left.rank_lt leftMember
  have rightBound := right.rank_lt rightMember
  have leftLengthBound : left.rank < allGuardTableCells.length := by
    rw [allGuardTableCells_length]
    exact leftBound
  have rightLengthBound : right.rank < allGuardTableCells.length := by
    rw [allGuardTableCells_length]
    exact rightBound
  have leftFound := List.findIdx_getElem
    (p := fun candidate : GuardTableCell => decide (candidate = left))
    (xs := allGuardTableCells) (w := leftLengthBound)
  have rightFound := List.findIdx_getElem
    (p := fun candidate : GuardTableCell => decide (candidate = right))
    (xs := allGuardTableCells) (w := rightLengthBound)
  change decide
    (allGuardTableCells[left.rank] = left) = true at leftFound
  change decide
    (allGuardTableCells[right.rank] = right) = true at rightFound
  have leftEq : allGuardTableCells[left.rank] = left :=
    of_decide_eq_true leftFound
  have rightEq : allGuardTableCells[right.rank] = right :=
    of_decide_eq_true rightFound
  have sameIndex :
      (⟨left.rank, leftLengthBound⟩ : Fin allGuardTableCells.length) =
        ⟨right.rank, rightLengthBound⟩ := Fin.ext same
  have sameEntry := congrArg
    (fun index : Fin allGuardTableCells.length =>
      allGuardTableCells[index]) sameIndex
  exact leftEq.symm.trans (sameEntry.trans rightEq)

end Grammar

namespace GuardWitnessKey

private def tableCell {tokens : List Token}
    (key : GuardWitnessKey tokens) : GuardTableCell := {
  production := key.productionInstance.production
  guard := key.guardInstance.guard
  polarity := key.polarity
}

private theorem tableCell_mem {tokens : List Token}
    (key : GuardWitnessKey tokens) :
    tableCell key ∈ allGuardTableCells := by
  exact allGuardTableCells_complete _ _ _ key.property.1

end GuardWitnessKey

private theorem mixedRadix_injective {width : Nat}
    {leftBlock rightBlock leftOffset rightOffset : Nat}
    (leftOffsetBound : leftOffset < width)
    (rightOffsetBound : rightOffset < width)
    (equality :
      leftBlock * width + leftOffset =
        rightBlock * width + rightOffset) :
    leftBlock = rightBlock ∧ leftOffset = rightOffset := by
  have widthPositive : 0 < width := Nat.zero_lt_of_lt leftOffsetBound
  have quotient (block offset : Nat) (offsetBound : offset < width) :
      (block * width + offset) / width = block := by
    rw [Nat.add_comm, Nat.mul_comm block width,
      Nat.add_mul_div_left _ _ widthPositive, Nat.div_eq_of_lt offsetBound]
    exact Nat.zero_add block
  have sameBlock : leftBlock = rightBlock := by
    rw [← quotient leftBlock leftOffset leftOffsetBound,
      equality, quotient rightBlock rightOffset rightOffsetBound]
  constructor
  · exact sameBlock
  · rw [sameBlock] at equality
    exact Nat.add_left_cancel equality

private theorem productionInstance_eq_of_fields
    {tokens : List Token} {left right : ProductionInstanceKey tokens}
    (production : left.production = right.production)
    (origin : left.origin = right.origin)
    (context : left.context = right.context) :
    left = right := by
  cases left
  cases right
  simp only at production origin context
  cases production
  cases origin
  cases context
  rfl

private theorem GuardWitnessKey.Raw.eq_of_fields
    {tokens : List Token} {left right : GuardWitnessKey.Raw tokens}
    (productionInstance :
      left.productionInstance = right.productionInstance)
    (guardInstance : left.guardInstance = right.guardInstance)
    (polarity : left.polarity = right.polarity) :
    left = right := by
  cases left
  cases right
  simp only at productionInstance guardInstance polarity
  cases productionInstance
  cases guardInstance
  cases polarity
  rfl

/-- Guard witnesses inject into their exact grammar cell, context, and origin. -/
theorem guard_witness_cardinality (tokens : List Token) :
    ∃ encode : GuardWitnessKey tokens →
        Fin (H * (1 + 3 * (tokens.length + 2)) * (tokens.length + 2)),
      Function.Injective encode := by
  obtain ⟨contextEncode, contextInjective, _contextSurjective⟩ :=
    guard_context_cardinality tokens
  let q := tokens.length + 2
  let c := 1 + 3 * q
  let rawEncode (key : GuardWitnessKey tokens) : Nat :=
    (key.tableCell.rank * c +
      (contextEncode key.productionInstance.context).val) * q +
      key.productionInstance.origin.val
  let encode (key : GuardWitnessKey tokens) :
      Fin (H * (1 + 3 * (tokens.length + 2)) *
        (tokens.length + 2)) := ⟨rawEncode key, by
    have cellBound := key.tableCell.rank_lt key.tableCell_mem
    have contextBound :=
      (contextEncode key.productionInstance.context).isLt
    have originBound := key.productionInstance.origin.isLt
    have innerBound :
        key.tableCell.rank * c +
            (contextEncode key.productionInstance.context).val < H * c := by
      have rowBound :
          key.tableCell.rank * c +
              (contextEncode key.productionInstance.context).val <
            (key.tableCell.rank + 1) * c := by
        rw [Nat.add_mul]
        simpa only [Nat.one_mul] using
          Nat.add_lt_add_left contextBound (key.tableCell.rank * c)
      exact Nat.lt_of_lt_of_le rowBound
        (Nat.mul_le_mul_right c (Nat.succ_le_of_lt cellBound))
    have outerBound : rawEncode key < H * c * q := by
      have blockBound :
          (key.tableCell.rank * c +
              (contextEncode key.productionInstance.context).val) * q +
              key.productionInstance.origin.val <
            ((key.tableCell.rank * c +
              (contextEncode key.productionInstance.context).val) + 1) * q := by
        calc
          _ < (key.tableCell.rank * c +
                (contextEncode key.productionInstance.context).val) * q + q :=
            Nat.add_lt_add_left originBound _
          _ = _ := by simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      exact Nat.lt_of_lt_of_le blockBound
        (Nat.mul_le_mul_right q (Nat.succ_le_of_lt innerBound))
    simpa [q, c] using outerBound
  ⟩
  refine ⟨encode, ?_⟩
  intro left right equality
  have rawEquality : rawEncode left = rawEncode right :=
    congrArg Fin.val equality
  have originBlocks := mixedRadix_injective
    left.productionInstance.origin.isLt
    right.productionInstance.origin.isLt rawEquality
  have contextBlocks := mixedRadix_injective
    (contextEncode left.productionInstance.context).isLt
    (contextEncode right.productionInstance.context).isLt originBlocks.1
  have cellEq : left.tableCell = right.tableCell :=
    GuardTableCell.rank_injective_on_mem
      left.tableCell_mem right.tableCell_mem contextBlocks.1
  have productionEq : left.productionInstance.production =
      right.productionInstance.production :=
    congrArg GuardTableCell.production cellEq
  have guardEq : left.guardInstance.guard = right.guardInstance.guard :=
    congrArg GuardTableCell.guard cellEq
  have polarityEq : left.polarity = right.polarity :=
    congrArg GuardTableCell.polarity cellEq
  have contextEq : left.productionInstance.context =
      right.productionInstance.context := by
    apply contextInjective
    apply Fin.ext
    exact contextBlocks.2
  have originEq : left.productionInstance.origin =
      right.productionInstance.origin :=
    Fin.ext originBlocks.2
  have productionInstanceEq : left.productionInstance =
      right.productionInstance :=
    productionInstance_eq_of_fields productionEq originEq contextEq
  have leftAnchor := left.property.2
  have rightAnchor := right.property.2
  change left.val.productionInstance =
    right.val.productionInstance at productionInstanceEq
  change left.val.guardInstance.guard =
    right.val.guardInstance.guard at guardEq
  change left.val.polarity = right.val.polarity at polarityEq
  rw [productionInstanceEq, guardEq, polarityEq] at leftAnchor
  have guardInstanceEq : left.val.guardInstance = right.val.guardInstance :=
    GuardAnchor.functional leftAnchor rightAnchor
  apply Subtype.ext
  change left.val = right.val
  exact GuardWitnessKey.Raw.eq_of_fields
    productionInstanceEq guardInstanceEq polarityEq

/-- The absent or source-preserving comma between repeated forall binders. -/
inductive OptionalCommaValue where
  | absent
  | present (comma : SourceSpan)

/-- One source-preserving postfix operation before it is folded over a callee. -/
inductive PostfixPartValue where
  | call
      (openParen : SourceSpan)
      (arguments : List Expression)
      (closeParen : SourceSpan)
  | select
      (dot : SourceSpan)
      (field : IdentifierOccurrence)
  | index
      (openBracket : SourceSpan)
      (index : Expression)
      (closeBracket : SourceSpan)

/-- The exact semantic result carrier of each of the seventy-five source rules. -/
def RuleValue : GrammarRuleId → Type
  | .module => ParsedModuleV1
  | .topItem => TopItem
  | .moduleRef => ModuleReference
  | .importDecl => ImportDecl
  | .importEntry => ImportSelectorEntry
  | .hidingClause => HidingClause
  | .exportDecl => ExportDecl
  | .localExportEntry => ExportEntry
  | .remoteExportEntry => RemoteExportEntry
  | .exportItem => ExportItem
  | .constructorSelection => ConstructorSelection
  | .pragmaDecl => PragmaDecl
  | .genericPrefix => GenericPrefix
  | .forallClause => ForallClause
  | .forallBinder => ForallBinder
  | .optionalComma => OptionalCommaValue
  | .predicateList => NonemptyList Predicate
  | .predicate => Predicate
  | .functionSignature => FunctionSignature
  | .functionDecl => FunctionDecl
  | .classMethod => ClassMethodDecl
  | .dataDecl => DataDecl
  | .dataConstructor => DataConstructor
  | .typeAliasDecl => TypeAliasDecl
  | .classDecl => ClassDecl
  | .instanceDecl => InstanceDecl
  | .instanceMethod => FunctionDecl
  | .contractDecl => ContractDecl
  | .contractMember => ContractMember
  | .fieldDecl => FieldDecl
  | .fallbackDecl => FallbackDecl
  | .contractConstructorDecl => ContractConstructorDecl
  | .parameter => Parameter
  | .body => Body
  | .type => TypeExpr
  | .typeAtom => TypeExpr
  | .qualifiedName => QualifiedName
  | .statement => Statement
  | .letStatement => Statement
  | .letBinding => LetBinding
  | .returnStatement => Statement
  | .blockStatement => Statement
  | .breakStatement => Statement
  | .continueStatement => Statement
  | .assemblyStatement => Statement
  | .ifStatement => Statement
  | .forStatement => Statement
  | .forInitItem => ForInitItem
  | .forPostItem => ForPostItem
  | .matchStatement => Statement
  | .matchArm => MatchArm
  | .armStatement => Statement
  | .assignmentStatement => Statement
  | .assignmentOperator => Located AssignmentOperator
  | .expressionStatement => Statement
  | .terminalExpression => Expression
  | .pattern => Pattern
  | .expression => Expression
  | .annotation => Expression
  | .conditional => Expression
  | .logicalOr => Expression
  | .logicalAnd => Expression
  | .equality => Expression
  | .relational => Expression
  | .bitOr => Expression
  | .bitXor => Expression
  | .bitAnd => Expression
  | .additive => Expression
  | .multiplicative => Expression
  | .prefix => Expression
  | .postfix => Expression
  | .postfixPart => PostfixPartValue
  | .atom => Expression
  | .lambda => Expression
  | .literal => Literal

/-- The literal equation tags of `RuleValue`, in definition branch order. -/
def ruleValueEquationTags : List GrammarRuleId := [
  .module, .topItem, .moduleRef, .importDecl, .importEntry,
  .hidingClause, .exportDecl, .localExportEntry, .remoteExportEntry,
  .exportItem, .constructorSelection, .pragmaDecl, .genericPrefix,
  .forallClause, .forallBinder, .optionalComma, .predicateList,
  .predicate, .functionSignature, .functionDecl, .classMethod, .dataDecl,
  .dataConstructor, .typeAliasDecl, .classDecl, .instanceDecl,
  .instanceMethod, .contractDecl, .contractMember, .fieldDecl,
  .fallbackDecl, .contractConstructorDecl, .parameter, .body, .type,
  .typeAtom, .qualifiedName, .statement, .letStatement, .letBinding,
  .returnStatement, .blockStatement, .breakStatement, .continueStatement,
  .assemblyStatement, .ifStatement, .forStatement, .forInitItem,
  .forPostItem, .matchStatement, .matchArm, .armStatement,
  .assignmentStatement, .assignmentOperator, .expressionStatement,
  .terminalExpression, .pattern, .expression, .annotation, .conditional,
  .logicalOr, .logicalAnd, .equality, .relational, .bitOr, .bitXor,
  .bitAnd, .additive, .multiplicative, .prefix, .postfix, .postfixPart,
  .atom, .lambda, .literal
]

/-- The semantic carrier has one explicit equation for every source rule. -/
theorem ruleValue_allGrammarRuleIds_exhaustive :
    ruleValueEquationTags = allGrammarRuleIds := by
  rfl

/-- The symbol selected by the dot of one incomplete item. -/
def NextSymbol {tokens : List Token}
    (item : DottedItem tokens) (symbol : GrammarSymbol) : Prop :=
  item.dot.val < item.production.rhs.length ∧
    item.production.rhs[item.dot.val]? = some symbol

/-- An item whose dot is exactly at the end of its production. -/
def CompleteItem {tokens : List Token} (item : DottedItem tokens) : Prop :=
  item.dot.val = item.production.rhs.length

/-- The exact structural update that advances one item's dot and cursor. -/
def AdvanceItem {tokens : List Token}
    (before : DottedItem tokens) (next : Boundary tokens)
    (after : DottedItem tokens) : Prop :=
  after.production = before.production ∧
    after.dot.val = before.dot.val + 1 ∧
    after.origin = before.origin ∧
    after.current = next

/-- A dot at zero selects the empty right-hand-side prefix. -/
theorem prefix_zero_layout
    {tokens : List Token}
    (item : DottedItem tokens)
    (zero : item.dot.val = 0) :
    [] = item.production.rhs.take item.dot.val := by
  rw [zero, List.take_zero]

/-- Scanning the next terminal appends exactly that terminal to the prefix. -/
theorem prefix_scan_layout
    {tokens : List Token}
    (before after : DottedItem tokens)
    (terminal : TerminalSymbol)
    (nextBoundary : Boundary tokens)
    (next : NextSymbol before (GrammarSymbol.terminal terminal))
    (advance : AdvanceItem before nextBoundary after) :
    before.production.rhs.take before.dot.val ++
        [GrammarSymbol.terminal terminal] =
      after.production.rhs.take after.dot.val := by
  rcases next with ⟨_inRange, lookup⟩
  rcases advance with ⟨production, dot, _origin, _current⟩
  have rhs : after.production.rhs = before.production.rhs :=
    congrArg ProductionId.rhs production
  rw [dot, rhs, List.take_add_one, lookup]
  rfl

/-- Completing the next nonterminal appends exactly that symbol to the prefix. -/
theorem prefix_complete_layout
    {tokens : List Token}
    (waiting finished after : DottedItem tokens)
    (next : NextSymbol waiting
      (GrammarSymbol.nonterminal finished.production.lhs))
    (advance : AdvanceItem waiting finished.current after) :
    waiting.production.rhs.take waiting.dot.val ++
        [GrammarSymbol.nonterminal finished.production.lhs] =
      after.production.rhs.take after.dot.val := by
  rcases next with ⟨_inRange, lookup⟩
  rcases advance with ⟨production, dot, _origin, _current⟩
  have rhs : after.production.rhs = waiting.production.rhs :=
    congrArg ProductionId.rhs production
  rw [dot, rhs, List.take_add_one, lookup]
  rfl

/-- A complete item's right-hand-side prefix is the full right-hand side. -/
theorem prefix_full_layout
    {tokens : List Token}
    (item : DottedItem tokens)
    (complete : CompleteItem item) :
    item.production.rhs.take item.dot.val = item.production.rhs := by
  unfold CompleteItem at complete
  rw [complete, List.take_length]

/-- The canonical root item is definitionally complete. -/
theorem canonicalCompleteRootItem_complete
    {tokens : List Token}
    (rule : GrammarRuleId)
    (origin finish : Boundary tokens)
    (context : GuardContext tokens) :
    CompleteItem
      (CanonicalCompleteRootItem tokens rule origin finish context).raw := by
  rfl

/-- The parser's terminal stream consists of retained tokens and logical EOF. -/
inductive TerminalStreamValue where
  | retained (token : Token)
  | endOfFile
  deriving Repr, BEq, DecidableEq

/-- Every retained token is valid for the file that owns the token stream. -/
def TokensOwnedBy (file : WorkspaceFile) (tokens : List Token) : Prop :=
  ∀ token, token ∈ tokens → token.span.ValidFor file

/-- Token-stream ownership is exactly pointwise validity of every member. -/
theorem tokensOwnedBy_exact
    (file : WorkspaceFile) (tokens : List Token) :
    TokensOwnedBy file tokens ↔
      ∀ token, token ∈ tokens → token.span.ValidFor file := by
  rfl

/-- Exact lookup in the retained-token stream extended by one logical EOF. -/
inductive TerminalAt
    (file : WorkspaceFile)
    (tokens : List Token) :
    TerminalCursor tokens → TerminalStreamValue → SourceSpan → Prop where
  | retained
      (cursor : TerminalCursor tokens)
      (token : Token)
      (inRange : cursor.val < tokens.length)
      (lookup : tokens[cursor.val]? = some token)
      (valid : token.span.ValidFor file) :
      TerminalAt file tokens cursor (.retained token) token.span
  | endOfFile
      (cursor : TerminalCursor tokens)
      (atEnd : cursor.val = tokens.length) :
      TerminalAt file tokens cursor .endOfFile {
        source := file.id
        startByte := file.content.utf8ByteSize
        endByte := file.content.utf8ByteSize
      }

namespace TerminalAt

/-- One terminal cursor determines both its terminal-stream value and span. -/
theorem functional
    {file : WorkspaceFile} {tokens : List Token}
    {cursor : TerminalCursor tokens}
    {leftValue rightValue : TerminalStreamValue}
    {leftSpan rightSpan : SourceSpan}
    (leftAt : TerminalAt file tokens cursor leftValue leftSpan)
    (rightAt : TerminalAt file tokens cursor rightValue rightSpan) :
    leftValue = rightValue ∧ leftSpan = rightSpan := by
  cases leftAt with
  | retained leftToken leftInRange leftLookup leftValid =>
      cases rightAt with
      | retained rightToken rightInRange rightLookup rightValid =>
          have tokenEq : leftToken = rightToken :=
            Option.some.inj (leftLookup.symm.trans rightLookup)
          subst rightToken
          exact ⟨rfl, rfl⟩
      | endOfFile atEnd => omega
  | endOfFile leftAtEnd =>
      cases rightAt with
      | retained rightToken rightInRange rightLookup rightValid => omega
      | endOfFile rightAtEnd => exact ⟨rfl, rfl⟩

end TerminalAt

/-- Exact agreement between one grammar terminal and one terminal-stream value. -/
def TerminalMatches : TerminalSymbol → TerminalStreamValue → Prop
  | .hardKeyword keyword, .retained token =>
      token.payload = .hardKeyword keyword
  | .contextualKeyword keyword, .retained token =>
      token.payload = .identifier keyword.spelling
  | .pragmaName kind, .retained token =>
      token.payload = .pragmaName kind
  | .symbol symbol, .retained token =>
      token.payload = .symbol symbol
  | .category .identifier, .retained token =>
      ∃ text parsed,
        token.payload = .identifier text ∧
          Identifier.parse text = some parsed
  | .category .pathComponent, .retained token =>
      (∃ text parsed,
        token.payload = .identifier text ∧
          PathSegment.parse text = some parsed) ∨
      (∃ keyword parsed,
        token.payload = .hardKeyword keyword ∧
          PathSegment.parse keyword.spelling = some parsed)
  | .category .decimalLiteral, .retained token =>
      ∃ spelling digits,
        token.payload = .decimalLiteral spelling digits
  | .category .hexadecimalLiteral, .retained token =>
      ∃ spelling digits,
        token.payload = .hexadecimalLiteral spelling digits
  | .category .stringLiteral, .retained token =>
      ∃ spelling decoded,
        token.payload = .stringLiteral spelling decoded
  | .category .assemblyBlock, .retained token =>
      ∃ slice, token.payload = .assemblyBlock slice
  | .endOfFile, .endOfFile => True
  | _, _ => False

/-- Enumerate every and only terminal/value pair accepted by the grammar. -/
theorem terminalMatches_exact
    (terminal : TerminalSymbol) (value : TerminalStreamValue) :
    TerminalMatches terminal value ↔
      (∃ keyword token,
        terminal = .hardKeyword keyword ∧
          value = .retained token ∧
          token.payload = .hardKeyword keyword) ∨
      (∃ keyword token,
        terminal = .contextualKeyword keyword ∧
          value = .retained token ∧
          token.payload = .identifier keyword.spelling) ∨
      (∃ kind token,
        terminal = .pragmaName kind ∧
          value = .retained token ∧
          token.payload = .pragmaName kind) ∨
      (∃ symbol token,
        terminal = .symbol symbol ∧
          value = .retained token ∧
          token.payload = .symbol symbol) ∨
      (∃ token text parsed,
        terminal = .category .identifier ∧
          value = .retained token ∧
          token.payload = .identifier text ∧
          Identifier.parse text = some parsed) ∨
      (∃ token,
        terminal = .category .pathComponent ∧
          value = .retained token ∧
          ((∃ text parsed,
              token.payload = .identifier text ∧
                PathSegment.parse text = some parsed) ∨
            (∃ keyword parsed,
              token.payload = .hardKeyword keyword ∧
                PathSegment.parse keyword.spelling = some parsed))) ∨
      (∃ token spelling digits,
        terminal = .category .decimalLiteral ∧
          value = .retained token ∧
          token.payload = .decimalLiteral spelling digits) ∨
      (∃ token spelling digits,
        terminal = .category .hexadecimalLiteral ∧
          value = .retained token ∧
          token.payload = .hexadecimalLiteral spelling digits) ∨
      (∃ token spelling decoded,
        terminal = .category .stringLiteral ∧
          value = .retained token ∧
          token.payload = .stringLiteral spelling decoded) ∨
      (∃ token slice,
        terminal = .category .assemblyBlock ∧
          value = .retained token ∧
          token.payload = .assemblyBlock slice) ∨
      (terminal = .endOfFile ∧ value = .endOfFile) := by
  cases terminal with
  | hardKeyword keyword =>
      cases value <;> simp [TerminalMatches]
  | contextualKeyword keyword =>
      cases value <;> simp [TerminalMatches]
  | pragmaName kind =>
      cases value <;> simp [TerminalMatches]
  | symbol symbol =>
      cases value <;> simp [TerminalMatches]
  | category category =>
      cases category <;> cases value <;> simp [TerminalMatches]
  | endOfFile =>
      cases value <;> simp [TerminalMatches]

/-- A terminal-stream value together with its exact lookup and match evidence. -/
structure MatchedTerminal
    (file : WorkspaceFile)
    (tokens : List Token)
    (terminal : TerminalSymbol) where
  cursor : TerminalCursor tokens
  value : TerminalStreamValue
  span : SourceSpan
  «at» : TerminalAt file tokens cursor value span
  «matches» : TerminalMatches terminal value
  deriving Repr, DecidableEq

instance {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol} :
    BEq (MatchedTerminal file tokens terminal) :=
  ⟨fun left right => decide (left = right)⟩

/-- Constructive executable test for the declarative terminal match. -/
def terminalMatchesBool : TerminalSymbol → TerminalStreamValue → Bool
  | .hardKeyword expected, .retained token =>
      decide (token.payload = .hardKeyword expected)
  | .contextualKeyword expected, .retained token =>
      decide (token.payload = .identifier expected.spelling)
  | .pragmaName expected, .retained token =>
      decide (token.payload = .pragmaName expected)
  | .symbol expected, .retained token =>
      decide (token.payload = .symbol expected)
  | .category .identifier, .retained token =>
      match token.payload with
      | .identifier text => (Identifier.parse text).isSome
      | _ => false
  | .category .pathComponent, .retained token =>
      match token.payload with
      | .identifier text => (PathSegment.parse text).isSome
      | .hardKeyword keyword => (PathSegment.parse keyword.spelling).isSome
      | _ => false
  | .category .decimalLiteral, .retained token =>
      match token.payload with
      | .decimalLiteral _ _ => true
      | _ => false
  | .category .hexadecimalLiteral, .retained token =>
      match token.payload with
      | .hexadecimalLiteral _ _ => true
      | _ => false
  | .category .stringLiteral, .retained token =>
      match token.payload with
      | .stringLiteral _ _ => true
      | _ => false
  | .category .assemblyBlock, .retained token =>
      match token.payload with
      | .assemblyBlock _ => true
      | _ => false
  | .endOfFile, .endOfFile => true
  | _, _ => false

/-- The executable terminal test accepts exactly the declarative relation. -/
theorem terminalMatchesBool_eq_true_iff
    (terminal : TerminalSymbol) (value : TerminalStreamValue) :
    terminalMatchesBool terminal value = true ↔
      TerminalMatches terminal value := by
  cases terminal with
  | hardKeyword keyword =>
      cases value with
      | retained token =>
          simp [terminalMatchesBool, TerminalMatches]
      | endOfFile => simp [terminalMatchesBool, TerminalMatches]
  | contextualKeyword keyword =>
      cases value with
      | retained token =>
          simp [terminalMatchesBool, TerminalMatches]
      | endOfFile => simp [terminalMatchesBool, TerminalMatches]
  | pragmaName kind =>
      cases value with
      | retained token =>
          simp [terminalMatchesBool, TerminalMatches]
      | endOfFile => simp [terminalMatchesBool, TerminalMatches]
  | symbol symbol =>
      cases value with
      | retained token =>
          simp [terminalMatchesBool, TerminalMatches]
      | endOfFile => simp [terminalMatchesBool, TerminalMatches]
  | category category =>
      cases category <;> cases value with
      | retained token =>
          rcases token with ⟨span, payload⟩
          cases payload <;>
            simp [terminalMatchesBool, TerminalMatches,
              Option.isSome_iff_exists]
      | endOfFile => simp [terminalMatchesBool, TerminalMatches]
  | endOfFile =>
      cases value <;> simp [terminalMatchesBool, TerminalMatches]

/-- Terminal matching is decidable without classical choice. -/
instance terminalMatchesDecidable
    (terminal : TerminalSymbol) (value : TerminalStreamValue) :
    Decidable (TerminalMatches terminal value) :=
  decidable_of_iff
    (terminalMatchesBool terminal value = true)
    (terminalMatchesBool_eq_true_iff terminal value)

namespace MatchedTerminal

/-- Construct the unique checked terminal match at one fixed stream cursor. -/
def atCursor?
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol) (cursor : TerminalCursor tokens) :
    Option { matched : MatchedTerminal file tokens terminal //
      matched.cursor = cursor } :=
  if inRange : cursor.val < tokens.length then
    let token := tokens[cursor.val]
    if matchedEvidence : TerminalMatches terminal (.retained token) then
      some ⟨{
        cursor := cursor
        value := .retained token
        span := token.span
        «at» := .retained cursor token inRange
          (List.getElem?_eq_getElem inRange)
          (owned token (List.getElem_mem inRange))
        «matches» := matchedEvidence
      }, rfl⟩
    else
      none
  else
    have atEnd : cursor.val = tokens.length := by omega
    if matchedEvidence : TerminalMatches terminal .endOfFile then
      some ⟨{
        cursor := cursor
        value := .endOfFile
        span := {
          source := file.id
          startByte := file.content.utf8ByteSize
          endByte := file.content.utf8ByteSize
        }
        «at» := .endOfFile cursor atEnd
        «matches» := matchedEvidence
      }, rfl⟩
    else
      none

/-- A computed terminal observation supplies both declarative premises. -/
theorem atCursor?_sound
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol) (cursor : TerminalCursor tokens)
    {result : { matched : MatchedTerminal file tokens terminal //
      matched.cursor = cursor }}
    (_selected : atCursor? file tokens owned terminal cursor = some result) :
    TerminalAt file tokens cursor result.val.value result.val.span ∧
      TerminalMatches terminal result.val.value := by
  constructor
  · simpa only [result.property] using result.val.at
  · exact result.val.matches

/-- Every declarative match at the fixed cursor is computed. -/
theorem atCursor?_complete
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol) (cursor : TerminalCursor tokens)
    {value : TerminalStreamValue} {span : SourceSpan}
    (terminalAt : TerminalAt file tokens cursor value span)
    (matchedEvidence : TerminalMatches terminal value) :
    ∃ result, atCursor? file tokens owned terminal cursor = some result := by
  cases terminalAt with
  | retained token inRange lookup valid =>
      have tokenEq : tokens[cursor.val] = token := by
        exact Option.some.inj
          ((List.getElem?_eq_getElem inRange).symm.trans lookup)
      subst token
      unfold atCursor?
      rw [dif_pos inRange, dif_pos matchedEvidence]
      exact ⟨_, rfl⟩
  | endOfFile atEnd =>
      have notInRange : ¬ cursor.val < tokens.length := by omega
      unfold atCursor?
      rw [dif_neg notInRange, dif_pos matchedEvidence]
      exact ⟨_, rfl⟩

end MatchedTerminal

/-- A matched logical EOF is at the retained-token limit and has the unique
empty span at the physical end of the file. -/
theorem matchedTerminal_eof_empty_span
    {file : WorkspaceFile} {tokens : List Token}
    (matched : MatchedTerminal file tokens .endOfFile) :
    matched.cursor.val = tokens.length ∧
      matched.value = .endOfFile ∧
      matched.span = {
        source := file.id
        startByte := file.content.utf8ByteSize
        endByte := file.content.utf8ByteSize
      } := by
  rcases matched with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases value with
  | retained token => simp [TerminalMatches] at matchedEvidence
  | endOfFile =>
      cases terminalAt with
      | endOfFile atEnd => exact ⟨atEnd, rfl, rfl⟩

/-- Exact spelling and parsed value projected from one identifier terminal. -/
def IdentifierProjects
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier) : Prop :=
  ∃ token : Token,
    terminal.value = .retained token ∧
      token.payload = .identifier spelling ∧
      Identifier.parse spelling = some parsed

/-- Expose the raw equations of an identifier projection. -/
theorem matchedTerminal_identifier_projection_exact
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier) :
    IdentifierProjects terminal spelling parsed ↔
      ∃ token : Token,
        terminal.value = .retained token ∧
          token.payload = .identifier spelling ∧
          Identifier.parse spelling = some parsed :=
  Iff.rfl

/-- Compute the spelling and parsed value of an identifier stream value. -/
def executableIdentifierProjection? :
    TerminalStreamValue → Option (String × Identifier)
  | .retained token =>
      match token.payload with
      | .identifier spelling =>
          match Identifier.parse spelling with
          | some parsed => some (spelling, parsed)
          | none => none
      | _ => none
  | .endOfFile => none

/-- Every value already checked as an identifier has a computed projection. -/
theorem executableIdentifierProjection?_isSome_of_matches
    (value : TerminalStreamValue)
    (matchedEvidence : TerminalMatches (.category .identifier) value) :
    (executableIdentifierProjection? value).isSome = true := by
  cases value with
  | endOfFile => simp [TerminalMatches] at matchedEvidence
  | retained token =>
      rcases matchedEvidence with ⟨spelling, parsed, payloadEq, parseEq⟩
      simp [executableIdentifierProjection?, payloadEq, parseEq]

/-- Constructively project one checked identifier terminal. -/
def MatchedTerminal.identifierProjection
    {file : WorkspaceFile} {tokens : List Token}
    (matched : MatchedTerminal file tokens (.category .identifier)) :
    String × Identifier :=
  (executableIdentifierProjection? matched.value).get (by
    exact executableIdentifierProjection?_isSome_of_matches
      matched.value matched.matches)

/-- The computed identifier projection satisfies the declarative relation. -/
theorem MatchedTerminal.identifierProjection_projects
    {file : WorkspaceFile} {tokens : List Token}
    (matched : MatchedTerminal file tokens (.category .identifier)) :
    IdentifierProjects matched matched.identifierProjection.1
      matched.identifierProjection.2 := by
  rcases matched with
    ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases value with
  | endOfFile => simp [TerminalMatches] at matchedEvidence
  | retained token =>
      rcases matchedEvidence with ⟨spelling, parsed, payloadEq, parseEq⟩
      unfold IdentifierProjects
      simp only [MatchedTerminal.identifierProjection,
        executableIdentifierProjection?, payloadEq, parseEq, Option.get_some]
      exact ⟨token, rfl, payloadEq, trivial⟩

/-- Exact spelling and parsed value projected from one path terminal. -/
def PathSegmentProjects
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .pathComponent))
    (spelling : String) (parsed : PathSegment) : Prop :=
  ∃ token : Token,
    terminal.value = .retained token ∧
      (token.payload = .identifier spelling ∨
        ∃ keyword : HardKeyword,
          token.payload = .hardKeyword keyword ∧
            spelling = keyword.spelling) ∧
      PathSegment.parse spelling = some parsed

/-- Expose both retained-token shapes of a path projection. -/
theorem matchedTerminal_path_projection_exact
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .pathComponent))
    (spelling : String) (parsed : PathSegment) :
    PathSegmentProjects terminal spelling parsed ↔
      ∃ token : Token,
        terminal.value = .retained token ∧
          (token.payload = .identifier spelling ∨
            ∃ keyword : HardKeyword,
              token.payload = .hardKeyword keyword ∧
                spelling = keyword.spelling) ∧
          PathSegment.parse spelling = some parsed :=
  Iff.rfl

/-- Constructively decode a checked path-component stream value. -/
def executablePathProjection? :
    TerminalStreamValue → Option (String × PathSegment)
  | .retained token =>
      match token.payload with
      | .identifier spelling =>
          match PathSegment.parse spelling with
          | some parsed => some (spelling, parsed)
          | none => none
      | .hardKeyword keyword =>
          match PathSegment.parse keyword.spelling with
          | some parsed => some (keyword.spelling, parsed)
          | none => none
      | _ => none
  | .endOfFile => none

/-- Every checked path component has a computed projection. -/
theorem executablePathProjection?_isSome_of_matches
    (value : TerminalStreamValue)
    (matchedEvidence : TerminalMatches (.category .pathComponent) value) :
    (executablePathProjection? value).isSome = true := by
  cases value with
  | endOfFile => simp [TerminalMatches] at matchedEvidence
  | retained token =>
      rcases matchedEvidence with
        ⟨spelling, parsed, payloadEq, parseEq⟩ |
        ⟨keyword, parsed, payloadEq, parseEq⟩
      · simp [executablePathProjection?, payloadEq, parseEq]
      · simp [executablePathProjection?, payloadEq, parseEq]

/-- Constructively project one checked path-component terminal. -/
def MatchedTerminal.pathProjection
    {file : WorkspaceFile} {tokens : List Token}
    (matched : MatchedTerminal file tokens (.category .pathComponent)) :
    String × PathSegment :=
  (executablePathProjection? matched.value).get (by
    exact executablePathProjection?_isSome_of_matches
      matched.value matched.matches)

/-- The computed path projection satisfies the declarative relation. -/
theorem MatchedTerminal.pathProjection_projects
    {file : WorkspaceFile} {tokens : List Token}
    (matched : MatchedTerminal file tokens (.category .pathComponent)) :
    PathSegmentProjects matched matched.pathProjection.1
      matched.pathProjection.2 := by
  rcases matched with
    ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases value with
  | endOfFile => simp [TerminalMatches] at matchedEvidence
  | retained token =>
      rcases matchedEvidence with
        ⟨spelling, parsed, payloadEq, parseEq⟩ |
        ⟨keyword, parsed, payloadEq, parseEq⟩
      · unfold PathSegmentProjects
        simp only [MatchedTerminal.pathProjection,
          executablePathProjection?, payloadEq, parseEq, Option.get_some]
        exact ⟨token, rfl, Or.inl payloadEq, trivial⟩
      · unfold PathSegmentProjects
        simp only [MatchedTerminal.pathProjection,
          executablePathProjection?, payloadEq, parseEq, Option.get_some]
        exact ⟨token, rfl, Or.inr ⟨keyword, payloadEq, rfl⟩, trivial⟩

/-- Exact spelling and external-library value projected from one path terminal. -/
def ExternalLibraryProjects
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .pathComponent))
    (spelling : String) (parsed : ExternalLibraryName) : Prop :=
  ∃ token : Token,
    terminal.value = .retained token ∧
      (token.payload = .identifier spelling ∨
        ∃ keyword : HardKeyword,
          token.payload = .hardKeyword keyword ∧
            spelling = keyword.spelling) ∧
      ExternalLibraryName.parse spelling = some parsed

/-- Expose both retained-token shapes of an external-library projection. -/
theorem matchedTerminal_external_projection_exact
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .pathComponent))
    (spelling : String) (parsed : ExternalLibraryName) :
    ExternalLibraryProjects terminal spelling parsed ↔
      ∃ token : Token,
        terminal.value = .retained token ∧
          (token.payload = .identifier spelling ∨
            ∃ keyword : HardKeyword,
              token.payload = .hardKeyword keyword ∧
                spelling = keyword.spelling) ∧
          ExternalLibraryName.parse spelling = some parsed :=
  Iff.rfl

/-- Exact spelling-preserving payload projected from one literal terminal. -/
def LiteralProjects
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    (literalPayload : LiteralPayload) : Prop :=
  ∃ token : Token,
    matched.value = .retained token ∧
      ((terminal = .category .decimalLiteral ∧
          ∃ spelling digits : String,
            token.payload = .decimalLiteral spelling digits ∧
              literalPayload = .decimal spelling digits) ∨
        (terminal = .category .hexadecimalLiteral ∧
          ∃ spelling digits : String,
            token.payload = .hexadecimalLiteral spelling digits ∧
              literalPayload = .hexadecimal spelling digits) ∨
        (terminal = .category .stringLiteral ∧
          ∃ spelling decoded : String,
            token.payload = .stringLiteral spelling decoded ∧
              literalPayload = .string spelling decoded))

/-- Expose the three exact terminal/payload branches of a literal projection. -/
theorem matchedTerminal_literal_projection_exact
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    (literalPayload : LiteralPayload) :
    LiteralProjects matched literalPayload ↔
      ∃ token : Token,
        matched.value = .retained token ∧
          ((terminal = .category .decimalLiteral ∧
              ∃ spelling digits : String,
                token.payload = .decimalLiteral spelling digits ∧
                  literalPayload = .decimal spelling digits) ∨
            (terminal = .category .hexadecimalLiteral ∧
              ∃ spelling digits : String,
                token.payload = .hexadecimalLiteral spelling digits ∧
                  literalPayload = .hexadecimal spelling digits) ∨
            (terminal = .category .stringLiteral ∧
              ∃ spelling decoded : String,
                token.payload = .stringLiteral spelling decoded ∧
                  literalPayload = .string spelling decoded)) :=
  Iff.rfl

/-- Compute a source-preserving literal payload from one stream value. -/
def executableLiteralProjection? :
    TerminalCategory → TerminalStreamValue → Option LiteralPayload
  | .decimalLiteral, .retained token =>
      match token.payload with
      | .decimalLiteral spelling digits => some (.decimal spelling digits)
      | _ => none
  | .hexadecimalLiteral, .retained token =>
      match token.payload with
      | .hexadecimalLiteral spelling digits =>
          some (.hexadecimal spelling digits)
      | _ => none
  | .stringLiteral, .retained token =>
      match token.payload with
      | .stringLiteral spelling decoded => some (.string spelling decoded)
      | _ => none
  | _, _ => none

/-- Every checked literal value has a computed payload. -/
theorem executableLiteralProjection?_isSome_of_matches
    (category : TerminalCategory) (value : TerminalStreamValue)
    (literalCategory : category = .decimalLiteral ∨
      category = .hexadecimalLiteral ∨ category = .stringLiteral)
    (matchedEvidence : TerminalMatches (.category category) value) :
    (executableLiteralProjection? category value).isSome = true := by
  rcases literalCategory with rfl | rfl | rfl <;>
    cases value with
    | endOfFile => simp [TerminalMatches] at matchedEvidence
    | retained token =>
        rcases matchedEvidence with ⟨spelling, payload, payloadEq⟩
        simp [executableLiteralProjection?, payloadEq]

/-- Constructively project one checked literal terminal. -/
def MatchedTerminal.literalProjection
    {file : WorkspaceFile} {tokens : List Token}
    (category : TerminalCategory)
    (literalCategory : category = .decimalLiteral ∨
      category = .hexadecimalLiteral ∨ category = .stringLiteral)
    (matched : MatchedTerminal file tokens (.category category)) :
    LiteralPayload :=
  (executableLiteralProjection? category matched.value).get (by
    exact executableLiteralProjection?_isSome_of_matches category
      matched.value literalCategory matched.matches)

/-- The computed literal payload satisfies the declarative projection. -/
theorem MatchedTerminal.literalProjection_projects
    {file : WorkspaceFile} {tokens : List Token}
    (category : TerminalCategory)
    (literalCategory : category = .decimalLiteral ∨
      category = .hexadecimalLiteral ∨ category = .stringLiteral)
    (matched : MatchedTerminal file tokens (.category category)) :
    LiteralProjects matched
      (matched.literalProjection category literalCategory) := by
  rcases literalCategory with rfl | rfl | rfl <;>
    rcases matched with
      ⟨cursor, value, span, terminalAt, matchedEvidence⟩ <;>
    cases value with
    | endOfFile => simp [TerminalMatches] at matchedEvidence
    | retained token =>
        rcases matchedEvidence with ⟨spelling, payload, payloadEq⟩
        unfold LiteralProjects
        simp only [MatchedTerminal.literalProjection,
          executableLiteralProjection?, payloadEq, Option.get_some]
        simp [payloadEq]

/-- Exact opaque assembly slice projected from one assembly terminal. -/
def AssemblySliceProjects
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .assemblyBlock))
    (slice : AssemblySlice) : Prop :=
  ∃ token : Token,
    terminal.value = .retained token ∧
      token.payload = .assemblyBlock slice

/-- Expose the retained token and payload equation of an assembly projection. -/
theorem matchedTerminal_assembly_projection_exact
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .assemblyBlock))
    (slice : AssemblySlice) :
    AssemblySliceProjects terminal slice ↔
      ∃ token : Token,
        terminal.value = .retained token ∧
          token.payload = .assemblyBlock slice :=
  Iff.rfl

/-- Compute the opaque assembly slice carried by one stream value. -/
def executableAssemblyProjection? :
    TerminalStreamValue → Option AssemblySlice
  | .retained token =>
      match token.payload with
      | .assemblyBlock slice => some slice
      | _ => none
  | .endOfFile => none

/-- Every value checked as an assembly block has a computed slice. -/
theorem executableAssemblyProjection?_isSome_of_matches
    (value : TerminalStreamValue)
    (matchedEvidence : TerminalMatches (.category .assemblyBlock) value) :
    (executableAssemblyProjection? value).isSome = true := by
  cases value with
  | endOfFile => simp [TerminalMatches] at matchedEvidence
  | retained token =>
      rcases matchedEvidence with ⟨slice, payloadEq⟩
      simp [executableAssemblyProjection?, payloadEq]

/-- Constructively project one checked assembly-block terminal. -/
def MatchedTerminal.assemblyProjection
    {file : WorkspaceFile} {tokens : List Token}
    (matched : MatchedTerminal file tokens (.category .assemblyBlock)) :
    AssemblySlice :=
  (executableAssemblyProjection? matched.value).get (by
    exact executableAssemblyProjection?_isSome_of_matches
      matched.value matched.matches)

/-- The computed assembly slice satisfies the declarative projection. -/
theorem MatchedTerminal.assemblyProjection_projects
    {file : WorkspaceFile} {tokens : List Token}
    (matched : MatchedTerminal file tokens (.category .assemblyBlock)) :
    AssemblySliceProjects matched matched.assemblyProjection := by
  rcases matched with
    ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases value with
  | endOfFile => simp [TerminalMatches] at matchedEvidence
  | retained token =>
      rcases matchedEvidence with ⟨slice, payloadEq⟩
      unfold AssemblySliceProjects
      simp only [MatchedTerminal.assemblyProjection,
        executableAssemblyProjection?, payloadEq, Option.get_some]
      exact ⟨token, rfl, payloadEq⟩

private theorem projectedPathSpelling_functional
    {token : Token} {left right : String}
    (leftShape : token.payload = .identifier left ∨
      ∃ keyword : HardKeyword,
        token.payload = .hardKeyword keyword ∧
          left = keyword.spelling)
    (rightShape : token.payload = .identifier right ∨
      ∃ keyword : HardKeyword,
        token.payload = .hardKeyword keyword ∧
          right = keyword.spelling) :
    left = right := by
  rcases leftShape with leftShape | ⟨leftKeyword, leftShape, leftSpelling⟩
  · rcases rightShape with rightShape |
        ⟨rightKeyword, rightShape, rightSpelling⟩
    · exact TokenKind.identifier.inj (leftShape.symm.trans rightShape)
    · simp_all
  · rcases rightShape with rightShape |
        ⟨rightKeyword, rightShape, rightSpelling⟩
    · simp_all
    · have keywordEq : leftKeyword = rightKeyword :=
        TokenKind.hardKeyword.inj (leftShape.symm.trans rightShape)
      rw [leftSpelling, rightSpelling, keywordEq]

/-- Every matched identifier has exactly one spelling-and-value projection. -/
theorem matchedTerminal_identifier_projection_exists_unique
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .identifier)) :
    ∃ projection : String × Identifier,
      IdentifierProjects terminal projection.1 projection.2 ∧
        ∀ other : String × Identifier,
          IdentifierProjects terminal other.1 other.2 →
            other = projection := by
  rcases terminal with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases value with
  | endOfFile => simp [TerminalMatches] at matchedEvidence
  | retained token =>
      rcases matchedEvidence with ⟨spelling, parsed, payloadEq, parseEq⟩
      refine ⟨(spelling, parsed),
        (matchedTerminal_identifier_projection_exact _ spelling parsed).mpr
          ⟨token, rfl, payloadEq, parseEq⟩, ?_⟩
      rintro ⟨otherSpelling, otherParsed⟩ otherProjects
      rcases (matchedTerminal_identifier_projection_exact
        _ otherSpelling otherParsed).mp otherProjects with
        ⟨otherToken, valueEq, otherPayload, otherParse⟩
      have tokenEq : token = otherToken := by
        simpa only [TerminalStreamValue.retained.injEq] using valueEq
      subst otherToken
      have spellingEq : spelling = otherSpelling :=
        TokenKind.identifier.inj (payloadEq.symm.trans otherPayload)
      subst otherSpelling
      have parsedEq : otherParsed = parsed :=
        Option.some.inj (otherParse.symm.trans parseEq)
      subst otherParsed
      rfl

namespace IdentifierProjects

/-- One matched identifier has at most one spelling and parsed value. -/
theorem functional
    {file : WorkspaceFile} {tokens : List Token}
    {matched : MatchedTerminal file tokens (.category .identifier)}
    {leftSpelling rightSpelling : String}
    {leftParsed rightParsed : Identifier}
    (leftProjects : IdentifierProjects matched leftSpelling leftParsed)
    (rightProjects : IdentifierProjects matched rightSpelling rightParsed) :
    leftSpelling = rightSpelling ∧ leftParsed = rightParsed := by
  rcases matchedTerminal_identifier_projection_exists_unique matched with
    ⟨canonical, canonicalProjects, unique⟩
  have pairEq :=
    (unique (leftSpelling, leftParsed) leftProjects).trans
      (unique (rightSpelling, rightParsed) rightProjects).symm
  exact Prod.mk.inj pairEq

end IdentifierProjects

/-- Every matched path component has exactly one spelling-and-value projection. -/
theorem matchedTerminal_path_projection_exists_unique
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .pathComponent)) :
    ∃ projection : String × PathSegment,
      PathSegmentProjects terminal projection.1 projection.2 ∧
        ∀ other : String × PathSegment,
          PathSegmentProjects terminal other.1 other.2 →
            other = projection := by
  rcases terminal with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases value with
  | endOfFile => simp [TerminalMatches] at matchedEvidence
  | retained token =>
      rcases matchedEvidence with
        ⟨spelling, parsed, payloadEq, parseEq⟩ |
        ⟨keyword, parsed, payloadEq, parseEq⟩
      · refine ⟨(spelling, parsed),
          (matchedTerminal_path_projection_exact _ spelling parsed).mpr
            ⟨token, rfl, Or.inl payloadEq, parseEq⟩, ?_⟩
        rintro ⟨otherSpelling, otherParsed⟩ otherProjects
        rcases (matchedTerminal_path_projection_exact
          _ otherSpelling otherParsed).mp otherProjects with
          ⟨otherToken, valueEq, otherShape, otherParse⟩
        have tokenEq : token = otherToken := by
          simpa only [TerminalStreamValue.retained.injEq] using valueEq
        subst otherToken
        have spellingEq : spelling = otherSpelling :=
          projectedPathSpelling_functional (Or.inl payloadEq) otherShape
        subst otherSpelling
        have parsedEq : otherParsed = parsed :=
          Option.some.inj (otherParse.symm.trans parseEq)
        subst otherParsed
        rfl
      · refine ⟨(keyword.spelling, parsed),
          (matchedTerminal_path_projection_exact
            _ keyword.spelling parsed).mpr
            ⟨token, rfl, Or.inr ⟨keyword, payloadEq, rfl⟩, parseEq⟩, ?_⟩
        rintro ⟨otherSpelling, otherParsed⟩ otherProjects
        rcases (matchedTerminal_path_projection_exact
          _ otherSpelling otherParsed).mp otherProjects with
          ⟨otherToken, valueEq, otherShape, otherParse⟩
        have tokenEq : token = otherToken := by
          simpa only [TerminalStreamValue.retained.injEq] using valueEq
        subst otherToken
        have spellingEq : keyword.spelling = otherSpelling :=
          projectedPathSpelling_functional
            (Or.inr ⟨keyword, payloadEq, rfl⟩) otherShape
        subst otherSpelling
        have parsedEq : otherParsed = parsed :=
          Option.some.inj (otherParse.symm.trans parseEq)
        subst otherParsed
        rfl

namespace PathSegmentProjects

/-- One matched path component has at most one spelling and parsed value. -/
theorem functional
    {file : WorkspaceFile} {tokens : List Token}
    {matched : MatchedTerminal file tokens (.category .pathComponent)}
    {leftSpelling rightSpelling : String}
    {leftParsed rightParsed : PathSegment}
    (leftProjects : PathSegmentProjects matched leftSpelling leftParsed)
    (rightProjects : PathSegmentProjects matched rightSpelling rightParsed) :
    leftSpelling = rightSpelling ∧ leftParsed = rightParsed := by
  rcases matchedTerminal_path_projection_exists_unique matched with
    ⟨canonical, canonicalProjects, unique⟩
  have pairEq :=
    (unique (leftSpelling, leftParsed) leftProjects).trans
      (unique (rightSpelling, rightParsed) rightProjects).symm
  exact Prod.mk.inj pairEq

end PathSegmentProjects

/-- Every matched external-library component has one spelling-and-value projection. -/
theorem matchedTerminal_external_projection_exists_unique
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .pathComponent)) :
    ∃ projection : String × ExternalLibraryName,
      ExternalLibraryProjects terminal projection.1 projection.2 ∧
        ∀ other : String × ExternalLibraryName,
          ExternalLibraryProjects terminal other.1 other.2 →
            other = projection := by
  rcases terminal with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases value with
  | endOfFile => simp [TerminalMatches] at matchedEvidence
  | retained token =>
      rcases matchedEvidence with
        ⟨spelling, segment, payloadEq, parseEq⟩ |
        ⟨keyword, segment, payloadEq, parseEq⟩
      · have externalParse :
            ExternalLibraryName.parse spelling = some ⟨segment⟩ := by
          simp [ExternalLibraryName.parse, parseEq]
        refine ⟨(spelling, ⟨segment⟩),
          (matchedTerminal_external_projection_exact
            _ spelling ⟨segment⟩).mpr
            ⟨token, rfl, Or.inl payloadEq, externalParse⟩, ?_⟩
        rintro ⟨otherSpelling, otherParsed⟩ otherProjects
        rcases (matchedTerminal_external_projection_exact
          _ otherSpelling otherParsed).mp otherProjects with
          ⟨otherToken, valueEq, otherShape, otherParse⟩
        have tokenEq : token = otherToken := by
          simpa only [TerminalStreamValue.retained.injEq] using valueEq
        subst otherToken
        have spellingEq : spelling = otherSpelling :=
          projectedPathSpelling_functional (Or.inl payloadEq) otherShape
        subst otherSpelling
        have parsedEq : otherParsed = ⟨segment⟩ :=
          Option.some.inj (otherParse.symm.trans externalParse)
        subst otherParsed
        rfl
      · have externalParse :
            ExternalLibraryName.parse keyword.spelling = some ⟨segment⟩ := by
          simp [ExternalLibraryName.parse, parseEq]
        refine ⟨(keyword.spelling, ⟨segment⟩),
          (matchedTerminal_external_projection_exact
            _ keyword.spelling ⟨segment⟩).mpr
            ⟨token, rfl, Or.inr ⟨keyword, payloadEq, rfl⟩, externalParse⟩,
          ?_⟩
        rintro ⟨otherSpelling, otherParsed⟩ otherProjects
        rcases (matchedTerminal_external_projection_exact
          _ otherSpelling otherParsed).mp otherProjects with
          ⟨otherToken, valueEq, otherShape, otherParse⟩
        have tokenEq : token = otherToken := by
          simpa only [TerminalStreamValue.retained.injEq] using valueEq
        subst otherToken
        have spellingEq : keyword.spelling = otherSpelling :=
          projectedPathSpelling_functional
            (Or.inr ⟨keyword, payloadEq, rfl⟩) otherShape
        subst otherSpelling
        have parsedEq : otherParsed = ⟨segment⟩ :=
          Option.some.inj (otherParse.symm.trans externalParse)
        subst otherParsed
        rfl

namespace ExternalLibraryProjects

/-- One matched external component has at most one spelling and parsed value. -/
theorem functional
    {file : WorkspaceFile} {tokens : List Token}
    {matched : MatchedTerminal file tokens (.category .pathComponent)}
    {leftSpelling rightSpelling : String}
    {leftParsed rightParsed : ExternalLibraryName}
    (leftProjects : ExternalLibraryProjects
      matched leftSpelling leftParsed)
    (rightProjects : ExternalLibraryProjects
      matched rightSpelling rightParsed) :
    leftSpelling = rightSpelling ∧ leftParsed = rightParsed := by
  rcases matchedTerminal_external_projection_exists_unique matched with
    ⟨canonical, canonicalProjects, unique⟩
  have pairEq :=
    (unique (leftSpelling, leftParsed) leftProjects).trans
      (unique (rightSpelling, rightParsed) rightProjects).symm
  exact Prod.mk.inj pairEq

end ExternalLibraryProjects

/-- Every matched literal in the closed literal category has one exact payload. -/
theorem matchedTerminal_literal_projection_exists_unique
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    (literalTerminal :
      terminal = .category .decimalLiteral ∨
        terminal = .category .hexadecimalLiteral ∨
        terminal = .category .stringLiteral) :
    ∃ literalPayload : LiteralPayload,
      LiteralProjects matched literalPayload ∧
        ∀ other : LiteralPayload,
          LiteralProjects matched other → other = literalPayload := by
  rcases literalTerminal with terminalEq | terminalEq | terminalEq
  · subst terminal
    rcases matched with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
    cases value with
    | endOfFile => simp [TerminalMatches] at matchedEvidence
    | retained token =>
        rcases matchedEvidence with ⟨spelling, digits, payloadEq⟩
        refine ⟨.decimal spelling digits,
          (matchedTerminal_literal_projection_exact
            _ (.decimal spelling digits)).mpr
            ⟨token, rfl, Or.inl ⟨rfl, spelling, digits, payloadEq, rfl⟩⟩,
          ?_⟩
        intro other otherProjects
        rcases (matchedTerminal_literal_projection_exact _ other).mp
          otherProjects with ⟨otherToken, valueEq, branch⟩
        have tokenEq : token = otherToken := by
          simpa only [TerminalStreamValue.retained.injEq] using valueEq
        subst otherToken
        rcases branch with branch | branch | branch
        · rcases branch with ⟨_, otherSpelling, otherDigits,
              otherPayload, otherLiteral⟩
          rcases TokenKind.decimalLiteral.inj
              (payloadEq.symm.trans otherPayload) with
            ⟨spellingEq, digitsEq⟩
          subst otherSpelling
          subst otherDigits
          exact otherLiteral
        · simp at branch
        · simp at branch
  · subst terminal
    rcases matched with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
    cases value with
    | endOfFile => simp [TerminalMatches] at matchedEvidence
    | retained token =>
        rcases matchedEvidence with ⟨spelling, digits, payloadEq⟩
        refine ⟨.hexadecimal spelling digits,
          (matchedTerminal_literal_projection_exact
            _ (.hexadecimal spelling digits)).mpr
            ⟨token, rfl, Or.inr (Or.inl
              ⟨rfl, spelling, digits, payloadEq, rfl⟩)⟩,
          ?_⟩
        intro other otherProjects
        rcases (matchedTerminal_literal_projection_exact _ other).mp
          otherProjects with ⟨otherToken, valueEq, branch⟩
        have tokenEq : token = otherToken := by
          simpa only [TerminalStreamValue.retained.injEq] using valueEq
        subst otherToken
        rcases branch with branch | branch | branch
        · simp at branch
        · rcases branch with ⟨_, otherSpelling, otherDigits,
              otherPayload, otherLiteral⟩
          rcases TokenKind.hexadecimalLiteral.inj
              (payloadEq.symm.trans otherPayload) with
            ⟨spellingEq, digitsEq⟩
          subst otherSpelling
          subst otherDigits
          exact otherLiteral
        · simp at branch
  · subst terminal
    rcases matched with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
    cases value with
    | endOfFile => simp [TerminalMatches] at matchedEvidence
    | retained token =>
        rcases matchedEvidence with ⟨spelling, decoded, payloadEq⟩
        refine ⟨.string spelling decoded,
          (matchedTerminal_literal_projection_exact
            _ (.string spelling decoded)).mpr
            ⟨token, rfl, Or.inr (Or.inr
              ⟨rfl, spelling, decoded, payloadEq, rfl⟩)⟩,
          ?_⟩
        intro other otherProjects
        rcases (matchedTerminal_literal_projection_exact _ other).mp
          otherProjects with ⟨otherToken, valueEq, branch⟩
        have tokenEq : token = otherToken := by
          simpa only [TerminalStreamValue.retained.injEq] using valueEq
        subst otherToken
        rcases branch with branch | branch | branch
        · simp at branch
        · simp at branch
        · rcases branch with ⟨_, otherSpelling, otherDecoded,
              otherPayload, otherLiteral⟩
          rcases TokenKind.stringLiteral.inj
              (payloadEq.symm.trans otherPayload) with
            ⟨spellingEq, decodedEq⟩
          subst otherSpelling
          subst otherDecoded
          exact otherLiteral

namespace LiteralProjects

/-- One matched literal terminal has at most one literal payload. -/
theorem functional
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    {matched : MatchedTerminal file tokens terminal}
    {left right : LiteralPayload}
    (leftProjects : LiteralProjects matched left)
    (rightProjects : LiteralProjects matched right) :
    left = right := by
  have literalTerminal :
      terminal = .category .decimalLiteral ∨
        terminal = .category .hexadecimalLiteral ∨
        terminal = .category .stringLiteral := by
    rcases leftProjects with ⟨token, valueEq, branch⟩
    rcases branch with branch | branch | branch
    · exact Or.inl branch.1
    · exact Or.inr (Or.inl branch.1)
    · exact Or.inr (Or.inr branch.1)
  rcases matchedTerminal_literal_projection_exists_unique
      matched literalTerminal with ⟨canonical, canonicalProjects, unique⟩
  exact (unique _ leftProjects).trans (unique _ rightProjects).symm

end LiteralProjects

/-- Every matched assembly block has exactly one retained assembly slice. -/
theorem matchedTerminal_assembly_projection_exists_unique
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .assemblyBlock)) :
    ∃ slice : AssemblySlice,
      AssemblySliceProjects terminal slice ∧
        ∀ other : AssemblySlice,
          AssemblySliceProjects terminal other → other = slice := by
  rcases terminal with ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases value with
  | endOfFile => simp [TerminalMatches] at matchedEvidence
  | retained token =>
      rcases matchedEvidence with ⟨slice, payloadEq⟩
      refine ⟨slice,
        (matchedTerminal_assembly_projection_exact _ slice).mpr
          ⟨token, rfl, payloadEq⟩, ?_⟩
      intro other otherProjects
      rcases (matchedTerminal_assembly_projection_exact _ other).mp
        otherProjects with ⟨otherToken, valueEq, otherPayload⟩
      have tokenEq : token = otherToken := by
        simpa only [TerminalStreamValue.retained.injEq] using valueEq
      subst otherToken
      exact TokenKind.assemblyBlock.inj (otherPayload.symm.trans payloadEq)

namespace AssemblySliceProjects

/-- One matched assembly block has at most one retained slice. -/
theorem functional
    {file : WorkspaceFile} {tokens : List Token}
    {matched : MatchedTerminal file tokens (.category .assemblyBlock)}
    {left right : AssemblySlice}
    (leftProjects : AssemblySliceProjects matched left)
    (rightProjects : AssemblySliceProjects matched right) :
    left = right := by
  rcases matchedTerminal_assembly_projection_exists_unique matched with
    ⟨canonical, canonicalProjects, unique⟩
  exact (unique _ leftProjects).trans (unique _ rightProjects).symm

end AssemblySliceProjects

/-- The structural size of one finite EBNF expression. -/
def ebnfSize : EbnfExpr → Nat
  | .atom _ => 1
  | .sequence children => 1 + (children.map ebnfSize).sum
  | .group child => 1 + ebnfSize child
  | .choice branches => 1 + (branches.map ebnfSize).sum
  | .optional child => 1 + ebnfSize child
  | .star child => 1 + ebnfSize child
  | .plus child => 1 + ebnfSize child
  | .list0 element => 1 + ebnfSize element
  | .list1 element => 1 + ebnfSize element

/-- The six unary constructors of the EBNF expression algebra. -/
inductive UnaryEbnfKind where
  | group
  | optional
  | star
  | plus
  | list0
  | list1

namespace UnaryEbnfKind

/-- Apply one unary EBNF constructor to its child expression. -/
def apply : UnaryEbnfKind → EbnfExpr → EbnfExpr
  | .group, child => .group child
  | .optional, child => .optional child
  | .star, child => .star child
  | .plus, child => .plus child
  | .list0, child => .list0 child
  | .list1, child => .list1 child

end UnaryEbnfKind

/-- An index selecting one EBNF expression or a sequence of expressions. -/
inductive EbnfValueIndex where
  | expression (expression : EbnfExpr)
  | expressions (expressions : List EbnfExpr)

namespace EbnfValueIndex

/-- The well-founded measure of an EBNF semantic-value index. -/
def measure : EbnfValueIndex → Nat
  | .expression value => 2 * ebnfSize value
  | .expressions values => 2 * (values.map ebnfSize).sum + 1

end EbnfValueIndex

/-- Every finite EBNF expression has positive structural size. -/
theorem ebnfSize_positive (expression : EbnfExpr) :
    0 < ebnfSize expression := by
  cases expression <;> simp only [ebnfSize] <;> omega

/-- A member's size is bounded by the sum of all mapped member sizes. -/
private theorem ebnfSize_le_mapped_sum
    {expression : EbnfExpr} :
    ∀ {expressions : List EbnfExpr},
      expression ∈ expressions →
        ebnfSize expression ≤ (expressions.map ebnfSize).sum
  | [], member => by
      simp at member
  | head :: tail, member => by
      rcases List.mem_cons.mp member with equal | inTail
      · subst head
        simp only [List.map_cons, List.sum_cons]
        exact Nat.le_add_right _ _
      · simp only [List.map_cons, List.sum_cons]
        exact Nat.le_trans
          (ebnfSize_le_mapped_sum inTail)
          (Nat.le_add_left _ _)

/-- A sequence's expression-list index is strictly smaller. -/
theorem measure_sequence_lt (children : List EbnfExpr) :
    EbnfValueIndex.measure (.expressions children) <
      EbnfValueIndex.measure (.expression (.sequence children)) := by
  simp only [EbnfValueIndex.measure, ebnfSize]
  omega

/-- A selected choice branch is strictly smaller than its choice. -/
theorem measure_choice_get_lt
    (branches : List EbnfExpr)
    (branch : Fin branches.length) :
    EbnfValueIndex.measure (.expression (branches.get branch)) <
      EbnfValueIndex.measure (.expression (.choice branches)) := by
  have bound : ebnfSize (branches.get branch) ≤
      (branches.map ebnfSize).sum :=
    ebnfSize_le_mapped_sum (List.get_mem branches branch)
  simp only [EbnfValueIndex.measure, ebnfSize]
  omega

/-- A unary constructor's child index is strictly smaller. -/
theorem measure_unary_child_lt
    (kind : UnaryEbnfKind)
    (child : EbnfExpr) :
    EbnfValueIndex.measure (.expression child) <
      EbnfValueIndex.measure (.expression (kind.apply child)) := by
  cases kind <;>
    simp only [UnaryEbnfKind.apply, EbnfValueIndex.measure, ebnfSize] <;>
    omega

/-- The head expression index is strictly smaller than the whole list. -/
theorem measure_cons_head_lt
    (child : EbnfExpr)
    (rest : List EbnfExpr) :
    EbnfValueIndex.measure (.expression child) <
      EbnfValueIndex.measure (.expressions (child :: rest)) := by
  simp only [EbnfValueIndex.measure, List.map_cons, List.sum_cons]
  omega

/-- The tail expression-list index is strictly smaller than the whole list. -/
theorem measure_cons_tail_lt
    (child : EbnfExpr)
    (rest : List EbnfExpr) :
    EbnfValueIndex.measure (.expressions rest) <
      EbnfValueIndex.measure (.expressions (child :: rest)) := by
  have positive := ebnfSize_positive child
  simp only [EbnfValueIndex.measure, List.map_cons, List.sum_cons]
  omega

/-- The well-founded semantic carrier shared by expressions and expression lists. -/
def EbnfFamily
    (file : WorkspaceFile)
    (tokens : List Token) :
    (index : EbnfValueIndex) → Type
  | .expression (.atom (.terminal terminal)) =>
      MatchedTerminal file tokens terminal
  | .expression (.atom (.nonterminal rule)) =>
      RuleValue rule
  | .expression (.sequence children) =>
      EbnfFamily file tokens (.expressions children)
  | .expression (.group child) =>
      EbnfFamily file tokens (.expression child)
  | .expression (.choice branches) =>
      (branch : Fin branches.length) ×
        EbnfFamily file tokens (.expression (branches.get branch))
  | .expression (.optional child) =>
      Option (EbnfFamily file tokens (.expression child))
  | .expression (.star child) =>
      List (EbnfFamily file tokens (.expression child))
  | .expression (.plus child) =>
      NonemptyList (EbnfFamily file tokens (.expression child))
  | .expression (.list0 element) =>
      List (EbnfFamily file tokens (.expression element))
  | .expression (.list1 element) =>
      NonemptyList (EbnfFamily file tokens (.expression element))
  | .expressions [] => Unit
  | .expressions (child :: rest) =>
      EbnfFamily file tokens (.expression child) ×
        EbnfFamily file tokens (.expressions rest)
termination_by index => index.measure
decreasing_by
  · exact measure_sequence_lt children
  · exact measure_unary_child_lt .group child
  · exact measure_choice_get_lt branches branch
  · exact measure_unary_child_lt .optional child
  · exact measure_unary_child_lt .star child
  · exact measure_unary_child_lt .plus child
  · exact measure_unary_child_lt .list0 element
  · exact measure_unary_child_lt .list1 element
  · exact measure_cons_head_lt child rest
  · exact measure_cons_tail_lt child rest

/-- The semantic carrier of one EBNF expression. -/
abbrev EbnfValue
    (file : WorkspaceFile)
    (tokens : List Token)
    (expression : EbnfExpr) : Type :=
  EbnfFamily file tokens (.expression expression)

/-- The heterogeneous semantic carrier of an expression sequence. -/
abbrev EbnfValues
    (file : WorkspaceFile)
    (tokens : List Token)
    (expressions : List EbnfExpr) : Type :=
  EbnfFamily file tokens (.expressions expressions)

/-- A terminal atom carries its exact checked terminal match. -/
@[simp] theorem ebnfValue_atom_terminal_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (terminal : TerminalSymbol) :
    EbnfValue file tokens (.atom (.terminal terminal)) =
      MatchedTerminal file tokens terminal := by
  exact EbnfFamily.eq_def file tokens _

/-- A nonterminal atom carries the exact semantic value of its source rule. -/
@[simp] theorem ebnfValue_atom_nonterminal_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (rule : GrammarRuleId) :
    EbnfValue file tokens (.atom (.nonterminal rule)) =
      RuleValue rule := by
  exact EbnfFamily.eq_def file tokens _

/-- A sequence expression carries its heterogeneous child sequence. -/
@[simp] theorem ebnfValue_sequence_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (children : List EbnfExpr) :
    EbnfValue file tokens (.sequence children) =
      EbnfValues file tokens children := by
  exact EbnfFamily.eq_def file tokens _

/-- A group carries exactly its child value. -/
@[simp] theorem ebnfValue_group_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    EbnfValue file tokens (.group child) =
      EbnfValue file tokens child := by
  exact EbnfFamily.eq_def file tokens _

/-- A choice carries its finite branch tag and that branch's exact value. -/
@[simp] theorem ebnfValue_choice_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (branches : List EbnfExpr) :
    EbnfValue file tokens (.choice branches) =
      ((branch : Fin branches.length) ×
        EbnfValue file tokens (branches.get branch)) := by
  exact EbnfFamily.eq_def file tokens _

/-- An optional expression carries an optional child value. -/
@[simp] theorem ebnfValue_optional_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    EbnfValue file tokens (.optional child) =
      Option (EbnfValue file tokens child) := by
  exact EbnfFamily.eq_def file tokens _

/-- A star expression carries its ordered child values. -/
@[simp] theorem ebnfValue_star_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    EbnfValue file tokens (.star child) =
      List (EbnfValue file tokens child) := by
  exact EbnfFamily.eq_def file tokens _

/-- A plus expression carries a nonempty ordered child sequence. -/
@[simp] theorem ebnfValue_plus_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    EbnfValue file tokens (.plus child) =
      NonemptyList (EbnfValue file tokens child) := by
  exact EbnfFamily.eq_def file tokens _

/-- A possibly empty comma list carries its ordered element values. -/
@[simp] theorem ebnfValue_list0_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (element : EbnfExpr) :
    EbnfValue file tokens (.list0 element) =
      List (EbnfValue file tokens element) := by
  exact EbnfFamily.eq_def file tokens _

/-- A nonempty comma list carries its nonempty ordered element values. -/
@[simp] theorem ebnfValue_list1_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (element : EbnfExpr) :
    EbnfValue file tokens (.list1 element) =
      NonemptyList (EbnfValue file tokens element) := by
  exact EbnfFamily.eq_def file tokens _

/-- The empty expression sequence carries `Unit`. -/
@[simp] theorem ebnfValues_nil_eq
    {file : WorkspaceFile}
    {tokens : List Token} :
    EbnfValues file tokens [] = Unit := by
  exact EbnfFamily.eq_def file tokens _

/-- A nonempty expression sequence carries its head and tail values. -/
@[simp] theorem ebnfValues_cons_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr)
    (rest : List EbnfExpr) :
    EbnfValues file tokens (child :: rest) =
      (EbnfValue file tokens child × EbnfValues file tokens rest) := by
  exact EbnfFamily.eq_def file tokens _

/-- The semantic value carried by one nonterminal symbol. -/
def NonterminalValue
    (file : WorkspaceFile)
    (tokens : List Token) : NonterminalSymbol → Type
  | .rule rule => RuleValue rule
  | .aux site => EbnfValue file tokens site.expression
  | .tail site =>
      List (EbnfValue file tokens site.element.expression)

/-- The semantic value carried by one grammar symbol. -/
def GrammarSymbolValue
    (file : WorkspaceFile)
    (tokens : List Token) : GrammarSymbol → Type
  | .terminal terminal => MatchedTerminal file tokens terminal
  | .nonterminal nonterminal =>
      NonterminalValue file tokens nonterminal

/-- A type-indexed tuple of semantic grammar-symbol values. -/
def GrammarSymbolValues
    (file : WorkspaceFile)
    (tokens : List Token) : List GrammarSymbol → Type
  | [] => Unit
  | symbol :: rest =>
      GrammarSymbolValue file tokens symbol ×
        GrammarSymbolValues file tokens rest

namespace GrammarSymbolValues

/-- Append two type-indexed grammar-symbol value tuples. -/
def append
    {file : WorkspaceFile}
    {tokens : List Token}
    {left right : List GrammarSymbol}
    (leftValues : GrammarSymbolValues file tokens left)
    (rightValues : GrammarSymbolValues file tokens right) :
    GrammarSymbolValues file tokens (left ++ right) :=
  match left with
  | [] => rightValues
  | _symbol :: _rest =>
      (leftValues.1, append leftValues.2 rightValues)

/-- Transport a grammar-symbol value tuple along an index equality. -/
def transport
    {file : WorkspaceFile}
    {tokens : List Token}
    {left right : List GrammarSymbol}
    (equality : left = right) :
    GrammarSymbolValues file tokens left →
      GrammarSymbolValues file tokens right :=
  Eq.mp (congrArg (GrammarSymbolValues file tokens) equality)

theorem transport_trans
    {file : WorkspaceFile} {tokens : List Token}
    {first second third : List GrammarSymbol}
    (left : first = second) (right : second = third)
    (value : GrammarSymbolValues file tokens first) :
    transport right (transport left value) =
      transport (left.trans right) value := by
  cases left
  cases right
  rfl

theorem transport_self
    {file : WorkspaceFile} {tokens : List Token}
    {symbols : List GrammarSymbol}
    (equality : symbols = symbols)
    (value : GrammarSymbolValues file tokens symbols) :
    transport equality value = value := by
  have exactEquality : equality = rfl := Subsingleton.elim _ _
  rw [exactEquality]
  rfl

theorem transport_append_pair
    {file : WorkspaceFile} {tokens : List Token}
    {priorSymbols full : List GrammarSymbol} {first second : GrammarSymbol}
    (priorLayout : priorSymbols = [first])
    (fullLayout : priorSymbols ++ [second] = full)
    (viewLayout : full = [first, second])
    (head : GrammarSymbolValue file tokens first)
    (last : GrammarSymbolValue file tokens second) :
    transport viewLayout
        (transport fullLayout
          (append (transport priorLayout.symm (head, ())) (last, ()))) =
      (head, (last, ())) := by
  subst priorSymbols
  subst full
  simp only [transport_self]
  rfl

theorem transport_append_pair_to
    {file : WorkspaceFile} {tokens : List Token}
    {priorSymbols full target : List GrammarSymbol}
    {first second : GrammarSymbol}
    (priorLayout : priorSymbols = [first])
    (fullLayout : priorSymbols ++ [second] = full)
    (viewLayout : full = target)
    (targetLayout : target = [first, second])
    (head : GrammarSymbolValue file tokens first)
    (last : GrammarSymbolValue file tokens second) :
    transport viewLayout
        (transport fullLayout
          (append (transport priorLayout.symm (head, ())) (last, ()))) =
      transport targetLayout.symm (head, (last, ())) := by
  subst priorSymbols
  subst full
  subst target
  simp only [transport_self]
  rfl

theorem transport_append_single
    {file : WorkspaceFile} {tokens : List Token}
    {full : List GrammarSymbol} {symbol : GrammarSymbol}
    (fullLayout : [symbol] = full)
    (viewLayout : full = [symbol])
    (value : GrammarSymbolValue file tokens symbol) :
    transport viewLayout
        (transport fullLayout
          (append (left := []) () (value, ()))) =
      (value, ()) := by
  subst full
  simp only [transport_self]
  rfl

theorem transport_append_single_to
    {file : WorkspaceFile} {tokens : List Token}
    {full : List GrammarSymbol} {source target : GrammarSymbol}
    (fullLayout : [source] = full)
    (viewLayout : full = [target])
    (symbolLayout : source = target)
    (value : GrammarSymbolValue file tokens source) :
    transport viewLayout
        (transport fullLayout
          (append (left := []) () (value, ()))) =
      (Eq.mp (congrArg (GrammarSymbolValue file tokens) symbolLayout) value,
        ()) := by
  subst full
  subst target
  simp only [transport_self]
  rfl

end GrammarSymbolValues

/-- Semantic values for the already consumed prefix of one item. -/
abbrev PrefixValues
    (file : WorkspaceFile)
    (tokens : List Token)
    (item : ContextualItemKey tokens) : Type :=
  GrammarSymbolValues file tokens
    (item.raw.production.rhs.take item.raw.dot.val)

namespace PrefixValues

/-- Construct the unique semantic value of a zero-length prefix. -/
def zeroValue
    {file : WorkspaceFile}
    {tokens : List Token}
    (item : ContextualItemKey tokens)
    (zero : item.raw.dot.val = 0) :
    PrefixValues file tokens item :=
  GrammarSymbolValues.transport
    (prefix_zero_layout item.raw zero) ()

/-- Append one matched terminal while scanning an item. -/
def scanValue
    {file : WorkspaceFile}
    {tokens : List Token}
    (before after : ContextualItemKey tokens)
    (terminal : TerminalSymbol)
    (next : NextSymbol before.raw (.terminal terminal))
    (matched : MatchedTerminal file tokens terminal)
    (advance : AdvanceItem before.raw
      matched.cursor.afterBoundary after.raw)
    (prior : PrefixValues file tokens before) :
    PrefixValues file tokens after :=
  GrammarSymbolValues.transport
    (prefix_scan_layout before.raw after.raw terminal
      matched.cursor.afterBoundary next advance)
    (GrammarSymbolValues.append prior (matched, ()))

/-- Append one completed nonterminal while advancing a waiting item. -/
def completeValue
    {file : WorkspaceFile}
    {tokens : List Token}
    (waiting finished after : ContextualItemKey tokens)
    (next : NextSymbol waiting.raw
      (.nonterminal finished.raw.production.lhs))
    (advance : AdvanceItem waiting.raw finished.raw.current after.raw)
    (prior : PrefixValues file tokens waiting)
    (value : NonterminalValue file tokens
      finished.raw.production.lhs) :
    PrefixValues file tokens after :=
  GrammarSymbolValues.transport
    (prefix_complete_layout waiting.raw finished.raw after.raw next advance)
    (GrammarSymbolValues.append prior (value, ()))

/-- Reindex a complete prefix as the full production right-hand side. -/
def fullValue
    {file : WorkspaceFile}
    {tokens : List Token}
    (item : ContextualItemKey tokens)
    (complete : CompleteItem item.raw)
    (prior : PrefixValues file tokens item) :
    GrammarSymbolValues file tokens item.raw.production.rhs :=
  GrammarSymbolValues.transport
    (prefix_full_layout item.raw complete) prior

/-- Completing a prefix and then viewing a complete item is one transport of
the prior tuple with its child appended. -/
theorem fullValue_completeValue_eq
    {file : WorkspaceFile} {tokens : List Token}
    (waiting finished after : ContextualItemKey tokens)
    (next : NextSymbol waiting.raw
      (.nonterminal finished.raw.production.lhs))
    (advance : AdvanceItem waiting.raw finished.raw.current after.raw)
    (complete : CompleteItem after.raw)
    (prior : PrefixValues file tokens waiting)
    (child : NonterminalValue file tokens
      finished.raw.production.lhs) :
    fullValue after complete
        (completeValue waiting finished after next advance prior child) =
      GrammarSymbolValues.transport
        ((prefix_complete_layout waiting.raw finished.raw after.raw
          next advance).trans (prefix_full_layout after.raw complete))
        (GrammarSymbolValues.append prior (child, ())) := by
  unfold fullValue completeValue
  exact GrammarSymbolValues.transport_trans _ _ _

end PrefixValues

namespace EbnfValue

/-- Transport one EBNF value along a checked expression equality. -/
def transport
    {file : WorkspaceFile}
    {tokens : List Token}
    {left right : EbnfExpr}
    (equality : left = right) :
    EbnfValue file tokens left → EbnfValue file tokens right :=
  Eq.mp (congrArg (EbnfValue file tokens) equality)

theorem transport_trans
    {file : WorkspaceFile} {tokens : List Token}
    {first second third : EbnfExpr}
    (left : first = second) (right : second = third)
    (value : EbnfValue file tokens first) :
    transport right (transport left value) =
      transport (left.trans right) value := by
  cases left
  cases right
  rfl

theorem transport_self
    {file : WorkspaceFile} {tokens : List Token}
    {expression : EbnfExpr} (equality : expression = expression)
    (value : EbnfValue file tokens expression) :
    transport equality value = value := by
  have exactEquality : equality = rfl := Subsingleton.elim _ _
  rw [exactEquality]
  rfl

/-- View a site-indexed value at a checked displayed expression shape. -/
def atShape
    {file : WorkspaceFile}
    {tokens : List Token}
    {site : GrammarSite}
    {expression : EbnfExpr}
    (shape : site.expression = expression) :
    EbnfValue file tokens site.expression →
      EbnfValue file tokens expression :=
  transport shape

/-- Return a displayed expression value to its checked site index. -/
def ofShape
    {file : WorkspaceFile}
    {tokens : List Token}
    {site : GrammarSite}
    {expression : EbnfExpr}
    (shape : site.expression = expression) :
    EbnfValue file tokens expression →
      EbnfValue file tokens site.expression :=
  transport shape.symm

/-- Construct the checked EBNF value of one terminal atom. -/
def terminalAtom
    {file : WorkspaceFile}
    {tokens : List Token}
    (terminal : TerminalSymbol) :
    MatchedTerminal file tokens terminal →
      EbnfValue file tokens (EbnfExpr.atom (.terminal terminal)) :=
  Eq.mp (ebnfValue_atom_terminal_eq terminal).symm

/-- Construct the checked EBNF value of one grammar-rule atom. -/
def ruleAtom
    {file : WorkspaceFile}
    {tokens : List Token}
    (rule : GrammarRuleId) :
    RuleValue rule →
      EbnfValue file tokens (EbnfExpr.atom (.nonterminal rule)) :=
  Eq.mp (ebnfValue_atom_nonterminal_eq rule).symm

/-- Construct the checked EBNF value of one sequence. -/
def sequence
    {file : WorkspaceFile}
    {tokens : List Token}
    (children : List EbnfExpr) :
    EbnfValues file tokens children →
      EbnfValue file tokens (EbnfExpr.sequence children) :=
  Eq.mp (ebnfValue_sequence_eq children).symm

/-- Construct the checked EBNF value of one group. -/
def group
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    EbnfValue file tokens child →
      EbnfValue file tokens (EbnfExpr.group child) :=
  Eq.mp (ebnfValue_group_eq child).symm

/-- Construct the checked EBNF value of one tagged choice branch. -/
def choice
    {file : WorkspaceFile}
    {tokens : List Token}
    (branches : List EbnfExpr) :
    ((branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch)) →
      EbnfValue file tokens (EbnfExpr.choice branches) :=
  Eq.mp (ebnfValue_choice_eq branches).symm

/-- Construct the checked EBNF value of one optional expression. -/
def optional
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    Option (EbnfValue file tokens child) →
      EbnfValue file tokens (EbnfExpr.optional child) :=
  Eq.mp (ebnfValue_optional_eq child).symm

/-- Construct the checked EBNF value of one star expression. -/
def star
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    List (EbnfValue file tokens child) →
      EbnfValue file tokens (EbnfExpr.star child) :=
  Eq.mp (ebnfValue_star_eq child).symm

/-- Construct the checked EBNF value of one plus expression. -/
def plus
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    NonemptyList (EbnfValue file tokens child) →
      EbnfValue file tokens (EbnfExpr.plus child) :=
  Eq.mp (ebnfValue_plus_eq child).symm

/-- Construct the checked EBNF value of one possibly empty comma list. -/
def list0
    {file : WorkspaceFile}
    {tokens : List Token}
    (element : EbnfExpr) :
    List (EbnfValue file tokens element) →
      EbnfValue file tokens (EbnfExpr.list0 element) :=
  Eq.mp (ebnfValue_list0_eq element).symm

/-- Construct the checked EBNF value of one nonempty comma list. -/
def list1
    {file : WorkspaceFile}
    {tokens : List Token}
    (element : EbnfExpr) :
    NonemptyList (EbnfValue file tokens element) →
      EbnfValue file tokens (EbnfExpr.list1 element) :=
  Eq.mp (ebnfValue_list1_eq element).symm

/-- Expression-index transport does not identify distinct EBNF values. -/
theorem transport_injective
    {file : WorkspaceFile} {tokens : List Token}
    {left right : EbnfExpr} (indexEq : left = right) :
    Function.Injective (transport (file := file) (tokens := tokens) indexEq) := by
  cases indexEq
  intro first second valueEq
  exact valueEq

/-- The terminal-atom builder retains its exact matched terminal. -/
theorem terminalAtom_injective
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol) :
    Function.Injective
      (terminalAtom (file := file) (tokens := tokens) terminal) := by
  intro first second valueEq
  have viewedEq := congrArg
    (Eq.mp (ebnfValue_atom_terminal_eq terminal)) valueEq
  simpa [terminalAtom, cast_cast] using viewedEq

/-- The rule-atom builder retains its exact semantic value. -/
theorem ruleAtom_injective
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) :
    Function.Injective
      (ruleAtom (file := file) (tokens := tokens) rule) := by
  intro first second valueEq
  have viewedEq := congrArg
    (Eq.mp (ebnfValue_atom_nonterminal_eq rule)) valueEq
  simpa [ruleAtom, cast_cast] using viewedEq

/-- The sequence builder retains its heterogeneous child tuple. -/
theorem sequence_injective
    {file : WorkspaceFile} {tokens : List Token}
    (children : List EbnfExpr) :
    Function.Injective
      (sequence (file := file) (tokens := tokens) children) := by
  intro first second valueEq
  have viewedEq := congrArg
    (Eq.mp (ebnfValue_sequence_eq children)) valueEq
  simpa [sequence, cast_cast] using viewedEq

/-- The group builder retains its child value. -/
theorem group_injective
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) :
    Function.Injective
      (group (file := file) (tokens := tokens) child) := by
  intro first second valueEq
  have viewedEq := congrArg
    (Eq.mp (ebnfValue_group_eq child)) valueEq
  simpa [group, cast_cast] using viewedEq

/-- The choice builder retains its dependent branch/value pair. -/
theorem choice_injective
    {file : WorkspaceFile} {tokens : List Token}
    (branches : List EbnfExpr) :
    Function.Injective
      (choice (file := file) (tokens := tokens) branches) := by
  intro first second valueEq
  have viewedEq := congrArg
    (Eq.mp (ebnfValue_choice_eq branches)) valueEq
  simpa [choice, cast_cast] using viewedEq

/-- The optional builder retains absence or the exact child value. -/
theorem optional_injective
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) :
    Function.Injective
      (optional (file := file) (tokens := tokens) child) := by
  intro first second valueEq
  have viewedEq := congrArg
    (Eq.mp (ebnfValue_optional_eq child)) valueEq
  simpa [optional, cast_cast] using viewedEq

/-- The star builder retains its ordered child list. -/
theorem star_injective
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) :
    Function.Injective
      (star (file := file) (tokens := tokens) child) := by
  intro first second valueEq
  have viewedEq := congrArg
    (Eq.mp (ebnfValue_star_eq child)) valueEq
  simpa [star, cast_cast] using viewedEq

/-- The plus builder retains its nonempty child list. -/
theorem plus_injective
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) :
    Function.Injective
      (plus (file := file) (tokens := tokens) child) := by
  intro first second valueEq
  have viewedEq := congrArg
    (Eq.mp (ebnfValue_plus_eq child)) valueEq
  simpa [plus, cast_cast] using viewedEq

/-- The list-zero builder retains its ordered child list. -/
theorem list0_injective
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) :
    Function.Injective
      (list0 (file := file) (tokens := tokens) child) := by
  intro first second valueEq
  have viewedEq := congrArg
    (Eq.mp (ebnfValue_list0_eq child)) valueEq
  simpa [list0, cast_cast] using viewedEq

/-- The list-one builder retains its nonempty child list. -/
theorem list1_injective
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) :
    Function.Injective
      (list1 (file := file) (tokens := tokens) child) := by
  intro first second valueEq
  have viewedEq := congrArg
    (Eq.mp (ebnfValue_list1_eq child)) valueEq
  simpa [list1, cast_cast] using viewedEq

end EbnfValue

namespace GrammarSymbolValues

/-- View production values at one checked canonical right-hand side. -/
def view
    {file : WorkspaceFile}
    {tokens : List Token}
    {production : ProductionId}
    {canonicalRhs : List GrammarSymbol}
    (layout : production.rhs = canonicalRhs) :
    GrammarSymbolValues file tokens production.rhs →
      GrammarSymbolValues file tokens canonicalRhs :=
  GrammarSymbolValues.transport layout

end GrammarSymbolValues

namespace EbnfValues

/-- Construct the unique semantic value of an empty expression sequence. -/
def nil
    {file : WorkspaceFile} {tokens : List Token} :
    EbnfValues file tokens [] :=
  Eq.mp (ebnfValues_nil_eq (file := file) (tokens := tokens)).symm ()

/-- Prepend one semantic value to an expression-sequence value. -/
def cons
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) (rest : List EbnfExpr)
    (head : EbnfValue file tokens child)
    (tail : EbnfValues file tokens rest) :
    EbnfValues file tokens (child :: rest) :=
  Eq.mp (ebnfValues_cons_eq child rest).symm (head, tail)

/-- Viewing the empty sequence constructor yields its unit payload. -/
@[simp] theorem nil_view
    {file : WorkspaceFile} {tokens : List Token} :
    Eq.mp (ebnfValues_nil_eq (file := file) (tokens := tokens))
      (nil (file := file) (tokens := tokens)) = () := by
  unfold nil
  change cast _ (cast _ ()) = ()
  rw [cast_cast]

/-- Viewing a cons sequence constructor yields its head and tail. -/
@[simp] theorem cons_view
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) (rest : List EbnfExpr)
    (head : EbnfValue file tokens child)
    (tail : EbnfValues file tokens rest) :
    Eq.mp (ebnfValues_cons_eq child rest)
      (cons child rest head tail) = (head, tail) := by
  unfold cons
  change cast _ (cast _ (head, tail)) = (head, tail)
  rw [cast_cast]
  apply cast_eq

/-- The sequence-cons builder retains both its head and heterogeneous tail. -/
theorem cons_injective
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) (rest : List EbnfExpr)
    {firstHead secondHead : EbnfValue file tokens child}
    {firstTail secondTail : EbnfValues file tokens rest}
    (valueEq : cons child rest firstHead firstTail =
      cons child rest secondHead secondTail) :
    firstHead = secondHead ∧ firstTail = secondTail := by
  have pairEq := congrArg
    (Eq.mp (ebnfValues_cons_eq
      (file := file) (tokens := tokens) child rest)) valueEq
  simpa using pairEq

/-- Convert auxiliary nonterminal values to their expression-indexed tuple. -/
def ofAuxiliaries
    {file : WorkspaceFile}
    {tokens : List Token}
    (sites : List GrammarSite) :
    GrammarSymbolValues file tokens
      (sites.map (fun site =>
        GrammarSymbol.nonterminal (.aux site))) →
      EbnfValues file tokens
        (sites.map GrammarSite.expression) :=
  match sites with
  | [] =>
      fun _values =>
        Eq.mp
          (ebnfValues_nil_eq (file := file) (tokens := tokens)).symm ()
  | site :: rest =>
      fun values =>
        Eq.mp
          (ebnfValues_cons_eq (file := file) (tokens := tokens)
            site.expression (rest.map GrammarSite.expression)).symm
          (values.1, ofAuxiliaries rest values.2)

/-- Viewing the empty auxiliary conversion yields the unique empty tuple. -/
@[simp] theorem ofAuxiliaries_nil_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (values : GrammarSymbolValues file tokens []) :
    Eq.mp (ebnfValues_nil_eq (file := file) (tokens := tokens))
      (ofAuxiliaries (file := file) (tokens := tokens) [] values) = () := by
  change cast _ (cast _ ()) = ()
  rw [cast_cast]

/-- Viewing a cons conversion preserves its head and recursive tail. -/
@[simp] theorem ofAuxiliaries_cons_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (site : GrammarSite)
    (rest : List GrammarSite)
    (head : EbnfValue file tokens site.expression)
    (tail : GrammarSymbolValues file tokens
      (rest.map (fun child =>
        GrammarSymbol.nonterminal (.aux child)))) :
    Eq.mp
        (ebnfValues_cons_eq (file := file) (tokens := tokens)
          site.expression (rest.map GrammarSite.expression))
        (ofAuxiliaries (file := file) (tokens := tokens) (site :: rest)
          (head, tail)) =
      (head, ofAuxiliaries rest tail) := by
  change cast _ (cast _ (head, ofAuxiliaries rest tail)) = _
  rw [cast_cast]
  apply cast_eq

end EbnfValues

namespace EbnfValue

/-- Viewing a value immediately after restoring its site index is identity. -/
private theorem atShape_ofShape_eq
    {file : WorkspaceFile} {tokens : List Token}
    {site : GrammarSite} {expression : EbnfExpr}
    (shape : site.expression = expression)
    (value : EbnfValue file tokens expression) :
    atShape shape (ofShape shape value) = value := by
  unfold atShape ofShape transport
  change cast _ (cast _ value) = value
  rw [cast_cast]
  apply cast_eq

end EbnfValue

namespace RootAction

/-- Extract the checked source-rule EBNF value from a root production. -/
def unpack
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) :
    GrammarSymbolValues file tokens (ProductionId.root rule).rhs →
      EbnfValue file tokens (m2cV1.rhs rule) :=
  fun values =>
    EbnfValue.atShape (GrammarSite.root_expression rule)
      (GrammarSymbolValues.view (ProductionId.rhs_root rule) values).1

/-- Root unpacking views the canonical child and restores its source shape. -/
@[simp] theorem unpack_eq
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (values : GrammarSymbolValues file tokens
      (ProductionId.root rule).rhs) :
    unpack rule values =
      EbnfValue.atShape (GrammarSite.root_expression rule)
        (GrammarSymbolValues.view
          (ProductionId.rhs_root rule) values).1 :=
  rfl

end RootAction

namespace AtomSite

/-- Construct the checked family value of one already translated atom. -/
private def packAtom
    {file : WorkspaceFile} {tokens : List Token} :
    (atom : EbnfAtom) →
      GrammarSymbolValue file tokens atom.grammarSymbol →
      EbnfValue file tokens (.atom atom)
  | .terminal terminal, value => EbnfValue.terminalAtom terminal value
  | .nonterminal rule, value =>
      EbnfValue.ruleAtom (file := file) (tokens := tokens) rule value

/-- Atom packing commutes with transport along an atom equality. -/
private theorem transport_packAtom
    {file : WorkspaceFile} {tokens : List Token}
    {left right : EbnfAtom}
    (equality : left = right)
    (value : GrammarSymbolValue file tokens left.grammarSymbol) :
    EbnfValue.transport (congrArg EbnfExpr.atom equality)
        (packAtom left value) =
      packAtom right
        (Eq.mp
          (congrArg (GrammarSymbolValue file tokens)
            (congrArg EbnfAtom.grammarSymbol equality))
          value) := by
  cases equality
  rfl

/-- Pack one expanded atom production into its auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.AtomSite) :
    GrammarSymbolValues file tokens (ProductionId.atom site).rhs →
      NonterminalValue file tokens (ProductionId.atom site).lhs :=
  fun values =>
    let atomValue :=
      Eq.mp (congrArg (GrammarSymbolValue file tokens) site.symbol_eq)
        (GrammarSymbolValues.view (ProductionId.rhs_atom site) values).1
    EbnfValue.ofShape site.expression_eq_atom
      (packAtom site.atom atomValue)

/-- View one packed atom at an explicitly checked atom index. -/
def packAtAtom
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.AtomSite) (atom : EbnfAtom)
    (atomEq : site.atom = atom)
    (values : GrammarSymbolValues file tokens
      (ProductionId.atom site).rhs) :
    EbnfValue file tokens (.atom atom) :=
  EbnfValue.transport (congrArg EbnfExpr.atom atomEq)
    (EbnfValue.atShape site.expression_eq_atom (pack site values))

/-- Packing a terminal atom retains its exact checked terminal match. -/
@[simp] theorem pack_terminal_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.AtomSite) (terminal : TerminalSymbol)
    (atomEq : site.atom = .terminal terminal)
    (values : GrammarSymbolValues file tokens
      (ProductionId.atom site).rhs) :
    packAtAtom site (.terminal terminal) atomEq values =
      EbnfValue.terminalAtom terminal
        (Eq.mp
          (congrArg (GrammarSymbolValue file tokens)
            (congrArg EbnfAtom.grammarSymbol atomEq))
          (Eq.mp
            (congrArg (GrammarSymbolValue file tokens) site.symbol_eq)
            (GrammarSymbolValues.view
              (ProductionId.rhs_atom site) values).1)) := by
  let atomValue :=
    Eq.mp (congrArg (GrammarSymbolValue file tokens) site.symbol_eq)
      (GrammarSymbolValues.view (ProductionId.rhs_atom site) values).1
  unfold packAtAtom pack
  change EbnfValue.transport (congrArg EbnfExpr.atom atomEq)
    (EbnfValue.atShape site.expression_eq_atom
      (EbnfValue.ofShape site.expression_eq_atom
        (packAtom site.atom atomValue))) = _
  rw [EbnfValue.atShape_ofShape_eq, transport_packAtom atomEq]
  rfl

/-- Packing a rule atom retains its exact source-rule semantic value. -/
@[simp] theorem pack_rule_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.AtomSite) (rule : GrammarRuleId)
    (atomEq : site.atom = .nonterminal rule)
    (values : GrammarSymbolValues file tokens
      (ProductionId.atom site).rhs) :
    packAtAtom site (.nonterminal rule) atomEq values =
      EbnfValue.ruleAtom (file := file) (tokens := tokens) rule
        (Eq.mp
          (congrArg (GrammarSymbolValue file tokens)
            (congrArg EbnfAtom.grammarSymbol atomEq))
          (Eq.mp
            (congrArg (GrammarSymbolValue file tokens) site.symbol_eq)
            (GrammarSymbolValues.view
              (ProductionId.rhs_atom site) values).1)) := by
  let atomValue :=
    Eq.mp (congrArg (GrammarSymbolValue file tokens) site.symbol_eq)
      (GrammarSymbolValues.view (ProductionId.rhs_atom site) values).1
  unfold packAtAtom pack
  change EbnfValue.transport (congrArg EbnfExpr.atom atomEq)
    (EbnfValue.atShape site.expression_eq_atom
      (EbnfValue.ofShape site.expression_eq_atom
        (packAtom site.atom atomValue))) = _
  rw [EbnfValue.atShape_ofShape_eq, transport_packAtom atomEq]
  rfl

end AtomSite

namespace SequenceSite

/-- Pack one expanded sequence into its auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.SequenceSite) :
    GrammarSymbolValues file tokens (ProductionId.seq site).rhs →
      NonterminalValue file tokens (ProductionId.seq site).lhs :=
  fun values =>
    EbnfValue.ofShape site.expression_eq_sequence
      (EbnfValue.sequence (site.children.map GrammarSite.expression)
        (EbnfValues.ofAuxiliaries site.children
          (GrammarSymbolValues.view (ProductionId.rhs_seq site) values)))

/-- Sequence packing preserves every child value in displayed order. -/
@[simp] theorem pack_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.SequenceSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.seq site).rhs) :
    EbnfValue.atShape site.expression_eq_sequence (pack site values) =
      EbnfValue.sequence (site.children.map GrammarSite.expression)
        (EbnfValues.ofAuxiliaries site.children
          (GrammarSymbolValues.view (ProductionId.rhs_seq site) values)) := by
  exact EbnfValue.atShape_ofShape_eq _ _

end SequenceSite

namespace GroupSite

/-- Pack one expanded group into its auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.GroupSite) :
    GrammarSymbolValues file tokens (ProductionId.group site).rhs →
      NonterminalValue file tokens (ProductionId.group site).lhs :=
  fun values =>
    EbnfValue.ofShape site.expression_eq_group
      (EbnfValue.group site.child.expression
        (GrammarSymbolValues.view (ProductionId.rhs_group site) values).1)

/-- Group packing preserves its unique checked child value. -/
@[simp] theorem pack_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.GroupSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.group site).rhs) :
    EbnfValue.atShape site.expression_eq_group (pack site values) =
      EbnfValue.group site.child.expression
        (GrammarSymbolValues.view
          (ProductionId.rhs_group site) values).1 := by
  exact EbnfValue.atShape_ofShape_eq _ _

end GroupSite

namespace ChoiceSite

/-- Pack one expanded choice branch into its tagged auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.ChoiceSite)
    (branch : Fin site.branchCount) :
    GrammarSymbolValues file tokens
      (ProductionId.choice site branch).rhs →
      NonterminalValue file tokens
        (ProductionId.choice site branch).lhs :=
  fun values =>
    let childValue :=
      EbnfValue.transport
        ((site.branch_expression branch).trans
          (site.branch_get_toList branch).symm)
        (GrammarSymbolValues.view
          (ProductionId.rhs_choice site branch) values).1
    EbnfValue.ofShape site.expression_eq_choice
      (EbnfValue.choice site.branchExpressions.toList
        ⟨site.branchListIndex branch, childValue⟩)

/-- Choice packing preserves the exact displayed branch tag and child. -/
@[simp] theorem pack_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.ChoiceSite)
    (branch : Fin site.branchCount)
    (values : GrammarSymbolValues file tokens
      (ProductionId.choice site branch).rhs) :
    EbnfValue.atShape site.expression_eq_choice
        (pack site branch values) =
      EbnfValue.choice site.branchExpressions.toList
        ⟨site.branchListIndex branch,
          EbnfValue.transport
            ((site.branch_expression branch).trans
              (site.branch_get_toList branch).symm)
            (GrammarSymbolValues.view
              (ProductionId.rhs_choice site branch) values).1⟩ := by
  exact EbnfValue.atShape_ofShape_eq _ _

end ChoiceSite

namespace OptionalSite

/-- Pack either expanded optional production into its auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.OptionalSite) (branch : OptionalBranch) :
    GrammarSymbolValues file tokens
      (ProductionId.opt site branch).rhs →
      NonterminalValue file tokens (ProductionId.opt site branch).lhs :=
  match branch with
  | .none => fun values =>
      match GrammarSymbolValues.view
          (ProductionId.rhs_opt_none site) values with
      | () =>
          EbnfValue.ofShape site.expression_eq_optional
            (EbnfValue.optional site.child.expression none)
  | .some => fun values =>
      EbnfValue.ofShape site.expression_eq_optional
        (EbnfValue.optional site.child.expression
          (some (GrammarSymbolValues.view
            (ProductionId.rhs_opt_some site) values).1))

/-- Empty optional packing yields the checked absent value. -/
@[simp] theorem pack_none_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .none).rhs) :
    EbnfValue.atShape site.expression_eq_optional
        (pack site .none values) =
      EbnfValue.optional site.child.expression none := by
  unfold pack
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_opt_none site) values = viewed
  cases viewed
  exact EbnfValue.atShape_ofShape_eq _ _

/-- Present optional packing preserves its unique checked child value. -/
@[simp] theorem pack_some_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .some).rhs) :
    EbnfValue.atShape site.expression_eq_optional
        (pack site .some values) =
      EbnfValue.optional site.child.expression
        (some (GrammarSymbolValues.view
          (ProductionId.rhs_opt_some site) values).1) := by
  exact EbnfValue.atShape_ofShape_eq _ _

end OptionalSite

namespace StarSite

/-- Pack either expanded star production into its auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.StarSite) (branch : NilConsBranch) :
    GrammarSymbolValues file tokens
      (ProductionId.star site branch).rhs →
      NonterminalValue file tokens (ProductionId.star site branch).lhs :=
  match branch with
  | .nil => fun values =>
      match GrammarSymbolValues.view
          (ProductionId.rhs_star_nil site) values with
      | () =>
          EbnfValue.ofShape site.expression_eq_star
            (EbnfValue.star site.child.expression [])
  | .cons => fun values =>
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_star_cons site) values
      let tailValue :=
        EbnfValue.atShape site.expression_eq_star viewed.2.1
      let tail :=
        Eq.mp (ebnfValue_star_eq site.child.expression) tailValue
      EbnfValue.ofShape site.expression_eq_star
        (EbnfValue.star site.child.expression (viewed.1 :: tail))

/-- Empty star packing yields the checked empty repetition. -/
@[simp] theorem pack_nil_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .nil).rhs) :
    EbnfValue.atShape site.expression_eq_star
        (pack site .nil values) =
      EbnfValue.star site.child.expression [] := by
  unfold pack
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_star_nil site) values = viewed
  cases viewed
  exact EbnfValue.atShape_ofShape_eq _ _

/-- Extending star packing prepends one child to the recursive repetition. -/
@[simp] theorem pack_cons_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .cons).rhs) :
    EbnfValue.atShape site.expression_eq_star
        (pack site .cons values) =
      EbnfValue.star site.child.expression
        ((GrammarSymbolValues.view
            (ProductionId.rhs_star_cons site) values).1 ::
          Eq.mp (ebnfValue_star_eq site.child.expression)
            (EbnfValue.atShape site.expression_eq_star
              (GrammarSymbolValues.view
                (ProductionId.rhs_star_cons site) values).2.1)) := by
  exact EbnfValue.atShape_ofShape_eq _ _

end StarSite

namespace PlusSite

/-- Pack either expanded plus production into its auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.PlusSite) (branch : OneConsBranch) :
    GrammarSymbolValues file tokens
      (ProductionId.plus site branch).rhs →
      NonterminalValue file tokens (ProductionId.plus site branch).lhs :=
  match branch with
  | .one => fun values =>
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_plus_one site) values
      EbnfValue.ofShape site.expression_eq_plus
        (EbnfValue.plus site.child.expression {
          head := viewed.1
          tail := []
        })
  | .cons => fun values =>
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_plus_cons site) values
      let tailValue :=
        EbnfValue.atShape site.expression_eq_plus viewed.2.1
      let tail :=
        Eq.mp (ebnfValue_plus_eq site.child.expression) tailValue
      EbnfValue.ofShape site.expression_eq_plus
        (EbnfValue.plus site.child.expression {
          head := viewed.1
          tail := tail.head :: tail.tail
        })

/-- Singleton plus packing yields one child and no remaining values. -/
@[simp] theorem pack_one_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .one).rhs) :
    EbnfValue.atShape site.expression_eq_plus
        (pack site .one values) =
      EbnfValue.plus site.child.expression {
        head := (GrammarSymbolValues.view
          (ProductionId.rhs_plus_one site) values).1
        tail := []
      } := by
  exact EbnfValue.atShape_ofShape_eq _ _

/-- Extending plus packing prepends one child to the recursive nonempty value. -/
@[simp] theorem pack_cons_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .cons).rhs) :
    let viewed := GrammarSymbolValues.view
      (ProductionId.rhs_plus_cons site) values
    let tail := Eq.mp (ebnfValue_plus_eq site.child.expression)
      (EbnfValue.atShape site.expression_eq_plus viewed.2.1)
    EbnfValue.atShape site.expression_eq_plus
        (pack site .cons values) =
      EbnfValue.plus site.child.expression {
        head := viewed.1
        tail := tail.head :: tail.tail
      } := by
  exact EbnfValue.atShape_ofShape_eq _ _

end PlusSite

namespace List0Site

/-- Pack either expanded zero-or-more list production into its EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.List0Site) (branch : NilConsBranch) :
    GrammarSymbolValues file tokens
      (ProductionId.list0 site branch).rhs →
      NonterminalValue file tokens (ProductionId.list0 site branch).lhs :=
  match branch with
  | .nil => fun values =>
      match GrammarSymbolValues.view
          (ProductionId.rhs_list0_nil site) values with
      | () =>
          EbnfValue.ofShape site.expression_eq_list0
            (EbnfValue.list0 site.element.expression [])
  | .cons => fun values =>
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_list0_cons site) values
      let tail := Eq.mp
        (congrArg
          (fun element : GrammarSite =>
            List (EbnfValue file tokens element.expression))
          (Grammar.ListSite.element_list0 site))
        viewed.2.1
      EbnfValue.ofShape site.expression_eq_list0
        (EbnfValue.list0 site.element.expression (viewed.1 :: tail))

/-- Empty zero-or-more list packing yields the checked empty list. -/
@[simp] theorem pack_nil_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .nil).rhs) :
    EbnfValue.atShape site.expression_eq_list0
        (pack site .nil values) =
      EbnfValue.list0 site.element.expression [] := by
  unfold pack
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_list0_nil site) values = viewed
  cases viewed
  exact EbnfValue.atShape_ofShape_eq _ _

/-- Extending zero-or-more list packing prepends its exact element. -/
@[simp] theorem pack_cons_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .cons).rhs) :
    let viewed := GrammarSymbolValues.view
      (ProductionId.rhs_list0_cons site) values
    let tail := Eq.mp
      (congrArg
        (fun element : GrammarSite =>
          List (EbnfValue file tokens element.expression))
        (Grammar.ListSite.element_list0 site))
      viewed.2.1
    EbnfValue.atShape site.expression_eq_list0
        (pack site .cons values) =
      EbnfValue.list0 site.element.expression (viewed.1 :: tail) := by
  exact EbnfValue.atShape_ofShape_eq _ _

end List0Site

namespace List1Site

/-- Pack one expanded nonempty list production into its EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.List1Site) :
    GrammarSymbolValues file tokens (ProductionId.list1 site).rhs →
      NonterminalValue file tokens (ProductionId.list1 site).lhs :=
  fun values =>
    let viewed := GrammarSymbolValues.view
      (ProductionId.rhs_list1 site) values
    let tail := Eq.mp
      (congrArg
        (fun element : GrammarSite =>
          List (EbnfValue file tokens element.expression))
        (Grammar.ListSite.element_list1 site))
      viewed.2.1
    EbnfValue.ofShape site.expression_eq_list1
      (EbnfValue.list1 site.element.expression {
        head := viewed.1
        tail := tail
      })

/-- Nonempty list packing preserves its head and exact comma-tail values. -/
@[simp] theorem pack_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.List1Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list1 site).rhs) :
    let viewed := GrammarSymbolValues.view
      (ProductionId.rhs_list1 site) values
    let tail := Eq.mp
      (congrArg
        (fun element : GrammarSite =>
          List (EbnfValue file tokens element.expression))
        (Grammar.ListSite.element_list1 site))
      viewed.2.1
    EbnfValue.atShape site.expression_eq_list1 (pack site values) =
      EbnfValue.list1 site.element.expression {
        head := viewed.1
        tail := tail
      } := by
  exact EbnfValue.atShape_ofShape_eq _ _

end List1Site

namespace ListSite

/-- Pack either expanded comma-tail production into its exact element list. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.ListSite) (branch : NilConsBranch) :
    GrammarSymbolValues file tokens
      (ProductionId.tail site branch).rhs →
      NonterminalValue file tokens (ProductionId.tail site branch).lhs :=
  match branch with
  | .nil => fun values =>
      match GrammarSymbolValues.view
          (ProductionId.rhs_tail_nil site) values with
      | () => []
  | .cons => fun values =>
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_tail_cons site) values
      viewed.2.1 :: viewed.2.2.1

/-- Empty comma-tail packing consumes its empty RHS and returns no values. -/
@[simp] theorem pack_nil_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .nil).rhs) :
    pack site .nil values = [] := by
  unfold pack
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_tail_nil site) values = viewed
  cases viewed
  rfl

/-- Extending comma-tail packing consumes its comma and prepends its element. -/
@[simp] theorem pack_cons_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .cons).rhs) :
    pack site .cons values =
      (GrammarSymbolValues.view
          (ProductionId.rhs_tail_cons site) values).2.1 ::
        (GrammarSymbolValues.view
          (ProductionId.rhs_tail_cons site) values).2.2.1 :=
  rfl

end ListSite

/-- Every outer production constructor has its checked total transport from
the exact RHS-indexed heterogeneous tuple to the corresponding action input or
auxiliary result. -/
theorem production_rhs_typed_hlist_transport
    {file : WorkspaceFile} {tokens : List Token}
    (production : ProductionId) :
    match production with
    | .root rule => Nonempty (
        GrammarSymbolValues file tokens (ProductionId.root rule).rhs →
          EbnfValue file tokens (m2cV1.rhs rule))
    | .atom site => Nonempty (
        GrammarSymbolValues file tokens (ProductionId.atom site).rhs →
          NonterminalValue file tokens (ProductionId.atom site).lhs)
    | .seq site => Nonempty (
        GrammarSymbolValues file tokens (ProductionId.seq site).rhs →
          NonterminalValue file tokens (ProductionId.seq site).lhs)
    | .group site => Nonempty (
        GrammarSymbolValues file tokens (ProductionId.group site).rhs →
          NonterminalValue file tokens (ProductionId.group site).lhs)
    | .choice site branch => Nonempty (
        GrammarSymbolValues file tokens
            (ProductionId.choice site branch).rhs →
          NonterminalValue file tokens
            (ProductionId.choice site branch).lhs)
    | .opt site branch => Nonempty (
        GrammarSymbolValues file tokens (ProductionId.opt site branch).rhs →
          NonterminalValue file tokens (ProductionId.opt site branch).lhs)
    | .star site branch => Nonempty (
        GrammarSymbolValues file tokens
            (ProductionId.star site branch).rhs →
          NonterminalValue file tokens (ProductionId.star site branch).lhs)
    | .plus site branch => Nonempty (
        GrammarSymbolValues file tokens
            (ProductionId.plus site branch).rhs →
          NonterminalValue file tokens (ProductionId.plus site branch).lhs)
    | .list0 site branch => Nonempty (
        GrammarSymbolValues file tokens
            (ProductionId.list0 site branch).rhs →
          NonterminalValue file tokens (ProductionId.list0 site branch).lhs)
    | .list1 site => Nonempty (
        GrammarSymbolValues file tokens (ProductionId.list1 site).rhs →
          NonterminalValue file tokens (ProductionId.list1 site).lhs)
    | .tail site branch => Nonempty (
        GrammarSymbolValues file tokens (ProductionId.tail site branch).rhs →
          NonterminalValue file tokens (ProductionId.tail site branch).lhs) := by
  cases production with
  | root rule => exact ⟨RootAction.unpack rule⟩
  | atom site => exact ⟨AtomSite.pack site⟩
  | seq site => exact ⟨SequenceSite.pack site⟩
  | group site => exact ⟨GroupSite.pack site⟩
  | choice site branch => exact ⟨ChoiceSite.pack site branch⟩
  | opt site branch => exact ⟨OptionalSite.pack site branch⟩
  | star site branch => exact ⟨StarSite.pack site branch⟩
  | plus site branch => exact ⟨PlusSite.pack site branch⟩
  | list0 site branch => exact ⟨List0Site.pack site branch⟩
  | list1 site => exact ⟨List1Site.pack site⟩
  | tail site branch => exact ⟨ListSite.pack site branch⟩

/-- Every typed action packer satisfies its checked canonical result equation,
exhaustively by the eleven outer production constructors and their branches. -/
theorem actionPackers_typed_exact
    {file : WorkspaceFile} {tokens : List Token}
    (production : ProductionId) :
    match production with
    | .root rule => ∀ (values : GrammarSymbolValues file tokens
        (ProductionId.root rule).rhs),
        RootAction.unpack (file := file) (tokens := tokens) rule values =
          EbnfValue.atShape (GrammarSite.root_expression rule)
            (GrammarSymbolValues.view
              (ProductionId.rhs_root rule) values).1
    | .atom site =>
        (∀ terminal (atomEq : site.atom = .terminal terminal)
            (values : GrammarSymbolValues file tokens
              (ProductionId.atom site).rhs),
          AtomSite.packAtAtom (file := file) (tokens := tokens)
              site (.terminal terminal) atomEq values =
            EbnfValue.terminalAtom terminal
              (Eq.mp
                (congrArg (GrammarSymbolValue file tokens)
                  (congrArg EbnfAtom.grammarSymbol atomEq))
                (Eq.mp
                  (congrArg (GrammarSymbolValue file tokens) site.symbol_eq)
                  (GrammarSymbolValues.view
                    (ProductionId.rhs_atom site) values).1))) ∧
        (∀ rule (atomEq : site.atom = .nonterminal rule)
            (values : GrammarSymbolValues file tokens
              (ProductionId.atom site).rhs),
          AtomSite.packAtAtom (file := file) (tokens := tokens)
              site (.nonterminal rule) atomEq values =
            EbnfValue.ruleAtom (file := file) (tokens := tokens) rule
              (Eq.mp
                (congrArg (GrammarSymbolValue file tokens)
                  (congrArg EbnfAtom.grammarSymbol atomEq))
                (Eq.mp
                  (congrArg (GrammarSymbolValue file tokens) site.symbol_eq)
                  (GrammarSymbolValues.view
                    (ProductionId.rhs_atom site) values).1)))
    | .seq site => ∀ (values : GrammarSymbolValues file tokens
        (ProductionId.seq site).rhs),
        EbnfValue.atShape site.expression_eq_sequence
            (SequenceSite.pack site values) =
          EbnfValue.sequence (site.children.map GrammarSite.expression)
            (EbnfValues.ofAuxiliaries site.children
              (GrammarSymbolValues.view
                (ProductionId.rhs_seq site) values))
    | .group site => ∀ (values : GrammarSymbolValues file tokens
        (ProductionId.group site).rhs),
        EbnfValue.atShape site.expression_eq_group
            (GroupSite.pack site values) =
          EbnfValue.group site.child.expression
            (GrammarSymbolValues.view
              (ProductionId.rhs_group site) values).1
    | .choice site branch => ∀ (values : GrammarSymbolValues file tokens
        (ProductionId.choice site branch).rhs),
        EbnfValue.atShape site.expression_eq_choice
            (ChoiceSite.pack site branch values) =
          EbnfValue.choice site.branchExpressions.toList
            ⟨site.branchListIndex branch,
              EbnfValue.transport
                ((site.branch_expression branch).trans
                  (site.branch_get_toList branch).symm)
                (GrammarSymbolValues.view
                  (ProductionId.rhs_choice site branch) values).1⟩
    | .opt site branch =>
        match branch with
        | .none => ∀ (values : GrammarSymbolValues file tokens
            (ProductionId.opt site .none).rhs),
            EbnfValue.atShape site.expression_eq_optional
                (OptionalSite.pack site .none values) =
              EbnfValue.optional site.child.expression none
        | .some => ∀ (values : GrammarSymbolValues file tokens
            (ProductionId.opt site .some).rhs),
            EbnfValue.atShape site.expression_eq_optional
                (OptionalSite.pack site .some values) =
              EbnfValue.optional site.child.expression
                (some (GrammarSymbolValues.view
                  (ProductionId.rhs_opt_some site) values).1)
    | .star site branch =>
        match branch with
        | .nil => ∀ (values : GrammarSymbolValues file tokens
            (ProductionId.star site .nil).rhs),
            EbnfValue.atShape site.expression_eq_star
                (StarSite.pack site .nil values) =
              EbnfValue.star site.child.expression []
        | .cons => ∀ (values : GrammarSymbolValues file tokens
            (ProductionId.star site .cons).rhs),
            EbnfValue.atShape site.expression_eq_star
                (StarSite.pack site .cons values) =
              EbnfValue.star site.child.expression
                ((GrammarSymbolValues.view
                    (ProductionId.rhs_star_cons site) values).1 ::
                  Eq.mp (ebnfValue_star_eq site.child.expression)
                    (EbnfValue.atShape site.expression_eq_star
                      (GrammarSymbolValues.view
                        (ProductionId.rhs_star_cons site) values).2.1))
    | .plus site branch =>
        match branch with
        | .one => ∀ (values : GrammarSymbolValues file tokens
            (ProductionId.plus site .one).rhs),
            EbnfValue.atShape site.expression_eq_plus
                (PlusSite.pack site .one values) =
              EbnfValue.plus site.child.expression {
                head := (GrammarSymbolValues.view
                  (ProductionId.rhs_plus_one site) values).1
                tail := []
              }
        | .cons => ∀ (values : GrammarSymbolValues file tokens
            (ProductionId.plus site .cons).rhs),
            let viewed := GrammarSymbolValues.view
              (ProductionId.rhs_plus_cons site) values
            let tail := Eq.mp (ebnfValue_plus_eq site.child.expression)
              (EbnfValue.atShape site.expression_eq_plus viewed.2.1)
            EbnfValue.atShape site.expression_eq_plus
                (PlusSite.pack site .cons values) =
              EbnfValue.plus site.child.expression {
                head := viewed.1
                tail := tail.head :: tail.tail
              }
    | .list0 site branch =>
        match branch with
        | .nil => ∀ (values : GrammarSymbolValues file tokens
            (ProductionId.list0 site .nil).rhs),
            EbnfValue.atShape site.expression_eq_list0
                (List0Site.pack site .nil values) =
              EbnfValue.list0 site.element.expression []
        | .cons => ∀ (values : GrammarSymbolValues file tokens
            (ProductionId.list0 site .cons).rhs),
            let viewed := GrammarSymbolValues.view
              (ProductionId.rhs_list0_cons site) values
            let tail := Eq.mp
              (congrArg
                (fun element : GrammarSite =>
                  List (EbnfValue file tokens element.expression))
                (ListSite.element_list0 site))
              viewed.2.1
            EbnfValue.atShape site.expression_eq_list0
                (List0Site.pack site .cons values) =
              EbnfValue.list0 site.element.expression (viewed.1 :: tail)
    | .list1 site => ∀ (values : GrammarSymbolValues file tokens
        (ProductionId.list1 site).rhs),
        let viewed := GrammarSymbolValues.view
          (ProductionId.rhs_list1 site) values
        let tail := Eq.mp
          (congrArg
            (fun element : GrammarSite =>
              List (EbnfValue file tokens element.expression))
            (ListSite.element_list1 site))
          viewed.2.1
        EbnfValue.atShape site.expression_eq_list1
            (List1Site.pack site values) =
          EbnfValue.list1 site.element.expression {
            head := viewed.1
            tail := tail
          }
    | .tail site branch =>
        match branch with
        | .nil => ∀ (values : GrammarSymbolValues file tokens
            (ProductionId.tail site .nil).rhs),
            ListSite.pack site .nil values = []
        | .cons => ∀ (values : GrammarSymbolValues file tokens
            (ProductionId.tail site .cons).rhs),
            ListSite.pack site .cons values =
              (GrammarSymbolValues.view
                  (ProductionId.rhs_tail_cons site) values).2.1 ::
                (GrammarSymbolValues.view
                  (ProductionId.rhs_tail_cons site) values).2.2.1 := by
  cases production with
  | root rule => exact fun values => RootAction.unpack_eq rule values
  | atom site =>
      exact ⟨fun terminal atomEq values =>
          AtomSite.pack_terminal_eq site terminal atomEq values,
        fun rule atomEq values =>
          AtomSite.pack_rule_eq site rule atomEq values⟩
  | seq site => exact fun values => SequenceSite.pack_eq site values
  | group site => exact fun values => GroupSite.pack_eq site values
  | choice site branch =>
      exact fun values => ChoiceSite.pack_eq site branch values
  | opt site branch =>
      cases branch with
      | none => exact fun values => OptionalSite.pack_none_eq site values
      | some => exact fun values => OptionalSite.pack_some_eq site values
  | star site branch =>
      cases branch with
      | nil => exact fun values => StarSite.pack_nil_eq site values
      | cons => exact fun values => StarSite.pack_cons_eq site values
  | plus site branch =>
      cases branch with
      | one => exact fun values => PlusSite.pack_one_eq site values
      | cons => exact fun values => PlusSite.pack_cons_eq site values
  | list0 site branch =>
      cases branch with
      | nil => exact fun values => List0Site.pack_nil_eq site values
      | cons => exact fun values => List0Site.pack_cons_eq site values
  | list1 site => exact fun values => List1Site.pack_eq site values
  | tail site branch =>
      cases branch with
      | nil => exact fun values => ListSite.pack_nil_eq site values
      | cons => exact fun values => ListSite.pack_cons_eq site values

namespace PackedEdgeKey

/-- Exact structural validity for an unguarded scanned or completed edge. -/
def Valid
    (file : WorkspaceFile)
    (tokens : List Token) :
    PackedEdgeKey tokens → Prop
  | .scanned before after terminalCursor =>
      ∃ terminal value span,
        NextSymbol before (GrammarSymbol.terminal terminal) ∧
          terminalCursor.beforeBoundary = before.current ∧
          TerminalAt file tokens terminalCursor value span ∧
          TerminalMatches terminal value ∧
          AdvanceItem before terminalCursor.afterBoundary after
  | .completed waiting finished after sharedCursor =>
      ∃ symbol,
        NextSymbol waiting (GrammarSymbol.nonterminal symbol) ∧
          CompleteItem finished ∧
          finished.production.lhs = symbol ∧
          waiting.current = sharedCursor ∧
          finished.origin = sharedCursor ∧
          AdvanceItem waiting finished.current after

end PackedEdgeKey

/-- Checked Type witness for one valid scanned edge. -/
structure ScannedEdgeWitness
    (file : WorkspaceFile)
    (tokens : List Token)
    (before after : DottedItem tokens)
    (cursor : TerminalCursor tokens) : Type where
  terminal : TerminalSymbol
  matched : MatchedTerminal file tokens terminal
  sameCursor : matched.cursor = cursor
  next : NextSymbol before (GrammarSymbol.terminal terminal)
  atCurrent : cursor.beforeBoundary = before.current
  advance : AdvanceItem before matched.cursor.afterBoundary after
  deriving Repr, DecidableEq

instance {file : WorkspaceFile} {tokens : List Token}
    {before after : DottedItem tokens} {cursor : TerminalCursor tokens} :
    BEq (ScannedEdgeWitness file tokens before after cursor) :=
  ⟨fun left right => decide (left = right)⟩

namespace ScannedEdgeWitness

/-- One fixed scanned edge key has a unique checked witness value. -/
theorem functional
    {file : WorkspaceFile} {tokens : List Token}
    {before after : DottedItem tokens}
    {cursor : TerminalCursor tokens}
    (left right : ScannedEdgeWitness file tokens before after cursor) :
    left = right := by
  cases left with
  | mk leftTerminal leftMatched leftSameCursor leftNext leftAtCurrent
      leftAdvance =>
      cases right with
      | mk rightTerminal rightMatched rightSameCursor rightNext rightAtCurrent
          rightAdvance =>
          have terminalEq : leftTerminal = rightTerminal := by
            have lookupEq := leftNext.2.symm.trans rightNext.2
            exact GrammarSymbol.terminal.inj (Option.some.inj lookupEq)
          subst rightTerminal
          have cursorEq : leftMatched.cursor = rightMatched.cursor :=
            leftSameCursor.trans rightSameCursor.symm
          cases leftMatched with
          | mk leftCursor leftValue leftSpan leftTerminalAt leftMatches =>
              cases rightMatched with
              | mk rightCursor rightValue rightSpan rightTerminalAt
                  rightMatches =>
                  simp only at cursorEq
                  subst rightCursor
                  rcases TerminalAt.functional leftTerminalAt rightTerminalAt with
                    ⟨valueEq, spanEq⟩
                  subst rightValue
                  subst rightSpan
                  rfl

end ScannedEdgeWitness

/-- Checked Type witness for one valid completed edge. -/
structure CompletedEdgeWitness
    (tokens : List Token)
    (waiting finished after : DottedItem tokens)
    (shared : Boundary tokens) : Type where
  next : NextSymbol waiting
    (GrammarSymbol.nonterminal finished.production.lhs)
  complete : CompleteItem finished
  waitingAtShared : waiting.current = shared
  finishedAtShared : finished.origin = shared
  advance : AdvanceItem waiting finished.current after
  deriving Repr, DecidableEq

instance {tokens : List Token}
    {waiting finished after : DottedItem tokens} {shared : Boundary tokens} :
    BEq (CompletedEdgeWitness tokens waiting finished after shared) :=
  ⟨fun left right => decide (left = right)⟩

namespace CompletedEdgeWitness

/-- One fixed completed edge key has a unique checked witness value. -/
theorem functional
    {tokens : List Token}
    {waiting finished after : DottedItem tokens}
    {shared : Boundary tokens}
    (left right : CompletedEdgeWitness tokens waiting finished after shared) :
    left = right := by
  cases left
  cases right
  rfl

end CompletedEdgeWitness

/-- A scanned edge is valid exactly when its checked Type witness is inhabited. -/
theorem packedEdge_scanned_valid_iff
    {file : WorkspaceFile}
    {tokens : List Token}
    {before after : DottedItem tokens}
    {cursor : TerminalCursor tokens} :
    PackedEdgeKey.Valid file tokens (.scanned before after cursor) ↔
      Nonempty (ScannedEdgeWitness file tokens before after cursor) := by
  constructor
  · rintro ⟨terminal, value, span, next, atCurrent,
      terminalAt, terminalMatches, advance⟩
    exact ⟨{
      terminal := terminal
      matched := {
        cursor := cursor
        value := value
        span := span
        «at» := terminalAt
        «matches» := terminalMatches
      }
      sameCursor := rfl
      next := next
      atCurrent := atCurrent
      advance := advance
    }⟩
  · rintro ⟨witness⟩
    rcases witness with
      ⟨terminal, matched, sameCursor, next, atCurrent, matchedAdvance⟩
    have terminalAt : TerminalAt file tokens cursor
        matched.value matched.span := by
      rw [← sameCursor]
      exact matched.at
    have afterBoundaryEq : matched.cursor.afterBoundary =
        cursor.afterBoundary :=
      congrArg TerminalCursor.afterBoundary sameCursor
    have advance : AdvanceItem before cursor.afterBoundary after := by
      rw [← afterBoundaryEq]
      exact matchedAdvance
    exact ⟨terminal, matched.value, matched.span, next, atCurrent,
      terminalAt, matched.matches, advance⟩

/-- A completed edge is valid exactly when its checked Type witness is inhabited. -/
theorem packedEdge_completed_valid_iff
    {file : WorkspaceFile}
    {tokens : List Token}
    {waiting finished after : DottedItem tokens}
    {shared : Boundary tokens} :
    PackedEdgeKey.Valid file tokens
        (.completed waiting finished after shared) ↔
      Nonempty
        (CompletedEdgeWitness tokens waiting finished after shared) := by
  constructor
  · rintro ⟨symbol, next, complete, lhs, waitingAtShared,
      finishedAtShared, advance⟩
    have exactNext : NextSymbol waiting
        (GrammarSymbol.nonterminal finished.production.lhs) := by
      rw [lhs]
      exact next
    exact ⟨{
      next := exactNext
      complete := complete
      waitingAtShared := waitingAtShared
      finishedAtShared := finishedAtShared
      advance := advance
    }⟩
  · rintro ⟨witness⟩
    exact ⟨finished.production.lhs, witness.next, witness.complete, rfl,
      witness.waitingAtShared, witness.finishedAtShared, witness.advance⟩

/-- The proof-irrelevant subtype of structurally valid unguarded edges. -/
abbrev PackedEdge (file : WorkspaceFile) (tokens : List Token) : Type :=
  { key : PackedEdgeKey tokens // PackedEdgeKey.Valid file tokens key }

namespace ContextualPackedEdgeKey

/-- Erase contexts from a contextual edge while preserving its raw edge key. -/
def rawProjection {tokens : List Token} :
    ContextualPackedEdgeKey tokens → PackedEdgeKey tokens
  | .scanned before after cursor =>
      PackedEdgeKey.scanned before.raw after.raw cursor
  | .completed waiting finished after shared =>
      PackedEdgeKey.completed waiting.raw finished.raw after.raw shared

/-- Raw edge validity together with the exact contextual transition. -/
def StructurallyValid
    (file : WorkspaceFile)
    (tokens : List Token)
    (key : ContextualPackedEdgeKey tokens) : Prop :=
  PackedEdgeKey.Valid file tokens key.rawProjection ∧
    match key with
    | .scanned before after _ =>
        before.context = after.context
    | .completed waiting finished after _ =>
        finished.context =
            descendContext waiting finished.raw.production ∧
          after.context = waiting.context

end ContextualPackedEdgeKey

/-- Structural validity is exactly raw validity plus the contextual equations. -/
theorem contextualPackedEdge_structural_equations
    {file : WorkspaceFile} {tokens : List Token}
    {key : ContextualPackedEdgeKey tokens} :
    ContextualPackedEdgeKey.StructurallyValid file tokens key ↔
      PackedEdgeKey.Valid file tokens key.rawProjection ∧
        match key with
        | .scanned before after _ =>
            before.context = after.context
        | .completed waiting finished after _ =>
            finished.context =
                descendContext waiting finished.raw.production ∧
              after.context = waiting.context := by
  rfl

/-- The proof-irrelevant subtype of structurally valid contextual edges. -/
abbrev StructurallyValidContextualPackedEdge
    (file : WorkspaceFile) (tokens : List Token) : Type :=
  { key : ContextualPackedEdgeKey tokens //
    ContextualPackedEdgeKey.StructurallyValid file tokens key }

/-- The constructor-specific domain of structurally valid contextual scans. -/
structure StructurallyValidContextualScannedEdge
    (file : WorkspaceFile) (tokens : List Token) where
  before : ContextualItemKey tokens
  after : ContextualItemKey tokens
  cursor : TerminalCursor tokens
  structural : ContextualPackedEdgeKey.StructurallyValid file tokens
    (.scanned before after cursor)

/-- The constructor-specific domain of structurally valid completions. -/
structure StructurallyValidContextualCompletedEdge
    (file : WorkspaceFile) (tokens : List Token) where
  waiting : ContextualItemKey tokens
  finished : ContextualItemKey tokens
  after : ContextualItemKey tokens
  shared : Boundary tokens
  structural : ContextualPackedEdgeKey.StructurallyValid file tokens
    (.completed waiting finished after shared)

private theorem advanceItem_after_functional
    {tokens : List Token}
    {before afterLeft afterRight : DottedItem tokens}
    {next : Boundary tokens}
    (left : AdvanceItem before next afterLeft)
    (right : AdvanceItem before next afterRight) :
    afterLeft = afterRight := by
  cases afterLeft with
  | mk leftProduction leftDot leftOrigin leftCurrent =>
      cases afterRight with
      | mk rightProduction rightDot rightOrigin rightCurrent =>
          rcases left with ⟨leftProductionEq, leftDotEq,
            leftOriginEq, leftCurrentEq⟩
          rcases right with ⟨rightProductionEq, rightDotEq,
            rightOriginEq, rightCurrentEq⟩
          have productionEq : leftProduction = rightProduction :=
            leftProductionEq.trans rightProductionEq.symm
          subst rightProduction
          have dotEq : leftDot = rightDot := by
            apply Fin.ext
            exact leftDotEq.trans rightDotEq.symm
          subst rightDot
          have originEq : leftOrigin = rightOrigin :=
            leftOriginEq.trans rightOriginEq.symm
          have currentEq : leftCurrent = rightCurrent :=
            leftCurrentEq.trans rightCurrentEq.symm
          cases originEq
          cases currentEq
          rfl

private def dottedSchema {tokens : List Token}
    (item : DottedItem tokens) : DottedRhs := {
  production := item.production
  dot := item.dot
}

private theorem dottedItem_reconstructed
    {tokens : List Token} {left right : DottedItem tokens}
    (schemaEqual : dottedSchema left = dottedSchema right)
    (originEqual : left.origin = right.origin)
    (currentEqual : left.current = right.current) :
    left = right := by
  cases left with
  | mk leftProduction leftDot leftOrigin leftCurrent =>
      cases right with
      | mk rightProduction rightDot rightOrigin rightCurrent =>
          simp only [dottedSchema] at schemaEqual
          cases schemaEqual
          cases originEqual
          cases currentEqual
          rfl

private theorem contextualItem_reconstructed
    {tokens : List Token} {left right : ContextualItemKey tokens}
    (rawEqual : left.raw = right.raw)
    (contextEqual : left.context = right.context) :
    left = right := by
  cases left
  cases right
  cases rawEqual
  cases contextEqual
  rfl

private theorem contextualScannedEdge_before_injective
    {file : WorkspaceFile} {tokens : List Token} :
    Function.Injective
      (fun edge : StructurallyValidContextualScannedEdge file tokens =>
        edge.before) := by
  intro left right beforeEqual
  cases left with
  | mk leftBefore leftAfter leftCursor leftValid =>
      cases right with
      | mk rightBefore rightAfter rightCursor rightValid =>
          simp only at beforeEqual
          subst rightBefore
          rcases leftValid.1 with
            ⟨_, _, _, _, leftAtCurrent, _, _, leftAdvance⟩
          rcases rightValid.1 with
            ⟨_, _, _, _, rightAtCurrent, _, _, rightAdvance⟩
          have cursorEqual : leftCursor = rightCursor := by
            apply Fin.ext
            simpa [TerminalCursor.beforeBoundary] using
              congrArg Fin.val
                (leftAtCurrent.trans rightAtCurrent.symm)
          subst rightCursor
          have rawAfterEqual : leftAfter.raw = rightAfter.raw :=
            advanceItem_after_functional leftAdvance rightAdvance
          have contextAfterEqual :
              leftAfter.context = rightAfter.context :=
            leftValid.2.symm.trans rightValid.2
          have afterEqual : leftAfter = rightAfter :=
            contextualItem_reconstructed rawAfterEqual contextAfterEqual
          cases afterEqual
          rfl

private structure ContextualCompletedEdgeProjection
    (tokens : List Token) where
  waitingContext : GuardContext tokens
  waitingSchema : DottedRhs
  finishedSchema : DottedRhs
  waitingOrigin : Boundary tokens
  shared : Boundary tokens
  finishedCurrent : Boundary tokens

private def contextualCompletedEdgeProjection
    {file : WorkspaceFile} {tokens : List Token}
    (edge : StructurallyValidContextualCompletedEdge file tokens) :
    ContextualCompletedEdgeProjection tokens := {
  waitingContext := edge.waiting.context
  waitingSchema := dottedSchema edge.waiting.raw
  finishedSchema := dottedSchema edge.finished.raw
  waitingOrigin := edge.waiting.raw.origin
  shared := edge.shared
  finishedCurrent := edge.finished.raw.current
}

private theorem contextualCompletedEdgeProjection_injective
    {file : WorkspaceFile} {tokens : List Token} :
    Function.Injective
      (@contextualCompletedEdgeProjection file tokens) := by
  intro left right projectionEqual
  cases left with
  | mk leftWaiting leftFinished leftAfter leftShared leftValid =>
      cases right with
      | mk rightWaiting rightFinished rightAfter rightShared rightValid =>
          have waitingContextEqual :
              leftWaiting.context = rightWaiting.context :=
            congrArg ContextualCompletedEdgeProjection.waitingContext
              projectionEqual
          have waitingSchemaEqual :
              dottedSchema leftWaiting.raw =
                dottedSchema rightWaiting.raw :=
            congrArg ContextualCompletedEdgeProjection.waitingSchema
              projectionEqual
          have waitingOriginEqual :
              leftWaiting.raw.origin = rightWaiting.raw.origin :=
            congrArg ContextualCompletedEdgeProjection.waitingOrigin
              projectionEqual
          have sharedEqual : leftShared = rightShared :=
            congrArg ContextualCompletedEdgeProjection.shared
              projectionEqual
          have finishedSchemaEqual :
              dottedSchema leftFinished.raw =
                dottedSchema rightFinished.raw :=
            congrArg ContextualCompletedEdgeProjection.finishedSchema
              projectionEqual
          have finishedCurrentEqual :
              leftFinished.raw.current = rightFinished.raw.current :=
            congrArg ContextualCompletedEdgeProjection.finishedCurrent
              projectionEqual
          rcases leftValid.1 with
            ⟨_, _, _, _, leftWaitingAtShared,
              leftFinishedAtShared, leftAdvance⟩
          rcases rightValid.1 with
            ⟨_, _, _, _, rightWaitingAtShared,
              rightFinishedAtShared, rightAdvance⟩
          have waitingCurrentEqual :
              leftWaiting.raw.current = rightWaiting.raw.current :=
            leftWaitingAtShared.trans
              (sharedEqual.trans rightWaitingAtShared.symm)
          have finishedOriginEqual :
              leftFinished.raw.origin = rightFinished.raw.origin :=
            leftFinishedAtShared.trans
              (sharedEqual.trans rightFinishedAtShared.symm)
          have waitingRawEqual :
              leftWaiting.raw = rightWaiting.raw :=
            dottedItem_reconstructed waitingSchemaEqual
              waitingOriginEqual waitingCurrentEqual
          have waitingEqual : leftWaiting = rightWaiting :=
            contextualItem_reconstructed waitingRawEqual
              waitingContextEqual
          have finishedRawEqual :
              leftFinished.raw = rightFinished.raw :=
            dottedItem_reconstructed finishedSchemaEqual
              finishedOriginEqual finishedCurrentEqual
          have finishedContextEqual :
              leftFinished.context = rightFinished.context := by
            rw [leftValid.2.1, rightValid.2.1,
              waitingEqual, finishedRawEqual]
          have finishedEqual : leftFinished = rightFinished :=
            contextualItem_reconstructed finishedRawEqual
              finishedContextEqual
          cases waitingEqual
          cases finishedEqual
          cases sharedEqual
          have afterRawEqual : leftAfter.raw = rightAfter.raw :=
            advanceItem_after_functional leftAdvance rightAdvance
          have afterContextEqual :
              leftAfter.context = rightAfter.context :=
            leftValid.2.2.trans rightValid.2.2.symm
          have afterEqual : leftAfter = rightAfter :=
            contextualItem_reconstructed afterRawEqual afterContextEqual
          cases afterEqual
          rfl

private theorem block_encode_injective
    {width leftBlock rightBlock leftOffset rightOffset : Nat}
    (leftBound : leftOffset < width)
    (rightBound : rightOffset < width)
    (equal : leftBlock * width + leftOffset =
      rightBlock * width + rightOffset) :
    leftBlock = rightBlock ∧ leftOffset = rightOffset := by
  have positive : 0 < width := Nat.zero_lt_of_lt leftBound
  have quotient (block offset : Nat) (bound : offset < width) :
      (block * width + offset) / width = block := by
    rw [Nat.add_comm, Nat.mul_comm block width,
      Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt bound]
    exact Nat.zero_add block
  have blockEqual : leftBlock = rightBlock := by
    rw [← quotient leftBlock leftOffset leftBound, equal,
      quotient rightBlock rightOffset rightBound]
  exact ⟨blockEqual, by
    rw [blockEqual] at equal
    exact Nat.add_left_cancel equal⟩

private theorem product_cardinality
    {α β : Type} {leftSize rightSize : Nat}
    (rightPositive : 0 < rightSize)
    (leftCardinality :
      ∃ encode : α → Fin leftSize,
        Function.Injective encode ∧ Function.Surjective encode)
    (rightCardinality :
      ∃ encode : β → Fin rightSize,
        Function.Injective encode ∧ Function.Surjective encode) :
    ∃ encode : α × β → Fin (leftSize * rightSize),
      Function.Injective encode ∧ Function.Surjective encode := by
  obtain ⟨leftEncode, leftInjective, leftSurjective⟩ := leftCardinality
  obtain ⟨rightEncode, rightInjective, rightSurjective⟩ :=
    rightCardinality
  let encode (value : α × β) : Fin (leftSize * rightSize) :=
    ⟨(leftEncode value.1).val * rightSize +
        (rightEncode value.2).val, by
      have rowBound :
          (leftEncode value.1).val * rightSize +
              (rightEncode value.2).val <
            ((leftEncode value.1).val + 1) * rightSize := by
        rw [Nat.add_mul]
        simpa only [Nat.one_mul] using Nat.add_lt_add_left
          (rightEncode value.2).isLt
          ((leftEncode value.1).val * rightSize)
      exact Nat.lt_of_lt_of_le rowBound
        (Nat.mul_le_mul_right rightSize
          (Nat.succ_le_of_lt (leftEncode value.1).isLt))⟩
  refine ⟨encode, ?_, ?_⟩
  · intro left right equal
    have rawEqual := congrArg Fin.val equal
    have coordinates := block_encode_injective
      (rightEncode left.2).isLt (rightEncode right.2).isLt rawEqual
    exact Prod.ext (leftInjective (Fin.ext coordinates.1))
      (rightInjective (Fin.ext coordinates.2))
  · intro value
    let leftIndex : Fin leftSize :=
      ⟨value.val / rightSize,
        (Nat.div_lt_iff_lt_mul rightPositive).mpr value.isLt⟩
    let rightIndex : Fin rightSize :=
      ⟨value.val % rightSize, Nat.mod_lt _ rightPositive⟩
    obtain ⟨left, leftEqual⟩ := leftSurjective leftIndex
    obtain ⟨right, rightEqual⟩ := rightSurjective rightIndex
    refine ⟨(left, right), Fin.ext ?_⟩
    simp only [encode]
    rw [leftEqual, rightEqual]
    simpa [leftIndex, rightIndex, Nat.add_comm, Nat.mul_comm] using
      Nat.mod_add_div value.val rightSize

private theorem fin_cardinality (size : Nat) :
    ∃ encode : Fin size → Fin size,
      Function.Injective encode ∧ Function.Surjective encode :=
  ⟨id, Function.injective_id, Function.surjective_id⟩

private theorem dotted_count_positive : 0 < D := by
  let dotted : DottedRhs := {
    production := .root .module
    dot := ⟨0, Nat.zero_lt_succ _⟩
  }
  have member := allDottedRhs_complete dotted
  have positive : 0 < allDottedRhs.length :=
    List.length_pos_of_mem member
  simpa [allDottedRhs_length] using positive

private abbrev ContextualItemCoordinates (tokens : List Token) :=
  ((GuardContext tokens × DottedRhs) × Boundary tokens) × Boundary tokens

private def contextualItemCoordinates {tokens : List Token}
    (item : ContextualItemKey tokens) : ContextualItemCoordinates tokens :=
  (((item.context, {
    production := item.raw.production
    dot := item.raw.dot
  }), item.raw.origin), item.raw.current)

private def contextualItemOfCoordinates {tokens : List Token}
    (coordinates : ContextualItemCoordinates tokens) :
    ContextualItemKey tokens := {
  raw := {
    production := coordinates.1.1.2.production
    dot := coordinates.1.1.2.dot
    origin := coordinates.1.2
    current := coordinates.2
  }
  context := coordinates.1.1.1
}

private theorem contextualItemCoordinates_bijective
    {tokens : List Token} :
    Function.Injective (@contextualItemCoordinates tokens) ∧
      Function.Surjective (@contextualItemCoordinates tokens) := by
  have leftInverse : Function.LeftInverse
      (@contextualItemOfCoordinates tokens)
      (@contextualItemCoordinates tokens) := by
    intro item
    cases item with
    | mk raw context => cases raw; rfl
  have rightInverse : Function.RightInverse
      (@contextualItemOfCoordinates tokens)
      (@contextualItemCoordinates tokens) := by
    intro coordinates
    rcases coordinates with ⟨contextSchemaOrigin, current⟩
    rcases contextSchemaOrigin with ⟨contextSchema, origin⟩
    rcases contextSchema with ⟨context, schema⟩
    cases schema
    rfl
  exact ⟨leftInverse.injective, rightInverse.surjective⟩

private abbrev CompletedEdgeCoordinates (tokens : List Token) :=
  (((((GuardContext tokens × DottedRhs) × DottedRhs) ×
    Boundary tokens) × Boundary tokens) × Boundary tokens)

private def completedEdgeCoordinates {tokens : List Token}
    (projection : ContextualCompletedEdgeProjection tokens) :
    CompletedEdgeCoordinates tokens :=
  (((((projection.waitingContext, projection.waitingSchema),
    projection.finishedSchema), projection.waitingOrigin),
    projection.shared), projection.finishedCurrent)

private def completedEdgeProjectionOfCoordinates {tokens : List Token}
    (coordinates : CompletedEdgeCoordinates tokens) :
    ContextualCompletedEdgeProjection tokens := {
  waitingContext := coordinates.1.1.1.1.1
  waitingSchema := coordinates.1.1.1.1.2
  finishedSchema := coordinates.1.1.1.2
  waitingOrigin := coordinates.1.1.2
  shared := coordinates.1.2
  finishedCurrent := coordinates.2
}

private theorem completedEdgeCoordinates_bijective
    {tokens : List Token} :
    Function.Injective (@completedEdgeCoordinates tokens) ∧
      Function.Surjective (@completedEdgeCoordinates tokens) := by
  have leftInverse : Function.LeftInverse
      (@completedEdgeProjectionOfCoordinates tokens)
      (@completedEdgeCoordinates tokens) := by
    intro projection
    cases projection
    rfl
  have rightInverse : Function.RightInverse
      (@completedEdgeProjectionOfCoordinates tokens)
      (@completedEdgeCoordinates tokens) := by
    intro coordinates
    rcases coordinates with ⟨withShared, current⟩
    rcases withShared with ⟨withOrigin, shared⟩
    rcases withOrigin with ⟨withFinished, origin⟩
    rcases withFinished with ⟨contextWaiting, finished⟩
    rcases contextWaiting with ⟨context, waiting⟩
    rfl
  exact ⟨leftInverse.injective, rightInverse.surjective⟩

/-- Exact contextual item cardinality and constructor-specific valid edge
bounds, with the finished context reconstructed rather than counted twice. -/
theorem contextual_item_edge_cardinality
    (file : WorkspaceFile) (tokens : List Token) :
    (∃ encode : ContextualItemKey tokens →
        Fin ((1 + 3 * (tokens.length + 2)) * D *
          (tokens.length + 2) * (tokens.length + 2)),
      Function.Injective encode ∧ Function.Surjective encode) ∧
    (∃ encode : StructurallyValidContextualScannedEdge file tokens →
        Fin ((1 + 3 * (tokens.length + 2)) * D *
          (tokens.length + 2) * (tokens.length + 2)),
      Function.Injective encode) ∧
    (∃ encode : StructurallyValidContextualCompletedEdge file tokens →
        Fin ((1 + 3 * (tokens.length + 2)) * D * D *
          (tokens.length + 2) * (tokens.length + 2) *
          (tokens.length + 2)),
      Function.Injective encode) := by
  let q := tokens.length + 2
  have qPositive : 0 < q := by simp [q]
  obtain ⟨contextDottedEncode, contextDottedInjective,
      contextDottedSurjective⟩ := product_cardinality
    dotted_count_positive (guard_context_cardinality tokens)
      dottedRhs_cardinality
  obtain ⟨contextDottedOriginEncode, contextDottedOriginInjective,
      contextDottedOriginSurjective⟩ := product_cardinality qPositive
    ⟨contextDottedEncode, contextDottedInjective,
      contextDottedSurjective⟩ (fin_cardinality q)
  obtain ⟨itemCoordinateEncode, itemCoordinateInjective,
      itemCoordinateSurjective⟩ := product_cardinality qPositive
    ⟨contextDottedOriginEncode, contextDottedOriginInjective,
      contextDottedOriginSurjective⟩ (fin_cardinality q)
  let itemEncode (item : ContextualItemKey tokens) :=
    itemCoordinateEncode (contextualItemCoordinates item)
  have itemInjective : Function.Injective itemEncode :=
    itemCoordinateInjective.comp contextualItemCoordinates_bijective.1
  have itemSurjective : Function.Surjective itemEncode := by
    intro value
    obtain ⟨coordinates, equal⟩ := itemCoordinateSurjective value
    obtain ⟨item, itemEqual⟩ :=
      contextualItemCoordinates_bijective.2 coordinates
    refine ⟨item, ?_⟩
    change itemCoordinateEncode (contextualItemCoordinates item) = value
    rw [itemEqual, equal]
  refine ⟨⟨itemEncode, itemInjective, itemSurjective⟩, ?_, ?_⟩
  · exact ⟨fun edge => itemEncode edge.before,
      itemInjective.comp contextualScannedEdge_before_injective⟩
  · obtain ⟨withFinishedEncode, withFinishedInjective,
        withFinishedSurjective⟩ := product_cardinality
      dotted_count_positive
      ⟨contextDottedEncode, contextDottedInjective,
        contextDottedSurjective⟩ dottedRhs_cardinality
    obtain ⟨withOriginEncode, withOriginInjective, withOriginSurjective⟩ :=
      product_cardinality qPositive
        ⟨withFinishedEncode, withFinishedInjective,
          withFinishedSurjective⟩ (fin_cardinality q)
    obtain ⟨withSharedEncode, withSharedInjective, withSharedSurjective⟩ :=
      product_cardinality qPositive
        ⟨withOriginEncode, withOriginInjective, withOriginSurjective⟩
        (fin_cardinality q)
    obtain ⟨completedCoordinateEncode, completedCoordinateInjective, _⟩ :=
      product_cardinality qPositive
        ⟨withSharedEncode, withSharedInjective, withSharedSurjective⟩
        (fin_cardinality q)
    exact ⟨fun edge => completedCoordinateEncode
        (completedEdgeCoordinates (contextualCompletedEdgeProjection edge)),
      completedCoordinateInjective.comp
        (completedEdgeCoordinates_bijective.1.comp
          contextualCompletedEdgeProjection_injective)⟩

/-- The physical byte selected by one chart boundary. -/
def BoundaryByte
    (file : WorkspaceFile)
    (tokens : List Token)
    (boundary : Boundary tokens)
    (byte : Nat) : Prop :=
  TokensOwnedBy file tokens ∧
    if inRange : boundary.val < tokens.length then
      byte = tokens[boundary.val].span.startByte
    else
      byte = file.content.utf8ByteSize

namespace BoundaryByte

/-- One chart boundary selects only one physical source byte. -/
theorem functional
    {file : WorkspaceFile}
    {tokens : List Token}
    {boundary : Boundary tokens}
    {left right : Nat}
    (leftAt : BoundaryByte file tokens boundary left)
    (rightAt : BoundaryByte file tokens boundary right) :
    left = right := by
  by_cases inRange : boundary.val < tokens.length
  · simp [BoundaryByte, inRange] at leftAt rightAt
    exact leftAt.2.trans rightAt.2.symm
  · simp [BoundaryByte, inRange] at leftAt rightAt
    exact leftAt.2.trans rightAt.2.symm

end BoundaryByte

/-- The exact source span covered by an ordered half-open chart interval. -/
def ConsumedSpan
    (file : WorkspaceFile)
    (tokens : List Token)
    (origin finish : Boundary tokens)
    (span : SourceSpan) : Prop :=
  TokensOwnedBy file tokens ∧
    origin.val ≤ finish.val ∧
    if occupied : origin.val < Nat.min finish.val tokens.length then
      have firstInRange : origin.val < tokens.length :=
        Nat.lt_of_lt_of_le occupied (Nat.min_le_right _ _)
      have lastInRange : Nat.min finish.val tokens.length - 1 < tokens.length := by
        have positive : 0 < Nat.min finish.val tokens.length :=
          Nat.zero_lt_of_lt occupied
        exact Nat.lt_of_lt_of_le
          (Nat.sub_lt positive Nat.zero_lt_one)
          (Nat.min_le_right _ _)
      span = {
        source := file.id
        startByte := (tokens[origin.val]'firstInRange).span.startByte
        endByte :=
          (tokens[Nat.min finish.val tokens.length - 1]'lastInRange).span.endByte
      }
    else
      ∃ byte,
        BoundaryByte file tokens origin byte ∧
          span = {
            source := file.id
            startByte := byte
            endByte := byte
          }

namespace ConsumedSpan

/-- One ordered chart interval has only one exact consumed source span. -/
theorem functional
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {left right : SourceSpan}
    (leftConsumed : ConsumedSpan file tokens origin finish left)
    (rightConsumed : ConsumedSpan file tokens origin finish right) :
    left = right := by
  by_cases occupied : origin.val < Nat.min finish.val tokens.length
  · simp [ConsumedSpan, occupied] at leftConsumed rightConsumed
    exact leftConsumed.2.2.trans rightConsumed.2.2.symm
  · simp [ConsumedSpan, occupied] at leftConsumed rightConsumed
    rcases leftConsumed.2.2 with ⟨leftByte, leftAt, leftSpan⟩
    rcases rightConsumed.2.2 with ⟨rightByte, rightAt, rightSpan⟩
    have byteEq : leftByte = rightByte :=
      BoundaryByte.functional leftAt rightAt
    subst rightByte
    exact leftSpan.trans rightSpan.symm

end ConsumedSpan

/-- Expose the two exact span branches: a nonempty retained-token interval
uses its first/last token endpoints, while an empty retained interval uses
the origin boundary byte and therefore excludes surrounding trivia. -/
theorem consumedSpan_boundary_trivia_exact
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens) (span : SourceSpan) :
    ConsumedSpan file tokens origin finish span ↔
      TokensOwnedBy file tokens ∧
        origin.val ≤ finish.val ∧
        ((∃ occupied : origin.val < Nat.min finish.val tokens.length,
            have firstInRange : origin.val < tokens.length :=
              Nat.lt_of_lt_of_le occupied (Nat.min_le_right _ _)
            have lastInRange :
                Nat.min finish.val tokens.length - 1 < tokens.length := by
              have positive : 0 < Nat.min finish.val tokens.length :=
                Nat.zero_lt_of_lt occupied
              exact Nat.lt_of_lt_of_le
                (Nat.sub_lt positive Nat.zero_lt_one)
                (Nat.min_le_right _ _)
            span = {
              source := file.id
              startByte := (tokens[origin.val]'firstInRange).span.startByte
              endByte :=
                (tokens[Nat.min finish.val tokens.length - 1]'lastInRange).span.endByte
            }) ∨
          (¬ origin.val < Nat.min finish.val tokens.length ∧
            let byte :=
              if inRange : origin.val < tokens.length then
                tokens[origin.val].span.startByte
              else
                file.content.utf8ByteSize
            span = {
              source := file.id
              startByte := byte
              endByte := byte
            })) := by
  by_cases occupied : origin.val < Nat.min finish.val tokens.length
  · constructor
    · intro consumed
      simp only [ConsumedSpan, occupied, ↓reduceDIte] at consumed
      exact ⟨consumed.1, consumed.2.1,
        Or.inl ⟨occupied, consumed.2.2⟩⟩
    · rintro ⟨owned, ordered, branch⟩
      rcases branch with branch | branch
      · rcases branch with ⟨_occupied, spanEq⟩
        simp only [ConsumedSpan, occupied, ↓reduceDIte]
        exact ⟨owned, ordered, spanEq⟩
      · exact (branch.1 occupied).elim
  · constructor
    · intro consumed
      simp only [ConsumedSpan, occupied, ↓reduceDIte] at consumed
      rcases consumed with ⟨owned, ordered, byte, atBoundary, spanEq⟩
      let exactByte : Nat :=
        if inRange : origin.val < tokens.length then
          tokens[origin.val].span.startByte
        else
          file.content.utf8ByteSize
      have exactAt : BoundaryByte file tokens origin exactByte := by
        unfold BoundaryByte exactByte
        refine ⟨owned, ?_⟩
        split <;> rfl
      have byteEq : byte = exactByte :=
        BoundaryByte.functional atBoundary exactAt
      subst byte
      exact ⟨owned, ordered, Or.inr ⟨occupied, by
        simpa [exactByte] using spanEq⟩⟩
    · rintro ⟨owned, ordered, branch⟩
      rcases branch with branch | branch
      · exact (occupied branch.1).elim
      · let exactByte : Nat :=
          if inRange : origin.val < tokens.length then
            tokens[origin.val].span.startByte
          else
            file.content.utf8ByteSize
        have exactAt : BoundaryByte file tokens origin exactByte := by
          unfold BoundaryByte exactByte
          refine ⟨owned, ?_⟩
          split <;> rfl
        simp only [ConsumedSpan, occupied, ↓reduceDIte]
        exact ⟨owned, ordered, exactByte, exactAt, by
          simpa [exactByte] using branch.2⟩

/-- A checked source span for one completed chart interval. -/
structure ConsumedSpanWitness
    (file : WorkspaceFile)
    (tokens : List Token)
    (origin finish : Boundary tokens) where
  span : SourceSpan
  consumed : ConsumedSpan file tokens origin finish span
  deriving Repr, DecidableEq

instance {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens} :
    BEq (ConsumedSpanWitness file tokens origin finish) :=
  ⟨fun left right => decide (left = right)⟩

/-- Locate a payload with an already checked consumed-span witness. -/
def sourceLoc
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {α : Type}
    (witness : ConsumedSpanWitness file tokens origin finish)
    (payload : α) : Located α :=
  { span := witness.span, payload := payload }

/-- A located payload uses the checked span of this completed interval. -/
def SourceLocates
    {α : Type}
    (file : WorkspaceFile)
    (tokens : List Token)
    (origin finish : Boundary tokens)
    (payload : α)
    (located : Located α) : Prop :=
  ∃ witness : ConsumedSpanWitness file tokens origin finish,
    located = sourceLoc witness payload

/-- Every checked consumed-span witness directly locates any payload. -/
theorem consumedSpanWitness_sourceLocates
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens} {alpha : Type}
    (witness : ConsumedSpanWitness file tokens origin finish)
    (payload : alpha) :
    SourceLocates file tokens origin finish payload
      (sourceLoc witness payload) := by
  exact ⟨witness, rfl⟩

namespace SourceLocates

/-- A payload and completed interval determine only one located value. -/
theorem functional
    {α : Type}
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {payload : α}
    {left right : Located α}
    (leftLocates : SourceLocates file tokens origin finish payload left)
    (rightLocates : SourceLocates file tokens origin finish payload right) :
    left = right := by
  rcases leftLocates with ⟨leftWitness, leftEq⟩
  rcases rightLocates with ⟨rightWitness, rightEq⟩
  have spanEq : leftWitness.span = rightWitness.span :=
    ConsumedSpan.functional leftWitness.consumed rightWitness.consumed
  calc
    left = sourceLoc leftWitness payload := leftEq
    _ = sourceLoc rightWitness payload := by
      simpa [sourceLoc] using
        congrArg
          (fun span => ({ span := span, payload := payload } : Located α))
          spanEq
    _ = right := rightEq.symm

end SourceLocates

/-- Source location with a fixed interval is injective in its payload. -/
theorem sourceLoc_eq_iff
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens} {alpha : Type}
    (leftWitness rightWitness : ConsumedSpanWitness
      file tokens origin finish)
    (left right : alpha) :
    sourceLoc leftWitness left = sourceLoc rightWitness right ↔ left = right := by
  constructor
  · intro locatedEq
    exact congrArg Located.payload locatedEq
  · intro payloadEq
    subst right
    exact SourceLocates.functional
      (consumedSpanWitness_sourceLocates leftWitness left)
      (consumedSpanWitness_sourceLocates rightWitness left)

namespace ConsumedSpanWitness

/-- Construct the exact consumed span for every owned, ordered chart interval. -/
def compute
    (file : WorkspaceFile)
    (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val) :
    ConsumedSpanWitness file tokens origin finish :=
  if occupied : origin.val < Nat.min finish.val tokens.length then
    have firstInRange : origin.val < tokens.length :=
      (Nat.lt_min.mp occupied).2
    have capPositive : 0 < Nat.min finish.val tokens.length :=
      Nat.lt_of_le_of_lt (Nat.zero_le origin.val) occupied
    have lastInRange : Nat.min finish.val tokens.length - 1 < tokens.length :=
      Nat.lt_of_lt_of_le
        (Nat.sub_lt capPositive Nat.zero_lt_one)
        (Nat.min_le_right _ _)
    let span : SourceSpan := {
      source := file.id
      startByte := (tokens[origin.val]'firstInRange).span.startByte
      endByte :=
        (tokens[Nat.min finish.val tokens.length - 1]'lastInRange).span.endByte
    }
    {
      span := span
      consumed := by
        simp [ConsumedSpan, occupied, span, owned, ordered]
    }
  else
    let byte : Nat :=
      if inRange : origin.val < tokens.length then
        tokens[origin.val].span.startByte
      else
        file.content.utf8ByteSize
    have atBoundary : BoundaryByte file tokens origin byte := by
      unfold BoundaryByte byte
      refine ⟨owned, ?_⟩
      split <;> rfl
    let span : SourceSpan := {
      source := file.id
      startByte := byte
      endByte := byte
    }
    {
      span := span
      consumed := by
        refine ⟨owned, ordered, ?_⟩
        simp only [occupied, ↓reduceDIte]
        exact ⟨byte, atBoundary, rfl⟩
    }

end ConsumedSpanWitness

namespace Expected

/-- The stable finite-table index within a payload-bearing constructor. -/
private def payloadIndex : Expected → Nat
  | .hardKeyword keyword => keyword.ctorIdx
  | .contextualKeyword keyword => keyword.ctorIdx
  | .pragmaName kind => kind.ctorIdx
  | .symbol value => value.ctorIdx
  | .identifier
  | .pathComponent
  | .literal
  | .assemblyBlock
  | .endOfFile => 0

/-- Compare expectations by constructor order and then displayed finite index. -/
protected def compare (left right : Expected) : Ordering :=
  match compare left.ctorIdx right.ctorIdx with
  | .eq => compare left.payloadIndex right.payloadIndex
  | order => order

instance : Ord Expected := ⟨Expected.compare⟩

end Expected

private def allExpectedHardKeywords : List HardKeyword := [
  .contractKw, .importKw, .exportKw, .hidingKw, .asKw, .letKw,
  .dataKw, .forallKw, .classKw, .instanceKw, .ifKw, .elseKw,
  .forKw, .switchKw, .caseKw, .defaultKw, .leaveKw, .continueKw,
  .breakKw, .assemblyKw, .matchKw, .functionKw, .fallbackKw,
  .payableKw, .publicKw, .constructorKw, .returnKw, .lamKw,
  .typeKw, .pragmaKw
]

private def allExpectedContextualKeywords : List ContextualKeyword := [
  .thenKw, .comptimeKw
]

private def allExpectedPragmaKinds : List PragmaKind := [
  .noCoverageCondition, .noPattersonCondition,
  .noBoundedVariableCondition, .noGenericInstanceFor
]

private def allExpectedSymbols : List Symbol := [
  .colonEqual, .arrow, .fatArrow, .equalEqual, .notEqual,
  .greaterEqual, .lessEqual, .logicalAnd, .logicalOr, .plusEqual,
  .minusEqual, .caretEqual, .ampEqual, .pipeEqual, .percentEqual,
  .plus, .minus, .star, .slash, .percent, .bang, .less, .greater,
  .equal, .pipe, .amp, .caret, .at, .question, .dot, .colon,
  .semicolon, .comma, .leftParen, .rightParen, .leftBrace,
  .rightBrace, .leftBracket, .rightBracket, .underscore
]

/-- The stable complete enumeration of diagnostic expectation classes. -/
def allExpected : List Expected :=
  allExpectedHardKeywords.map .hardKeyword ++
  allExpectedContextualKeywords.map .contextualKeyword ++
  allExpectedPragmaKinds.map .pragmaName ++
  allExpectedSymbols.map .symbol ++
  [.identifier, .pathComponent, .literal, .assemblyBlock, .endOfFile]

/-- Every diagnostic expectation occurs in the stable enumeration. -/
theorem allExpected_complete (expected : Expected) :
    expected ∈ allExpected := by
  cases expected with
  | hardKeyword keyword => cases keyword <;>
      simp [allExpected, allExpectedHardKeywords]
  | contextualKeyword keyword => cases keyword <;>
      simp [allExpected, allExpectedContextualKeywords]
  | pragmaName kind => cases kind <;>
      simp [allExpected, allExpectedPragmaKinds]
  | symbol symbol => cases symbol <;>
      simp [allExpected, allExpectedSymbols]
  | identifier => simp [allExpected]
  | pathComponent => simp [allExpected]
  | literal => simp [allExpected]
  | assemblyBlock => simp [allExpected]
  | endOfFile => simp [allExpected]

/-- The stable expectation enumeration contains no duplicates. -/
theorem allExpected_nodup : allExpected.Nodup := by
  simp [allExpected, allExpectedHardKeywords,
    allExpectedContextualKeywords, allExpectedPragmaKinds,
    allExpectedSymbols]

/-- The expectation enumeration follows the canonical diagnostic order. -/
theorem allExpected_sorted :
    allExpected.Pairwise
      (fun left right => Expected.compare left right = .lt) := by
  decide

/-- There are exactly eighty-one closed diagnostic expectation classes. -/
theorem allExpected_length : allExpected.length = 81 := by
  rfl

/-- Membership in the enumeration is exactly inhabitation by an expectation. -/
theorem allExpected_exact (expected : Expected) :
    expected ∈ allExpected ↔ True := by
  exact iff_true_intro (allExpected_complete expected)

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- The ten generated production families whose semantic action is a direct,
proof-free packer.  Source-rule roots are deliberately excluded: their
reductions also construct source spans and remain the separate execution
boundary. -/
def AuxiliaryProduction : ProductionId → Prop
  | .root _ => False
  | .atom _ => True
  | .seq _ => True
  | .group _ => True
  | .choice _ _ => True
  | .opt _ _ => True
  | .star _ _ => True
  | .plus _ _ => True
  | .list0 _ _ => True
  | .list1 _ => True
  | .tail _ _ => True

/-- Execute any auxiliary generated action by its checked grammar-site
packer.  The result is computational; the proof argument only excludes the
source-rule root branch. -/
def executeAuxiliaryAction
    {file : WorkspaceFile} {tokens : List Token}
    (production : ProductionId)
    (auxiliary : AuxiliaryProduction production)
    (input : GrammarSymbolValues file tokens production.rhs) :
    NonterminalValue file tokens production.lhs :=
  match production with
  | .root _ => False.elim auxiliary
  | .atom site => AtomSite.pack site input
  | .seq site => SequenceSite.pack site input
  | .group site => GroupSite.pack site input
  | .choice site branch => ChoiceSite.pack site branch input
  | .opt site branch => OptionalSite.pack site branch input
  | .star site branch => StarSite.pack site branch input
  | .plus site branch => PlusSite.pack site branch input
  | .list0 site branch => List0Site.pack site branch input
  | .list1 site => List1Site.pack site input
  | .tail site branch => ListSite.pack site branch input

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

namespace EbnfValue

/-- View a terminal atom as its exact checked terminal match. -/
def terminalView
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol)
    (input : EbnfValue file tokens (.atom (.terminal terminal))) :
    MatchedTerminal file tokens terminal :=
  Eq.mp (ebnfValue_atom_terminal_eq terminal) input

/-- Rebuilding a viewed terminal atom recovers the original value. -/
theorem terminal_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol)
    (input : EbnfValue file tokens (.atom (.terminal terminal))) :
    terminalAtom terminal (terminalView terminal input) = input := by
  simp [terminalView, terminalAtom]

/-- View a source-rule atom as its exact rule-indexed value. -/
def ruleView
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (input : EbnfValue file tokens (.atom (.nonterminal rule))) :
    RuleValue rule :=
  Eq.mp (ebnfValue_atom_nonterminal_eq rule) input

/-- Rebuilding a viewed source-rule atom recovers the original value. -/
theorem rule_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (input : EbnfValue file tokens (.atom (.nonterminal rule))) :
    ruleAtom rule (ruleView rule input) = input := by
  simp [ruleView, ruleAtom]

/-- View a sequence as its exact heterogeneous child tuple. -/
def sequenceView
    {file : WorkspaceFile} {tokens : List Token}
    (children : List EbnfExpr)
    (input : EbnfValue file tokens (.sequence children)) :
    EbnfValues file tokens children :=
  Eq.mp (ebnfValue_sequence_eq children) input

/-- Rebuilding a viewed sequence recovers the original value. -/
theorem sequence_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (children : List EbnfExpr)
    (input : EbnfValue file tokens (.sequence children)) :
    sequence children (sequenceView children input) = input := by
  simp [sequenceView, sequence]

/-- View a group as its exact child value. -/
def groupView
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (input : EbnfValue file tokens (.group child)) :
    EbnfValue file tokens child :=
  Eq.mp (ebnfValue_group_eq child) input

/-- Rebuilding a viewed group recovers the original value. -/
theorem group_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (input : EbnfValue file tokens (.group child)) :
    group child (groupView child input) = input := by
  simp [groupView, group]

/-- View a choice as its exact dependent branch and child value. -/
def choiceView
    {file : WorkspaceFile} {tokens : List Token}
    (branches : List EbnfExpr)
    (input : EbnfValue file tokens (.choice branches)) :
    (branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch) :=
  Eq.mp (ebnfValue_choice_eq branches) input

/-- Rebuilding a viewed choice recovers the original value. -/
theorem choice_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (branches : List EbnfExpr)
    (input : EbnfValue file tokens (.choice branches)) :
    choice branches (choiceView branches input) = input := by
  simp [choiceView, choice]

/-- View a binary choice without exposing its dependent finite index. -/
def choice2View
    {file : WorkspaceFile} {tokens : List Token}
    (first second : EbnfExpr)
    (input : EbnfValue file tokens (.choice [first, second])) :
    Sum (EbnfValue file tokens first) (EbnfValue file tokens second) :=
  match choiceView [first, second] input with
  | ⟨⟨0, _⟩, raw⟩ => .inl raw
  | ⟨⟨1, _⟩, raw⟩ => .inr raw

/-- Rebuilding a viewed binary choice recovers the original value. -/
theorem choice2_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (first second : EbnfExpr)
    (input : EbnfValue file tokens (.choice [first, second])) :
    (match choice2View first second input with
      | .inl raw => choice [first, second] ⟨0, raw⟩
      | .inr raw => choice [first, second] ⟨1, raw⟩) = input := by
  unfold choice2View
  generalize selectedEq : choiceView [first, second] input = selected
  rcases selected with ⟨⟨branch, bound⟩, raw⟩
  have values : branch = 0 ∨ branch = 1 := by
    have : branch < 2 := by simpa using bound
    omega
  rcases values with rfl | rfl
  · have rebuild := choice_of_view [first, second] input
    rw [selectedEq] at rebuild
    exact rebuild
  · have rebuild := choice_of_view [first, second] input
    rw [selectedEq] at rebuild
    exact rebuild

/-- View a ternary choice without exposing its dependent finite index. -/
def choice3View
    {file : WorkspaceFile} {tokens : List Token}
    (first second third : EbnfExpr)
    (input : EbnfValue file tokens (.choice [first, second, third])) :
    Sum (EbnfValue file tokens first)
      (Sum (EbnfValue file tokens second) (EbnfValue file tokens third)) :=
  match choiceView [first, second, third] input with
  | ⟨⟨0, _⟩, raw⟩ => .inl raw
  | ⟨⟨1, _⟩, raw⟩ => .inr (.inl raw)
  | ⟨⟨2, _⟩, raw⟩ => .inr (.inr raw)

/-- Rebuilding a viewed ternary choice recovers the original value. -/
theorem choice3_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (first second third : EbnfExpr)
    (input : EbnfValue file tokens (.choice [first, second, third])) :
    (match choice3View first second third input with
      | .inl raw => choice [first, second, third] ⟨0, raw⟩
      | .inr (.inl raw) => choice [first, second, third] ⟨1, raw⟩
      | .inr (.inr raw) => choice [first, second, third] ⟨2, raw⟩) = input := by
  unfold choice3View
  generalize selectedEq : choiceView [first, second, third] input = selected
  rcases selected with ⟨⟨branch, bound⟩, raw⟩
  have values : branch = 0 ∨ branch = 1 ∨ branch = 2 := by
    have : branch < 3 := by simpa using bound
    omega
  rcases values with rfl | rfl | rfl
  all_goals
    have rebuild := choice_of_view [first, second, third] input
    rw [selectedEq] at rebuild
    exact rebuild

/-- View a four-way choice without exposing its dependent finite index. -/
def choice4View
    {file : WorkspaceFile} {tokens : List Token}
    (first second third fourth : EbnfExpr)
    (input : EbnfValue file tokens
      (.choice [first, second, third, fourth])) :
    Sum (EbnfValue file tokens first)
      (Sum (EbnfValue file tokens second)
        (Sum (EbnfValue file tokens third)
          (EbnfValue file tokens fourth))) :=
  match choiceView [first, second, third, fourth] input with
  | ⟨⟨0, _⟩, raw⟩ => .inl raw
  | ⟨⟨1, _⟩, raw⟩ => .inr (.inl raw)
  | ⟨⟨2, _⟩, raw⟩ => .inr (.inr (.inl raw))
  | ⟨⟨3, _⟩, raw⟩ => .inr (.inr (.inr raw))

/-- Rebuilding a viewed four-way choice recovers its original value. -/
theorem choice4_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (first second third fourth : EbnfExpr)
    (input : EbnfValue file tokens
      (.choice [first, second, third, fourth])) :
    (match choice4View first second third fourth input with
      | .inl raw => choice [first, second, third, fourth] ⟨0, raw⟩
      | .inr (.inl raw) =>
          choice [first, second, third, fourth] ⟨1, raw⟩
      | .inr (.inr (.inl raw)) =>
          choice [first, second, third, fourth] ⟨2, raw⟩
      | .inr (.inr (.inr raw)) =>
          choice [first, second, third, fourth] ⟨3, raw⟩) = input := by
  unfold choice4View
  generalize selectedEq :
    choiceView [first, second, third, fourth] input = selected
  rcases selected with ⟨⟨branch, bound⟩, raw⟩
  have values : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨
      branch = 3 := by
    have : branch < 4 := by simpa using bound
    omega
  rcases values with rfl | rfl | rfl | rfl
  all_goals
    have rebuild := choice_of_view
      [first, second, third, fourth] input
    rw [selectedEq] at rebuild
    exact rebuild
/-- View an optional expression as its exact optional child. -/
def optionalView
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (input : EbnfValue file tokens (.optional child)) :
    Option (EbnfValue file tokens child) :=
  Eq.mp (ebnfValue_optional_eq child) input

/-- Rebuilding a viewed optional expression recovers the original value. -/
theorem optional_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (input : EbnfValue file tokens (.optional child)) :
    optional child (optionalView child input) = input := by
  simp [optionalView, optional]

/-- View a star expression as its exact ordered child list. -/
def starView
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (input : EbnfValue file tokens (.star child)) :
    List (EbnfValue file tokens child) :=
  Eq.mp (ebnfValue_star_eq child) input

/-- Rebuilding a viewed star expression recovers the original value. -/
theorem star_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (input : EbnfValue file tokens (.star child)) :
    star child (starView child input) = input := by
  simp [starView, star]

/-- View a plus expression as its exact nonempty child list. -/
def plusView
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (input : EbnfValue file tokens (.plus child)) :
    NonemptyList (EbnfValue file tokens child) :=
  Eq.mp (ebnfValue_plus_eq child) input

/-- Rebuilding a viewed plus expression recovers the original value. -/
theorem plus_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (input : EbnfValue file tokens (.plus child)) :
    plus child (plusView child input) = input := by
  simp [plusView, plus]

/-- View a list-zero expression as its exact ordered child list. -/
def list0View
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (input : EbnfValue file tokens (.list0 child)) :
    List (EbnfValue file tokens child) :=
  Eq.mp (ebnfValue_list0_eq child) input

/-- Rebuilding a viewed list-zero expression recovers the original value. -/
theorem list0_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (input : EbnfValue file tokens (.list0 child)) :
    list0 child (list0View child input) = input := by
  simp [list0View, list0]

/-- View a list-one expression as its exact nonempty child list. -/
def list1View
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (input : EbnfValue file tokens (.list1 child)) :
    NonemptyList (EbnfValue file tokens child) :=
  Eq.mp (ebnfValue_list1_eq child) input

/-- Rebuilding a viewed list-one expression recovers the original value. -/
theorem list1_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (input : EbnfValue file tokens (.list1 child)) :
    list1 child (list1View child input) = input := by
  simp [list1View, list1]

end EbnfValue

namespace EbnfValues

private theorem eqMp_rebuild
    {alpha beta : Sort _} (typeEq : alpha = beta) (input : alpha) :
    Eq.mp typeEq.symm (Eq.mp typeEq input) = input := by
  cases typeEq
  rfl

/-- View a nonempty heterogeneous sequence as its exact head and tail. -/
def consView
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) (rest : List EbnfExpr)
    (input : EbnfValues file tokens (child :: rest)) :
    EbnfValue file tokens child × EbnfValues file tokens rest :=
  Eq.mp (ebnfValues_cons_eq child rest) input

/-- Rebuilding a viewed heterogeneous sequence recovers the original value. -/
theorem cons_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr) (rest : List EbnfExpr)
    (input : EbnfValues file tokens (child :: rest)) :
    cons child rest (consView child rest input).1
        (consView child rest input).2 = input := by
  exact eqMp_rebuild (ebnfValues_cons_eq child rest) input

/-- The empty heterogeneous sequence has exactly its canonical value. -/
theorem nil_unique
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValues file tokens []) :
    nil = input := by
  unfold nil
  have viewed :
      Eq.mp (ebnfValues_nil_eq (file := file) (tokens := tokens)) input = () :=
    Subsingleton.elim _ _
  rw [← viewed]
  simp

end EbnfValues

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- Execute a generated auxiliary action when the production is not a
source-rule root.  Returning `none` isolates root reduction as the remaining
source-span-aware execution boundary. -/
def executeAuxiliaryAction?
    {file : WorkspaceFile} {tokens : List Token}
    (production : ProductionId)
    (input : GrammarSymbolValues file tokens production.rhs) :
    Option (NonterminalValue file tokens production.lhs) :=
  match production with
  | .root _ => none
  | .atom site => some (AtomSite.pack site input)
  | .seq site => some (SequenceSite.pack site input)
  | .group site => some (GroupSite.pack site input)
  | .choice site branch => some (ChoiceSite.pack site branch input)
  | .opt site branch => some (OptionalSite.pack site branch input)
  | .star site branch => some (StarSite.pack site branch input)
  | .plus site branch => some (PlusSite.pack site branch input)
  | .list0 site branch => some (List0Site.pack site branch input)
  | .list1 site => some (List1Site.pack site input)
  | .tail site branch => some (ListSite.pack site branch input)

/-- The optional executor returns the same typed value as the proof-indexed
auxiliary executor whenever the production is auxiliary. -/
theorem executeAuxiliaryAction?_eq_some
    {file : WorkspaceFile} {tokens : List Token}
    (production : ProductionId)
    (auxiliary : AuxiliaryProduction production)
    (input : GrammarSymbolValues file tokens production.rhs) :
    executeAuxiliaryAction? production input =
      some (executeAuxiliaryAction production auxiliary input) := by
  cases production <;> first | contradiction | rfl

end Solcore.Surface.Multi

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- The first source-rule roots whose semantic reductions are directly
executable from their typed EBNF values. -/
inductive ExecutableRootRule : GrammarRuleId → Type where
  | module : ExecutableRootRule .module
  | topItem : ExecutableRootRule .topItem
  | moduleRef : ExecutableRootRule .moduleRef
  | importDecl : ExecutableRootRule .importDecl
  | exportDecl : ExecutableRootRule .exportDecl
  | importEntry : ExecutableRootRule .importEntry
  | localExportEntry : ExecutableRootRule .localExportEntry
  | remoteExportEntry : ExecutableRootRule .remoteExportEntry
  | optionalComma : ExecutableRootRule .optionalComma
  | predicateList : ExecutableRootRule .predicateList
  | predicate : ExecutableRootRule .predicate
  | functionSignature : ExecutableRootRule .functionSignature
  | instanceMethod : ExecutableRootRule .instanceMethod
  | armStatement : ExecutableRootRule .armStatement
  | matchArm : ExecutableRootRule .matchArm
  | statement : ExecutableRootRule .statement
  | terminalExpression : ExecutableRootRule .terminalExpression
  | pattern : ExecutableRootRule .pattern
  | expression : ExecutableRootRule .expression
  | annotation : ExecutableRootRule .annotation
  | conditional : ExecutableRootRule .conditional
  | blockStatement : ExecutableRootRule .blockStatement
  | functionDecl : ExecutableRootRule .functionDecl
  | classMethod : ExecutableRootRule .classMethod
  | letStatement : ExecutableRootRule .letStatement
  | letBinding : ExecutableRootRule .letBinding
  | breakStatement : ExecutableRootRule .breakStatement
  | continueStatement : ExecutableRootRule .continueStatement
  | assemblyStatement : ExecutableRootRule .assemblyStatement
  | ifStatement : ExecutableRootRule .ifStatement
  | matchStatement : ExecutableRootRule .matchStatement
  | returnStatement : ExecutableRootRule .returnStatement
  | assignmentStatement : ExecutableRootRule .assignmentStatement
  | parameter : ExecutableRootRule .parameter
  | dataDecl : ExecutableRootRule .dataDecl
  | contractDecl : ExecutableRootRule .contractDecl
  | dataConstructor : ExecutableRootRule .dataConstructor
  | typeAliasDecl : ExecutableRootRule .typeAliasDecl
  | classDecl : ExecutableRootRule .classDecl
  | instanceDecl : ExecutableRootRule .instanceDecl
  | fieldDecl : ExecutableRootRule .fieldDecl
  | fallbackDecl : ExecutableRootRule .fallbackDecl
  | contractConstructorDecl : ExecutableRootRule .contractConstructorDecl
  | pragmaDecl : ExecutableRootRule .pragmaDecl
  | genericPrefix : ExecutableRootRule .genericPrefix
  | forallClause : ExecutableRootRule .forallClause
  | forallBinder : ExecutableRootRule .forallBinder
  | exportItem : ExecutableRootRule .exportItem
  | constructorSelection : ExecutableRootRule .constructorSelection
  | hidingClause : ExecutableRootRule .hidingClause
  | body : ExecutableRootRule .body
  | type : ExecutableRootRule .type
  | typeAtom : ExecutableRootRule .typeAtom
  | qualifiedName : ExecutableRootRule .qualifiedName
  | forStatement : ExecutableRootRule .forStatement
  | forInitItem : ExecutableRootRule .forInitItem
  | forPostItem : ExecutableRootRule .forPostItem
  | expressionStatement : ExecutableRootRule .expressionStatement
  | contractMember : ExecutableRootRule .contractMember
  | assignmentOperator : ExecutableRootRule .assignmentOperator
  | logicalOr : ExecutableRootRule .logicalOr
  | logicalAnd : ExecutableRootRule .logicalAnd
  | equality : ExecutableRootRule .equality
  | relational : ExecutableRootRule .relational
  | bitOr : ExecutableRootRule .bitOr
  | bitXor : ExecutableRootRule .bitXor
  | bitAnd : ExecutableRootRule .bitAnd
  | additive : ExecutableRootRule .additive
  | multiplicative : ExecutableRootRule .multiplicative
  | prefix : ExecutableRootRule .prefix
  | postfixExpr : ExecutableRootRule .postfix
  | postfixPart : ExecutableRootRule .postfixPart
  | atomExpr : ExecutableRootRule .atom
  | literalValue : ExecutableRootRule .literal
  | lambdaExpr : ExecutableRootRule .lambda

/-- Build the complete source-located module value from its ordered items. -/
def executableModuleValue
    (file : WorkspaceFile) (items : List TopItem) : ParsedModuleV1 := {
  span := {
    source := file.id
    startByte := 0
    endByte := file.content.utf8ByteSize
  }
  payload := {
    source := file.id
    items := items
  }
}

/-- Execute the optional-comma source rule. -/
def executeOptionalCommaRoot
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .optionalComma)) :
    OptionalCommaValue :=
  match EbnfValue.optionalView
      (.atom (.terminal (.symbol .comma))) input with
  | none => .absent
  | some rawComma =>
      .present (EbnfValue.terminalView (.symbol .comma) rawComma).span

/-- Execute the top-item source rule, locating the selected declaration at
the completed chart interval. -/
def executeTopItemRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .topItem)) : TopItem :=
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish owned ordered
  match EbnfValue.choiceView [
      .atom (.nonterminal .importDecl),
      .atom (.nonterminal .exportDecl),
      .atom (.nonterminal .pragmaDecl),
      .atom (.nonterminal .dataDecl),
      .atom (.nonterminal .typeAliasDecl),
      .atom (.nonterminal .classDecl),
      .atom (.nonterminal .instanceDecl),
      .atom (.nonterminal .contractDecl),
      .atom (.nonterminal .functionDecl)] input with
  | ⟨⟨0, _⟩, raw⟩ =>
      sourceLoc witness (.importDecl (EbnfValue.ruleView .importDecl raw))
  | ⟨⟨1, _⟩, raw⟩ =>
      sourceLoc witness (.exportDecl (EbnfValue.ruleView .exportDecl raw))
  | ⟨⟨2, _⟩, raw⟩ =>
      sourceLoc witness (.pragmaDecl (EbnfValue.ruleView .pragmaDecl raw))
  | ⟨⟨3, _⟩, raw⟩ =>
      sourceLoc witness (.dataDecl (EbnfValue.ruleView .dataDecl raw))
  | ⟨⟨4, _⟩, raw⟩ =>
      sourceLoc witness (.typeAliasDecl (EbnfValue.ruleView .typeAliasDecl raw))
  | ⟨⟨5, _⟩, raw⟩ =>
      sourceLoc witness (.classDecl (EbnfValue.ruleView .classDecl raw))
  | ⟨⟨6, _⟩, raw⟩ =>
      sourceLoc witness (.instanceDecl (EbnfValue.ruleView .instanceDecl raw))
  | ⟨⟨7, _⟩, raw⟩ =>
      sourceLoc witness (.contractDecl (EbnfValue.ruleView .contractDecl raw))
  | ⟨⟨8, _⟩, raw⟩ =>
      sourceLoc witness (.functionDecl (EbnfValue.ruleView .functionDecl raw))


/-- Execute the module source rule by decoding its exact ordered item list. -/
def executeModuleRoot
    (file : WorkspaceFile) {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .module)) : ParsedModuleV1 :=
  let itemAtom : EbnfExpr := .atom (.nonterminal .topItem)
  let eofAtom : EbnfExpr := .atom (.terminal .endOfFile)
  let values := EbnfValue.sequenceView [.star itemAtom, eofAtom] input
  let first := EbnfValues.consView (.star itemAtom) [eofAtom] values
  let rawItems := EbnfValue.starView itemAtom first.1
  executableModuleValue file (rawItems.map (EbnfValue.ruleView .topItem))

/-- Decode a nonempty predicate list from its typed EBNF root value. -/
def executePredicateListRoot
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .predicateList)) :
    NonemptyList Predicate :=
  (EbnfValue.list1View (.atom (.nonterminal .predicate)) input).map
    (EbnfValue.ruleView .predicate)

/-- Decode an instance method's transparent function-declaration root. -/
def executeInstanceMethodRoot
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .instanceMethod)) :
    FunctionDecl :=
  EbnfValue.ruleView .functionDecl input

/-- Decode an arm statement's transparent statement root. -/
def executeArmStatementRoot
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .armStatement)) : Statement :=
  EbnfValue.ruleView .statement input

/-- Execute a statement root by decoding its selected statement subtype. -/
def executeStatementRoot
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .statement)) : Statement :=
  match EbnfValue.choiceView [
      .atom (.nonterminal .letStatement),
      .atom (.nonterminal .returnStatement),
      .atom (.nonterminal .matchStatement),
      .atom (.nonterminal .ifStatement),
      .atom (.nonterminal .forStatement),
      .atom (.nonterminal .assemblyStatement),
      .atom (.nonterminal .blockStatement),
      .atom (.nonterminal .breakStatement),
      .atom (.nonterminal .continueStatement),
      .atom (.nonterminal .assignmentStatement),
      .atom (.nonterminal .expressionStatement)] input with
  | ⟨⟨0, _⟩, raw⟩ => EbnfValue.ruleView .letStatement raw
  | ⟨⟨1, _⟩, raw⟩ => EbnfValue.ruleView .returnStatement raw
  | ⟨⟨2, _⟩, raw⟩ => EbnfValue.ruleView .matchStatement raw
  | ⟨⟨3, _⟩, raw⟩ => EbnfValue.ruleView .ifStatement raw
  | ⟨⟨4, _⟩, raw⟩ => EbnfValue.ruleView .forStatement raw
  | ⟨⟨5, _⟩, raw⟩ => EbnfValue.ruleView .assemblyStatement raw
  | ⟨⟨6, _⟩, raw⟩ => EbnfValue.ruleView .blockStatement raw
  | ⟨⟨7, _⟩, raw⟩ => EbnfValue.ruleView .breakStatement raw
  | ⟨⟨8, _⟩, raw⟩ => EbnfValue.ruleView .continueStatement raw
  | ⟨⟨9, _⟩, raw⟩ => EbnfValue.ruleView .assignmentStatement raw
  | ⟨⟨10, _⟩, raw⟩ => EbnfValue.ruleView .expressionStatement raw

/-- Decode a terminal-expression root without changing its expression. -/
def executeTerminalExpressionRoot
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .terminalExpression)) :
    Expression :=
  EbnfValue.ruleView .expression input

/-- Decode the expression root's transparent annotation value. -/
def executeExpressionRoot
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .expression)) : Expression :=
  EbnfValue.ruleView .annotation input

namespace EbnfValue

/-- View an exact two-child sequence as its two typed child values. -/
def sequence2View
    {file : WorkspaceFile} {tokens : List Token}
    (first second : EbnfExpr)
    (input : EbnfValue file tokens (.sequence [first, second])) :
    EbnfValue file tokens first × EbnfValue file tokens second :=
  let values := sequenceView [first, second] input
  let firstView := EbnfValues.consView first [second] values
  let secondView := EbnfValues.consView second [] firstView.2
  (firstView.1, secondView.1)

/-- Rebuilding a viewed two-child sequence recovers the original value. -/
theorem sequence2_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (first second : EbnfExpr)
    (input : EbnfValue file tokens (.sequence [first, second])) :
    sequence [first, second]
      (EbnfValues.cons first [second] (sequence2View first second input).1
        (EbnfValues.cons second [] (sequence2View first second input).2
          EbnfValues.nil)) = input := by
  let values := sequenceView [first, second] input
  let firstView := EbnfValues.consView first [second] values
  let secondView := EbnfValues.consView second [] firstView.2
  have nilEq : EbnfValues.nil = secondView.2 :=
    EbnfValues.nil_unique secondView.2
  have tailEq : EbnfValues.cons second [] secondView.1 EbnfValues.nil =
      firstView.2 := by
    rw [nilEq]
    exact EbnfValues.cons_of_view second [] firstView.2
  have valuesEq : EbnfValues.cons first [second] firstView.1
      (EbnfValues.cons second [] secondView.1 EbnfValues.nil) = values := by
    rw [tailEq]
    exact EbnfValues.cons_of_view first [second] values
  change sequence [first, second]
    (EbnfValues.cons first [second] firstView.1
      (EbnfValues.cons second [] secondView.1 EbnfValues.nil)) = input
  rw [valuesEq]
  exact sequence_of_view [first, second] input

/-- View an exact three-child sequence as its typed child values. -/
def sequence3View
    {file : WorkspaceFile} {tokens : List Token}
    (first second third : EbnfExpr)
    (input : EbnfValue file tokens (.sequence [first, second, third])) :
    EbnfValue file tokens first × EbnfValue file tokens second ×
      EbnfValue file tokens third :=
  let values := sequenceView [first, second, third] input
  let firstView := EbnfValues.consView first [second, third] values
  let secondView := EbnfValues.consView second [third] firstView.2
  let thirdView := EbnfValues.consView third [] secondView.2
  (firstView.1, secondView.1, thirdView.1)

/-- Rebuilding a viewed three-child sequence recovers the original value. -/
theorem sequence3_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (first second third : EbnfExpr)
    (input : EbnfValue file tokens (.sequence [first, second, third])) :
    sequence [first, second, third]
      (EbnfValues.cons first [second, third]
        (sequence3View first second third input).1
        (EbnfValues.cons second [third]
          (sequence3View first second third input).2.1
          (EbnfValues.cons third []
            (sequence3View first second third input).2.2
            EbnfValues.nil))) = input := by
  let values := sequenceView [first, second, third] input
  let firstView := EbnfValues.consView first [second, third] values
  let secondView := EbnfValues.consView second [third] firstView.2
  let thirdView := EbnfValues.consView third [] secondView.2
  have thirdTailEq : EbnfValues.cons third [] thirdView.1
      EbnfValues.nil = secondView.2 := by
    rw [EbnfValues.nil_unique thirdView.2]
    exact EbnfValues.cons_of_view third [] secondView.2
  have secondTailEq : EbnfValues.cons second [third] secondView.1
      (EbnfValues.cons third [] thirdView.1 EbnfValues.nil) =
        firstView.2 := by
    rw [thirdTailEq]
    exact EbnfValues.cons_of_view second [third] firstView.2
  have valuesEq : EbnfValues.cons first [second, third] firstView.1
      (EbnfValues.cons second [third] secondView.1
        (EbnfValues.cons third [] thirdView.1 EbnfValues.nil)) = values := by
    rw [secondTailEq]
    exact EbnfValues.cons_of_view first [second, third] values
  change sequence [first, second, third]
    (EbnfValues.cons first [second, third] firstView.1
      (EbnfValues.cons second [third] secondView.1
        (EbnfValues.cons third [] thirdView.1 EbnfValues.nil))) = input
  rw [valuesEq]
  exact sequence_of_view [first, second, third] input

/-- View an exact four-child sequence as its typed child values. -/
def sequence4View
    {file : WorkspaceFile} {tokens : List Token}
    (first second third fourth : EbnfExpr)
    (input : EbnfValue file tokens
      (.sequence [first, second, third, fourth])) :
    EbnfValue file tokens first × EbnfValue file tokens second ×
      EbnfValue file tokens third × EbnfValue file tokens fourth :=
  let values := sequenceView [first, second, third, fourth] input
  let firstView := EbnfValues.consView first [second, third, fourth] values
  let secondView := EbnfValues.consView second [third, fourth] firstView.2
  let thirdView := EbnfValues.consView third [fourth] secondView.2
  let fourthView := EbnfValues.consView fourth [] thirdView.2
  (firstView.1, secondView.1, thirdView.1, fourthView.1)

/-- Rebuilding a viewed four-child sequence recovers the original value. -/
theorem sequence4_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (first second third fourth : EbnfExpr)
    (input : EbnfValue file tokens
      (.sequence [first, second, third, fourth])) :
    sequence [first, second, third, fourth]
      (EbnfValues.cons first [second, third, fourth]
        (sequence4View first second third fourth input).1
        (EbnfValues.cons second [third, fourth]
          (sequence4View first second third fourth input).2.1
          (EbnfValues.cons third [fourth]
            (sequence4View first second third fourth input).2.2.1
            (EbnfValues.cons fourth []
              (sequence4View first second third fourth input).2.2.2
              EbnfValues.nil)))) = input := by
  let values := sequenceView [first, second, third, fourth] input
  let firstView := EbnfValues.consView first [second, third, fourth] values
  let secondView := EbnfValues.consView second [third, fourth] firstView.2
  let thirdView := EbnfValues.consView third [fourth] secondView.2
  let fourthView := EbnfValues.consView fourth [] thirdView.2
  have fourthTailEq : EbnfValues.cons fourth [] fourthView.1
      EbnfValues.nil = thirdView.2 := by
    rw [EbnfValues.nil_unique fourthView.2]
    exact EbnfValues.cons_of_view fourth [] thirdView.2
  have thirdTailEq : EbnfValues.cons third [fourth] thirdView.1
      (EbnfValues.cons fourth [] fourthView.1 EbnfValues.nil) =
        secondView.2 := by
    rw [fourthTailEq]
    exact EbnfValues.cons_of_view third [fourth] secondView.2
  have secondTailEq : EbnfValues.cons second [third, fourth] secondView.1
      (EbnfValues.cons third [fourth] thirdView.1
        (EbnfValues.cons fourth [] fourthView.1 EbnfValues.nil)) =
        firstView.2 := by
    rw [thirdTailEq]
    exact EbnfValues.cons_of_view second [third, fourth] firstView.2
  have valuesEq :
      EbnfValues.cons first [second, third, fourth] firstView.1
        (EbnfValues.cons second [third, fourth] secondView.1
          (EbnfValues.cons third [fourth] thirdView.1
            (EbnfValues.cons fourth [] fourthView.1 EbnfValues.nil))) =
        values := by
    rw [secondTailEq]
    exact EbnfValues.cons_of_view first [second, third, fourth] values
  change sequence [first, second, third, fourth]
    (EbnfValues.cons first [second, third, fourth] firstView.1
      (EbnfValues.cons second [third, fourth] secondView.1
        (EbnfValues.cons third [fourth] thirdView.1
          (EbnfValues.cons fourth [] fourthView.1 EbnfValues.nil)))) = input
  rw [valuesEq]
  exact sequence_of_view [first, second, third, fourth] input

/-- A fully typed product of one semantic value for every sequence child. -/
def SequenceValues
    (file : WorkspaceFile) (tokens : List Token) : List EbnfExpr → Type
  | [] => Unit
  | child :: rest =>
      EbnfValue file tokens child × SequenceValues file tokens rest

/-- Flatten the indexed EBNF sequence carrier into its typed product. -/
def sequenceValuesView
    {file : WorkspaceFile} {tokens : List Token} :
    (children : List EbnfExpr) →
      EbnfValues file tokens children → SequenceValues file tokens children
  | [], _ => ()
  | child :: rest, input =>
      let viewed := EbnfValues.consView child rest input
      (viewed.1, sequenceValuesView rest viewed.2)

/-- Rebuild the indexed EBNF sequence carrier from its typed product. -/
def sequenceValuesBuild
    {file : WorkspaceFile} {tokens : List Token} :
    (children : List EbnfExpr) →
      SequenceValues file tokens children → EbnfValues file tokens children
  | [], _ => EbnfValues.nil
  | child :: rest, viewed =>
      EbnfValues.cons child rest viewed.1
        (sequenceValuesBuild rest viewed.2)

/-- Flattening and rebuilding an indexed sequence carrier is lossless. -/
theorem sequenceValues_build_view
    {file : WorkspaceFile} {tokens : List Token}
    (children : List EbnfExpr) (input : EbnfValues file tokens children) :
    sequenceValuesBuild children (sequenceValuesView children input) =
      input := by
  induction children with
  | nil => exact EbnfValues.nil_unique input
  | cons child rest induction =>
      simp only [sequenceValuesView, sequenceValuesBuild]
      let viewed := EbnfValues.consView child rest input
      calc
        _ = EbnfValues.cons child rest viewed.1 viewed.2 := by
          apply congrArg (EbnfValues.cons child rest viewed.1)
          exact induction viewed.2
        _ = input := EbnfValues.cons_of_view child rest input

/-- View an arbitrary finite sequence as its fully typed child product. -/
def sequenceFlatView
    {file : WorkspaceFile} {tokens : List Token}
    (children : List EbnfExpr)
    (input : EbnfValue file tokens (.sequence children)) :
    SequenceValues file tokens children :=
  sequenceValuesView children (sequenceView children input)

/-- Rebuilding an arbitrary flattened sequence recovers its original value. -/
theorem sequence_of_flat_view
    {file : WorkspaceFile} {tokens : List Token}
    (children : List EbnfExpr)
    (input : EbnfValue file tokens (.sequence children)) :
    sequence children
      (sequenceValuesBuild children (sequenceFlatView children input)) =
        input := by
  unfold sequenceFlatView
  rw [sequenceValues_build_view]
  exact sequence_of_view children input


/-- A grouped pair of source-rule atoms. -/
def rulePairTailExpr
    (first second : GrammarRuleId) : EbnfExpr :=
  .group (.sequence [
    .atom (.nonterminal first), .atom (.nonterminal second)])

/-- Decode one grouped pair of source-rule values. -/
def rulePairTailView
    {file : WorkspaceFile} {tokens : List Token}
    (first second : GrammarRuleId)
    (input : EbnfValue file tokens (rulePairTailExpr first second)) :
    RuleValue first × RuleValue second :=
  let firstAtom : EbnfExpr := .atom (.nonterminal first)
  let secondAtom : EbnfExpr := .atom (.nonterminal second)
  let rawSequence := groupView (.sequence [firstAtom, secondAtom]) input
  let viewed := sequence2View firstAtom secondAtom rawSequence
  (ruleView first viewed.1, ruleView second viewed.2)

/-- Rebuild one grouped pair of source-rule values. -/
def rulePairTailValue
    {file : WorkspaceFile} {tokens : List Token}
    (first second : GrammarRuleId)
    (value : RuleValue first × RuleValue second) :
    EbnfValue file tokens (rulePairTailExpr first second) :=
  let firstAtom : EbnfExpr := .atom (.nonterminal first)
  let secondAtom : EbnfExpr := .atom (.nonterminal second)
  group (.sequence [firstAtom, secondAtom])
    (sequence [firstAtom, secondAtom]
      (EbnfValues.cons firstAtom [secondAtom]
        (ruleAtom first value.1)
        (EbnfValues.cons secondAtom [] (ruleAtom second value.2)
          EbnfValues.nil)))

/-- Rebuilding a viewed source-rule pair recovers its original value. -/
theorem rulePairTailValue_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (first second : GrammarRuleId)
    (input : EbnfValue file tokens (rulePairTailExpr first second)) :
    rulePairTailValue first second
      (rulePairTailView first second input) = input := by
  let firstAtom : EbnfExpr := .atom (.nonterminal first)
  let secondAtom : EbnfExpr := .atom (.nonterminal second)
  let rawSequence := groupView (.sequence [firstAtom, secondAtom]) input
  let viewed := sequence2View firstAtom secondAtom rawSequence
  have firstEq := rule_of_view first viewed.1
  have secondEq := rule_of_view second viewed.2
  have sequenceEq := sequence2_of_view firstAtom secondAtom rawSequence
  have groupEq := group_of_view
    (.sequence [firstAtom, secondAtom]) input
  change group (.sequence [firstAtom, secondAtom])
    (sequence [firstAtom, secondAtom]
      (EbnfValues.cons firstAtom [secondAtom]
        (ruleAtom first (ruleView first viewed.1))
        (EbnfValues.cons secondAtom []
          (ruleAtom second (ruleView second viewed.2)) EbnfValues.nil))) =
    input
  rw [firstEq, secondEq, sequenceEq]
  exact groupEq

/-- The parenthesized nonempty type arguments shared by declarations. -/
def typeArgumentsExpr : EbnfExpr :=
  .sequence [
    .atom (.terminal (.symbol .leftParen)),
    .list1 (.atom (.nonterminal .type)),
    .atom (.terminal (.symbol .rightParen))]

/-- Decode parenthesized nonempty type arguments without losing delimiters. -/
def typeArgumentsView
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens typeArgumentsExpr) :
    MatchedTerminal file tokens (.symbol .leftParen) ×
      (NonemptyList TypeExpr ×
        (MatchedTerminal file tokens (.symbol .rightParen) × Unit)) :=
  let openAtom : EbnfExpr :=
    .atom (.terminal (.symbol .leftParen))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let closeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .rightParen))
  let viewed := sequenceFlatView
    [openAtom, .list1 typeAtom, closeAtom] input
  (terminalView (.symbol .leftParen) viewed.1,
    (list1View typeAtom viewed.2.1).map (ruleView .type),
    terminalView (.symbol .rightParen) viewed.2.2.1, ())

/-- Rebuild parenthesized nonempty type arguments from their semantic view. -/
def typeArgumentsValue
    {file : WorkspaceFile} {tokens : List Token}
    (value : MatchedTerminal file tokens (.symbol .leftParen) ×
      (NonemptyList TypeExpr ×
        (MatchedTerminal file tokens (.symbol .rightParen) × Unit))) :
    EbnfValue file tokens typeArgumentsExpr :=
  let openAtom : EbnfExpr :=
    .atom (.terminal (.symbol .leftParen))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let closeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .rightParen))
  sequence [openAtom, .list1 typeAtom, closeAtom]
    (EbnfValues.cons openAtom [.list1 typeAtom, closeAtom]
      (terminalAtom (.symbol .leftParen) value.1)
      (EbnfValues.cons (.list1 typeAtom) [closeAtom]
        (list1 typeAtom (value.2.1.map (ruleAtom .type)))
        (EbnfValues.cons closeAtom []
          (terminalAtom (.symbol .rightParen) value.2.2.1)
          EbnfValues.nil)))

/-- Decoding and rebuilding type arguments recovers their typed input. -/
theorem typeArgumentsValue_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens typeArgumentsExpr) :
    typeArgumentsValue (typeArgumentsView input) = input := by
  let openAtom : EbnfExpr :=
    .atom (.terminal (.symbol .leftParen))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let closeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .rightParen))
  let children : List EbnfExpr :=
    [openAtom, .list1 typeAtom, closeAtom]
  generalize viewEq : sequenceFlatView children input = viewed
  rcases viewed with ⟨rawOpen, rawTypes, rawClose, ⟨⟩⟩
  let typeValues := list1View typeAtom rawTypes
  let types : NonemptyList TypeExpr :=
    typeValues.map fun raw => ruleView .type raw
  have typeValuesEq :
      types.map (ruleAtom .type) = typeValues := by
    dsimp only [types]
    cases typeValues with
    | mk head tail =>
        simp only [NonemptyList.map, NonemptyList.mk.injEq]
        constructor
        · exact rule_of_view .type head
        · induction tail with
          | nil => rfl
          | cons next rest induction =>
              change ruleAtom .type (ruleView .type next) ::
                  (rest.map fun raw => ruleView .type raw).map
                    (ruleAtom .type) = next :: rest
              rw [rule_of_view .type next]
              exact congrArg (List.cons next) induction
  have inputEq := sequence_of_flat_view children input
  rw [viewEq] at inputEq
  have decodedEq : typeArgumentsView input =
      (terminalView (.symbol .leftParen) rawOpen, types,
        terminalView (.symbol .rightParen) rawClose, ()) := by
    simp [typeArgumentsView, openAtom, typeAtom,
      closeAtom, children, viewEq, types, typeValues]
  rw [decodedEq]
  simp only [typeArgumentsValue, typeArgumentsExpr]
  rw [terminal_of_view (.symbol .leftParen) rawOpen,
    typeValuesEq, list1_of_view typeAtom rawTypes,
    terminal_of_view (.symbol .rightParen) rawClose]
  exact inputEq

end EbnfValue

/-- Construct the exact empty or nonempty body of one executable match arm. -/
def executableMatchArmBody
    {tokens : List Token}
    (file : WorkspaceFile)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow)) :
    List Statement → Body
  | [] => {
      span := {
        source := file.id
        startByte := fatArrow.span.endByte
        endByte := fatArrow.span.endByte
      }
      payload := {
        origin := .matchArm fatArrow.span
        statements := []
      }
    }
  | first :: rest =>
      let last := rest.getLastD first
      {
        span := {
          source := file.id
          startByte := first.span.startByte
          endByte := last.span.endByte
        }
        payload := {
          origin := .matchArm fatArrow.span
          statements := first :: rest
        }
      }

/-- Execute a match-arm root from its pattern list and ordered statements. -/
def executeMatchArmRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .matchArm)) : MatchArm :=
  let pipeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .pipe))
  let patternAtom : EbnfExpr := .atom (.nonterminal .pattern)
  let arrowAtom : EbnfExpr :=
    .atom (.terminal (.symbol .fatArrow))
  let statementAtom : EbnfExpr := .atom (.nonterminal .armStatement)
  let children : List EbnfExpr := [pipeAtom, .list1 patternAtom,
    arrowAtom, .star statementAtom]
  let viewed := EbnfValue.sequenceFlatView children input
  let patterns := (EbnfValue.list1View patternAtom viewed.2.1).map
    (EbnfValue.ruleView .pattern)
  let arrow := EbnfValue.terminalView (.symbol .fatArrow) viewed.2.2.1
  let statements := (EbnfValue.starView statementAtom
    viewed.2.2.2.1).map (EbnfValue.ruleView .armStatement)
  sourceLoc
    (ConsumedSpanWitness.compute file tokens origin finish owned ordered) {
      patterns := patterns
      body := executableMatchArmBody file arrow statements
    }

/-- Execute all three import-declaration forms. -/
def executeImportDeclRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .importDecl)) :
    ImportDecl :=
  let moduleChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .importKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .semicolon))]
  let aliasChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .importKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.hardKeyword .asKw)),
    .atom (.terminal (.category .identifier)),
    .atom (.terminal (.symbol .semicolon))]
  let entryAtom : EbnfExpr := .atom (.nonterminal .importEntry)
  let hidingAtom : EbnfExpr := .atom (.nonterminal .hidingClause)
  let itemsChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .importKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.symbol .leftBrace)), .list0 entryAtom,
    .atom (.terminal (.symbol .rightBrace)), .optional hidingAtom,
    .atom (.terminal (.symbol .semicolon))]
  let branches : List EbnfExpr := [.sequence moduleChildren,
    .sequence aliasChildren, .sequence itemsChildren]
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish owned ordered
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence3View
        (.atom (.terminal (.hardKeyword .importKw)))
        (.atom (.nonterminal .moduleRef))
        (.atom (.terminal (.symbol .semicolon))) raw
      sourceLoc witness {
        moduleRef := EbnfValue.ruleView .moduleRef viewed.2.1
        mode := .module none
      }
  | ⟨⟨1, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequenceFlatView aliasChildren raw
      let name := EbnfValue.terminalView
        (.category .identifier) viewed.2.2.2.1
      sourceLoc witness {
        moduleRef := EbnfValue.ruleView .moduleRef viewed.2.1
        mode := .module (some {
          span := name.span
          payload := name.identifierProjection.2
        })
      }
  | ⟨⟨2, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequenceFlatView itemsChildren raw
      let reference := EbnfValue.ruleView .moduleRef viewed.2.1
      let openBrace := EbnfValue.terminalView
        (.symbol .leftBrace) viewed.2.2.2.1
      let rawEntries := viewed.2.2.2.2.1
      let entries := (EbnfValue.list0View entryAtom rawEntries).map
        (EbnfValue.ruleView .importEntry)
      let closeBrace := EbnfValue.terminalView
        (.symbol .rightBrace) viewed.2.2.2.2.2.1
      let hidingValue := (EbnfValue.optionalView hidingAtom
        viewed.2.2.2.2.2.2.1).map
          (EbnfValue.ruleView .hidingClause)
      sourceLoc witness {
        moduleRef := reference
        mode := .items
          ({
            span := {
              source := file.id
              startByte := openBrace.span.startByte
              endByte := closeBrace.span.endByte
            }
            payload := { entries := entries }
          } : ImportSelection) hidingValue
      }

/-- Execute all five export-declaration forms. -/
def executeExportDeclRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .exportDecl)) :
    ExportDecl :=
  let localAtom : EbnfExpr := .atom (.nonterminal .localExportEntry)
  let remoteAtom : EbnfExpr := .atom (.nonterminal .remoteExportEntry)
  let localChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.terminal (.symbol .leftBrace)), .list0 localAtom,
    .atom (.terminal (.symbol .rightBrace)),
    .atom (.terminal (.symbol .semicolon))]
  let moduleChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .semicolon))]
  let aliasChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.hardKeyword .asKw)),
    .atom (.terminal (.category .identifier)),
    .atom (.terminal (.symbol .semicolon))]
  let wildcardChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef), .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.symbol .star)),
    .atom (.terminal (.symbol .semicolon))]
  let bracedChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef), .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.symbol .leftBrace)), .list0 remoteAtom,
    .atom (.terminal (.symbol .rightBrace)),
    .atom (.terminal (.symbol .semicolon))]
  let branches : List EbnfExpr := [.sequence localChildren,
    .sequence moduleChildren, .sequence aliasChildren,
    .sequence wildcardChildren, .sequence bracedChildren]
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish owned ordered
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequenceFlatView localChildren raw
      let openBrace := EbnfValue.terminalView
        (.symbol .leftBrace) viewed.2.1
      let entries := (EbnfValue.list0View localAtom viewed.2.2.1).map
        (EbnfValue.ruleView .localExportEntry)
      let closeBrace := EbnfValue.terminalView
        (.symbol .rightBrace) viewed.2.2.2.1
      sourceLoc witness (.local ({
        span := {
          source := file.id
          startByte := openBrace.span.startByte
          endByte := closeBrace.span.endByte
        }
        payload := { entries := entries }
      } : LocalExportList))
  | ⟨⟨1, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequenceFlatView moduleChildren raw
      sourceLoc witness (.module
        (EbnfValue.ruleView .moduleRef viewed.2.1) none)
  | ⟨⟨2, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequenceFlatView aliasChildren raw
      let name := EbnfValue.terminalView
        (.category .identifier) viewed.2.2.2.1
      sourceLoc witness (.module
        (EbnfValue.ruleView .moduleRef viewed.2.1)
        (some { span := name.span, payload := name.identifierProjection.2 }))
  | ⟨⟨3, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequenceFlatView wildcardChildren raw
      let reference := EbnfValue.ruleView .moduleRef viewed.2.1
      let dot := EbnfValue.terminalView (.symbol .dot) viewed.2.2.1
      let star := EbnfValue.terminalView (.symbol .star) viewed.2.2.2.1
      sourceLoc witness (.from reference ({
        span := {
          source := file.id
          startByte := dot.span.startByte
          endByte := star.span.endByte
        }
        payload := .dotWildcard {
          span := star.span
          payload := .wildcard
        }
      } : RemoteExportSelection))
  | ⟨⟨4, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequenceFlatView bracedChildren raw
      let reference := EbnfValue.ruleView .moduleRef viewed.2.1
      let openBrace := EbnfValue.terminalView
        (.symbol .leftBrace) viewed.2.2.2.1
      let entries := (EbnfValue.list0View remoteAtom
        viewed.2.2.2.2.1).map (EbnfValue.ruleView .remoteExportEntry)
      let closeBrace := EbnfValue.terminalView
        (.symbol .rightBrace) viewed.2.2.2.2.2.1
      sourceLoc witness (.from reference ({
        span := {
          source := file.id
          startByte := openBrace.span.startByte
          endByte := closeBrace.span.endByte
        }
        payload := .braced entries
      } : RemoteExportSelection))

private def shallowRootWitness
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val) :
    ConsumedSpanWitness file tokens origin finish :=
  ConsumedSpanWitness.compute file tokens origin finish owned ordered

/-- Execute one generic predicate and its optional nonempty type arguments. -/
def executePredicateRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .predicate)) : Predicate :=
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let argumentChildren : List EbnfExpr := [
    .atom (.terminal (.symbol .leftParen)), .list1 typeAtom,
    .atom (.terminal (.symbol .rightParen))]
  let argumentChild : EbnfExpr := .sequence argumentChildren
  let children : List EbnfExpr := [
    .atom (.nonterminal .typeAtom),
    .atom (.terminal (.symbol .colon)),
    .atom (.nonterminal .qualifiedName), .optional argumentChild]
  let viewed := EbnfValue.sequenceFlatView children input
  let parameters := (EbnfValue.optionalView argumentChild
    viewed.2.2.2.1).map fun rawArguments =>
      let argumentView := EbnfValue.sequenceFlatView
        argumentChildren rawArguments
      (EbnfValue.list1View typeAtom argumentView.2.1).map
        (EbnfValue.ruleView .type)
  sourceLoc (ConsumedSpanWitness.compute
    file tokens origin finish owned ordered) {
      main := EbnfValue.ruleView .typeAtom viewed.1
      className := EbnfValue.ruleView .qualifiedName viewed.2.2.1
      parameters := parameters
    }

/-- Execute a function signature and its optional modifiers and return type. -/
def executeFunctionSignatureRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .functionSignature)) :
    FunctionSignature :=
  let genericAtom : EbnfExpr := .atom (.nonterminal .genericPrefix)
  let publicAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .publicKw))
  let payableAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .payableKw))
  let parameterAtom : EbnfExpr := .atom (.nonterminal .parameter)
  let returnChild : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .arrow)), .atom (.nonterminal .type)]
  let children : List EbnfExpr := [.optional genericAtom,
    .optional publicAtom, .optional payableAtom,
    .atom (.terminal (.hardKeyword .functionKw)),
    .atom (.terminal (.category .identifier)),
    .atom (.terminal (.symbol .leftParen)), .list0 parameterAtom,
    .atom (.terminal (.symbol .rightParen)), .optional returnChild]
  let ⟨rawGeneric, rawPublic, rawPayable, _, rawName, _, rawParameters,
    _, rawReturn, ⟨⟩⟩ := EbnfValue.sequenceFlatView children input
  let genericPrefix := (EbnfValue.optionalView genericAtom rawGeneric).map
    (EbnfValue.ruleView .genericPrefix)
  let publicToken := (EbnfValue.optionalView publicAtom rawPublic).map
    (EbnfValue.terminalView (.hardKeyword .publicKw))
  let payableToken := (EbnfValue.optionalView payableAtom rawPayable).map
    (EbnfValue.terminalView (.hardKeyword .payableKw))
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let parameters := (EbnfValue.list0View parameterAtom rawParameters).map
    (EbnfValue.ruleView .parameter)
  let returnValue := (EbnfValue.optionalView returnChild rawReturn).map
    fun raw =>
      let pair := EbnfValue.sequence2View
        (.atom (.terminal (.symbol .arrow)))
        (.atom (.nonterminal .type)) raw
      (EbnfValue.terminalView (.symbol .arrow) pair.1,
        EbnfValue.ruleView .type pair.2, ())
  sourceLoc
    (ConsumedSpanWitness.compute file tokens origin finish owned ordered) {
      genericPrefix := genericPrefix
      «public» := publicToken.map fun terminal =>
        { span := terminal.span, payload := .publicModifier }
      payable := payableToken.map fun terminal =>
        { span := terminal.span, payload := .payableModifier }
      name := { span := name.span, payload := name.identifierProjection.2 }
      parameters := parameters
      returnType := returnValue.map fun value => value.2.1
    }

/-- Execute an annotation with or without its optional type suffix. -/
def executeAnnotationRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .annotation)) : Expression :=
  let expressionAtom : EbnfExpr := .atom (.nonterminal .conditional)
  let colonAtom : EbnfExpr := .atom (.terminal (.symbol .colon))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let suffix : EbnfExpr := .sequence [colonAtom, typeAtom]
  let viewed := EbnfValue.sequence2View
    expressionAtom (.optional suffix) input
  let expression := EbnfValue.ruleView .conditional viewed.1
  match EbnfValue.optionalView suffix viewed.2 with
  | none => expression
  | some rawSuffix =>
      let suffixView := EbnfValue.sequence2View
        colonAtom typeAtom rawSuffix
      sourceLoc (ConsumedSpanWitness.compute
        file tokens origin finish owned ordered)
        (.annotation expression (EbnfValue.ruleView .type suffixView.2))

/-- Execute keyword and ternary conditional-expression roots. -/
def executeConditionalRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .conditional)) : Expression :=
  let keywordChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .ifKw)),
    .atom (.nonterminal .conditional),
    .atom (.terminal (.contextualKeyword .thenKw)),
    .atom (.nonterminal .conditional),
    .atom (.terminal (.hardKeyword .elseKw)),
    .atom (.nonterminal .conditional)]
  let ternaryChildren : List EbnfExpr := [
    .atom (.terminal (.symbol .question)),
    .atom (.nonterminal .conditional),
    .atom (.terminal (.symbol .colon)),
    .atom (.nonterminal .conditional)]
  let logicalOrAtom : EbnfExpr := .atom (.nonterminal .logicalOr)
  let ternaryBranch : EbnfExpr := .sequence ternaryChildren
  let logicalBranch : EbnfExpr :=
    .sequence [logicalOrAtom, .optional ternaryBranch]
  let keywordBranch : EbnfExpr := .sequence keywordChildren
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish owned ordered
  match EbnfValue.choice2View keywordBranch logicalBranch input with
  | .inl rawKeyword =>
      let values := EbnfValue.sequenceFlatView keywordChildren rawKeyword
      sourceLoc witness (.keywordConditional
        (EbnfValue.ruleView .conditional values.2.1)
        (EbnfValue.ruleView .conditional values.2.2.2.1)
        (EbnfValue.ruleView .conditional values.2.2.2.2.2.1))
  | .inr rawLogical =>
      let viewed := EbnfValue.sequence2View
        logicalOrAtom (.optional ternaryBranch) rawLogical
      let condition := EbnfValue.ruleView .logicalOr viewed.1
      match EbnfValue.optionalView ternaryBranch viewed.2 with
      | none => condition
      | some rawTernary =>
          let values := EbnfValue.sequence4View
            (.atom (.terminal (.symbol .question)))
            (.atom (.nonterminal .conditional))
            (.atom (.terminal (.symbol .colon)))
            (.atom (.nonterminal .conditional)) rawTernary
          sourceLoc witness (.ternaryConditional condition
            (EbnfValue.ruleView .conditional values.2.1)
            (EbnfValue.ruleView .conditional values.2.2.2))

/-- Execute a block-statement root from its body value. -/
def executeBlockStatementRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .blockStatement)) : Statement :=
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered)
    (.block (EbnfValue.ruleView .body input))

/-- Execute a function declaration from its signature and body. -/
def executeFunctionDeclRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .functionDecl)) : FunctionDecl :=
  let viewed := EbnfValue.sequence2View
    (.atom (.nonterminal .functionSignature))
    (.atom (.nonterminal .body)) input
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered) {
    signature := EbnfValue.ruleView .functionSignature viewed.1
    body := EbnfValue.ruleView .body viewed.2
  }

/-- Execute a declaration-only class method. -/
def executeClassMethodRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .classMethod)) :
    ClassMethodDecl :=
  let viewed := EbnfValue.sequence2View
    (.atom (.nonterminal .functionSignature))
    (.atom (.terminal (.symbol .semicolon))) input
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered) {
    signature := EbnfValue.ruleView .functionSignature viewed.1
    terminator :=
      (EbnfValue.terminalView (.symbol .semicolon) viewed.2).span
  }

/-- Execute a let statement from its binding and checked terminator. -/
def executeLetStatementRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .letStatement)) : Statement :=
  let viewed := EbnfValue.sequence2View
    (.atom (.nonterminal .letBinding))
    (.atom (.terminal (.symbol .semicolon))) input
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered)
    (.letBinding (EbnfValue.ruleView .letBinding viewed.1))

/-- Execute every let-binding form and both initializer states. -/
def executeLetBindingRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .letBinding)) : LetBinding :=
  let letAtom : EbnfExpr := .atom (.terminal (.hardKeyword .letKw))
  let nameAtom : EbnfExpr := .atom (.terminal (.category .identifier))
  let colonAtom : EbnfExpr := .atom (.terminal (.symbol .colon))
  let comptimeAtom : EbnfExpr :=
    .atom (.terminal (.contextualKeyword .comptimeKw))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let typeSeq : EbnfExpr := .sequence [colonAtom, .optional comptimeAtom,
    typeAtom]
  let equalAtom : EbnfExpr := .atom (.terminal (.symbol .equal))
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let initSeq : EbnfExpr := .sequence [equalAtom, expressionAtom]
  let children := [letAtom, nameAtom, .optional typeSeq, .optional initSeq]
  let ⟨_, rawName, rawType, rawInit, ⟨⟩⟩ :=
    EbnfValue.sequenceFlatView children input
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let typeData := (EbnfValue.optionalView typeSeq rawType).map fun raw =>
    let values := EbnfValue.sequenceFlatView
      [colonAtom, .optional comptimeAtom, typeAtom] raw
    let comptime := (EbnfValue.optionalView comptimeAtom values.2.1).map
      (EbnfValue.terminalView (.contextualKeyword .comptimeKw))
    (comptime, EbnfValue.ruleView .type values.2.2.1)
  let initializer := (EbnfValue.optionalView initSeq rawInit).map fun raw =>
    let values := EbnfValue.sequenceFlatView
      [equalAtom, expressionAtom] raw
    (EbnfValue.terminalView (.symbol .equal) values.1,
      EbnfValue.ruleView .expression values.2.1)
  sourceLoc (ConsumedSpanWitness.compute
    file tokens origin finish owned ordered) {
    comptime := typeData.bind fun value => value.1.map fun terminal =>
      { span := terminal.span, payload := .comptimeModifier }
    name := { span := name.span, payload := name.identifierProjection.2 }
    type := typeData.map Prod.snd
    initializer := initializer.map Prod.snd
  }

/-- Execute a break statement, retaining its terminator span. -/
def executeBreakStatementRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .breakStatement)) : Statement :=
  let viewed := EbnfValue.sequence2View
    (.atom (.terminal (.hardKeyword .breakKw)))
    (.atom (.terminal (.symbol .semicolon))) input
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered)
    (.break (EbnfValue.terminalView (.symbol .semicolon) viewed.2).span)

/-- Execute a continue statement, retaining its terminator span. -/
def executeContinueStatementRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .continueStatement)) : Statement :=
  let viewed := EbnfValue.sequence2View
    (.atom (.terminal (.hardKeyword .continueKw)))
    (.atom (.terminal (.symbol .semicolon))) input
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered)
    (.continue (EbnfValue.terminalView (.symbol .semicolon) viewed.2).span)

/-- Execute an opaque assembly statement from its checked block token. -/
def executeAssemblyStatementRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .assemblyStatement)) :
    Statement :=
  let viewed := EbnfValue.sequence2View
    (.atom (.terminal (.hardKeyword .assemblyKw)))
    (.atom (.terminal (.category .assemblyBlock))) input
  let assembly := EbnfValue.terminalView (.category .assemblyBlock) viewed.2
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered)
    (.assembly assembly.assemblyProjection)

/-- Execute an if statement, preserving the optional else body. -/
def executeIfStatementRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .ifStatement)) : Statement :=
  let ifAtom : EbnfExpr := .atom (.terminal (.hardKeyword .ifKw))
  let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftParen))
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightParen))
  let bodyAtom : EbnfExpr := .atom (.nonterminal .body)
  let elseAtom : EbnfExpr := .atom (.terminal (.hardKeyword .elseKw))
  let elseChildren : List EbnfExpr := [elseAtom, bodyAtom]
  let elseSeq : EbnfExpr := .sequence elseChildren
  let children : List EbnfExpr := [ifAtom, openAtom, expressionAtom,
    closeAtom, bodyAtom, .optional elseSeq]
  let ⟨_, _, rawCondition, _, rawThen, rawElse, ⟨⟩⟩ :=
    EbnfValue.sequenceFlatView children input
  let condition := EbnfValue.ruleView .expression rawCondition
  let thenBody := EbnfValue.ruleView .body rawThen
  let elseBody := (EbnfValue.optionalView elseSeq rawElse).map fun raw =>
    let viewed := EbnfValue.sequence2View elseAtom bodyAtom raw
    EbnfValue.ruleView .body viewed.2
  sourceLoc
    (ConsumedSpanWitness.compute file tokens origin finish owned ordered)
    (.ifThenElse condition thenBody elseBody)

/-- Execute a match statement from its nonempty scrutinees and arms. -/
def executeMatchStatementRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .matchStatement)) :
    Statement :=
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let armAtom : EbnfExpr := .atom (.nonterminal .matchArm)
  let semicolonAtom : EbnfExpr :=
    .atom (.terminal (.symbol .semicolon))
  let children : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .matchKw)), .list1 expressionAtom,
    .atom (.terminal (.symbol .leftBrace)), .plus armAtom,
    .atom (.terminal (.symbol .rightBrace)), .optional semicolonAtom]
  let ⟨_, rawScrutinees, _, rawArms, _, rawTerminator, ⟨⟩⟩ :=
    EbnfValue.sequenceFlatView children input
  let scrutinees := (EbnfValue.list1View
    expressionAtom rawScrutinees).map (EbnfValue.ruleView .expression)
  let arms := (EbnfValue.plusView armAtom rawArms).map
    (EbnfValue.ruleView .matchArm)
  let terminator := (EbnfValue.optionalView
    semicolonAtom rawTerminator).map
      (EbnfValue.terminalView (.symbol .semicolon))
  sourceLoc
    (ConsumedSpanWitness.compute file tokens origin finish owned ordered)
    (.match scrutinees arms (terminator.map MatchedTerminal.span))

/-- Execute a return statement from its optional value and terminator. -/
def executeReturnStatementRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .returnStatement)) : Statement :=
  let viewed := EbnfValue.sequence3View
    (.atom (.terminal (.hardKeyword .returnKw)))
    (.optional (.atom (.nonterminal .expression)))
    (.atom (.terminal (.symbol .semicolon))) input
  let value := (EbnfValue.optionalView
    (.atom (.nonterminal .expression)) viewed.2.1).map
      (EbnfValue.ruleView .expression)
  let semicolon := EbnfValue.terminalView (.symbol .semicolon) viewed.2.2
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered)
    (.return value semicolon.span)

/-- Execute an assignment statement from its typed operands and operator. -/
def executeAssignmentStatementRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .assignmentStatement)) :
    Statement :=
  let viewed := EbnfValue.sequence4View
    (.atom (.nonterminal .expression))
    (.atom (.nonterminal .assignmentOperator))
    (.atom (.nonterminal .expression))
    (.atom (.terminal (.symbol .semicolon))) input
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered)
    (.assignment
      (EbnfValue.ruleView .assignmentOperator viewed.2.1)
      (EbnfValue.ruleView .expression viewed.1)
      (EbnfValue.ruleView .expression viewed.2.2.1))

/-- Execute one parameter from its optional modifier and type. -/
def executeParameterRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .parameter)) : Parameter :=
  let comptimeAtom : EbnfExpr :=
    .atom (.terminal (.contextualKeyword .comptimeKw))
  let nameAtom : EbnfExpr := .atom (.terminal (.category .identifier))
  let typeChild : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .colon)),
    .atom (.nonterminal .type)]
  let viewed := EbnfValue.sequence3View
    (.optional comptimeAtom) nameAtom (.optional typeChild) input
  let comptime := (EbnfValue.optionalView comptimeAtom viewed.1).map
    (EbnfValue.terminalView (.contextualKeyword .comptimeKw))
  let name := EbnfValue.terminalView (.category .identifier) viewed.2.1
  let typeValue := (EbnfValue.optionalView typeChild viewed.2.2).map fun raw =>
    let pair := EbnfValue.sequence2View
      (.atom (.terminal (.symbol .colon)))
      (.atom (.nonterminal .type)) raw
    (EbnfValue.terminalView (.symbol .colon) pair.1,
      EbnfValue.ruleView .type pair.2, ())
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered) {
    comptime := comptime.map fun terminal =>
      { span := terminal.span, payload := .comptimeModifier }
    name := { span := name.span, payload := name.identifierProjection.2 }
    type := typeValue.map fun value => value.2.1
  }

/-- Execute an algebraic-data declaration and its optional parameters and constructors. -/
def executeDataDeclRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .dataDecl)) : DataDecl :=
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let constructorAtom : EbnfExpr :=
    .atom (.nonterminal .dataConstructor)
  let parameterChild : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .leftParen)), .list1 identifierAtom,
    .atom (.terminal (.symbol .rightParen))]
  let constructorTail : EbnfExpr := .group (.sequence [
    .atom (.terminal (.symbol .pipe)), constructorAtom])
  let constructorChild : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .equal)), constructorAtom,
    .star constructorTail]
  let children : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .dataKw)), identifierAtom,
    .optional parameterChild, .optional constructorChild,
    .atom (.terminal (.symbol .semicolon))]
  let ⟨_, rawName, rawParameters, rawConstructors, _, ⟨⟩⟩ :=
    EbnfValue.sequenceFlatView children input
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let parameters := (EbnfValue.optionalView
    parameterChild rawParameters).map fun raw =>
      let parameterChildren : List EbnfExpr := [
        .atom (.terminal (.symbol .leftParen)), .list1 identifierAtom,
        .atom (.terminal (.symbol .rightParen))]
      let ⟨_, rawNames, _, ⟨⟩⟩ :=
        EbnfValue.sequenceFlatView parameterChildren raw
      (EbnfValue.list1View identifierAtom rawNames).map fun value =>
        let terminal := EbnfValue.terminalView
          (.category .identifier) value
        { span := terminal.span, payload := terminal.identifierProjection.2 }
  let constructors := (EbnfValue.optionalView
    constructorChild rawConstructors).map fun raw =>
      let viewed := EbnfValue.sequence3View
        (.atom (.terminal (.symbol .equal))) constructorAtom
        (.star constructorTail) raw
      let head : DataConstructor :=
        EbnfValue.ruleView .dataConstructor viewed.2.1
      let tail : List DataConstructor :=
        (EbnfValue.starView constructorTail viewed.2.2).map
        fun rawTail =>
          let sequence := EbnfValue.groupView
            (.sequence [.atom (.terminal (.symbol .pipe)),
              constructorAtom]) rawTail
          let pair := EbnfValue.sequence2View
            (.atom (.terminal (.symbol .pipe))) constructorAtom sequence
          EbnfValue.ruleView .dataConstructor pair.2
      { head := head, tail := tail }
  sourceLoc
    (ConsumedSpanWitness.compute file tokens origin finish owned ordered) {
      name := { span := name.span, payload := name.identifierProjection.2 }
      parameters := parameters
      constructors := constructors
    }

/-- Execute a type-class declaration and its optional type arguments. -/
def executeClassDeclRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .classDecl)) : ClassDecl :=
  let genericAtom : EbnfExpr := .atom (.nonterminal .genericPrefix)
  let typeAtom : EbnfExpr := .atom (.nonterminal .typeAtom)
  let nameAtom : EbnfExpr := .atom (.terminal (.category .identifier))
  let methodAtom : EbnfExpr := .atom (.nonterminal .classMethod)
  let parameterChild := EbnfValue.typeArgumentsExpr
  let children : List EbnfExpr := [.optional genericAtom,
    .atom (.terminal (.hardKeyword .classKw)), typeAtom,
    .atom (.terminal (.symbol .colon)), nameAtom,
    .optional parameterChild,
    .atom (.terminal (.symbol .leftBrace)), .star methodAtom,
    .atom (.terminal (.symbol .rightBrace))]
  let ⟨rawGeneric, _, rawMain, _, rawName, rawParameters, _, rawMethods,
    _, ⟨⟩⟩ := EbnfValue.sequenceFlatView children input
  let genericPrefix := (EbnfValue.optionalView genericAtom rawGeneric).map
    (EbnfValue.ruleView .genericPrefix)
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let parameterData := (EbnfValue.optionalView
    parameterChild rawParameters).map EbnfValue.typeArgumentsView
  let parameters := parameterData.map fun value => value.2.1
  let methods := (EbnfValue.starView methodAtom rawMethods).map
    (EbnfValue.ruleView .classMethod)
  sourceLoc
    (ConsumedSpanWitness.compute file tokens origin finish owned ordered) {
      genericPrefix := genericPrefix
      main := EbnfValue.ruleView .typeAtom rawMain
      className := {
        span := name.span
        payload := name.identifierProjection.2
      }
      parameters := parameters
      methods := methods
    }

/-- Execute a contract declaration and preserve its ordered members. -/
def executeContractDeclRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .contractDecl)) :
    ContractDecl :=
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let memberAtom : EbnfExpr := .atom (.nonterminal .contractMember)
  let parameterChild : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .leftParen)), .list1 identifierAtom,
    .atom (.terminal (.symbol .rightParen))]
  let children : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .contractKw)), identifierAtom,
    .optional parameterChild,
    .atom (.terminal (.symbol .leftBrace)), .star memberAtom,
    .atom (.terminal (.symbol .rightBrace))]
  let ⟨_, rawName, rawParameters, _, rawMembers, _, ⟨⟩⟩ :=
    EbnfValue.sequenceFlatView children input
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let parameters := (EbnfValue.optionalView
    parameterChild rawParameters).map fun raw =>
      let parameterChildren : List EbnfExpr := [
        .atom (.terminal (.symbol .leftParen)), .list1 identifierAtom,
        .atom (.terminal (.symbol .rightParen))]
      let ⟨_, rawNames, _, ⟨⟩⟩ :=
        EbnfValue.sequenceFlatView parameterChildren raw
      (EbnfValue.list1View identifierAtom rawNames).map fun value =>
        let terminal := EbnfValue.terminalView
          (.category .identifier) value
        { span := terminal.span, payload := terminal.identifierProjection.2 }
  let members := (EbnfValue.starView memberAtom rawMembers).map
    (EbnfValue.ruleView .contractMember)
  sourceLoc
    (ConsumedSpanWitness.compute file tokens origin finish owned ordered) {
      name := { span := name.span, payload := name.identifierProjection.2 }
      parameters := parameters
      members := members
    }

/-- Execute an instance declaration with all modifiers, arguments, and methods. -/
def executeInstanceDeclRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .instanceDecl)) :
    InstanceDecl :=
  let genericAtom : EbnfExpr := .atom (.nonterminal .genericPrefix)
  let defaultAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .defaultKw))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let argumentChild : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .leftParen)), .list1 typeAtom,
    .atom (.terminal (.symbol .rightParen))]
  let methodAtom : EbnfExpr := .atom (.nonterminal .instanceMethod)
  let children : List EbnfExpr := [
    .optional genericAtom, .optional defaultAtom,
    .atom (.terminal (.hardKeyword .instanceKw)),
    .atom (.nonterminal .typeAtom),
    .atom (.terminal (.symbol .colon)),
    .atom (.nonterminal .qualifiedName), .optional argumentChild,
    .atom (.terminal (.symbol .leftBrace)), .star methodAtom,
    .atom (.terminal (.symbol .rightBrace))]
  let ⟨rawGeneric, rawDefault, _, rawMain, _, rawClassName,
    rawArguments, _, rawMethods, _, ⟨⟩⟩ :=
      EbnfValue.sequenceFlatView children input
  let genericPrefix := (EbnfValue.optionalView
    genericAtom rawGeneric).map (EbnfValue.ruleView .genericPrefix)
  let defaultToken := (EbnfValue.optionalView
    defaultAtom rawDefault).map
      (EbnfValue.terminalView (.hardKeyword .defaultKw))
  let parameters := (EbnfValue.optionalView
    argumentChild rawArguments).map fun raw =>
      let viewed := EbnfValue.sequence3View
        (.atom (.terminal (.symbol .leftParen))) (.list1 typeAtom)
        (.atom (.terminal (.symbol .rightParen))) raw
      (EbnfValue.list1View typeAtom viewed.2.1).map
        (EbnfValue.ruleView .type)
  let methods := (EbnfValue.starView methodAtom rawMethods).map
    (EbnfValue.ruleView .instanceMethod)
  sourceLoc
    (ConsumedSpanWitness.compute file tokens origin finish owned ordered) {
      genericPrefix := genericPrefix
      «default» := defaultToken.map fun terminal =>
        { span := terminal.span, payload := .defaultModifier }
      main := EbnfValue.ruleView .typeAtom rawMain
      className := EbnfValue.ruleView .qualifiedName rawClassName
      parameters := parameters
      methods := methods
    }

/-- Execute one algebraic-data constructor and its optional field types. -/
def executeDataConstructorRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .dataConstructor)) :
    DataConstructor :=
  let nameAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let arguments : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .leftParen)), .list1 typeAtom,
    .atom (.terminal (.symbol .rightParen))]
  let viewed := EbnfValue.sequence2View
    nameAtom (.optional arguments) input
  let name := EbnfValue.terminalView (.category .identifier) viewed.1
  let fields := (EbnfValue.optionalView arguments viewed.2).map fun raw =>
    let argumentView := EbnfValue.sequence3View
      (.atom (.terminal (.symbol .leftParen))) (.list1 typeAtom)
      (.atom (.terminal (.symbol .rightParen))) raw
    (EbnfValue.list1View typeAtom argumentView.2.1).map
      (EbnfValue.ruleView .type)
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered) {
    name := { span := name.span, payload := name.identifierProjection.2 }
    fields := fields
  }

/-- Execute a type-alias declaration and its optional type parameters. -/
def executeTypeAliasDeclRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .typeAliasDecl)) :
    TypeAliasDecl :=
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let parameterChild : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .leftParen)), .list1 identifierAtom,
    .atom (.terminal (.symbol .rightParen))]
  let children : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .typeKw)), identifierAtom,
    .optional parameterChild, .atom (.terminal (.symbol .equal)),
    .atom (.nonterminal .type),
    .atom (.terminal (.symbol .semicolon))]
  let ⟨_, rawName, rawOptional, _, rawBody, _, ⟨⟩⟩ :=
    EbnfValue.sequenceFlatView children input
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let parameters := (EbnfValue.optionalView parameterChild rawOptional).map
    fun rawParameters =>
      let parameterChildren : List EbnfExpr := [
        .atom (.terminal (.symbol .leftParen)), .list1 identifierAtom,
        .atom (.terminal (.symbol .rightParen))]
      let ⟨_, rawNames, _, ⟨⟩⟩ :=
        EbnfValue.sequenceFlatView parameterChildren rawParameters
      (EbnfValue.list1View identifierAtom rawNames).map fun raw =>
        let parameter := EbnfValue.terminalView
          (.category .identifier) raw
        { span := parameter.span,
          payload := parameter.identifierProjection.2 }
  sourceLoc
    (ConsumedSpanWitness.compute file tokens origin finish owned ordered) {
      name := { span := name.span, payload := name.identifierProjection.2 }
      parameters := parameters
      body := EbnfValue.ruleView .type rawBody
    }

/-- Execute one contract field declaration and its optional initializer. -/
def executeFieldDeclRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .fieldDecl)) : FieldDecl :=
  let nameAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let colonAtom : EbnfExpr := .atom (.terminal (.symbol .colon))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let equalAtom : EbnfExpr := .atom (.terminal (.symbol .equal))
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let initializerChild : EbnfExpr :=
    .sequence [equalAtom, expressionAtom]
  let semicolonAtom : EbnfExpr := .atom (.terminal (.symbol .semicolon))
  let children : List EbnfExpr := [nameAtom, colonAtom, typeAtom,
    .optional initializerChild, semicolonAtom]
  let viewed := EbnfValue.sequenceFlatView children input
  let name := EbnfValue.terminalView (.category .identifier) viewed.1
  let typeValue := EbnfValue.ruleView .type viewed.2.2.1
  let initializer := (EbnfValue.optionalView initializerChild
    viewed.2.2.2.1).map fun raw =>
      let pair := EbnfValue.sequence2View equalAtom expressionAtom raw
      (EbnfValue.terminalView (.symbol .equal) pair.1,
        EbnfValue.ruleView .expression pair.2, ())
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered) {
    name := { span := name.span, payload := name.identifierProjection.2 }
    type := typeValue
    initializer := initializer.map fun value => value.2.1
  }

/-- Execute a fallback declaration and its optional modifiers and return type. -/
def executeFallbackDeclRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .fallbackDecl)) :
    FallbackDecl :=
  let genericAtom : EbnfExpr := .atom (.nonterminal .genericPrefix)
  let publicAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .publicKw))
  let payableAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .payableKw))
  let parameterAtom : EbnfExpr := .atom (.nonterminal .parameter)
  let returnChild : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .arrow)), .atom (.nonterminal .type)]
  let children : List EbnfExpr := [.optional genericAtom,
    .optional publicAtom, .optional payableAtom,
    .atom (.terminal (.hardKeyword .fallbackKw)),
    .atom (.terminal (.symbol .leftParen)), .list0 parameterAtom,
    .atom (.terminal (.symbol .rightParen)), .optional returnChild,
    .atom (.nonterminal .body)]
  let ⟨rawGeneric, rawPublic, rawPayable, rawFallback, _, rawParameters,
    _, rawReturn, rawBody, ⟨⟩⟩ :=
    EbnfValue.sequenceFlatView children input
  let genericPrefix := (EbnfValue.optionalView genericAtom rawGeneric).map
    (EbnfValue.ruleView .genericPrefix)
  let publicToken := (EbnfValue.optionalView publicAtom rawPublic).map
    (EbnfValue.terminalView (.hardKeyword .publicKw))
  let payableToken := (EbnfValue.optionalView payableAtom rawPayable).map
    (EbnfValue.terminalView (.hardKeyword .payableKw))
  let fallbackKw := EbnfValue.terminalView
    (.hardKeyword .fallbackKw) rawFallback
  let parameters := (EbnfValue.list0View parameterAtom rawParameters).map
    (EbnfValue.ruleView .parameter)
  let returnValue := (EbnfValue.optionalView returnChild rawReturn).map
    fun raw =>
      let pair := EbnfValue.sequence2View
        (.atom (.terminal (.symbol .arrow)))
        (.atom (.nonterminal .type)) raw
      (EbnfValue.terminalView (.symbol .arrow) pair.1,
        EbnfValue.ruleView .type pair.2, ())
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered) {
    genericPrefix := genericPrefix
    «public» := publicToken.map fun terminal =>
      { span := terminal.span, payload := .publicModifier }
    payable := payableToken.map fun terminal =>
      { span := terminal.span, payload := .payableModifier }
    marker := { span := fallbackKw.span, payload := .fallbackName }
    parameters := parameters
    returnType := returnValue.map fun value => value.2.1
    body := EbnfValue.ruleView .body rawBody
  }

/-- Execute a contract-constructor declaration and its optional modifiers. -/
def executeContractConstructorDeclRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens
      (m2cV1.rhs .contractConstructorDecl)) :
    ContractConstructorDecl :=
  let publicAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .publicKw))
  let payableAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .payableKw))
  let parameterAtom : EbnfExpr := .atom (.nonterminal .parameter)
  let children : List EbnfExpr := [.optional publicAtom,
    .optional payableAtom,
    .atom (.terminal (.hardKeyword .constructorKw)),
    .atom (.terminal (.symbol .leftParen)), .list0 parameterAtom,
    .atom (.terminal (.symbol .rightParen)),
    .atom (.nonterminal .body)]
  let ⟨rawPublic, rawPayable, rawConstructor, _, rawParameters,
    _, rawBody, ⟨⟩⟩ := EbnfValue.sequenceFlatView children input
  let publicToken := (EbnfValue.optionalView publicAtom rawPublic).map
    (EbnfValue.terminalView (.hardKeyword .publicKw))
  let payableToken := (EbnfValue.optionalView payableAtom rawPayable).map
    (EbnfValue.terminalView (.hardKeyword .payableKw))
  let constructorKw := EbnfValue.terminalView
    (.hardKeyword .constructorKw) rawConstructor
  let parameters := (EbnfValue.list0View parameterAtom rawParameters).map
    (EbnfValue.ruleView .parameter)
  sourceLoc
      (ConsumedSpanWitness.compute file tokens origin finish owned ordered) {
    «public» := publicToken.map fun terminal =>
      { span := terminal.span, payload := .publicModifier }
    payable := payableToken.map fun terminal =>
      { span := terminal.span, payload := .payableModifier }
    marker := {
      span := constructorKw.span, payload := .contractConstructorName }
    parameters := parameters
    body := EbnfValue.ruleView .body rawBody
  }

/-- Decode the optional nonempty matched identifier targets of one pragma. -/
def pragmaTargetTerminals
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (.optional (.list1
      (.atom (.terminal (.category .identifier)))))) :
    Option (NonemptyList (MatchedTerminal file tokens
      (.category .identifier))) :=
  (EbnfValue.optionalView (.list1
    (.atom (.terminal (.category .identifier)))) input).map fun raw =>
      (EbnfValue.list1View
        (.atom (.terminal (.category .identifier))) raw).map
          (EbnfValue.terminalView (.category .identifier))

/-- Rebuilding computed pragma target terminals recovers their exact input. -/
theorem pragmaTargetTerminals_rebuild
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (.optional (.list1
      (.atom (.terminal (.category .identifier)))))) :
    EbnfValue.optional (.list1
      (.atom (.terminal (.category .identifier))))
      ((pragmaTargetTerminals input).map fun terminals =>
        EbnfValue.list1 (.atom (.terminal (.category .identifier)))
          (terminals.map (EbnfValue.terminalAtom
            (.category .identifier)))) = input := by
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let child : EbnfExpr := .list1 identifierAtom
  unfold pragmaTargetTerminals
  generalize selectedEq : EbnfValue.optionalView child input = selected
  cases selected with
  | none =>
      simp only [Option.map]
      calc
        _ = EbnfValue.optional child
            (EbnfValue.optionalView child input) := by rw [selectedEq]
        _ = input := EbnfValue.optional_of_view child input
  | some raw =>
      let values := EbnfValue.list1View identifierAtom raw
      have valuesEq : (values.map (EbnfValue.terminalView
          (.category .identifier))).map (EbnfValue.terminalAtom
            (.category .identifier)) = values := by
        cases values with
        | mk head tail =>
            simp only [NonemptyList.map, NonemptyList.mk.injEq]
            constructor
            · exact EbnfValue.terminal_of_view
                (.category .identifier) head
            · induction tail with
              | nil => rfl
              | cons next rest induction =>
                  simp [EbnfValue.terminal_of_view, induction]
      have rawEq : EbnfValue.list1 identifierAtom
          ((values.map (EbnfValue.terminalView
            (.category .identifier))).map (EbnfValue.terminalAtom
              (.category .identifier))) = raw := by
        rw [valuesEq]
        exact EbnfValue.list1_of_view identifierAtom raw
      simp only [Option.map]
      calc
        _ = EbnfValue.optional child (some raw) := by rw [rawEq]
        _ = EbnfValue.optional child
            (EbnfValue.optionalView child input) := by rw [selectedEq]
        _ = input := EbnfValue.optional_of_view child input

/-- Locate the computed pragma targets in source order. -/
def executePragmaTargets
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (.optional (.list1
      (.atom (.terminal (.category .identifier)))))) :
    List IdentifierOccurrence :=
  (pragmaTargetTerminals input).elim [] fun terminals =>
    let targets := terminals.map fun terminal =>
      { span := terminal.span, payload := terminal.identifierProjection.2 }
    targets.head :: targets.tail

/-- Execute one of the four fixed pragma declarations. -/
def executePragmaDeclRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .pragmaDecl)) : PragmaDecl :=
  let targetsAtom : EbnfExpr := .optional (.list1
    (.atom (.terminal (.category .identifier))))
  let branches : List EbnfExpr := [
    .sequence [.atom (.terminal (.hardKeyword .pragmaKw)),
      .atom (.terminal (.pragmaName .noCoverageCondition)), targetsAtom,
      .atom (.terminal (.symbol .semicolon))],
    .sequence [.atom (.terminal (.hardKeyword .pragmaKw)),
      .atom (.terminal (.pragmaName .noPattersonCondition)), targetsAtom,
      .atom (.terminal (.symbol .semicolon))],
    .sequence [.atom (.terminal (.hardKeyword .pragmaKw)),
      .atom (.terminal (.pragmaName .noBoundedVariableCondition)), targetsAtom,
      .atom (.terminal (.symbol .semicolon))],
    .sequence [.atom (.terminal (.hardKeyword .pragmaKw)),
      .atom (.terminal (.pragmaName .noGenericInstanceFor)), targetsAtom,
      .atom (.terminal (.symbol .semicolon))]]
  let witness := shallowRootWitness file tokens origin finish owned ordered
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence4View
        (.atom (.terminal (.hardKeyword .pragmaKw)))
        (.atom (.terminal (.pragmaName .noCoverageCondition))) targetsAtom
        (.atom (.terminal (.symbol .semicolon))) raw
      let kindToken := EbnfValue.terminalView
        (.pragmaName .noCoverageCondition) viewed.2.1
      sourceLoc witness {
        kind := { span := kindToken.span, payload := .noCoverageCondition }
        targets := executePragmaTargets viewed.2.2.1
      }
  | ⟨⟨1, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence4View
        (.atom (.terminal (.hardKeyword .pragmaKw)))
        (.atom (.terminal (.pragmaName .noPattersonCondition))) targetsAtom
        (.atom (.terminal (.symbol .semicolon))) raw
      let kindToken := EbnfValue.terminalView
        (.pragmaName .noPattersonCondition) viewed.2.1
      sourceLoc witness {
        kind := { span := kindToken.span, payload := .noPattersonCondition }
        targets := executePragmaTargets viewed.2.2.1
      }
  | ⟨⟨2, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence4View
        (.atom (.terminal (.hardKeyword .pragmaKw)))
        (.atom (.terminal (.pragmaName .noBoundedVariableCondition)))
        targetsAtom (.atom (.terminal (.symbol .semicolon))) raw
      let kindToken := EbnfValue.terminalView
        (.pragmaName .noBoundedVariableCondition) viewed.2.1
      sourceLoc witness {
        kind := {
          span := kindToken.span, payload := .noBoundedVariableCondition }
        targets := executePragmaTargets viewed.2.2.1
      }
  | ⟨⟨3, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence4View
        (.atom (.terminal (.hardKeyword .pragmaKw)))
        (.atom (.terminal (.pragmaName .noGenericInstanceFor))) targetsAtom
        (.atom (.terminal (.symbol .semicolon))) raw
      let kindToken := EbnfValue.terminalView
        (.pragmaName .noGenericInstanceFor) viewed.2.1
      sourceLoc witness {
        kind := { span := kindToken.span, payload := .noGenericInstanceFor }
        targets := executePragmaTargets viewed.2.2.1
      }

/-- Execute a universal clause with its optional predicate context. -/
def executeGenericPrefixRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .genericPrefix)) :
    GenericPrefix :=
  let contextChildren : List EbnfExpr := [
    .atom (.nonterminal .predicateList),
    .atom (.terminal (.symbol .fatArrow))]
  let children : List EbnfExpr := [
    .atom (.nonterminal .forallClause),
    .optional (.sequence contextChildren)]
  let viewed := EbnfValue.sequenceFlatView children input
  let forallClause := EbnfValue.ruleView .forallClause viewed.1
  let context := (EbnfValue.optionalView
    (.sequence contextChildren) viewed.2.1).map fun raw =>
      let pair := EbnfValue.sequenceFlatView contextChildren raw
      EbnfValue.ruleView .predicateList pair.1
  sourceLoc
    (ConsumedSpanWitness.compute file tokens origin finish owned ordered) {
      forallClause := forallClause
      context := context
    }

/-- Execute a universal clause from its nonempty ordered binder sequence. -/
def executeForallClauseRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .forallClause)) :
    ForallClause :=
  let tail := EbnfValue.rulePairTailExpr .optionalComma .forallBinder
  let viewed := EbnfValue.sequence4View
    (.atom (.terminal (.hardKeyword .forallKw)))
    (.atom (.nonterminal .forallBinder)) (.star tail)
    (.atom (.terminal (.symbol .dot))) input
  let first := EbnfValue.ruleView .forallBinder viewed.2.1
  let rest := (EbnfValue.starView tail viewed.2.2.1).map
    (EbnfValue.rulePairTailView .optionalComma .forallBinder)
  sourceLoc
    (ConsumedSpanWitness.compute file tokens origin finish owned ordered) {
      binders := {
        head := first
        tail := rest.map Prod.snd
      }
    }

/-- Execute one universal binder, including its optional class arguments. -/
def executeForallBinderRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .forallBinder)) :
    ForallBinder :=
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let argumentChildren : List EbnfExpr := [
    .atom (.terminal (.symbol .leftParen)), .list1 typeAtom,
    .atom (.terminal (.symbol .rightParen))]
  let argumentChild : EbnfExpr := .sequence argumentChildren
  let boundedChildren : List EbnfExpr := [identifierAtom,
    .atom (.terminal (.symbol .colon)),
    .atom (.nonterminal .qualifiedName), .optional argumentChild]
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish owned ordered
  match EbnfValue.choice2View identifierAtom
      (.sequence boundedChildren) input with
  | .inl rawName =>
      let name := EbnfValue.terminalView
        (.category .identifier) rawName
      sourceLoc witness (.bare ({
        span := name.span
        payload := name.identifierProjection.2 } : IdentifierOccurrence))
  | .inr rawBounded =>
      let viewed := EbnfValue.sequenceFlatView boundedChildren rawBounded
      let name := EbnfValue.terminalView
        (.category .identifier) viewed.1
      let arguments := (EbnfValue.optionalView argumentChild
        viewed.2.2.2.1).map fun rawArguments =>
          let argumentView := EbnfValue.sequenceFlatView
            argumentChildren rawArguments
          (EbnfValue.list1View typeAtom argumentView.2.1).map
            (EbnfValue.ruleView .type)
      sourceLoc witness (.bounded
        ({
          span := name.span
          payload := name.identifierProjection.2
        } : IdentifierOccurrence)
        (EbnfValue.ruleView .qualifiedName viewed.2.2.1) arguments)

/-- Execute one exported item and its optional constructor selection. -/
def executeExportItemRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .exportItem)) :
    ExportItem :=
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let selectionAtom : EbnfExpr :=
    .atom (.nonterminal .constructorSelection)
  let viewed := EbnfValue.sequence2View
    identifierAtom (.optional selectionAtom) input
  let name := EbnfValue.terminalView
    (.category .identifier) viewed.1
  let selection := (EbnfValue.optionalView selectionAtom viewed.2).map
    (EbnfValue.ruleView .constructorSelection)
  sourceLoc
      (ConsumedSpanWitness.compute file tokens origin finish owned ordered) {
    name := { span := name.span, payload := name.identifierProjection.2 }
    constructors := selection
  }

/-- Execute constructor selections attached to exported items. -/
def executeConstructorSelectionRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens
      (m2cV1.rhs .constructorSelection)) : ConstructorSelection :=
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let allChildren : List EbnfExpr := [
    .atom (.terminal (.symbol .leftParen)),
    .atom (.terminal (.symbol .star)),
    .atom (.terminal (.symbol .rightParen))]
  let namedChildren : List EbnfExpr := [
    .atom (.terminal (.symbol .leftParen)), .list1 identifierAtom,
    .atom (.terminal (.symbol .rightParen))]
  let branches : List EbnfExpr :=
    [.sequence allChildren, .sequence namedChildren]
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish owned ordered
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequenceFlatView allChildren raw
      let star := EbnfValue.terminalView (.symbol .star) viewed.2.1
      sourceLoc witness (.all {
        span := star.span
        payload := .wildcard
      })
  | ⟨⟨1, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequenceFlatView namedChildren raw
      let names := (EbnfValue.list1View identifierAtom viewed.2.1).map
        fun rawName =>
          let name := EbnfValue.terminalView
            (.category .identifier) rawName
          ({ span := name.span, payload := name.identifierProjection.2 } :
            IdentifierOccurrence)
      sourceLoc witness (.named names)

/-- Execute one import-hiding clause and its ordered identifier names. -/
def executeHidingClauseRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .hidingClause)) :
    HidingClause :=
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let viewed := EbnfValue.sequence4View
    (.atom (.terminal (.hardKeyword .hidingKw)))
    (.atom (.terminal (.symbol .leftBrace)))
    (.list0 identifierAtom)
    (.atom (.terminal (.symbol .rightBrace))) input
  let names := (EbnfValue.list0View identifierAtom viewed.2.2.1).map
    fun rawName =>
      let name := EbnfValue.terminalView
        (.category .identifier) rawName
      ({ span := name.span, payload := name.identifierProjection.2 } :
        IdentifierOccurrence)
  sourceLoc
    (ConsumedSpanWitness.compute file tokens origin finish owned ordered) {
      names := names
    }

/-- Execute one wildcard, named, or aliased import-selector entry. -/
def executeImportEntryRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .importEntry)) :
    ImportSelectorEntry :=
  let starAtom : EbnfExpr :=
    .atom (.terminal (.symbol .star))
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let aliasChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .asKw)), identifierAtom]
  let namedChildren : List EbnfExpr := [
    identifierAtom, .optional (.sequence aliasChildren)]
  let witness := shallowRootWitness file tokens origin finish owned ordered
  match EbnfValue.choice2View starAtom (.sequence namedChildren) input with
  | .inl raw =>
      let star := EbnfValue.terminalView (.symbol .star) raw
      sourceLoc witness (.wildcard {
        span := star.span
        payload := .wildcard
      })
  | .inr raw =>
      let viewed := EbnfValue.sequence2View identifierAtom
        (.optional (.sequence aliasChildren)) raw
      let name := EbnfValue.terminalView
        (.category .identifier) viewed.1
      let alias := (EbnfValue.optionalView (.sequence aliasChildren)
        viewed.2).map fun rawAlias =>
          let aliasViewed := EbnfValue.sequence2View
            (.atom (.terminal (.hardKeyword .asKw)))
            identifierAtom rawAlias
          let aliasName := EbnfValue.terminalView
            (.category .identifier) aliasViewed.2
          (⟨aliasName.span, aliasName.identifierProjection.2⟩ :
            IdentifierOccurrence)
      sourceLoc witness (.named
        ⟨name.span, name.identifierProjection.2⟩ alias)

/-- Execute one wildcard, item, or module-wildcard local export entry. -/
def executeLocalExportEntryRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .localExportEntry)) :
    ExportEntry :=
  let starAtom : EbnfExpr :=
    .atom (.terminal (.symbol .star))
  let allChildren : List EbnfExpr := [
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .dot)), starAtom]
  let branches : List EbnfExpr := [
    starAtom, .atom (.nonterminal .exportItem), .sequence allChildren]
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish owned ordered
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      let star := EbnfValue.terminalView (.symbol .star) raw
      sourceLoc witness (.wildcard {
        span := star.span
        payload := .wildcard
      })
  | ⟨⟨1, _⟩, raw⟩ =>
      sourceLoc witness (.item (EbnfValue.ruleView .exportItem raw))
  | ⟨⟨2, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequenceFlatView allChildren raw
      let reference := EbnfValue.ruleView .moduleRef viewed.1
      let star := EbnfValue.terminalView (.symbol .star) viewed.2.2.1
      sourceLoc witness (.allFrom reference {
        span := star.span
        payload := .wildcard
      })

/-- Execute one remote export selector entry. -/
def executeRemoteExportEntryRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .remoteExportEntry)) :
    RemoteExportEntry :=
  let starAtom : EbnfExpr :=
    .atom (.terminal (.symbol .star))
  let itemAtom : EbnfExpr :=
    .atom (.nonterminal .exportItem)
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish owned ordered
  match EbnfValue.choice2View starAtom itemAtom input with
  | .inl raw =>
      let star := EbnfValue.terminalView (.symbol .star) raw
      sourceLoc witness (.wildcard {
        span := star.span
        payload := .wildcard
      })
  | .inr raw =>
      sourceLoc witness (.item (EbnfValue.ruleView .exportItem raw))

/-- Execute a braced body from its ordered statement values. -/
def executeBodyRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .body)) : Body :=
  let statementAtom : EbnfExpr := .atom (.nonterminal .statement)
  let viewed := EbnfValue.sequence3View
    (.atom (.terminal (.symbol .leftBrace))) (.star statementAtom)
    (.atom (.terminal (.symbol .rightBrace))) input
  let openBrace := EbnfValue.terminalView (.symbol .leftBrace) viewed.1
  let statements := (EbnfValue.starView statementAtom viewed.2.1).map
    (EbnfValue.ruleView .statement)
  let closeBrace := EbnfValue.terminalView (.symbol .rightBrace) viewed.2.2
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered) {
    origin := .braced openBrace.span closeBrace.span
    statements := statements
  }

/-- Execute a type root, including recursive compile-time and arrow types. -/
def executeTypeRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .type)) : TypeExpr :=
  let comptimeAtom : EbnfExpr :=
    .atom (.terminal (.contextualKeyword .comptimeKw))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let atomAtom : EbnfExpr := .atom (.nonterminal .typeAtom)
  let arrowAtom : EbnfExpr := .atom (.terminal (.symbol .arrow))
  let arrowSeq : EbnfExpr := .sequence [arrowAtom, typeAtom]
  let comptimeBranch : EbnfExpr := .sequence [comptimeAtom, typeAtom]
  let plainBranch : EbnfExpr :=
    .sequence [atomAtom, .optional arrowSeq]
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish owned ordered
  match EbnfValue.choice2View comptimeBranch plainBranch input with
  | .inl raw =>
      let viewed := EbnfValue.sequence2View comptimeAtom typeAtom raw
      let comptime := EbnfValue.terminalView
        (.contextualKeyword .comptimeKw) viewed.1
      let inner := EbnfValue.ruleView .type viewed.2
      sourceLoc witness (.comptime
        { span := comptime.span, payload := .comptimeModifier } inner)
  | .inr raw =>
      let viewed := EbnfValue.sequence2View
        atomAtom (.optional arrowSeq) raw
      let domain := EbnfValue.ruleView .typeAtom viewed.1
      match EbnfValue.optionalView arrowSeq viewed.2 with
      | none => domain
      | some rawArrow =>
          let arrowViewed := EbnfValue.sequence2View
            arrowAtom typeAtom rawArrow
          let codomain := EbnfValue.ruleView .type arrowViewed.2
          sourceLoc witness (.function domain codomain)

/-- Decode every semantic component of a `for` statement root. -/
def executeForStatementRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .forStatement)) :
    Statement :=
  let initAtom : EbnfExpr := .atom (.nonterminal .forInitItem)
  let postAtom : EbnfExpr := .atom (.nonterminal .forPostItem)
  let children : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .forKw)),
    .atom (.terminal (.symbol .leftParen)), .list0 initAtom,
    .atom (.terminal (.symbol .semicolon)),
    .atom (.nonterminal .expression),
    .atom (.terminal (.symbol .semicolon)), .list0 postAtom,
    .atom (.terminal (.symbol .rightParen)),
    .atom (.nonterminal .body)]
  let ⟨_, _, rawInit, _, rawCondition, _, rawPost, _, rawBody, ⟨⟩⟩ :=
    EbnfValue.sequenceFlatView children input
  let initializers := (EbnfValue.list0View initAtom rawInit).map
    (EbnfValue.ruleView .forInitItem)
  let post := (EbnfValue.list0View postAtom rawPost).map
    (EbnfValue.ruleView .forPostItem)
  sourceLoc (ConsumedSpanWitness.compute
      file tokens origin finish owned ordered)
    (.forLoop initializers (EbnfValue.ruleView .expression rawCondition)
      post (EbnfValue.ruleView .body rawBody))

/-- Execute a `for` initializer from its selected typed alternative. -/
def executeForInitItemRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .forInitItem)) :
    ForInitItem :=
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let operatorAtom : EbnfExpr := .atom (.nonterminal .assignmentOperator)
  let branches : List EbnfExpr := [
    .atom (.nonterminal .letBinding),
    .sequence [expressionAtom, operatorAtom, expressionAtom],
    expressionAtom]
  let witness := shallowRootWitness file tokens origin finish owned ordered
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      sourceLoc witness (.letBinding (EbnfValue.ruleView .letBinding raw))
  | ⟨⟨1, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence3View
        expressionAtom operatorAtom expressionAtom raw
      sourceLoc witness (.assignment
        (EbnfValue.ruleView .assignmentOperator viewed.2.1)
        (EbnfValue.ruleView .expression viewed.1)
        (EbnfValue.ruleView .expression viewed.2.2))
  | ⟨⟨2, _⟩, raw⟩ =>
      sourceLoc witness (.expression (EbnfValue.ruleView .expression raw))

/-- Execute a `for` post item from its selected typed alternative. -/
def executeForPostItemRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .forPostItem)) :
    ForPostItem :=
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let operatorAtom : EbnfExpr := .atom (.nonterminal .assignmentOperator)
  let branches : List EbnfExpr := [
    .sequence [expressionAtom, operatorAtom, expressionAtom], expressionAtom]
  let witness := shallowRootWitness file tokens origin finish owned ordered
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence3View
        expressionAtom operatorAtom expressionAtom raw
      sourceLoc witness (.assignment
        (EbnfValue.ruleView .assignmentOperator viewed.2.1)
        (EbnfValue.ruleView .expression viewed.1)
        (EbnfValue.ruleView .expression viewed.2.2))
  | ⟨⟨1, _⟩, raw⟩ =>
      sourceLoc witness (.expression (EbnfValue.ruleView .expression raw))

/-- Execute an expression statement from its terminated or terminal branch. -/
def executeExpressionStatementRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .expressionStatement)) :
    Statement :=
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let semicolonAtom : EbnfExpr := .atom (.terminal (.symbol .semicolon))
  let branches : List EbnfExpr := [
    .sequence [expressionAtom, semicolonAtom],
    .atom (.nonterminal .terminalExpression)]
  let witness := shallowRootWitness file tokens origin finish owned ordered
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence2View expressionAtom semicolonAtom raw
      let semicolon := EbnfValue.terminalView (.symbol .semicolon) viewed.2
      sourceLoc witness (.expression
        (EbnfValue.ruleView .expression viewed.1) (some semicolon.span))
  | ⟨⟨1, _⟩, raw⟩ =>
      sourceLoc witness (.expression
        (EbnfValue.ruleView .terminalExpression raw) none)

/-- Execute a contract member from its selected declaration alternative. -/
def executeContractMemberRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .contractMember)) :
    ContractMember :=
  let witness := shallowRootWitness file tokens origin finish owned ordered
  match EbnfValue.choiceView [
      .atom (.nonterminal .dataDecl),
      .atom (.nonterminal .typeAliasDecl),
      .atom (.nonterminal .fieldDecl),
      .atom (.nonterminal .functionDecl),
      .atom (.nonterminal .fallbackDecl),
      .atom (.nonterminal .contractConstructorDecl)] input with
  | ⟨⟨0, _⟩, raw⟩ =>
      sourceLoc witness (.dataDecl (EbnfValue.ruleView .dataDecl raw))
  | ⟨⟨1, _⟩, raw⟩ =>
      sourceLoc witness (.typeAlias (EbnfValue.ruleView .typeAliasDecl raw))
  | ⟨⟨2, _⟩, raw⟩ =>
      sourceLoc witness (.field (EbnfValue.ruleView .fieldDecl raw))
  | ⟨⟨3, _⟩, raw⟩ =>
      sourceLoc witness (.function (EbnfValue.ruleView .functionDecl raw))
  | ⟨⟨4, _⟩, raw⟩ =>
      sourceLoc witness (.fallback (EbnfValue.ruleView .fallbackDecl raw))
  | ⟨⟨5, _⟩, raw⟩ => sourceLoc witness
      (.constructor (EbnfValue.ruleView .contractConstructorDecl raw))

namespace EbnfValue

/-- A grouped pair of fixed grammar terminals. -/
def terminalPairTailExpr
    (first second : TerminalSymbol) : EbnfExpr :=
  .group (.sequence [
    .atom (.terminal first), .atom (.terminal second)])

/-- Decode one grouped pair of fixed grammar terminals. -/
def terminalPairTailView
    {file : WorkspaceFile} {tokens : List Token}
    (first second : TerminalSymbol)
    (input : EbnfValue file tokens (terminalPairTailExpr first second)) :
    MatchedTerminal file tokens first × MatchedTerminal file tokens second :=
  let firstAtom : EbnfExpr := .atom (.terminal first)
  let secondAtom : EbnfExpr := .atom (.terminal second)
  let rawSequence := groupView (.sequence [firstAtom, secondAtom]) input
  let viewed := sequence2View firstAtom secondAtom rawSequence
  (terminalView first viewed.1, terminalView second viewed.2)

/-- Rebuild one grouped pair of fixed grammar terminals. -/
def terminalPairTailValue
    {file : WorkspaceFile} {tokens : List Token}
    (first second : TerminalSymbol)
    (value : MatchedTerminal file tokens first ×
      MatchedTerminal file tokens second) :
    EbnfValue file tokens (terminalPairTailExpr first second) :=
  let firstAtom : EbnfExpr := .atom (.terminal first)
  let secondAtom : EbnfExpr := .atom (.terminal second)
  group (.sequence [firstAtom, secondAtom])
    (sequence [firstAtom, secondAtom]
      (EbnfValues.cons firstAtom [secondAtom]
        (terminalAtom first value.1)
        (EbnfValues.cons secondAtom [] (terminalAtom second value.2)
          EbnfValues.nil)))

/-- Rebuilding a viewed terminal pair recovers its original value. -/
theorem terminalPairTailValue_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (first second : TerminalSymbol)
    (input : EbnfValue file tokens (terminalPairTailExpr first second)) :
    terminalPairTailValue first second
      (terminalPairTailView first second input) = input := by
  let firstAtom : EbnfExpr := .atom (.terminal first)
  let secondAtom : EbnfExpr := .atom (.terminal second)
  let rawSequence := groupView (.sequence [firstAtom, secondAtom]) input
  let viewed := sequence2View firstAtom secondAtom rawSequence
  have firstEq := terminal_of_view first viewed.1
  have secondEq := terminal_of_view second viewed.2
  have sequenceEq := sequence2_of_view firstAtom secondAtom rawSequence
  have groupEq := group_of_view
    (.sequence [firstAtom, secondAtom]) input
  change group (.sequence [firstAtom, secondAtom])
    (sequence [firstAtom, secondAtom]
      (EbnfValues.cons firstAtom [secondAtom]
        (terminalAtom first (terminalView first viewed.1))
        (EbnfValues.cons secondAtom []
          (terminalAtom second (terminalView second viewed.2))
          EbnfValues.nil))) = input
  rw [firstEq, secondEq, sequenceEq]
  exact groupEq

/-- The common grouped tail of a fixed-operator infix level. -/
def fixedInfixTailExpr
    (terminal : TerminalSymbol) (operand : GrammarRuleId) : EbnfExpr :=
  .group (.sequence [
    .atom (.terminal terminal), .atom (.nonterminal operand)])

/-- Decode one fixed-operator infix tail. -/
def fixedInfixTailView
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol) (operand : GrammarRuleId)
    (input : EbnfValue file tokens (fixedInfixTailExpr terminal operand)) :
    MatchedTerminal file tokens terminal × RuleValue operand :=
  let terminalAtom : EbnfExpr := .atom (.terminal terminal)
  let operandAtom : EbnfExpr := .atom (.nonterminal operand)
  let rawSequence := groupView (.sequence [terminalAtom, operandAtom]) input
  let viewed := sequence2View terminalAtom operandAtom rawSequence
  (terminalView terminal viewed.1, ruleView operand viewed.2)

/-- Rebuild one fixed-operator infix tail from its semantic view. -/
def fixedInfixTailValue
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol) (operand : GrammarRuleId)
    (value : MatchedTerminal file tokens terminal × RuleValue operand) :
    EbnfValue file tokens (fixedInfixTailExpr terminal operand) :=
  let terminalAtom : EbnfExpr := .atom (.terminal terminal)
  let operandAtom : EbnfExpr := .atom (.nonterminal operand)
  group (.sequence [terminalAtom, operandAtom])
    (sequence [terminalAtom, operandAtom]
      (EbnfValues.cons terminalAtom [operandAtom]
        (EbnfValue.terminalAtom terminal value.1)
        (EbnfValues.cons operandAtom [] (ruleAtom operand value.2)
          EbnfValues.nil)))

/-- Rebuilding a fixed-operator tail view recovers the original value. -/
theorem fixedInfixTailValue_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol) (operand : GrammarRuleId)
    (input : EbnfValue file tokens (fixedInfixTailExpr terminal operand)) :
    fixedInfixTailValue terminal operand
      (fixedInfixTailView terminal operand input) = input := by
  let terminalAtom : EbnfExpr := .atom (.terminal terminal)
  let operandAtom : EbnfExpr := .atom (.nonterminal operand)
  let rawSequence := groupView (.sequence [terminalAtom, operandAtom]) input
  let viewed := sequence2View terminalAtom operandAtom rawSequence
  have terminalEq := terminal_of_view terminal viewed.1
  have operandEq := rule_of_view operand viewed.2
  have sequenceEq := sequence2_of_view
    terminalAtom operandAtom rawSequence
  have groupEq := group_of_view
    (.sequence [terminalAtom, operandAtom]) input
  change group (.sequence [terminalAtom, operandAtom])
    (sequence [terminalAtom, operandAtom]
      (EbnfValues.cons terminalAtom [operandAtom]
        (EbnfValue.terminalAtom terminal (terminalView terminal viewed.1))
        (EbnfValues.cons operandAtom []
          (ruleAtom operand (ruleView operand viewed.2)) EbnfValues.nil))) = input
  rw [terminalEq, operandEq, sequenceEq]
  exact groupEq

/-- The common source-rule EBNF shape of a fixed-operator infix level. -/
def fixedInfixRootExpr
    (terminal : TerminalSymbol) (operand : GrammarRuleId) : EbnfExpr :=
  .sequence [
    .atom (.nonterminal operand), .star (fixedInfixTailExpr terminal operand)]

/-- Decode a complete fixed-operator infix level. -/
def fixedInfixRootView
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol) (operand : GrammarRuleId)
    (input : EbnfValue file tokens (fixedInfixRootExpr terminal operand)) :
    RuleValue operand ×
      List (MatchedTerminal file tokens terminal × RuleValue operand) :=
  let operandAtom : EbnfExpr := .atom (.nonterminal operand)
  let tail := fixedInfixTailExpr terminal operand
  let viewed := sequence2View operandAtom (.star tail) input
  (ruleView operand viewed.1,
    (starView tail viewed.2).map (fixedInfixTailView terminal operand))

/-- Rebuild a complete fixed-operator infix level from its semantic view. -/
def fixedInfixRootValue
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol) (operand : GrammarRuleId)
    (value : RuleValue operand ×
      List (MatchedTerminal file tokens terminal × RuleValue operand)) :
    EbnfValue file tokens (fixedInfixRootExpr terminal operand) :=
  let operandAtom : EbnfExpr := .atom (.nonterminal operand)
  let tail := fixedInfixTailExpr terminal operand
  sequence [operandAtom, .star tail]
    (EbnfValues.cons operandAtom [.star tail]
      (ruleAtom operand value.1)
      (EbnfValues.cons (.star tail) []
        (star tail (value.2.map (fixedInfixTailValue terminal operand)))
        EbnfValues.nil))

/-- Rebuilding a fixed-operator root view recovers the original value. -/
theorem fixedInfixRootValue_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol) (operand : GrammarRuleId)
    (input : EbnfValue file tokens (fixedInfixRootExpr terminal operand)) :
    fixedInfixRootValue terminal operand
      (fixedInfixRootView terminal operand input) = input := by
  let operandAtom : EbnfExpr := .atom (.nonterminal operand)
  let tail := fixedInfixTailExpr terminal operand
  let viewed := sequence2View operandAtom (.star tail) input
  let rawTails := starView tail viewed.2
  have operandEq := rule_of_view operand viewed.1
  have tailsEq :
      (rawTails.map (fixedInfixTailView terminal operand)).map
          (fixedInfixTailValue terminal operand) = rawTails := by
    induction rawTails with
    | nil => rfl
    | cons head rest induction =>
        simp [fixedInfixTailValue_of_view, induction]
  have starEq := star_of_view tail viewed.2
  have sequenceEq := sequence2_of_view operandAtom (.star tail) input
  change sequence [operandAtom, .star tail]
    (EbnfValues.cons operandAtom [.star tail]
      (ruleAtom operand (ruleView operand viewed.1))
      (EbnfValues.cons (.star tail) []
        (star tail
          ((rawTails.map (fixedInfixTailView terminal operand)).map
            (fixedInfixTailValue terminal operand))) EbnfValues.nil)) = input
  rw [operandEq, tailsEq, starEq]
  exact sequenceEq

/-- The grouped `+` or `-` tail of the additive level. -/
def additiveTailExpr : EbnfExpr :=
  .group (.sequence [
    .group (.choice [
      .atom (.terminal (.symbol .plus)),
      .atom (.terminal (.symbol .minus))]),
    .atom (.nonterminal .multiplicative)])

/-- Decode one additive tail into its selected operator and right operand. -/
def additiveTailView
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens additiveTailExpr) :
    Sum
      (MatchedTerminal file tokens (.symbol .plus))
      (MatchedTerminal file tokens (.symbol .minus)) × Expression :=
  let plusAtom : EbnfExpr := .atom (.terminal (.symbol .plus))
  let minusAtom : EbnfExpr := .atom (.terminal (.symbol .minus))
  let operatorExpr : EbnfExpr := .group (.choice [plusAtom, minusAtom])
  let operandAtom : EbnfExpr := .atom (.nonterminal .multiplicative)
  let rawSequence := groupView (.sequence [operatorExpr, operandAtom]) input
  let viewed := sequence2View operatorExpr operandAtom rawSequence
  let rawChoice := groupView (.choice [plusAtom, minusAtom]) viewed.1
  let operator := match choice2View plusAtom minusAtom rawChoice with
    | .inl raw => Sum.inl (terminalView (.symbol .plus) raw)
    | .inr raw => Sum.inr (terminalView (.symbol .minus) raw)
  (operator, ruleView .multiplicative viewed.2)

/-- Rebuild one additive tail from its semantic view. -/
def additiveTailValue
    {file : WorkspaceFile} {tokens : List Token}
    (value : Sum
      (MatchedTerminal file tokens (.symbol .plus))
      (MatchedTerminal file tokens (.symbol .minus)) × Expression) :
    EbnfValue file tokens additiveTailExpr :=
  let plusAtom : EbnfExpr := .atom (.terminal (.symbol .plus))
  let minusAtom : EbnfExpr := .atom (.terminal (.symbol .minus))
  let operatorExpr : EbnfExpr := .group (.choice [plusAtom, minusAtom])
  let operandAtom : EbnfExpr := .atom (.nonterminal .multiplicative)
  group (.sequence [operatorExpr, operandAtom])
    (sequence [operatorExpr, operandAtom]
      (EbnfValues.cons operatorExpr [operandAtom]
        (group (.choice [plusAtom, minusAtom])
          (match value.1 with
          | .inl plus => choice [plusAtom, minusAtom]
              ⟨0, terminalAtom (.symbol .plus) plus⟩
          | .inr minus => choice [plusAtom, minusAtom]
              ⟨1, terminalAtom (.symbol .minus) minus⟩))
        (EbnfValues.cons operandAtom []
          (ruleAtom .multiplicative value.2) EbnfValues.nil)))

/-- Rebuilding a decoded additive tail recovers its typed input. -/
theorem additiveTailValue_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens additiveTailExpr) :
    additiveTailValue (additiveTailView input) = input := by
  let plusAtom : EbnfExpr := .atom (.terminal (.symbol .plus))
  let minusAtom : EbnfExpr := .atom (.terminal (.symbol .minus))
  let operatorExpr : EbnfExpr := .group (.choice [plusAtom, minusAtom])
  let operandAtom : EbnfExpr := .atom (.nonterminal .multiplicative)
  let rawSequence := groupView (.sequence [operatorExpr, operandAtom]) input
  let viewed := sequence2View operatorExpr operandAtom rawSequence
  let rawChoice := groupView (.choice [plusAtom, minusAtom]) viewed.1
  generalize choiceEq : choice2View plusAtom minusAtom rawChoice = selected
  have choiceValueEq := choice2_of_view plusAtom minusAtom rawChoice
  rw [choiceEq] at choiceValueEq
  have operatorEq := group_of_view (.choice [plusAtom, minusAtom]) viewed.1
  have operandEq := rule_of_view .multiplicative viewed.2
  have sequenceEq := sequence2_of_view operatorExpr operandAtom rawSequence
  have outerGroupEq := group_of_view
    (.sequence [operatorExpr, operandAtom]) input
  cases selected with
  | inl raw =>
      have terminalEq := terminal_of_view (.symbol .plus) raw
      have choiceRebuildEq : choice [plusAtom, minusAtom]
          ⟨(0 : Fin 2), raw⟩ = rawChoice := by
        simpa using choiceValueEq
      simp only [additiveTailValue, additiveTailView, plusAtom, minusAtom,
        operatorExpr, operandAtom, rawSequence, viewed, rawChoice, choiceEq]
      rw [terminalEq, choiceRebuildEq, operatorEq, operandEq, sequenceEq]
      exact outerGroupEq
  | inr raw =>
      have terminalEq := terminal_of_view (.symbol .minus) raw
      have choiceRebuildEq : choice [plusAtom, minusAtom]
          ⟨(1 : Fin 2), raw⟩ = rawChoice := by
        simpa using choiceValueEq
      simp only [additiveTailValue, additiveTailView, plusAtom, minusAtom,
        operatorExpr, operandAtom, rawSequence, viewed, rawChoice, choiceEq]
      rw [terminalEq, choiceRebuildEq, operatorEq, operandEq, sequenceEq]
      exact outerGroupEq

/-- The grouped `*`, `/`, or `%` tail of the multiplicative level. -/
def multiplicativeTailExpr : EbnfExpr :=
  .group (.sequence [
    .group (.choice [
      .atom (.terminal (.symbol .star)),
      .atom (.terminal (.symbol .slash)),
      .atom (.terminal (.symbol .percent))]),
    .atom (.nonterminal .prefix)])

/-- Decode one multiplicative tail into its operator and right operand. -/
def multiplicativeTailView
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens multiplicativeTailExpr) :
    Sum
      (MatchedTerminal file tokens (.symbol .star))
      (Sum
        (MatchedTerminal file tokens (.symbol .slash))
        (MatchedTerminal file tokens (.symbol .percent))) × Expression :=
  let starAtom : EbnfExpr := .atom (.terminal (.symbol .star))
  let slashAtom : EbnfExpr := .atom (.terminal (.symbol .slash))
  let percentAtom : EbnfExpr := .atom (.terminal (.symbol .percent))
  let operatorExpr : EbnfExpr :=
    .group (.choice [starAtom, slashAtom, percentAtom])
  let operandAtom : EbnfExpr := .atom (.nonterminal .prefix)
  let rawSequence := groupView (.sequence [operatorExpr, operandAtom]) input
  let viewed := sequence2View operatorExpr operandAtom rawSequence
  let rawChoice := groupView
    (.choice [starAtom, slashAtom, percentAtom]) viewed.1
  let operator := match choice3View starAtom slashAtom percentAtom rawChoice with
    | .inl raw => Sum.inl (terminalView (.symbol .star) raw)
    | .inr (.inl raw) =>
        Sum.inr (Sum.inl (terminalView (.symbol .slash) raw))
    | .inr (.inr raw) =>
        Sum.inr (Sum.inr (terminalView (.symbol .percent) raw))
  (operator, ruleView .prefix viewed.2)

/-- Rebuild one multiplicative tail from its semantic view. -/
def multiplicativeTailValue
    {file : WorkspaceFile} {tokens : List Token}
    (value : Sum
      (MatchedTerminal file tokens (.symbol .star))
      (Sum
        (MatchedTerminal file tokens (.symbol .slash))
        (MatchedTerminal file tokens (.symbol .percent))) × Expression) :
    EbnfValue file tokens multiplicativeTailExpr :=
  let starAtom : EbnfExpr := .atom (.terminal (.symbol .star))
  let slashAtom : EbnfExpr := .atom (.terminal (.symbol .slash))
  let percentAtom : EbnfExpr := .atom (.terminal (.symbol .percent))
  let operatorExpr : EbnfExpr :=
    .group (.choice [starAtom, slashAtom, percentAtom])
  let operandAtom : EbnfExpr := .atom (.nonterminal .prefix)
  group (.sequence [operatorExpr, operandAtom])
    (sequence [operatorExpr, operandAtom]
      (EbnfValues.cons operatorExpr [operandAtom]
        (group (.choice [starAtom, slashAtom, percentAtom])
          (match value.1 with
          | .inl star => choice [starAtom, slashAtom, percentAtom]
              ⟨0, terminalAtom (.symbol .star) star⟩
          | .inr (.inl slash) => choice [starAtom, slashAtom, percentAtom]
              ⟨1, terminalAtom (.symbol .slash) slash⟩
          | .inr (.inr percent) => choice [starAtom, slashAtom, percentAtom]
              ⟨2, terminalAtom (.symbol .percent) percent⟩))
        (EbnfValues.cons operandAtom []
          (ruleAtom .prefix value.2) EbnfValues.nil)))

/-- Rebuilding a decoded multiplicative tail recovers its typed input. -/
theorem multiplicativeTailValue_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens multiplicativeTailExpr) :
    multiplicativeTailValue (multiplicativeTailView input) = input := by
  let starAtom : EbnfExpr := .atom (.terminal (.symbol .star))
  let slashAtom : EbnfExpr := .atom (.terminal (.symbol .slash))
  let percentAtom : EbnfExpr := .atom (.terminal (.symbol .percent))
  let operatorExpr : EbnfExpr :=
    .group (.choice [starAtom, slashAtom, percentAtom])
  let operandAtom : EbnfExpr := .atom (.nonterminal .prefix)
  let rawSequence := groupView (.sequence [operatorExpr, operandAtom]) input
  let viewed := sequence2View operatorExpr operandAtom rawSequence
  let rawChoice := groupView
    (.choice [starAtom, slashAtom, percentAtom]) viewed.1
  generalize choiceEq : choice3View starAtom slashAtom percentAtom rawChoice =
    selected
  have choiceValueEq := choice3_of_view
    starAtom slashAtom percentAtom rawChoice
  rw [choiceEq] at choiceValueEq
  have operatorEq := group_of_view
    (.choice [starAtom, slashAtom, percentAtom]) viewed.1
  have operandEq := rule_of_view .prefix viewed.2
  have sequenceEq := sequence2_of_view operatorExpr operandAtom rawSequence
  have outerGroupEq := group_of_view
    (.sequence [operatorExpr, operandAtom]) input
  cases selected with
  | inl raw =>
      have terminalEq := terminal_of_view (.symbol .star) raw
      have choiceRebuildEq : choice [starAtom, slashAtom, percentAtom]
          ⟨(0 : Fin 3), raw⟩ = rawChoice := by
        simpa using choiceValueEq
      simp only [multiplicativeTailValue, multiplicativeTailView,
        starAtom, slashAtom, percentAtom, operatorExpr, operandAtom,
        rawSequence, viewed, rawChoice, choiceEq]
      rw [terminalEq, choiceRebuildEq, operatorEq, operandEq, sequenceEq]
      exact outerGroupEq
  | inr rest =>
      cases rest with
      | inl raw =>
          have terminalEq := terminal_of_view (.symbol .slash) raw
          have choiceRebuildEq : choice [starAtom, slashAtom, percentAtom]
              ⟨(1 : Fin 3), raw⟩ = rawChoice := by
            simpa using choiceValueEq
          simp only [multiplicativeTailValue, multiplicativeTailView,
            starAtom, slashAtom, percentAtom, operatorExpr, operandAtom,
            rawSequence, viewed, rawChoice, choiceEq]
          rw [terminalEq, choiceRebuildEq, operatorEq, operandEq, sequenceEq]
          exact outerGroupEq
      | inr raw =>
          have terminalEq := terminal_of_view (.symbol .percent) raw
          have choiceRebuildEq : choice [starAtom, slashAtom, percentAtom]
              ⟨(2 : Fin 3), raw⟩ = rawChoice := by
            simpa using choiceValueEq
          simp only [multiplicativeTailValue, multiplicativeTailView,
            starAtom, slashAtom, percentAtom, operatorExpr, operandAtom,
            rawSequence, viewed, rawChoice, choiceEq]
          rw [terminalEq, choiceRebuildEq, operatorEq, operandEq, sequenceEq]
          exact outerGroupEq

/-- The optional `==` or `!=` tail of the equality level. -/
def equalityTailExpr : EbnfExpr :=
  .sequence [
    .group (.choice [
      .atom (.terminal (.symbol .equalEqual)),
      .atom (.terminal (.symbol .notEqual))]),
    .atom (.nonterminal .relational)]

/-- Decode an equality tail into its selected operator and right operand. -/
def equalityTailView
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens equalityTailExpr) :
    Sum
      (MatchedTerminal file tokens (.symbol .equalEqual))
      (MatchedTerminal file tokens (.symbol .notEqual)) × Expression :=
  let equalAtom : EbnfExpr :=
    .atom (.terminal (.symbol .equalEqual))
  let notEqualAtom : EbnfExpr :=
    .atom (.terminal (.symbol .notEqual))
  let operatorExpr : EbnfExpr :=
    .group (.choice [equalAtom, notEqualAtom])
  let operandAtom : EbnfExpr := .atom (.nonterminal .relational)
  let viewed := sequence2View operatorExpr operandAtom input
  let rawChoice := groupView
    (.choice [equalAtom, notEqualAtom]) viewed.1
  let operator := match choice2View equalAtom notEqualAtom rawChoice with
    | .inl raw => Sum.inl (terminalView (.symbol .equalEqual) raw)
    | .inr raw => Sum.inr (terminalView (.symbol .notEqual) raw)
  (operator, ruleView .relational viewed.2)

/-- Rebuild one equality tail from its semantic view. -/
def equalityTailValue
    {file : WorkspaceFile} {tokens : List Token}
    (value : Sum
      (MatchedTerminal file tokens (.symbol .equalEqual))
      (MatchedTerminal file tokens (.symbol .notEqual)) × Expression) :
    EbnfValue file tokens equalityTailExpr :=
  let equalAtom : EbnfExpr :=
    .atom (.terminal (.symbol .equalEqual))
  let notEqualAtom : EbnfExpr :=
    .atom (.terminal (.symbol .notEqual))
  let operatorExpr : EbnfExpr :=
    .group (.choice [equalAtom, notEqualAtom])
  let operandAtom : EbnfExpr := .atom (.nonterminal .relational)
  sequence [operatorExpr, operandAtom]
    (EbnfValues.cons operatorExpr [operandAtom]
      (group (.choice [equalAtom, notEqualAtom])
        (match value.1 with
        | .inl equal => choice [equalAtom, notEqualAtom]
            ⟨0, terminalAtom (.symbol .equalEqual) equal⟩
        | .inr notEqual => choice [equalAtom, notEqualAtom]
            ⟨1, terminalAtom (.symbol .notEqual) notEqual⟩))
      (EbnfValues.cons operandAtom []
        (ruleAtom .relational value.2) EbnfValues.nil))

/-- Rebuilding a decoded equality tail recovers its typed input. -/
theorem equalityTailValue_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens equalityTailExpr) :
    equalityTailValue (equalityTailView input) = input := by
  let equalAtom : EbnfExpr :=
    .atom (.terminal (.symbol .equalEqual))
  let notEqualAtom : EbnfExpr :=
    .atom (.terminal (.symbol .notEqual))
  let operatorExpr : EbnfExpr :=
    .group (.choice [equalAtom, notEqualAtom])
  let operandAtom : EbnfExpr := .atom (.nonterminal .relational)
  let viewed := sequence2View operatorExpr operandAtom input
  let rawChoice := groupView
    (.choice [equalAtom, notEqualAtom]) viewed.1
  generalize choiceEq : choice2View equalAtom notEqualAtom rawChoice = selected
  have choiceValueEq := choice2_of_view equalAtom notEqualAtom rawChoice
  rw [choiceEq] at choiceValueEq
  have operatorEq := group_of_view
    (.choice [equalAtom, notEqualAtom]) viewed.1
  have operandEq := rule_of_view .relational viewed.2
  have sequenceEq := sequence2_of_view operatorExpr operandAtom input
  cases selected with
  | inl raw =>
      have terminalEq := terminal_of_view (.symbol .equalEqual) raw
      have choiceRebuildEq : choice [equalAtom, notEqualAtom]
          ⟨(0 : Fin 2), raw⟩ = rawChoice := by
        simpa using choiceValueEq
      simp only [equalityTailValue, equalityTailView, equalAtom,
        notEqualAtom, operatorExpr, operandAtom, viewed, rawChoice, choiceEq]
      rw [terminalEq, choiceRebuildEq, operatorEq, operandEq]
      exact sequenceEq
  | inr raw =>
      have terminalEq := terminal_of_view (.symbol .notEqual) raw
      have choiceRebuildEq : choice [equalAtom, notEqualAtom]
          ⟨(1 : Fin 2), raw⟩ = rawChoice := by
        simpa using choiceValueEq
      simp only [equalityTailValue, equalityTailView, equalAtom,
        notEqualAtom, operatorExpr, operandAtom, viewed, rawChoice, choiceEq]
      rw [terminalEq, choiceRebuildEq, operatorEq, operandEq]
      exact sequenceEq
end EbnfValue

/-- Locate a payload at the exact span of a matched terminal. -/
def executableTerminalLoc
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol} {α : Type}
    (matched : MatchedTerminal file tokens terminal) (payload : α) :
    Located α :=
  { span := matched.span, payload := payload }

/-- Execute every module-reference spelling and root interpretation. -/
def executeModuleRefRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .moduleRef)) :
    ModuleReference :=
  let pathAtom : EbnfExpr :=
    .atom (.terminal (.category .pathComponent))
  let tail := EbnfValue.terminalPairTailExpr
    (.symbol .dot) (.category .pathComponent)
  let externalChildren : List EbnfExpr := [
    .atom (.terminal (.symbol .at)), pathAtom,
    .atom (.terminal (.symbol .dot)), pathAtom, .star tail]
  let localChildren : List EbnfExpr := [pathAtom, .star tail]
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish owned ordered
  match EbnfValue.choice2View
      (.sequence externalChildren) (.sequence localChildren) input with
  | .inl raw =>
      let viewed := EbnfValue.sequenceFlatView externalChildren raw
      let atToken := EbnfValue.terminalView (.symbol .at) viewed.1
      let library := EbnfValue.terminalView
        (.category .pathComponent) viewed.2.1
      let next := EbnfValue.terminalView
        (.category .pathComponent) viewed.2.2.2.1
      let rest := (EbnfValue.starView tail viewed.2.2.2.2.1).map
        (EbnfValue.terminalPairTailView
          (.symbol .dot) (.category .pathComponent))
      sourceLoc witness (.external
        (executableTerminalLoc atToken .externalSigil)
        (executableTerminalLoc library {
          segment := library.pathProjection.2 })
        {
          head := executableTerminalLoc next next.pathProjection.2
          tail := rest.map fun entry =>
            executableTerminalLoc entry.2 entry.2.pathProjection.2
        })
  | .inr raw =>
      let viewed := EbnfValue.sequence2View pathAtom (.star tail) raw
      let first := EbnfValue.terminalView
        (.category .pathComponent) viewed.1
      let rest := (EbnfValue.starView tail viewed.2).map
        (EbnfValue.terminalPairTailView
          (.symbol .dot) (.category .pathComponent))
      sourceLoc witness <|
        if first.pathProjection.1 = "std" then
          .standard
            (executableTerminalLoc first .standardRoot)
            (rest.map fun entry =>
              executableTerminalLoc entry.2 entry.2.pathProjection.2)
        else if first.pathProjection.1 = "lib" then
          match rest with
          | [] => .relative {
              head := executableTerminalLoc first first.pathProjection.2
              tail := []
            }
          | next :: remaining => .libraryRoot
              (executableTerminalLoc first .libraryRoot) {
                head := executableTerminalLoc
                  next.2 next.2.pathProjection.2
                tail := remaining.map fun entry =>
                  executableTerminalLoc entry.2 entry.2.pathProjection.2
              }
        else
          .relative {
            head := executableTerminalLoc first first.pathProjection.2
            tail := rest.map fun entry =>
              executableTerminalLoc entry.2 entry.2.pathProjection.2
          }

/-- Execute an assignment operator from its selected terminal branch. -/
def executeAssignmentOperatorRoot
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .assignmentOperator)) :
    Located AssignmentOperator :=
  match EbnfValue.choiceView [
      .atom (.terminal (.symbol .equal)),
      .atom (.terminal (.symbol .plusEqual)),
      .atom (.terminal (.symbol .minusEqual)),
      .atom (.terminal (.symbol .caretEqual)),
      .atom (.terminal (.symbol .ampEqual)),
      .atom (.terminal (.symbol .pipeEqual)),
      .atom (.terminal (.symbol .percentEqual))] input with
  | ⟨⟨0, _⟩, raw⟩ =>
      executableTerminalLoc
        (EbnfValue.terminalView (.symbol .equal) raw) .equal
  | ⟨⟨1, _⟩, raw⟩ =>
      executableTerminalLoc
        (EbnfValue.terminalView (.symbol .plusEqual) raw) .addEqual
  | ⟨⟨2, _⟩, raw⟩ =>
      executableTerminalLoc
        (EbnfValue.terminalView (.symbol .minusEqual) raw) .subtractEqual
  | ⟨⟨3, _⟩, raw⟩ =>
      executableTerminalLoc
        (EbnfValue.terminalView (.symbol .caretEqual) raw) .bitXorEqual
  | ⟨⟨4, _⟩, raw⟩ =>
      executableTerminalLoc
        (EbnfValue.terminalView (.symbol .ampEqual) raw) .bitAndEqual
  | ⟨⟨5, _⟩, raw⟩ =>
      executableTerminalLoc
        (EbnfValue.terminalView (.symbol .pipeEqual) raw) .bitOrEqual
  | ⟨⟨6, _⟩, raw⟩ =>
      executableTerminalLoc
        (EbnfValue.terminalView (.symbol .percentEqual) raw) .moduloEqual

/-- Execute a prefix expression from its recursive or postfix branch. -/
def executePrefixRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .prefix)) : Expression :=
  let branches : List EbnfExpr := [
    .sequence [
      .atom (.terminal (.symbol .bang)),
      .atom (.nonterminal .prefix)],
    .atom (.nonterminal .postfix)]
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence2View
        (.atom (.terminal (.symbol .bang)))
        (.atom (.nonterminal .prefix)) raw
      let operator := EbnfValue.terminalView (.symbol .bang) viewed.1
      sourceLoc (shallowRootWitness file tokens origin finish owned ordered)
        (.prefix (executableTerminalLoc operator .logicalNot)
          (EbnfValue.ruleView .prefix viewed.2))
  | ⟨⟨1, _⟩, raw⟩ => EbnfValue.ruleView .postfix raw

/-- Execute one postfix part from its selected typed branch. -/
def executePostfixPartRoot
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .postfixPart)) :
    PostfixPartValue :=
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let branches : List EbnfExpr := [
    .sequence [
      .atom (.terminal (.symbol .leftParen)),
      .list0 expressionAtom,
      .atom (.terminal (.symbol .rightParen))],
    .sequence [
      .atom (.terminal (.symbol .dot)),
      .atom (.terminal (.category .identifier))],
    .sequence [
      .atom (.terminal (.symbol .leftBracket)),
      expressionAtom,
      .atom (.terminal (.symbol .rightBracket))]]
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence3View
        (.atom (.terminal (.symbol .leftParen))) (.list0 expressionAtom)
        (.atom (.terminal (.symbol .rightParen))) raw
      .call
        (EbnfValue.terminalView (.symbol .leftParen) viewed.1).span
        ((EbnfValue.list0View expressionAtom viewed.2.1).map
          (EbnfValue.ruleView .expression))
        (EbnfValue.terminalView (.symbol .rightParen) viewed.2.2).span
  | ⟨⟨1, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence2View
        (.atom (.terminal (.symbol .dot)))
        (.atom (.terminal (.category .identifier))) raw
      let dot := EbnfValue.terminalView (.symbol .dot) viewed.1
      let field := EbnfValue.terminalView (.category .identifier) viewed.2
      .select dot.span
        (executableTerminalLoc field field.identifierProjection.2)
  | ⟨⟨2, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence3View
        (.atom (.terminal (.symbol .leftBracket))) expressionAtom
        (.atom (.terminal (.symbol .rightBracket))) raw
      .index
        (EbnfValue.terminalView (.symbol .leftBracket) viewed.1).span
        (EbnfValue.ruleView .expression viewed.2.1)
        (EbnfValue.terminalView (.symbol .rightBracket) viewed.2.2).span

/-- Execute a qualified name from its first and dotted identifier matches. -/
def executeQualifiedNameRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .qualifiedName)) :
    QualifiedName :=
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let tail := EbnfValue.terminalPairTailExpr
    (.symbol .dot) (.category .identifier)
  let viewed := EbnfValue.sequence2View identifierAtom (.star tail) input
  let first := EbnfValue.terminalView (.category .identifier) viewed.1
  let rest := (EbnfValue.starView tail viewed.2).map
    (EbnfValue.terminalPairTailView
      (.symbol .dot) (.category .identifier))
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered) {
    components := {
      head := executableTerminalLoc first first.identifierProjection.2
      tail := rest.map fun entry =>
        executableTerminalLoc entry.2 entry.2.identifierProjection.2
    }
  }

/-- Execute a literal from its selected source token category. -/
def executeLiteralRoot
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .literal)) : Literal :=
  match EbnfValue.choiceView [
      .atom (.terminal (.category .decimalLiteral)),
      .atom (.terminal (.category .hexadecimalLiteral)),
      .atom (.terminal (.category .stringLiteral))] input with
  | ⟨⟨0, _⟩, raw⟩ =>
      let terminal := EbnfValue.terminalView (.category .decimalLiteral) raw
      executableTerminalLoc terminal
        (terminal.literalProjection .decimalLiteral (by simp))
  | ⟨⟨1, _⟩, raw⟩ =>
      let terminal := EbnfValue.terminalView
        (.category .hexadecimalLiteral) raw
      executableTerminalLoc terminal
        (terminal.literalProjection .hexadecimalLiteral (by simp))
  | ⟨⟨2, _⟩, raw⟩ =>
      let terminal := EbnfValue.terminalView (.category .stringLiteral) raw
      executableTerminalLoc terminal
        (terminal.literalProjection .stringLiteral (by simp))

/-- Execute a lambda from its arbitrary-length typed sequence view. -/
def executeLambdaRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .lambda)) : Expression :=
  let parameterAtom : EbnfExpr := .atom (.nonterminal .parameter)
  let returnExpr : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .arrow)),
    .atom (.nonterminal .type)]
  let children : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .lamKw)),
    .atom (.terminal (.symbol .leftParen)),
    .list0 parameterAtom,
    .atom (.terminal (.symbol .rightParen)),
    .optional returnExpr,
    .atom (.nonterminal .body)]
  let viewed := EbnfValue.sequenceFlatView children input
  let parameters := (EbnfValue.list0View parameterAtom viewed.2.2.1).map
    (EbnfValue.ruleView .parameter)
  let returnType := (EbnfValue.optionalView returnExpr
    viewed.2.2.2.2.1).map fun raw =>
      let returnViewed := EbnfValue.sequence2View
        (.atom (.terminal (.symbol .arrow)))
        (.atom (.nonterminal .type)) raw
      (EbnfValue.terminalView (.symbol .arrow) returnViewed.1,
        EbnfValue.ruleView .type returnViewed.2)
  let body := EbnfValue.ruleView .body viewed.2.2.2.2.2.1
  sourceLoc (shallowRootWitness file tokens origin finish owned ordered)
    (.lambda parameters (returnType.map Prod.snd) body)

/-- Execute an atomic expression from its selected typed branch. -/
def executeAtomRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .atom)) : Expression :=
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let argumentExpr : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .leftParen)),
    .list0 expressionAtom,
    .atom (.terminal (.symbol .rightParen))]
  let tupleTail := EbnfValue.fixedInfixTailExpr
    (.symbol .comma) .expression
  let branches : List EbnfExpr := [
    .atom (.nonterminal .literal),
    .atom (.terminal (.category .identifier)),
    .sequence [
      .atom (.terminal (.symbol .dot)),
      .atom (.terminal (.category .identifier)),
      .optional argumentExpr],
    .sequence [
      .atom (.terminal (.symbol .at)),
      .atom (.nonterminal .typeAtom)],
    .atom (.nonterminal .lambda),
    .sequence [
      .atom (.terminal (.symbol .leftParen)),
      .atom (.terminal (.symbol .rightParen))],
    .sequence [
      .atom (.terminal (.symbol .leftParen)), expressionAtom,
      .atom (.terminal (.symbol .rightParen))],
    .sequence [
      .atom (.terminal (.symbol .leftParen)), expressionAtom,
      .atom (.terminal (.symbol .comma)), expressionAtom,
      .star tupleTail,
      .atom (.terminal (.symbol .rightParen))]]
  let witness := shallowRootWitness file tokens origin finish owned ordered
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      sourceLoc witness (.literal (EbnfValue.ruleView .literal raw))
  | ⟨⟨1, _⟩, raw⟩ =>
      let name := EbnfValue.terminalView (.category .identifier) raw
      sourceLoc witness
        (.name (executableTerminalLoc name name.identifierProjection.2))
  | ⟨⟨2, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence3View
        (.atom (.terminal (.symbol .dot)))
        (.atom (.terminal (.category .identifier)))
        (.optional argumentExpr) raw
      let dot := EbnfValue.terminalView (.symbol .dot) viewed.1
      let name := EbnfValue.terminalView (.category .identifier) viewed.2.1
      let arguments := (EbnfValue.optionalView argumentExpr viewed.2.2).map
        fun argumentRaw =>
          let argumentView := EbnfValue.sequence3View
            (.atom (.terminal (.symbol .leftParen)))
            (.list0 expressionAtom)
            (.atom (.terminal (.symbol .rightParen))) argumentRaw
          (EbnfValue.list0View expressionAtom argumentView.2.1).map
            (EbnfValue.ruleView .expression)
      sourceLoc witness (.dotConstructor
        (executableTerminalLoc dot ())
        (executableTerminalLoc name name.identifierProjection.2) arguments)
  | ⟨⟨3, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence2View
        (.atom (.terminal (.symbol .at)))
        (.atom (.nonterminal .typeAtom)) raw
      let marker := EbnfValue.terminalView (.symbol .at) viewed.1
      sourceLoc witness (.proxy (executableTerminalLoc marker ())
        (EbnfValue.ruleView .typeAtom viewed.2))
  | ⟨⟨4, _⟩, raw⟩ => EbnfValue.ruleView .lambda raw
  | ⟨⟨5, _⟩, _raw⟩ => sourceLoc witness (.tuple [])
  | ⟨⟨6, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence3View
        (.atom (.terminal (.symbol .leftParen))) expressionAtom
        (.atom (.terminal (.symbol .rightParen))) raw
      sourceLoc witness (.group (EbnfValue.ruleView .expression viewed.2.1))
  | ⟨⟨7, _⟩, raw⟩ =>
      let children : List EbnfExpr := [
        .atom (.terminal (.symbol .leftParen)), expressionAtom,
        .atom (.terminal (.symbol .comma)), expressionAtom,
        .star tupleTail,
        .atom (.terminal (.symbol .rightParen))]
      let viewed := EbnfValue.sequenceFlatView children raw
      let first := EbnfValue.ruleView .expression viewed.2.1
      let second := EbnfValue.ruleView .expression viewed.2.2.2.1
      let rest := (EbnfValue.starView tupleTail
        viewed.2.2.2.2.1).map fun tail =>
          (EbnfValue.fixedInfixTailView
            (.symbol .comma) .expression tail).2
      sourceLoc witness (.tuple (first :: second :: rest))

/-- Locate an infix result between its left and right operands. -/
def executableBetween
    (file : WorkspaceFile) {α : Type}
    (firstSpan lastSpan : SourceSpan) (payload : α) : Located α := {
  span := {
    source := file.id
    startByte := firstSpan.startByte
    endByte := lastSpan.endByte
  }
  payload := payload
}

/-- Fold already decoded infix operations in source order. -/
def executeInfixLeft
    (file : WorkspaceFile) :
    Expression → List (Located InfixOperator × Expression) → Expression
  | left, [] => left
  | left, (operator, right) :: rest =>
      executeInfixLeft file
        (executableBetween file left.span right.span
          (.infix operator left right)) rest

/-- Fold source-ordered postfix pieces over their receiver. -/
def executePostfixLeft
    (file : WorkspaceFile) : Expression → List PostfixPartValue → Expression
  | receiver, [] => receiver
  | receiver, part :: rest =>
      let next := match part with
        | .call _ arguments closeParen =>
            executableBetween file receiver.span closeParen
              (.call receiver arguments)
        | .select _ field =>
            executableBetween file receiver.span field.span
              (.select receiver field)
        | .index _ index closeBracket =>
            executableBetween file receiver.span closeBracket
              (.index receiver index)
      executePostfixLeft file next rest

/-- Execute a postfix root from its atom and ordered postfix pieces. -/
def executePostfixRoot
    (file : WorkspaceFile) {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .postfix)) : Expression :=
  let atomExpr : EbnfExpr := .atom (.nonterminal .atom)
  let partExpr : EbnfExpr := .atom (.nonterminal .postfixPart)
  let viewed := EbnfValue.sequence2View atomExpr (.star partExpr) input
  executePostfixLeft file (EbnfValue.ruleView .atom viewed.1)
    ((EbnfValue.starView partExpr viewed.2).map
      (EbnfValue.ruleView .postfixPart))

/-- Execute any fixed-operator infix root from its typed EBNF value. -/
def executeFixedInfixRoot
    (file : WorkspaceFile) {tokens : List Token}
    (terminal : TerminalSymbol) (operand : GrammarRuleId)
    (asExpression : RuleValue operand → Expression)
    (operator : InfixOperator)
    (input : EbnfValue file tokens
      (EbnfValue.fixedInfixRootExpr terminal operand)) : Expression :=
  let viewed := EbnfValue.fixedInfixRootView terminal operand input
  executeInfixLeft file (asExpression viewed.1)
    (viewed.2.map fun value =>
      (executableTerminalLoc value.1 operator, asExpression value.2))

def executeLogicalOrRoot
    (file : WorkspaceFile) {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .logicalOr)) : Expression :=
  executeFixedInfixRoot file (.symbol .logicalOr) .logicalAnd id .logicalOr input

def executeLogicalAndRoot
    (file : WorkspaceFile) {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .logicalAnd)) : Expression :=
  executeFixedInfixRoot file (.symbol .logicalAnd) .equality id .logicalAnd input

/-- Execute an equality root with no operator or one selected operator. -/
def executeEqualityRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .equality)) : Expression :=
  let operandAtom : EbnfExpr := .atom (.nonterminal .relational)
  let tail := EbnfValue.equalityTailExpr
  let viewed := EbnfValue.sequence2View
    operandAtom (.optional tail) input
  let left := EbnfValue.ruleView .relational viewed.1
  match EbnfValue.optionalView tail viewed.2 with
  | none => left
  | some rawTail =>
      let decoded := EbnfValue.equalityTailView rawTail
      let operator := match decoded.1 with
        | .inl equal => executableTerminalLoc equal .equal
        | .inr notEqual => executableTerminalLoc notEqual .notEqual
      sourceLoc
        (ConsumedSpanWitness.compute file tokens origin finish owned ordered)
        (.infix operator left decoded.2)

/-- Execute a relational root, including the operator-free form. -/
def executeRelationalRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .relational)) : Expression :=
  let operand : EbnfExpr := .atom (.nonterminal .bitOr)
  let lessAtom : EbnfExpr := .atom (.terminal (.symbol .less))
  let greaterAtom : EbnfExpr := .atom (.terminal (.symbol .greater))
  let lessEqualAtom : EbnfExpr := .atom (.terminal (.symbol .lessEqual))
  let greaterEqualAtom : EbnfExpr :=
    .atom (.terminal (.symbol .greaterEqual))
  let operatorExpr : EbnfExpr := .group (.choice [lessAtom, greaterAtom,
    lessEqualAtom, greaterEqualAtom])
  let tail : EbnfExpr := .sequence [operatorExpr, operand]
  let outer := EbnfValue.sequence2View operand (.optional tail) input
  let left := EbnfValue.ruleView .bitOr outer.1
  match EbnfValue.optionalView tail outer.2 with
  | none => left
  | some rawTail =>
      let inner := EbnfValue.sequence2View operatorExpr operand rawTail
      let right := EbnfValue.ruleView .bitOr inner.2
      let witness := ConsumedSpanWitness.compute
        file tokens origin finish owned ordered
      let rawChoice := EbnfValue.groupView
        (.choice [lessAtom, greaterAtom, lessEqualAtom, greaterEqualAtom])
        inner.1
      match EbnfValue.choice4View lessAtom greaterAtom lessEqualAtom
          greaterEqualAtom rawChoice with
      | .inl raw =>
          let operator := EbnfValue.terminalView (.symbol .less) raw
          sourceLoc witness (.infix
            (executableTerminalLoc operator .less) left right)
      | .inr (.inl raw) =>
          let operator := EbnfValue.terminalView (.symbol .greater) raw
          sourceLoc witness (.infix
            (executableTerminalLoc operator .greater) left right)
      | .inr (.inr (.inl raw)) =>
          let operator := EbnfValue.terminalView (.symbol .lessEqual) raw
          sourceLoc witness (.infix
            (executableTerminalLoc operator .lessEqual) left right)
      | .inr (.inr (.inr raw)) =>
          let operator := EbnfValue.terminalView (.symbol .greaterEqual) raw
          sourceLoc witness (.infix
            (executableTerminalLoc operator .greaterEqual) left right)

def executeBitOrRoot
    (file : WorkspaceFile) {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .bitOr)) : Expression :=
  executeFixedInfixRoot file (.symbol .pipe) .bitXor id .bitOr input

def executeBitXorRoot
    (file : WorkspaceFile) {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .bitXor)) : Expression :=
  executeFixedInfixRoot file (.symbol .caret) .bitAnd id .bitXor input

def executeBitAndRoot
    (file : WorkspaceFile) {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .bitAnd)) : Expression :=
  executeFixedInfixRoot file (.symbol .amp) .additive id .bitAnd input

/-- Execute an additive root from its left operand and ordered mixed tails. -/
def executeAdditiveRoot
    (file : WorkspaceFile) {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .additive)) : Expression :=
  let operandAtom : EbnfExpr := .atom (.nonterminal .multiplicative)
  let tail := EbnfValue.additiveTailExpr
  let viewed := EbnfValue.sequence2View operandAtom (.star tail) input
  let left := EbnfValue.ruleView .multiplicative viewed.1
  let rest := (EbnfValue.starView tail viewed.2).map
    EbnfValue.additiveTailView
  executeInfixLeft file left (rest.map fun value =>
    ((match value.1 with
      | .inl plus => executableTerminalLoc plus .add
      | .inr minus => executableTerminalLoc minus .subtract), value.2))

/-- Execute a multiplicative root from its left operand and mixed tails. -/
def executeMultiplicativeRoot
    (file : WorkspaceFile) {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .multiplicative)) : Expression :=
  let operandAtom : EbnfExpr := .atom (.nonterminal .prefix)
  let tail := EbnfValue.multiplicativeTailExpr
  let viewed := EbnfValue.sequence2View operandAtom (.star tail) input
  let left := EbnfValue.ruleView .prefix viewed.1
  let rest := (EbnfValue.starView tail viewed.2).map
    EbnfValue.multiplicativeTailView
  executeInfixLeft file left (rest.map fun value =>
    ((match value.1 with
      | .inl star => executableTerminalLoc star .multiply
      | .inr (.inl slash) => executableTerminalLoc slash .divide
      | .inr (.inr percent) => executableTerminalLoc percent .modulo), value.2))

/-- Execute every pattern form from its selected typed branch. -/
def executePatternRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .pattern)) : Pattern :=
  let underscoreAtom : EbnfExpr :=
    .atom (.terminal (.symbol .underscore))
  let literalAtom : EbnfExpr := .atom (.nonterminal .literal)
  let dotAtom : EbnfExpr := .atom (.terminal (.symbol .dot))
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let comptimeAtom : EbnfExpr :=
    .atom (.terminal (.contextualKeyword .comptimeKw))
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let nameAtom : EbnfExpr := .atom (.nonterminal .qualifiedName)
  let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftParen))
  let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightParen))
  let commaAtom : EbnfExpr := .atom (.terminal (.symbol .comma))
  let patternAtom : EbnfExpr := .atom (.nonterminal .pattern)
  let argumentsExpr : EbnfExpr :=
    .sequence [openAtom, .list1 patternAtom, closeAtom]
  let tupleTail := EbnfValue.fixedInfixTailExpr
    (.symbol .comma) .pattern
  let branches : List EbnfExpr := [
    underscoreAtom,
    literalAtom,
    .sequence [dotAtom, identifierAtom, .optional argumentsExpr],
    .sequence [comptimeAtom, expressionAtom],
    .sequence [nameAtom, .optional argumentsExpr],
    .sequence [openAtom, closeAtom],
    .sequence [openAtom, patternAtom, closeAtom],
    .sequence [openAtom, patternAtom, commaAtom, patternAtom,
      .star tupleTail, closeAtom]]
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish owned ordered
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      let underscore := EbnfValue.terminalView
        (.symbol .underscore) raw
      sourceLoc witness (.wildcard
        (executableTerminalLoc underscore .wildcard))
  | ⟨⟨1, _⟩, raw⟩ =>
      sourceLoc witness (.literal (EbnfValue.ruleView .literal raw))
  | ⟨⟨2, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence3View
        dotAtom identifierAtom (.optional argumentsExpr) raw
      let dot := EbnfValue.terminalView (.symbol .dot) viewed.1
      let name := EbnfValue.terminalView
        (.category .identifier) viewed.2.1
      let arguments := (EbnfValue.optionalView argumentsExpr
        viewed.2.2).map fun argumentRaw =>
          let argumentView := EbnfValue.sequence3View
            openAtom (.list1 patternAtom) closeAtom argumentRaw
          (EbnfValue.list1View patternAtom argumentView.2.1).map
            (EbnfValue.ruleView .pattern)
      sourceLoc witness (.dotConstructor
        (executableTerminalLoc dot ())
        (executableTerminalLoc name name.identifierProjection.2)
        arguments)
  | ⟨⟨3, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence2View
        comptimeAtom expressionAtom raw
      let comptime := EbnfValue.terminalView
        (.contextualKeyword .comptimeKw) viewed.1
      sourceLoc witness (.comptime
        (executableTerminalLoc comptime .comptimeModifier)
        (EbnfValue.ruleView .expression viewed.2))
  | ⟨⟨4, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence2View
        nameAtom (.optional argumentsExpr) raw
      let name := EbnfValue.ruleView .qualifiedName viewed.1
      let arguments := (EbnfValue.optionalView argumentsExpr
        viewed.2).map fun argumentRaw =>
          let argumentView := EbnfValue.sequence3View
            openAtom (.list1 patternAtom) closeAtom argumentRaw
          (EbnfValue.list1View patternAtom argumentView.2.1).map
            (EbnfValue.ruleView .pattern)
      sourceLoc witness (.named name arguments)
  | ⟨⟨5, _⟩, _raw⟩ => sourceLoc witness (.tuple [])
  | ⟨⟨6, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence3View
        openAtom patternAtom closeAtom raw
      sourceLoc witness
        (.group (EbnfValue.ruleView .pattern viewed.2.1))
  | ⟨⟨7, _⟩, raw⟩ =>
      let children : List EbnfExpr := [openAtom, patternAtom,
        commaAtom, patternAtom, .star tupleTail, closeAtom]
      let viewed := EbnfValue.sequenceFlatView children raw
      let first := EbnfValue.ruleView .pattern viewed.2.1
      let second := EbnfValue.ruleView .pattern viewed.2.2.2.1
      let rest := (EbnfValue.starView tupleTail
        viewed.2.2.2.2.1).map fun tail =>
          (EbnfValue.fixedInfixTailView
            (.symbol .comma) .pattern tail).2
      sourceLoc witness (.tuple (first :: second :: rest))

/-- Execute every atomic type form from its selected typed branch. -/
def executeTypeAtomRoot
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs .typeAtom)) : TypeExpr :=
  let atAtom : EbnfExpr := .atom (.terminal (.symbol .at))
  let atomAtom : EbnfExpr := .atom (.nonterminal .typeAtom)
  let nameAtom : EbnfExpr := .atom (.nonterminal .qualifiedName)
  let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftParen))
  let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightParen))
  let commaAtom : EbnfExpr := .atom (.terminal (.symbol .comma))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let argumentsExpr : EbnfExpr :=
    .sequence [openAtom, .list1 typeAtom, closeAtom]
  let tupleTail := EbnfValue.fixedInfixTailExpr (.symbol .comma) .type
  let branches : List EbnfExpr := [
    .sequence [atAtom, atomAtom],
    .sequence [nameAtom, .optional argumentsExpr],
    .sequence [openAtom, closeAtom],
    .sequence [openAtom, typeAtom, closeAtom],
    .sequence [openAtom, typeAtom, commaAtom, typeAtom,
      .star tupleTail, closeAtom]]
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish owned ordered
  match EbnfValue.choiceView branches input with
  | ⟨⟨0, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence2View atAtom atomAtom raw
      let marker := EbnfValue.terminalView (.symbol .at) viewed.1
      let inner := EbnfValue.ruleView .typeAtom viewed.2
      sourceLoc witness
        (.proxy (executableTerminalLoc marker ()) inner)
  | ⟨⟨1, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence2View
        nameAtom (.optional argumentsExpr) raw
      let name := EbnfValue.ruleView .qualifiedName viewed.1
      let arguments := (EbnfValue.optionalView argumentsExpr viewed.2).map
        fun rawArguments =>
          let argumentView := EbnfValue.sequence3View
            openAtom (.list1 typeAtom) closeAtom rawArguments
          (EbnfValue.list1View typeAtom argumentView.2.1).map
            (EbnfValue.ruleView .type)
      sourceLoc witness (.named name arguments)
  | ⟨⟨2, _⟩, _raw⟩ => sourceLoc witness (.tuple [])
  | ⟨⟨3, _⟩, raw⟩ =>
      let viewed := EbnfValue.sequence3View
        openAtom typeAtom closeAtom raw
      sourceLoc witness (.group (EbnfValue.ruleView .type viewed.2.1))
  | ⟨⟨4, _⟩, raw⟩ =>
      let children : List EbnfExpr := [openAtom, typeAtom, commaAtom,
        typeAtom, .star tupleTail, closeAtom]
      let viewed := EbnfValue.sequenceFlatView children raw
      let first := EbnfValue.ruleView .type viewed.2.1
      let second := EbnfValue.ruleView .type viewed.2.2.2.1
      let rest := (EbnfValue.starView tupleTail
        viewed.2.2.2.2.1).map fun tail =>
          (EbnfValue.fixedInfixTailView
            (.symbol .comma) .type tail).2
      sourceLoc witness (.tuple (first :: second :: rest))

/-- Execute one currently supported source-rule root. -/
def executeRootRule
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (rule : GrammarRuleId)
    (executable : ExecutableRootRule rule)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : EbnfValue file tokens (m2cV1.rhs rule)) : RuleValue rule :=
  match executable with
  | .module => executeModuleRoot file input
  | .topItem => executeTopItemRoot file tokens origin finish owned ordered input
  | .moduleRef =>
      executeModuleRefRoot file tokens origin finish owned ordered input
  | .importDecl =>
      executeImportDeclRoot file tokens origin finish owned ordered input
  | .exportDecl =>
      executeExportDeclRoot file tokens origin finish owned ordered input
  | .importEntry =>
      executeImportEntryRoot file tokens origin finish owned ordered input
  | .localExportEntry =>
      executeLocalExportEntryRoot file tokens origin finish owned ordered input
  | .remoteExportEntry =>
      executeRemoteExportEntryRoot file tokens origin finish owned ordered input
  | .optionalComma => executeOptionalCommaRoot input
  | .predicateList => executePredicateListRoot input
  | .predicate =>
      executePredicateRoot file tokens origin finish owned ordered input
  | .functionSignature =>
      executeFunctionSignatureRoot file tokens origin finish owned ordered input
  | .instanceMethod => executeInstanceMethodRoot input
  | .armStatement => executeArmStatementRoot input
  | .matchArm =>
      executeMatchArmRoot file tokens origin finish owned ordered input
  | .statement => executeStatementRoot input
  | .terminalExpression => executeTerminalExpressionRoot input
  | .pattern =>
      executePatternRoot file tokens origin finish owned ordered input
  | .expression => executeExpressionRoot input
  | .annotation =>
      executeAnnotationRoot file tokens origin finish owned ordered input
  | .conditional =>
      executeConditionalRoot file tokens origin finish owned ordered input
  | .blockStatement =>
      executeBlockStatementRoot file tokens origin finish owned ordered input
  | .functionDecl =>
      executeFunctionDeclRoot file tokens origin finish owned ordered input
  | .classMethod =>
      executeClassMethodRoot file tokens origin finish owned ordered input
  | .letStatement =>
      executeLetStatementRoot file tokens origin finish owned ordered input
  | .letBinding =>
      executeLetBindingRoot file tokens origin finish owned ordered input
  | .breakStatement =>
      executeBreakStatementRoot file tokens origin finish owned ordered input
  | .continueStatement =>
      executeContinueStatementRoot file tokens origin finish owned ordered input
  | .assemblyStatement =>
      executeAssemblyStatementRoot file tokens origin finish owned ordered input
  | .ifStatement =>
      executeIfStatementRoot file tokens origin finish owned ordered input
  | .matchStatement =>
      executeMatchStatementRoot file tokens origin finish owned ordered input
  | .returnStatement =>
      executeReturnStatementRoot file tokens origin finish owned ordered input
  | .assignmentStatement =>
      executeAssignmentStatementRoot file tokens origin finish owned ordered input
  | .parameter =>
      executeParameterRoot file tokens origin finish owned ordered input
  | .dataDecl =>
      executeDataDeclRoot file tokens origin finish owned ordered input
  | .contractDecl =>
      executeContractDeclRoot file tokens origin finish owned ordered input
  | .dataConstructor =>
      executeDataConstructorRoot file tokens origin finish owned ordered input
  | .typeAliasDecl =>
      executeTypeAliasDeclRoot file tokens origin finish owned ordered input
  | .classDecl =>
      executeClassDeclRoot file tokens origin finish owned ordered input
  | .instanceDecl =>
      executeInstanceDeclRoot file tokens origin finish owned ordered input
  | .fieldDecl =>
      executeFieldDeclRoot file tokens origin finish owned ordered input
  | .fallbackDecl =>
      executeFallbackDeclRoot file tokens origin finish owned ordered input
  | .contractConstructorDecl =>
      executeContractConstructorDeclRoot file tokens origin finish
        owned ordered input
  | .pragmaDecl =>
      executePragmaDeclRoot file tokens origin finish owned ordered input
  | .genericPrefix =>
      executeGenericPrefixRoot file tokens origin finish owned ordered input
  | .forallClause =>
      executeForallClauseRoot file tokens origin finish owned ordered input
  | .forallBinder =>
      executeForallBinderRoot file tokens origin finish owned ordered input
  | .exportItem =>
      executeExportItemRoot file tokens origin finish owned ordered input
  | .constructorSelection =>
      executeConstructorSelectionRoot file tokens origin finish
        owned ordered input
  | .hidingClause =>
      executeHidingClauseRoot file tokens origin finish owned ordered input
  | .body => executeBodyRoot file tokens origin finish owned ordered input
  | .type => executeTypeRoot file tokens origin finish owned ordered input
  | .typeAtom =>
      executeTypeAtomRoot file tokens origin finish owned ordered input
  | .qualifiedName =>
      executeQualifiedNameRoot file tokens origin finish owned ordered input
  | .forStatement =>
      executeForStatementRoot file tokens origin finish owned ordered input
  | .forInitItem =>
      executeForInitItemRoot file tokens origin finish owned ordered input
  | .forPostItem =>
      executeForPostItemRoot file tokens origin finish owned ordered input
  | .expressionStatement =>
      executeExpressionStatementRoot file tokens origin finish owned ordered input
  | .contractMember =>
      executeContractMemberRoot file tokens origin finish owned ordered input
  | .assignmentOperator => executeAssignmentOperatorRoot input
  | .logicalOr => executeLogicalOrRoot file input
  | .logicalAnd => executeLogicalAndRoot file input
  | .equality =>
      executeEqualityRoot file tokens origin finish owned ordered input
  | .relational =>
      executeRelationalRoot file tokens origin finish owned ordered input
  | .bitOr => executeBitOrRoot file input
  | .bitXor => executeBitXorRoot file input
  | .bitAnd => executeBitAndRoot file input
  | .additive => executeAdditiveRoot file input
  | .multiplicative => executeMultiplicativeRoot file input
  | .prefix =>
      executePrefixRoot file tokens origin finish owned ordered input
  | .postfixExpr => executePostfixRoot file input
  | .postfixPart => executePostfixPartRoot input
  | .atomExpr =>
      executeAtomRoot file tokens origin finish owned ordered input
  | .literalValue => executeLiteralRoot input
  | .lambdaExpr =>
      executeLambdaRoot file tokens origin finish owned ordered input

/-- Execute one supported root production directly from its chart action
tuple. -/
def executeRootAction
    (file : WorkspaceFile) (tokens : List Token)
    (origin finish : Boundary tokens)
    (rule : GrammarRuleId)
    (executable : ExecutableRootRule rule)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : GrammarSymbolValues file tokens (ProductionId.root rule).rhs) :
    NonterminalValue file tokens (ProductionId.root rule).lhs :=
  executeRootRule file tokens origin finish rule executable owned ordered
    (RootAction.unpack rule input)

end Solcore.Surface.Multi
