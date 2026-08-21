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
