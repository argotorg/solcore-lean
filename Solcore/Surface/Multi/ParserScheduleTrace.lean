import Solcore.Surface.Multi.ParserSchedule

set_option autoImplicit false

namespace Solcore.Surface.Multi

/-!
Fresh-address tracking for the fixed fast-parser schedule.

Each address family is stored as a finite set of the canonical ranks supplied
by `ParserSchedule`.  The only public update rejects an address whose rank was
already visited.  This module supplies schedule-local accounting invariants;
it does not define parser transitions or connect charges to parsing behavior.
-/

private theorem nodup_length_le_of_subset
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    {left right : List alpha} (unique : left.Nodup)
    (subset : left ⊆ right) : left.length ≤ right.length := by
  induction left generalizing right with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at unique
      have headMember : head ∈ right := subset (by simp)
      have tailSubset : tail ⊆ right.erase head := by
        intro value valueMember
        rw [List.mem_erase_of_ne]
        · exact subset (by simp [valueMember])
        · intro equal
          exact unique.1 (equal.symm ▸ valueMember)
      have tailBound := induction unique.2 tailSubset
      rw [List.length_erase_of_mem headMember] at tailBound
      simp only [List.length_cons]
      have rightPositive := List.length_pos_of_mem headMember
      omega

/-- A finite set of canonical schedule ranks, stored newest first. -/
structure ScheduleRankSet where
  valuesRev : List Nat
  unique : valuesRev.Nodup

namespace ScheduleRankSet

/-- The empty rank set. -/
def empty : ScheduleRankSet := {
  valuesRev := []
  unique := by simp
}

/-- Executable membership in a rank set. -/
def contains (set : ScheduleRankSet) (rank : Nat) : Bool :=
  set.valuesRev.contains rank

/-- Cardinality of a rank set. -/
def card (set : ScheduleRankSet) : Nat :=
  set.valuesRev.length

/-- Insert a rank whose freshness has already been established. -/
def insert (set : ScheduleRankSet) (rank : Nat)
    (fresh : rank ∉ set.valuesRev) : ScheduleRankSet := {
  valuesRev := rank :: set.valuesRev
  unique := List.nodup_cons.mpr ⟨fresh, set.unique⟩
}

@[simp] theorem contains_empty (rank : Nat) :
    empty.contains rank = false := by
  rfl

@[simp] theorem card_empty : empty.card = 0 := by
  rfl

@[simp] theorem card_insert
    (set : ScheduleRankSet) (rank : Nat)
    (fresh : rank ∉ set.valuesRev) :
    (set.insert rank fresh).card = set.card + 1 := by
  simp [insert, card]

@[simp] theorem contains_insert_self
    (set : ScheduleRankSet) (rank : Nat)
    (fresh : rank ∉ set.valuesRev) :
    (set.insert rank fresh).contains rank = true := by
  simp [insert, contains]

/-- Inserting one rank preserves membership answers for every other rank. -/
theorem contains_insert_of_ne
    (set : ScheduleRankSet) (inserted existing : Nat)
    (fresh : inserted ∉ set.valuesRev)
    (different : inserted ≠ existing) :
    (set.insert inserted fresh).contains existing = set.contains existing := by
  simp [insert, contains, Ne.symm different]

theorem contains_eq_true_iff_mem
    (set : ScheduleRankSet) (rank : Nat) :
    set.contains rank = true ↔ rank ∈ set.valuesRev := by
  simp [contains]

theorem card_le_of_bounded {capacity : Nat}
    (set : ScheduleRankSet)
    (bounded : ∀ rank, rank ∈ set.valuesRev → rank < capacity) :
    set.card ≤ capacity := by
  have subset : set.valuesRev ⊆ List.range capacity := by
    intro rank member
    exact List.mem_range.mpr (bounded rank member)
  have bound := nodup_length_le_of_subset set.unique subset
  simpa [card] using bound

end ScheduleRankSet

/-- Three disjoint visited-address sets for one token sequence. -/
structure FastParserScheduleTrace (tokens : List Token) where
  fixedVisited : ScheduleRankSet
  boundaryVisited : ScheduleRankSet
  memoVisited : ScheduleRankSet
  fixedBounded : ∀ rank, rank ∈ fixedVisited.valuesRev → rank < 1
  boundaryBounded : ∀ rank, rank ∈ boundaryVisited.valuesRev →
    rank < fastBoundarySlotAddressCapacity tokens
  memoBounded : ∀ rank, rank ∈ memoVisited.valuesRev →
    rank < fastMemoSlotAddressCapacity tokens

namespace FastParserScheduleTrace

/-- The trace before any schedule address has been charged. -/
def empty (tokens : List Token) : FastParserScheduleTrace tokens := {
  fixedVisited := ScheduleRankSet.empty
  boundaryVisited := ScheduleRankSet.empty
  memoVisited := ScheduleRankSet.empty
  fixedBounded := by
    intro rank member
    change rank ∈ ([] : List Nat) at member
    simp at member
  boundaryBounded := by
    intro rank member
    change rank ∈ ([] : List Nat) at member
    simp at member
  memoBounded := by
    intro rank member
    change rank ∈ ([] : List Nat) at member
    simp at member
}

/-- Whether an address rank is already present in its component set. -/
def visited {tokens : List Token} (trace : FastParserScheduleTrace tokens) :
    FastParserUnitAddress tokens → Bool
  | .fixed address => trace.fixedVisited.contains address.rank.val
  | .boundarySlot address => trace.boundaryVisited.contains address.rank.val
  | .memoSlot address => trace.memoVisited.contains address.rank.val

@[simp] theorem empty_visited (tokens : List Token)
    (address : FastParserUnitAddress tokens) :
    (empty tokens).visited address = false := by
  cases address <;> rfl

private def chargeFixed? {tokens : List Token}
    (trace : FastParserScheduleTrace tokens)
    (address : FastFixedUnitAddress) :
    Option (FastParserScheduleTrace tokens) :=
  if fresh : address.rank.val ∉ trace.fixedVisited.valuesRev then
    some {
      fixedVisited := trace.fixedVisited.insert address.rank.val fresh
      boundaryVisited := trace.boundaryVisited
      memoVisited := trace.memoVisited
      fixedBounded := by
        intro rank member
        change rank ∈ address.rank.val :: trace.fixedVisited.valuesRev at member
        simp only [List.mem_cons] at member
        rcases member with equal | oldMember
        · exact equal ▸ address.rank.isLt
        · exact trace.fixedBounded rank oldMember
      boundaryBounded := trace.boundaryBounded
      memoBounded := trace.memoBounded
    }
  else
    none

private def chargeBoundary? {tokens : List Token}
    (trace : FastParserScheduleTrace tokens)
    (address : FastBoundarySlotAddress tokens) :
    Option (FastParserScheduleTrace tokens) :=
  if fresh : address.rank.val ∉ trace.boundaryVisited.valuesRev then
    some {
      fixedVisited := trace.fixedVisited
      boundaryVisited := trace.boundaryVisited.insert address.rank.val fresh
      memoVisited := trace.memoVisited
      fixedBounded := trace.fixedBounded
      boundaryBounded := by
        intro rank member
        change rank ∈
          address.rank.val :: trace.boundaryVisited.valuesRev at member
        simp only [List.mem_cons] at member
        rcases member with equal | oldMember
        · exact equal ▸ address.rank.isLt
        · exact trace.boundaryBounded rank oldMember
      memoBounded := trace.memoBounded
    }
  else
    none

private def chargeMemo? {tokens : List Token}
    (trace : FastParserScheduleTrace tokens)
    (address : FastMemoSlotAddress tokens) :
    Option (FastParserScheduleTrace tokens) :=
  if fresh : address.rank.val ∉ trace.memoVisited.valuesRev then
    some {
      fixedVisited := trace.fixedVisited
      boundaryVisited := trace.boundaryVisited
      memoVisited := trace.memoVisited.insert address.rank.val fresh
      fixedBounded := trace.fixedBounded
      boundaryBounded := trace.boundaryBounded
      memoBounded := by
        intro rank member
        change rank ∈ address.rank.val :: trace.memoVisited.valuesRev at member
        simp only [List.mem_cons] at member
        rcases member with equal | oldMember
        · exact equal ▸ address.rank.isLt
        · exact trace.memoBounded rank oldMember
    }
  else
    none

/-- Charge one address exactly when its canonical rank is fresh. -/
def charge? {tokens : List Token} (trace : FastParserScheduleTrace tokens) :
    FastParserUnitAddress tokens → Option (FastParserScheduleTrace tokens)
  | .fixed address => chargeFixed? trace address
  | .boundarySlot address => chargeBoundary? trace address
  | .memoSlot address => chargeMemo? trace address

/-- Resource ledger obtained only from the three finite-set cardinalities. -/
def ledger {tokens : List Token}
    (trace : FastParserScheduleTrace tokens) : ParserResourceLedger := {
  fixedUnits := trace.fixedVisited.card
  boundarySlotUnits := trace.boundaryVisited.card
  memoSlotUnits := trace.memoVisited.card
}

/-- Total number of distinct charged addresses. -/
def actualUnits {tokens : List Token}
    (trace : FastParserScheduleTrace tokens) : Nat :=
  trace.ledger.total

@[simp] theorem empty_ledger (tokens : List Token) :
    (empty tokens).ledger = {
      fixedUnits := 0
      boundarySlotUnits := 0
      memoSlotUnits := 0
    } := by
  rfl

@[simp] theorem empty_actualUnits (tokens : List Token) :
    (empty tokens).actualUnits = 0 := by
  rfl

theorem ledger_fitsWithin {tokens : List Token}
    (trace : FastParserScheduleTrace tokens) :
    trace.ledger.FitsWithin (fastParserScheduleAddressCapacity tokens) := by
  exact ⟨trace.fixedVisited.card_le_of_bounded trace.fixedBounded,
    trace.boundaryVisited.card_le_of_bounded trace.boundaryBounded,
    trace.memoVisited.card_le_of_bounded trace.memoBounded⟩

/-- Every trace is bounded because each component is a set of ranks in its
declared finite capacity. -/
theorem actualUnits_le_parseBound {tokens : List Token}
    (trace : FastParserScheduleTrace tokens) :
    trace.actualUnits ≤ parseBound (tokens.length + 1) := by
  apply parseUnits_le_parseBound_of_ledger
    (ledger := trace.ledger)
  · exact Nat.le_refl _
  · simpa using trace.ledger_fitsWithin

private theorem freshOption_eq_none_iff_contains
    {Result : Type} (set : ScheduleRankSet) (rank : Nat)
    (onFresh : rank ∉ set.valuesRev → Result) :
    (if fresh : rank ∉ set.valuesRev then
        some (onFresh fresh)
      else
        none) = none ↔ set.contains rank = true := by
  by_cases fresh : rank ∉ set.valuesRev
  · rw [dif_pos fresh]
    constructor
    · intro impossible
      cases impossible
    · intro present
      have member :=
        (ScheduleRankSet.contains_eq_true_iff_mem set rank).mp present
      exact (fresh member).elim
  · have member : rank ∈ set.valuesRev := by
      exact Decidable.byContradiction fresh
    rw [dif_neg fresh]
    constructor
    · intro _
      exact (ScheduleRankSet.contains_eq_true_iff_mem set rank).mpr member
    · intro _
      rfl

@[simp] theorem charge?_eq_none_iff_visited {tokens : List Token}
    (trace : FastParserScheduleTrace tokens)
    (address : FastParserUnitAddress tokens) :
    trace.charge? address = none ↔ trace.visited address = true := by
  cases address with
  | fixed address =>
      change chargeFixed? trace address = none ↔
        trace.fixedVisited.contains address.rank.val = true
      unfold chargeFixed?
      exact freshOption_eq_none_iff_contains _ _ _
  | boundarySlot address =>
      change chargeBoundary? trace address = none ↔
        trace.boundaryVisited.contains address.rank.val = true
      unfold chargeBoundary?
      exact freshOption_eq_none_iff_contains _ _ _
  | memoSlot address =>
      change chargeMemo? trace address = none ↔
        trace.memoVisited.contains address.rank.val = true
      unfold chargeMemo?
      exact freshOption_eq_none_iff_contains _ _ _

private theorem chargeFixed?_success_visited {tokens : List Token}
    {trace result : FastParserScheduleTrace tokens}
    {address : FastFixedUnitAddress}
    (selected : chargeFixed? trace address = some result) :
    result.fixedVisited.contains address.rank.val = true := by
  unfold chargeFixed? at selected
  split at selected
  · rename_i fresh
    cases selected
    exact ScheduleRankSet.contains_insert_self _ _ fresh
  · cases selected

private theorem chargeBoundary?_success_visited {tokens : List Token}
    {trace result : FastParserScheduleTrace tokens}
    {address : FastBoundarySlotAddress tokens}
    (selected : chargeBoundary? trace address = some result) :
    result.boundaryVisited.contains address.rank.val = true := by
  unfold chargeBoundary? at selected
  split at selected
  · rename_i fresh
    cases selected
    exact ScheduleRankSet.contains_insert_self _ _ fresh
  · cases selected

private theorem chargeMemo?_success_visited {tokens : List Token}
    {trace result : FastParserScheduleTrace tokens}
    {address : FastMemoSlotAddress tokens}
    (selected : chargeMemo? trace address = some result) :
    result.memoVisited.contains address.rank.val = true := by
  unfold chargeMemo? at selected
  split at selected
  · rename_i fresh
    cases selected
    exact ScheduleRankSet.contains_insert_self _ _ fresh
  · cases selected

theorem charge?_success_visited {tokens : List Token}
    {trace result : FastParserScheduleTrace tokens}
    {address : FastParserUnitAddress tokens}
    (selected : trace.charge? address = some result) :
    result.visited address = true := by
  cases address with
  | fixed address =>
      change chargeFixed? trace address = some result at selected
      change result.fixedVisited.contains address.rank.val = true
      exact chargeFixed?_success_visited selected
  | boundarySlot address =>
      change chargeBoundary? trace address = some result at selected
      change result.boundaryVisited.contains address.rank.val = true
      exact chargeBoundary?_success_visited selected
  | memoSlot address =>
      change chargeMemo? trace address = some result at selected
      change result.memoVisited.contains address.rank.val = true
      exact chargeMemo?_success_visited selected

/-- Recharging an address immediately after its successful first charge is
rejected. -/
theorem charge?_duplicate {tokens : List Token}
    {trace result : FastParserScheduleTrace tokens}
    {address : FastParserUnitAddress tokens}
    (selected : trace.charge? address = some result) :
    result.charge? address = none := by
  rw [charge?_eq_none_iff_visited]
  exact charge?_success_visited selected

/-- A successful charge preserves the non-visited status of every address with
a different canonical rank. -/
theorem charge?_success_preserves_not_visited {tokens : List Token}
    {trace result : FastParserScheduleTrace tokens}
    {charged existing : FastParserUnitAddress tokens}
    (selected : trace.charge? charged = some result)
    (different : charged.rank ≠ existing.rank)
    (unvisited : trace.visited existing = false) :
    result.visited existing = false := by
  cases charged with
  | fixed chargedAddress =>
      change chargeFixed? trace chargedAddress = some result at selected
      unfold chargeFixed? at selected
      split at selected
      · rename_i fresh
        cases selected
        cases existing with
        | fixed existingAddress =>
            simp only [visited] at unvisited ⊢
            rw [ScheduleRankSet.contains_insert_of_ne]
            · exact unvisited
            · intro equal
              apply different
              have addressEqual : chargedAddress = existingAddress :=
                FastFixedUnitAddress.rank_injective (Fin.ext equal)
              cases addressEqual
              rfl
        | boundarySlot existingAddress =>
            simpa only [visited] using unvisited
        | memoSlot existingAddress =>
            simpa only [visited] using unvisited
      · cases selected
  | boundarySlot chargedAddress =>
      change chargeBoundary? trace chargedAddress = some result at selected
      unfold chargeBoundary? at selected
      split at selected
      · rename_i fresh
        cases selected
        cases existing with
        | fixed existingAddress =>
            simpa only [visited] using unvisited
        | boundarySlot existingAddress =>
            simp only [visited] at unvisited ⊢
            rw [ScheduleRankSet.contains_insert_of_ne]
            · exact unvisited
            · intro equal
              apply different
              have addressEqual : chargedAddress = existingAddress :=
                FastBoundarySlotAddress.rank_injective (Fin.ext equal)
              cases addressEqual
              rfl
        | memoSlot existingAddress =>
            simpa only [visited] using unvisited
      · cases selected
  | memoSlot chargedAddress =>
      change chargeMemo? trace chargedAddress = some result at selected
      unfold chargeMemo? at selected
      split at selected
      · rename_i fresh
        cases selected
        cases existing with
        | fixed existingAddress =>
            simpa only [visited] using unvisited
        | boundarySlot existingAddress =>
            simpa only [visited] using unvisited
        | memoSlot existingAddress =>
            simp only [visited] at unvisited ⊢
            rw [ScheduleRankSet.contains_insert_of_ne]
            · exact unvisited
            · intro equal
              apply different
              have addressEqual : chargedAddress = existingAddress :=
                FastMemoSlotAddress.rank_injective (Fin.ext equal)
              cases addressEqual
              rfl
      · cases selected

/-- Every successful fresh charge increases the distinct-address total by
exactly one. -/
theorem charge?_actualUnits {tokens : List Token}
    {trace result : FastParserScheduleTrace tokens}
    {address : FastParserUnitAddress tokens}
    (selected : trace.charge? address = some result) :
    result.actualUnits = trace.actualUnits + 1 := by
  cases address with
  | fixed address =>
      change chargeFixed? trace address = some result at selected
      unfold chargeFixed? at selected
      split at selected
      · rename_i fresh
        cases selected
        change
          (trace.fixedVisited.insert address.rank.val fresh).card +
              trace.boundaryVisited.card + trace.memoVisited.card =
            trace.fixedVisited.card + trace.boundaryVisited.card +
              trace.memoVisited.card + 1
        rw [ScheduleRankSet.card_insert]
        omega
      · cases selected
  | boundarySlot address =>
      change chargeBoundary? trace address = some result at selected
      unfold chargeBoundary? at selected
      split at selected
      · rename_i fresh
        cases selected
        change
          trace.fixedVisited.card +
              (trace.boundaryVisited.insert address.rank.val fresh).card +
                trace.memoVisited.card =
            trace.fixedVisited.card + trace.boundaryVisited.card +
              trace.memoVisited.card + 1
        rw [ScheduleRankSet.card_insert]
        omega
      · cases selected
  | memoSlot address =>
      change chargeMemo? trace address = some result at selected
      unfold chargeMemo? at selected
      split at selected
      · rename_i fresh
        cases selected
        change
          trace.fixedVisited.card + trace.boundaryVisited.card +
              (trace.memoVisited.insert address.rank.val fresh).card =
            trace.fixedVisited.card + trace.boundaryVisited.card +
              trace.memoVisited.card + 1
        rw [ScheduleRankSet.card_insert]
        omega
      · cases selected

end FastParserScheduleTrace

end Solcore.Surface.Multi
