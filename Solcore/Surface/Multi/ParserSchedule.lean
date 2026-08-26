import Solcore.Surface.Multi.ParserCore
import Solcore.Surface.Multi.ParserResourceAccounting

set_option autoImplicit false

namespace Solcore.Surface.Multi

/-!
Typed addresses and numeric accounting for the fixed fast-parser schedule.

This module defines only the finite address space and an efficient counter that
can be charged with those addresses.  It does not define a parser or connect a
parser transition to a charge.  In particular, these addresses are independent
of the larger contextual chart address space.
-/

/-- A constructive certificate that a type has exactly `size` inhabitants. -/
structure ExactFiniteRanking (alpha : Type) (size : Nat) where
  rank : alpha → Fin size
  injective : Function.Injective rank
  surjective : Function.Surjective rank

private def finPairRank {leftSize rightSize : Nat}
    (left : Fin leftSize) (right : Fin rightSize) :
    Fin (leftSize * rightSize) := by
  refine ⟨left.val * rightSize + right.val, ?_⟩
  have withinRow :
      left.val * rightSize + right.val <
        left.val * rightSize + rightSize :=
    Nat.add_lt_add_left right.isLt _
  have nextRow :
      left.val * rightSize + rightSize =
        (left.val + 1) * rightSize := by
    simp [Nat.add_mul]
  have afterLastRow :
      (left.val + 1) * rightSize ≤ leftSize * rightSize :=
    Nat.mul_le_mul_right rightSize (Nat.succ_le_of_lt left.isLt)
  exact Nat.lt_of_lt_of_le (nextRow ▸ withinRow) afterLastRow

private theorem finPairRank_injective {leftSize rightSize : Nat} :
    Function.Injective
      (fun pair : Fin leftSize × Fin rightSize =>
        finPairRank pair.1 pair.2) := by
  intro left right equal
  have rightSizePositive : 0 < rightSize := by
    exact Nat.zero_lt_of_lt left.2.isLt
  have leftQuotient :
      (finPairRank left.1 left.2).val / rightSize = left.1.val := by
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · rw [show (left.1.val + 1) * rightSize =
        left.1.val * rightSize + rightSize by simp [Nat.add_mul]]
      exact Nat.add_lt_add_left left.2.isLt _
  have rightQuotient :
      (finPairRank right.1 right.2).val / rightSize = right.1.val := by
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · rw [show (right.1.val + 1) * rightSize =
        right.1.val * rightSize + rightSize by simp [Nat.add_mul]]
      exact Nat.add_lt_add_left right.2.isLt _
  have sameLeftValue : left.1.val = right.1.val := by
    calc
      left.1.val =
          (finPairRank left.1 left.2).val / rightSize :=
        leftQuotient.symm
      _ = (finPairRank right.1 right.2).val / rightSize := by
        exact congrArg (fun value => value.val / rightSize) equal
      _ = right.1.val := rightQuotient
  have sameRightValue : left.2.val = right.2.val := by
    have equalValue := congrArg Fin.val equal
    simp only [finPairRank] at equalValue
    rw [sameLeftValue] at equalValue
    exact Nat.add_left_cancel equalValue
  exact Prod.ext (Fin.ext sameLeftValue) (Fin.ext sameRightValue)

private theorem finPairRank_surjective {leftSize rightSize : Nat} :
    Function.Surjective
      (fun pair : Fin leftSize × Fin rightSize =>
        finPairRank pair.1 pair.2) := by
  intro value
  have productPositive : 0 < leftSize * rightSize :=
    Nat.zero_lt_of_lt value.isLt
  have rightSizePositive : 0 < rightSize := by
    apply Nat.pos_of_ne_zero
    intro rightSizeZero
    simp [rightSizeZero] at productPositive
  let left : Fin leftSize := {
    val := value.val / rightSize
    isLt := Nat.div_lt_of_lt_mul (by
      exact Nat.lt_of_lt_of_eq value.isLt
        (Nat.mul_comm leftSize rightSize))
  }
  let right : Fin rightSize := {
    val := value.val % rightSize
    isLt := Nat.mod_lt _ rightSizePositive
  }
  refine ⟨(left, right), Fin.ext ?_⟩
  exact Nat.div_add_mod' value.val rightSize

private theorem finPairRank_components
    {leftSize rightSize : Nat}
    {leftFirst rightFirst : Fin leftSize}
    {leftSecond rightSecond : Fin rightSize}
    (equal :
      finPairRank leftFirst leftSecond =
        finPairRank rightFirst rightSecond) :
    leftFirst = rightFirst ∧ leftSecond = rightSecond := by
  have pairEqual :
      (leftFirst, leftSecond) = (rightFirst, rightSecond) := by
    apply finPairRank_injective
    exact equal
  exact ⟨congrArg Prod.fst pairEqual, congrArg Prod.snd pairEqual⟩

/-- The canonical index of a memo-key family in the displayed grammar
enumeration. -/
abbrev FastMemoKindIndex : Type := Fin Grammar.F

namespace FastMemoKindIndex

/-- Recover the grammar memo-key family selected by a schedule index. -/
def kind (index : FastMemoKindIndex) : Grammar.FastMemoKeyKind :=
  Grammar.allFastMemoKeyKinds[index.val]'(by
    exact (show index.val < Grammar.allFastMemoKeyKinds.length from
      index.isLt))

end FastMemoKindIndex

/-- The sole fixed unit reserved by the fast-parser schedule. -/
inductive FastFixedUnitAddress where
  | startup
  deriving Repr, DecidableEq

namespace FastFixedUnitAddress

/-- Rank the fixed startup address in its one-element capacity. -/
def rank : FastFixedUnitAddress → Fin 1
  | .startup => ⟨0, by omega⟩

theorem rank_injective : Function.Injective rank := by
  intro left right _
  cases left
  cases right
  rfl

theorem rank_surjective : Function.Surjective rank := by
  intro value
  refine ⟨.startup, Fin.ext ?_⟩
  omega

/-- The fixed address family has exactly the fixed schedule capacity. -/
def ranking : ExactFiniteRanking FastFixedUnitAddress 1 := {
  rank
  injective := rank_injective
  surjective := rank_surjective
}

end FastFixedUnitAddress

/-- One of the 32 fixed boundary-local slots for a displayed memo-key family. -/
structure FastBoundarySlotAddress (tokens : List Token) where
  kind : FastMemoKindIndex
  boundary : Boundary tokens
  slot : Fin 32
  deriving Repr, DecidableEq

/-- Exact capacity of the boundary-local address family. -/
def fastBoundarySlotAddressCapacity (tokens : List Token) : Nat :=
  32 * Grammar.F * (tokens.length + 2)

namespace FastBoundarySlotAddress

/-- A finite rank for boundary-local addresses.  The rank is an encoding, not
an execution-order declaration. -/
def rank {tokens : List Token} (address : FastBoundarySlotAddress tokens) :
    Fin (fastBoundarySlotAddressCapacity tokens) :=
  finPairRank (finPairRank address.slot address.kind) address.boundary

theorem rank_injective {tokens : List Token} :
    Function.Injective (@rank tokens) := by
  intro left right equal
  obtain ⟨innerEqual, boundaryEqual⟩ :=
    finPairRank_components equal
  obtain ⟨slotEqual, kindEqual⟩ :=
    finPairRank_components innerEqual
  cases left
  cases right
  simp_all

theorem rank_surjective {tokens : List Token} :
    Function.Surjective (@rank tokens) := by
  intro value
  obtain ⟨outer, outerEqual⟩ := finPairRank_surjective value
  obtain ⟨inner, innerEqual⟩ := finPairRank_surjective outer.1
  change finPairRank outer.1 outer.2 = value at outerEqual
  change finPairRank inner.1 inner.2 = outer.1 at innerEqual
  refine ⟨{
    kind := inner.2
    boundary := outer.2
    slot := inner.1
  }, ?_⟩
  change finPairRank (finPairRank inner.1 inner.2) outer.2 = value
  rw [innerEqual, outerEqual]

/-- Boundary-local addresses exactly fill their numeric schedule component. -/
def ranking (tokens : List Token) :
    ExactFiniteRanking (FastBoundarySlotAddress tokens)
      (fastBoundarySlotAddressCapacity tokens) := {
  rank
  injective := rank_injective
  surjective := rank_surjective
}

end FastBoundarySlotAddress

/-- One of the 256 fixed span-local slots for a displayed memo-key family. -/
structure FastMemoSlotAddress (tokens : List Token) where
  kind : FastMemoKindIndex
  start : Boundary tokens
  finish : Boundary tokens
  slot : Fin 256
  deriving Repr, DecidableEq

/-- Exact capacity of the span-local memo address family. -/
def fastMemoSlotAddressCapacity (tokens : List Token) : Nat :=
  256 * Grammar.F * (tokens.length + 2) * (tokens.length + 2)

namespace FastMemoSlotAddress

/-- A finite rank for span-local memo addresses.  The rank is an encoding, not
an execution-order declaration. -/
def rank {tokens : List Token} (address : FastMemoSlotAddress tokens) :
    Fin (fastMemoSlotAddressCapacity tokens) :=
  finPairRank
    (finPairRank (finPairRank address.slot address.kind) address.start)
    address.finish

theorem rank_injective {tokens : List Token} :
    Function.Injective (@rank tokens) := by
  intro left right equal
  change
    finPairRank
        (finPairRank (finPairRank left.slot left.kind) left.start)
        left.finish =
      finPairRank
        (finPairRank (finPairRank right.slot right.kind) right.start)
        right.finish at equal
  obtain ⟨throughStartEqual, finishEqual⟩ :=
    finPairRank_components equal
  obtain ⟨throughKindEqual, startEqual⟩ :=
    finPairRank_components throughStartEqual
  obtain ⟨slotEqual, kindEqual⟩ :=
    finPairRank_components throughKindEqual
  cases left
  cases right
  simp_all

theorem rank_surjective {tokens : List Token} :
    Function.Surjective (@rank tokens) := by
  intro value
  obtain ⟨throughFinish, finishEqual⟩ := finPairRank_surjective value
  obtain ⟨throughStart, startEqual⟩ :=
    finPairRank_surjective throughFinish.1
  obtain ⟨slotKind, kindEqual⟩ := finPairRank_surjective throughStart.1
  change finPairRank throughFinish.1 throughFinish.2 = value at finishEqual
  change finPairRank throughStart.1 throughStart.2 =
    throughFinish.1 at startEqual
  change finPairRank slotKind.1 slotKind.2 = throughStart.1 at kindEqual
  refine ⟨{
    kind := slotKind.2
    start := throughStart.2
    finish := throughFinish.2
    slot := slotKind.1
  }, ?_⟩
  change
    finPairRank
        (finPairRank (finPairRank slotKind.1 slotKind.2) throughStart.2)
        throughFinish.2 = value
  rw [kindEqual, startEqual, finishEqual]

/-- Span-local addresses exactly fill their numeric schedule component. -/
def ranking (tokens : List Token) :
    ExactFiniteRanking (FastMemoSlotAddress tokens)
      (fastMemoSlotAddressCapacity tokens) := {
  rank
  injective := rank_injective
  surjective := rank_surjective
}

end FastMemoSlotAddress

/-- Every chargeable unit family in the fixed fast-parser schedule. -/
inductive FastParserUnitAddress (tokens : List Token) where
  | fixed (address : FastFixedUnitAddress)
  | boundarySlot (address : FastBoundarySlotAddress tokens)
  | memoSlot (address : FastMemoSlotAddress tokens)
  deriving Repr, DecidableEq

/-- Address capacities packaged in the public parser-resource ledger shape. -/
def fastParserScheduleAddressCapacity
    (tokens : List Token) : ParserResourceLedger := {
  fixedUnits := 1
  boundarySlotUnits := fastBoundarySlotAddressCapacity tokens
  memoSlotUnits := fastMemoSlotAddressCapacity tokens
}

/-- Total size of the disjoint fixed, boundary-local, and span-local address
families. -/
def fastParserUnitAddressCapacity (tokens : List Token) : Nat :=
  1 + fastBoundarySlotAddressCapacity tokens +
    fastMemoSlotAddressCapacity tokens

namespace FastParserUnitAddress

/-- Rank the three tagged address families into adjacent numeric regions. -/
def rank {tokens : List Token} (address : FastParserUnitAddress tokens) :
    Fin (fastParserUnitAddressCapacity tokens) := by
  cases address with
  | fixed fixedAddress =>
      refine ⟨fixedAddress.rank.val, ?_⟩
      have := fixedAddress.rank.isLt
      unfold fastParserUnitAddressCapacity
      omega
  | boundarySlot boundaryAddress =>
      refine ⟨1 + boundaryAddress.rank.val, ?_⟩
      have := boundaryAddress.rank.isLt
      unfold fastParserUnitAddressCapacity
      omega
  | memoSlot memoAddress =>
      refine ⟨1 + fastBoundarySlotAddressCapacity tokens +
        memoAddress.rank.val, ?_⟩
      have := memoAddress.rank.isLt
      unfold fastParserUnitAddressCapacity
      omega

theorem rank_injective {tokens : List Token} :
    Function.Injective (@rank tokens) := by
  intro left right equal
  have equalValue := congrArg Fin.val equal
  cases left with
  | fixed leftAddress =>
      cases right with
      | fixed rightAddress =>
          cases leftAddress
          cases rightAddress
          rfl
      | boundarySlot rightAddress =>
          have := rightAddress.rank.isLt
          simp only [rank] at equalValue
          omega
      | memoSlot rightAddress =>
          have := rightAddress.rank.isLt
          simp only [rank] at equalValue
          omega
  | boundarySlot leftAddress =>
      cases right with
      | fixed rightAddress =>
          have := leftAddress.rank.isLt
          simp only [rank] at equalValue
          omega
      | boundarySlot rightAddress =>
          have addressRankEqual :
              leftAddress.rank = rightAddress.rank := by
            apply Fin.ext
            simp only [rank] at equalValue
            omega
          have addressEqual :=
            FastBoundarySlotAddress.rank_injective addressRankEqual
          cases addressEqual
          rfl
      | memoSlot rightAddress =>
          have leftBound := leftAddress.rank.isLt
          have rightBound := rightAddress.rank.isLt
          simp only [rank] at equalValue
          omega
  | memoSlot leftAddress =>
      cases right with
      | fixed rightAddress =>
          have := leftAddress.rank.isLt
          simp only [rank] at equalValue
          omega
      | boundarySlot rightAddress =>
          have leftBound := leftAddress.rank.isLt
          have rightBound := rightAddress.rank.isLt
          simp only [rank] at equalValue
          omega
      | memoSlot rightAddress =>
          have addressRankEqual : leftAddress.rank = rightAddress.rank := by
            apply Fin.ext
            simp only [rank] at equalValue
            omega
          have addressEqual :=
            FastMemoSlotAddress.rank_injective addressRankEqual
          cases addressEqual
          rfl

theorem rank_surjective {tokens : List Token} :
    Function.Surjective (@rank tokens) := by
  intro value
  by_cases inFixedRegion : value.val < 1
  · have valueZero : value.val = 0 := by omega
    refine ⟨.fixed .startup, Fin.ext ?_⟩
    exact valueZero.symm
  · by_cases inBoundaryRegion :
      value.val < 1 + fastBoundarySlotAddressCapacity tokens
    · let boundaryIndex : Fin (fastBoundarySlotAddressCapacity tokens) := {
        val := value.val - 1
        isLt := by omega
      }
      obtain ⟨address, addressRankEqual⟩ :=
        FastBoundarySlotAddress.rank_surjective boundaryIndex
      refine ⟨.boundarySlot address, Fin.ext ?_⟩
      have equalValue := congrArg Fin.val addressRankEqual
      simp only [rank]
      change address.rank.val = value.val - 1 at equalValue
      omega
    · let memoIndex : Fin (fastMemoSlotAddressCapacity tokens) := {
        val := value.val -
          (1 + fastBoundarySlotAddressCapacity tokens)
        isLt := by
          have valueBound := value.isLt
          unfold fastParserUnitAddressCapacity at valueBound
          omega
      }
      obtain ⟨address, addressRankEqual⟩ :=
        FastMemoSlotAddress.rank_surjective memoIndex
      refine ⟨.memoSlot address, Fin.ext ?_⟩
      have equalValue := congrArg Fin.val addressRankEqual
      simp only [rank]
      change address.rank.val = value.val -
        (1 + fastBoundarySlotAddressCapacity tokens) at equalValue
      omega

/-- The tagged address universe has exactly the sum of all three capacities. -/
def ranking (tokens : List Token) :
    ExactFiniteRanking (FastParserUnitAddress tokens)
      (fastParserUnitAddressCapacity tokens) := {
  rank
  injective := rank_injective
  surjective := rank_surjective
}

end FastParserUnitAddress

/-- Token-indexed address capacities are exactly the fixed numeric schedule
with its logical end-of-file terminal included. -/
@[simp] theorem fastParserScheduleAddressCapacity_eq
    (tokens : List Token) :
    fastParserScheduleAddressCapacity tokens =
      parserScheduleCapacity (tokens.length + 1) := by
  rfl

@[simp] theorem fastParserScheduleAddressCapacity_total
    (tokens : List Token) :
    (fastParserScheduleAddressCapacity tokens).total =
      parseBound (tokens.length + 1) := by
  rw [fastParserScheduleAddressCapacity_eq,
    parserScheduleCapacity_total]

@[simp] theorem fastParserUnitAddressCapacity_eq_total
    (tokens : List Token) :
    fastParserUnitAddressCapacity tokens =
      (fastParserScheduleAddressCapacity tokens).total := by
  rfl

@[simp] theorem fastParserUnitAddressCapacity_eq_parseBound
    (tokens : List Token) :
    fastParserUnitAddressCapacity tokens =
      parseBound (tokens.length + 1) := by
  rw [fastParserUnitAddressCapacity_eq_total,
    fastParserScheduleAddressCapacity_total]

/-- A lightweight token-indexed counter for future transitions charged with
typed schedule addresses.  It records only the component totals, not a
materialized trace.  Repeated-address prevention and the resulting capacity
certificate remain obligations of the future transition system. -/
structure FastParserCounter (tokens : List Token) where
  fixedUnits : Nat
  boundarySlotUnits : Nat
  memoSlotUnits : Nat
  deriving Repr, DecidableEq

namespace FastParserCounter

/-- The empty fast-schedule counter. -/
def zero (tokens : List Token) : FastParserCounter tokens := {
  fixedUnits := 0
  boundarySlotUnits := 0
  memoSlotUnits := 0
}

/-- Project a counter into the common parser-resource ledger. -/
def ledger {tokens : List Token}
    (counter : FastParserCounter tokens) : ParserResourceLedger := {
  fixedUnits := counter.fixedUnits
  boundarySlotUnits := counter.boundarySlotUnits
  memoSlotUnits := counter.memoSlotUnits
}

/-- Total units recorded by the counter. -/
def actualUnits {tokens : List Token}
    (counter : FastParserCounter tokens) : Nat :=
  counter.fixedUnits + counter.boundarySlotUnits + counter.memoSlotUnits

/-- Charge one typed schedule address to its ledger component. -/
def charge {tokens : List Token} (counter : FastParserCounter tokens) :
    FastParserUnitAddress tokens → FastParserCounter tokens
  | .fixed _ => { counter with fixedUnits := counter.fixedUnits + 1 }
  | .boundarySlot _ => {
      counter with boundarySlotUnits := counter.boundarySlotUnits + 1
    }
  | .memoSlot _ => {
      counter with memoSlotUnits := counter.memoSlotUnits + 1
    }

@[simp] theorem zero_ledger (tokens : List Token) : (zero tokens).ledger = {
    fixedUnits := 0
    boundarySlotUnits := 0
    memoSlotUnits := 0
  } := by
  rfl

@[simp] theorem actualUnits_eq_ledger_total {tokens : List Token}
    (counter : FastParserCounter tokens) :
    counter.actualUnits = counter.ledger.total := by
  rfl

@[simp] theorem charge_actualUnits {tokens : List Token}
    (counter : FastParserCounter tokens)
    (address : FastParserUnitAddress tokens) :
    (counter.charge address).actualUnits = counter.actualUnits + 1 := by
  cases address <;> simp [charge, actualUnits]
  all_goals omega

/-- Numeric reduction for any counter whose three components have separately
been proved to fit the token-indexed schedule. -/
theorem actualUnits_le_parseBound {tokens : List Token}
    (counter : FastParserCounter tokens)
    (fits : counter.ledger.FitsWithin
      (fastParserScheduleAddressCapacity tokens)) :
    counter.actualUnits ≤ parseBound (tokens.length + 1) := by
  apply parseUnits_le_parseBound_of_ledger
    (ledger := counter.ledger)
  · rw [actualUnits_eq_ledger_total]
    exact Nat.le_refl _
  · simpa using fits

end FastParserCounter

end Solcore.Surface.Multi
