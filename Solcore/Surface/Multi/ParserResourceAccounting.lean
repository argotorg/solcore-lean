import Solcore.Surface.Multi.ResourceBounds

set_option autoImplicit false

namespace Solcore.Surface.Multi

/-!
The optimized parser schedule described by `parseBound` has three numeric
components.  This module exposes their accounting shape and the exact
reduction needed by a counted executor.

The existing `Chart.G` counter uses a separate, larger chart address universe.
Its private execution ledger is intentionally not reinterpreted as this fast
schedule.  Connecting a future public fast-parser counter requires both an
operational accounting theorem and the component bounds made explicit below.
-/

/-- Recorded work split according to the three summands of the fixed fast
parser schedule. -/
structure ParserResourceLedger where
  fixedUnits : Nat
  boundarySlotUnits : Nat
  memoSlotUnits : Nat
deriving DecidableEq, Repr

namespace ParserResourceLedger

/-- Total units represented by a parser-resource ledger. -/
def total (ledger : ParserResourceLedger) : Nat :=
  ledger.fixedUnits + ledger.boundarySlotUnits + ledger.memoSlotUnits

@[simp] theorem total_equation (ledger : ParserResourceLedger) :
    ledger.total =
      ledger.fixedUnits + ledger.boundarySlotUnits + ledger.memoSlotUnits := by
  rfl

theorem fixedUnits_le_total (ledger : ParserResourceLedger) :
    ledger.fixedUnits ≤ ledger.total := by
  simp only [total]
  omega

theorem boundarySlotUnits_le_total (ledger : ParserResourceLedger) :
    ledger.boundarySlotUnits ≤ ledger.total := by
  simp only [total]
  omega

theorem memoSlotUnits_le_total (ledger : ParserResourceLedger) :
    ledger.memoSlotUnits ≤ ledger.total := by
  simp only [total]
  omega

/-- Componentwise comparison of two ledgers. -/
def FitsWithin (ledger capacity : ParserResourceLedger) : Prop :=
  ledger.fixedUnits ≤ capacity.fixedUnits ∧
    ledger.boundarySlotUnits ≤ capacity.boundarySlotUnits ∧
    ledger.memoSlotUnits ≤ capacity.memoSlotUnits

theorem total_le_total {ledger capacity : ParserResourceLedger}
    (fits : ledger.FitsWithin capacity) :
    ledger.total ≤ capacity.total := by
  rcases fits with ⟨fixedBound, boundaryBound, memoBound⟩
  simp only [total]
  omega

end ParserResourceLedger

/-- The three schedule capacities whose sum is exactly `parseBound`.
`terminalCount` already includes the logical end-of-file terminal. -/
def parserScheduleCapacity (terminalCount : Nat) : ParserResourceLedger :=
  let boundaryCount := terminalCount + 1
  {
    fixedUnits := 1
    boundarySlotUnits := 32 * Grammar.F * boundaryCount
    memoSlotUnits :=
      256 * Grammar.F * boundaryCount * boundaryCount
  }

@[simp] theorem parserScheduleCapacity_fixedUnits (terminalCount : Nat) :
    (parserScheduleCapacity terminalCount).fixedUnits = 1 := by
  rfl

@[simp] theorem parserScheduleCapacity_boundarySlotUnits
    (terminalCount : Nat) :
    (parserScheduleCapacity terminalCount).boundarySlotUnits =
      32 * Grammar.F * (terminalCount + 1) := by
  rfl

@[simp] theorem parserScheduleCapacity_memoSlotUnits
    (terminalCount : Nat) :
    (parserScheduleCapacity terminalCount).memoSlotUnits =
      256 * Grammar.F * (terminalCount + 1) * (terminalCount + 1) := by
  rfl

/-- The capacity ledger is an exact decomposition of the fixed parser bound. -/
@[simp] theorem parserScheduleCapacity_total
    (terminalCount : Nat) :
    (parserScheduleCapacity terminalCount).total = parseBound terminalCount := by
  rfl

theorem parserScheduleCapacity_total_positive (terminalCount : Nat) :
    0 < (parserScheduleCapacity terminalCount).total := by
  rw [parserScheduleCapacity_total]
  exact parseBound_positive terminalCount

/-- A ledger proved componentwise within the fixed schedule is bounded by
`parseBound`.  This theorem does not assert that an executor has yet supplied
such a ledger. -/
theorem ParserResourceLedger.total_le_parseBound
    {terminalCount : Nat} {ledger : ParserResourceLedger}
    (fits : ledger.FitsWithin (parserScheduleCapacity terminalCount)) :
    ledger.total ≤ parseBound terminalCount := by
  rw [← parserScheduleCapacity_total terminalCount]
  exact ParserResourceLedger.total_le_total fits

/-- Final numeric reduction for a counted parser.  The first premise is the
operational correspondence from its execution counter to this ledger; the
second premise assigns every recorded component to the fixed schedule. -/
theorem parseUnits_le_parseBound_of_ledger
    {terminalCount actualUnits : Nat} {ledger : ParserResourceLedger}
    (accounted : actualUnits ≤ ledger.total)
    (fits : ledger.FitsWithin (parserScheduleCapacity terminalCount)) :
    actualUnits ≤ parseBound terminalCount := by
  exact Nat.le_trans accounted (ledger.total_le_parseBound fits)

/-- Equivalent reduction with the three required component inequalities
spelled out for an executor proof. -/
theorem parseUnits_le_parseBound_of_component_bounds
    {terminalCount actualUnits : Nat}
    {fixedUnits boundarySlotUnits memoSlotUnits : Nat}
    (accounted :
      actualUnits ≤ fixedUnits + boundarySlotUnits + memoSlotUnits)
    (fixedBound : fixedUnits ≤ 1)
    (boundaryBound :
      boundarySlotUnits ≤ 32 * Grammar.F * (terminalCount + 1))
    (memoBound :
      memoSlotUnits ≤
        256 * Grammar.F * (terminalCount + 1) * (terminalCount + 1)) :
    actualUnits ≤ parseBound terminalCount := by
  let ledger : ParserResourceLedger := {
    fixedUnits
    boundarySlotUnits
    memoSlotUnits
  }
  apply parseUnits_le_parseBound_of_ledger
    (ledger := ledger)
  · simpa only [ledger, ParserResourceLedger.total] using accounted
  · exact ⟨fixedBound, boundaryBound, memoBound⟩

end Solcore.Surface.Multi
