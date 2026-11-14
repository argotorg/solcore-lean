import Solcore.Core.Syntax

/-!
# Panics

Solidity's `Panic(code)` as a Core language failure. Each panic code fails with its own reason
in the top 256 words, the same in every function. The word just below them is the reason of
`DirtyHigherBitsForInteger()`, upstream's ABI decoders' error, which a conversion of a word that
is not canonical for its fixed-width type raises. The fault-site tables allocate their reasons
below both (`tableBound`), and diagnostics decode a reason in that reserved range as the error it
names. Main declarations: `SourceCorePanics.reason`, `SourceCorePanics.code?`,
`SourceCorePanics.revertData`, `SourceCorePanics.dirtyReason` and
`SourceCorePanics.dirtyRevertData`.

The codes that Lean's source language raises are `divisionByZero` (`0x12`, unchecked `/` and `%`
by zero), with the integer types `arithmetic` (`0x11`), and with memory arrays `allocation`
(`0x41`, a length from 2^251 − 1 on) and `outOfBounds` (`0x32`, an index from the length on).
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCorePanics

/-- The first reason of the panic range. -/
def base : Nat := 2 ^ 256 - 2 ^ 8

/-- Division or remainder by zero. -/
def divisionByZero : UInt8 := 0x12

/-- An arithmetic result outside its type. -/
def arithmetic : UInt8 := 0x11

/-- A memory array too long to allocate. -/
def allocation : UInt8 := 0x41

/-- A memory array read at or past the array's length. -/
def outOfBounds : UInt8 := 0x32

theorem base_add_lt (code : UInt8) : base + code.toNat < Core.wordModulus := by
  have bound := code.toNat_lt
  simp only [base, Core.wordModulus] at bound ⊢
  omega

/-- The Core failure reason of `Panic(code)`. -/
def reason (code : UInt8) : Core.Word := ⟨base + code.toNat, base_add_lt code⟩

/-- The panic code of a reason in the panic range. -/
def code? (reason : Core.Word) : Option UInt8 :=
  if base ≤ reason.val then some (UInt8.ofNat (reason.val - base)) else none

theorem reason_val (code : UInt8) : (reason code).val = base + code.toNat := rfl

theorem base_le_reason (code : UInt8) : base ≤ (reason code).val := by
  simp [reason_val]

theorem code?_reason (code : UInt8) : code? (reason code) = some code := by
  rw [code?, if_pos (base_le_reason code), reason_val, Nat.add_sub_cancel_left, UInt8.ofNat_toNat]

theorem reason_injective {first second : UInt8} (same : reason first = reason second) : first = second := by
  have codes := congrArg code? same
  simpa only [code?_reason, Option.some.injEq] using codes

/-- A reason below the panic range is no panic. -/
theorem code?_eq_none {reason : Core.Word} (below : reason.val < base) : code? reason = none := by
  simp [code?, Nat.not_le.mpr below]

/-- Upstream's revert data for `Panic(code)`: the selector `0x4e487b71`, then the code as a
32-byte big-endian word. -/
def revertData (code : UInt8) : ByteArray :=
  ⟨#[0x4e, 0x48, 0x7b, 0x71] ++ Array.replicate 31 0 ++ #[code]⟩

theorem revertData_size (code : UInt8) : (revertData code).size = 36 := by
  simp [revertData, ByteArray.size]

/-- The bound below which the fault-site tables allocate their reasons: the reason of
`DirtyHigherBitsForInteger()` and the panic range lie at or above it. -/
def tableBound : Nat := base - 1

theorem tableBound_lt_base : tableBound < base := by
  unfold tableBound base
  decide

theorem tableBound_lt : tableBound < Core.wordModulus := by
  unfold tableBound base Core.wordModulus
  decide

/-- The Core failure reason of `DirtyHigherBitsForInteger()`: the word at `tableBound`, just below
the panic range. -/
def dirtyReason : Core.Word := ⟨tableBound, tableBound_lt⟩

theorem dirtyReason_val : dirtyReason.val = tableBound := rfl

/-- The dirty-integer reason is no panic. -/
theorem code?_dirtyReason : code? dirtyReason = none :=
  code?_eq_none tableBound_lt_base

/-- A reason below `tableBound` is not the dirty-integer reason. -/
theorem ne_dirtyReason_of_lt {reason : Core.Word} (below : reason.val < tableBound) :
    reason ≠ dirtyReason := by
  intro same
  rw [same, dirtyReason_val] at below
  exact Nat.lt_irrefl _ below

/-- A reason below `tableBound` is no panic. -/
theorem code?_eq_none_of_lt {reason : Core.Word} (below : reason.val < tableBound) :
    code? reason = none :=
  code?_eq_none (Nat.lt_trans below tableBound_lt_base)

/-- No panic's reason is the dirty-integer reason. -/
theorem reason_ne_dirtyReason (code : UInt8) : reason code ≠ dirtyReason := by
  intro same
  have value := congrArg Fin.val same
  have high := base_le_reason code
  have below := tableBound_lt_base
  change (reason code).val = tableBound at value
  omega

/-- Upstream's revert data for `DirtyHigherBitsForInteger()`: its selector `0x6cc54a63`, with no
arguments. -/
def dirtyRevertData : ByteArray := ⟨#[0x6c, 0xc5, 0x4a, 0x63]⟩

theorem dirtyRevertData_size : dirtyRevertData.size = 4 := by
  simp [dirtyRevertData, ByteArray.size]

end Solcore.Frontend.SourceCorePanics
