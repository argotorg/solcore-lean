import Solcore.Core.Syntax

/-!
# Panics

Solidity's `Panic(code)` as a Core language failure. Each panic code fails with its own reason
in the top 256 words, the same in every function. The fault-site tables allocate their reasons
below that range, and diagnostics decode a reason in it as the panic it names. Main declarations:
`SourceCorePanics.reason`, `SourceCorePanics.code?` and `SourceCorePanics.revertData`.

The codes that Lean's source language raises are `divisionByZero` (`0x12`, unchecked `/` and `%`
by zero) and, with the integer types, `arithmetic` (`0x11`).
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCorePanics

/-- The first reason of the panic range. -/
def base : Nat := 2 ^ 256 - 2 ^ 8

/-- Division or remainder by zero. -/
def divisionByZero : UInt8 := 0x12

/-- An arithmetic result outside its type. -/
def arithmetic : UInt8 := 0x11

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

end Solcore.Frontend.SourceCorePanics
