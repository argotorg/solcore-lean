import Solcore.ContractRuntime.RuntimeScalars

/-! Lossless internal conversion between runtime addresses and Core words. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

private theorem addressModulus_lt_wordModulus :
    addressModulus < Core.wordModulus := by
  decide

/-- Widen an address to a Core word while preserving its natural-number value. -/
def addressToWord (address : Address) : Core.Word :=
  ⟨address.val, Nat.lt_trans address.isLt addressModulus_lt_wordModulus⟩

/--
Narrow a Core word only when its value fits in an address, without truncation
or modular reduction.
-/
def wordToAddress? (word : Core.Word) : Option Address :=
  if inRange : word.val < addressModulus then
    some ⟨word.val, inRange⟩
  else
    none

end Solcore.ContractRuntime
