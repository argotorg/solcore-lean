import Solcore.ContractRuntime.FrameTrace

/-! Non-strict prefix factorization for finite chronological frame traces. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace

universe u

/-- An earlier trace whose ordered extension equals the later trace. -/
def IsPrefixOf {Event : Type u}
    (earlier later : FrameTrace Event) : Prop :=
  ∃ fragment, later = append earlier fragment

end Solcore.ContractRuntime.FrameTrace
