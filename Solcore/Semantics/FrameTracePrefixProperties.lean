import Solcore.Semantics.FrameTracePrefix
import Solcore.Semantics.FrameTraceProperties

/-! Canonical witnesses and transitivity for ordered trace prefixes. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameTrace

universe u

theorem empty_isPrefixOf {Event : Type u}
    (trace : FrameTrace Event) :
    IsPrefixOf empty trace :=
  ⟨trace, (append_empty_left trace).symm⟩

theorem isPrefixOf_refl {Event : Type u}
    (trace : FrameTrace Event) :
    IsPrefixOf trace trace :=
  ⟨empty, (append_empty_right trace).symm⟩

theorem isPrefixOf_append {Event : Type u}
    (earlier fragment : FrameTrace Event) :
    IsPrefixOf earlier (append earlier fragment) :=
  ⟨fragment, rfl⟩

theorem isPrefixOf_trans
    {Event : Type u} {first second third : FrameTrace Event}
    (firstSecond : IsPrefixOf first second)
    (secondThird : IsPrefixOf second third) :
    IsPrefixOf first third := by
  rcases firstSecond with ⟨middleFragment, rfl⟩
  rcases secondThird with ⟨lastFragment, rfl⟩
  exact ⟨append middleFragment lastFragment,
    append_assoc first middleFragment lastFragment⟩

end Solcore.Semantics.FrameTrace
