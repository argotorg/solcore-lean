import Solcore.Frontend.DirectWordBinary

/-! One exact correspondence for the finite direct-operator interpretation. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem directWordBinary?_iff {source : Syntax.BinaryOp} {op : Core.BinaryOp} :
    directWordBinary? source = some op ↔ DirectWordBinary source op := by
  constructor
  · intro accepted
    cases source <;> simp only [directWordBinary?, Option.some.injEq, reduceCtorEq] at accepted
    all_goals subst op; constructor
  · intro operator
    cases operator <;> rfl

end Solcore.Frontend
