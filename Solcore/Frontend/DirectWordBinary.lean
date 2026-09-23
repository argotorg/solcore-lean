import Solcore.Syntax.Operator
import Solcore.Core.Syntax

/-! The fixed Word interpretation of the ten directly lowered source operators.
The finite relation is independent of checking and runtime evaluation. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive DirectWordBinary : Syntax.BinaryOp → Core.BinaryOp → Prop where
  | add : DirectWordBinary .add .wordAdd
  | subtract : DirectWordBinary .subtract .wordSub
  | multiply : DirectWordBinary .multiply .wordMul
  | divide : DirectWordBinary .divide .wordDiv
  | modulo : DirectWordBinary .modulo .wordMod
  | bitAnd : DirectWordBinary .bitAnd .wordAnd
  | bitOr : DirectWordBinary .bitOr .wordOr
  | bitXor : DirectWordBinary .bitXor .wordXor
  | greater : DirectWordBinary .greater .wordGt
  | equal : DirectWordBinary .equal .wordEq

def directWordBinary? : Syntax.BinaryOp → Option Core.BinaryOp
  | .add => some .wordAdd
  | .subtract => some .wordSub
  | .multiply => some .wordMul
  | .divide => some .wordDiv
  | .modulo => some .wordMod
  | .bitAnd => some .wordAnd
  | .bitOr => some .wordOr
  | .bitXor => some .wordXor
  | .greater => some .wordGt
  | .equal => some .wordEq
  | _ => none

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.DirectWordBinaryProperties`
-/

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
