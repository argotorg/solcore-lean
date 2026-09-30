/-! Mathematical integer operations used by native Core primitives. These
pure definitions keep zero-divisor and infinite two's-complement behavior
explicit. Integer-to-Word conversion remains the existing modulo conversion. -/

set_option autoImplicit false

namespace Solcore.Core.Integer

def divide (left right : Int) : Int :=
  if right = 0 then 0 else left / right

def modulo (left right : Int) : Int :=
  if right = 0 then 0 else left % right

def bitAnd : Int → Int → Int
  | .ofNat left, .ofNat right => .ofNat (left &&& right)
  | .ofNat left, .negSucc right => .ofNat (left ^^^ (left &&& right))
  | .negSucc left, .ofNat right => .ofNat (right ^^^ (right &&& left))
  | .negSucc left, .negSucc right => .negSucc (left ||| right)

def bitOr : Int → Int → Int
  | .ofNat left, .ofNat right => .ofNat (left ||| right)
  | .ofNat left, .negSucc right => .negSucc (right ^^^ (right &&& left))
  | .negSucc left, .ofNat right => .negSucc (left ^^^ (left &&& right))
  | .negSucc left, .negSucc right => .negSucc (left &&& right)

def bitXor : Int → Int → Int
  | .ofNat left, .ofNat right => .ofNat (left ^^^ right)
  | .ofNat left, .negSucc right => .negSucc (left ^^^ right)
  | .negSucc left, .ofNat right => .negSucc (left ^^^ right)
  | .negSucc left, .negSucc right => .ofNat (left ^^^ right)

@[simp] theorem divide_zero (left : Int) : divide left 0 = 0 := by simp [divide]
@[simp] theorem modulo_zero (left : Int) : modulo left 0 = 0 := by simp [modulo]

theorem divide_nonzero (left right : Int) (nonzero : right ≠ 0) :
    divide left right = left / right := by simp [divide, nonzero]

theorem modulo_nonzero (left right : Int) (nonzero : right ≠ 0) :
    modulo left right = left % right := by simp [modulo, nonzero]

end Solcore.Core.Integer
