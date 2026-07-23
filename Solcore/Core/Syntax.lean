set_option autoImplicit false

namespace Solcore.Core

def wordModulus : Nat := 2 ^ 256

abbrev Word := Fin wordModulus

namespace Word

def ofNat? (value : Nat) : Option Word :=
  if isLt : value < wordModulus then
    some ⟨value, isLt⟩
  else
    none

def zero : Word := ⟨0, by simp [wordModulus]⟩

end Word

inductive Ty where
  | unit
  | bool
  | word
  deriving Repr, BEq, DecidableEq

inductive Expr where
  | unit
  | bool (value : Bool)
  | word (value : Word)
  | var (index : Nat)
  | letE (value : Expr) (body : Expr)
  | ifE (condition : Expr) (thenBranch : Expr) (elseBranch : Expr)
  deriving Repr, BEq, DecidableEq

inductive Value where
  | unit
  | bool (value : Bool)
  | word (value : Word)
  deriving Repr, BEq, DecidableEq

def Value.type : Value → Ty
  | .unit => .unit
  | .bool _ => .bool
  | .word _ => .word

abbrev Context := List Ty

abbrev Environment := List Value

structure Program where
  resultType : Ty
  body : Expr
  deriving Repr, BEq, DecidableEq

end Solcore.Core
