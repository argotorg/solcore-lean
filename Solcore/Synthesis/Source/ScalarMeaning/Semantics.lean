import Solcore.Synthesis.Source.ScalarMeaning.Syntax

/-! Independent meaning of the emitted Rust-dialect fragment. Words are
natural numbers below `2^256`; operators follow the EVM instruction that the
pinned standard library (`std/std.sol` and `std/opcodes.sol` at solcore-rs
`2a745e12974c373c3799fec81b48a53c7dce2ab4`) selects for `word` operands.
Locals live in a stack of lexical scopes: `let` declares in the innermost
scope, assignment updates the nearest binding, and each `if` branch runs in a
fresh scope that is discarded afterwards. Nothing here refers to Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

namespace Evm

/-- The number of distinct EVM words. -/
def modulus : Nat := 2 ^ 256

/-- `ADD`: `Add<word>.add` is `addWord`, which calls the `add` opcode wrapper. -/
def add (left right : Nat) : Nat := (left + right) % modulus

/-- `SUB`: `Sub<word>.sub` is `subWord`, which calls the `sub` opcode wrapper. -/
def sub (left right : Nat) : Nat := (left + modulus - right) % modulus

/-- `MUL`: `Mul<word>.mul` is `mulWord`, which calls the `mul` opcode wrapper. -/
def mul (left right : Nat) : Nat := (left * right) % modulus

/-- `AND`: `BitAnd<word>.band` is `bandWord`, which calls `and`. -/
def and (left right : Nat) : Nat := left &&& right

/-- `OR`: `BitOr<word>.bor` is `borWord`, which calls `or`. -/
def or (left right : Nat) : Nat := left ||| right

/-- `XOR`: `BitXor<word>.bxor` is `bxorWord`, which calls `xor`. -/
def xor (left right : Nat) : Nat := left ^^^ right

/-- `NOT`: `BitNot<word>.bnot` is `bnotWord`, which calls `not`. -/
def not (value : Nat) : Nat := modulus - 1 - value

/-- `EQ` returns one for equal words and zero otherwise. -/
def eq (left right : Nat) : Nat := if left = right then 1 else 0

/-- `GT` is the unsigned comparison `left > right`. -/
def gt (left right : Nat) : Nat := if right < left then 1 else 0

end Evm

/-- The standard library's `tobool`: zero is `false`, every other word is
`true`. `Eq<word>.eq` is `tobool(eq(x, y))` and `Ord<word>.gt` is
`tobool(gt(x, y))`. -/
def toBool (word : Nat) : Bool := !(word == 0)

/-- Runtime values of the fragment. `uint256` is the standard library enum
wrapping one word. -/
inductive Value where
  | word (value : Nat)
  | bool (value : Bool)
  | uint256 (value : Nat)
  deriving Repr, BEq, DecidableEq

def LocalType.admits : LocalType → Value → Bool
  | .word, .word _ => true
  | .bool, .bool _ => true
  | _, _ => false

/-- Assignment keeps the type of the existing binding. -/
def Value.sameType : Value → Value → Bool
  | .word _, .word _ => true
  | .bool _, .bool _ => true
  | .uint256 _, .uint256 _ => true
  | _, _ => false

/-- `!` is the standard library function `not` on `bool`; `~` is
`BitNot<word>.bnot`. -/
def UnaryOp.apply : UnaryOp → Value → Option Value
  | .not, .bool flag => some (.bool (!flag))
  | .bitNot, .word value => some (.word (Evm.not value))
  | _, _ => none

/-- The infix operators resolve to the `word` instances of `Add`, `Sub`,
`Mul`, `BitAnd`, `BitOr`, `BitXor`, `Eq` and `Ord`. Other operand types are
outside this fragment. -/
def BinaryOp.apply : BinaryOp → Value → Value → Option Value
  | .add, .word left, .word right => some (.word (Evm.add left right))
  | .sub, .word left, .word right => some (.word (Evm.sub left right))
  | .mul, .word left, .word right => some (.word (Evm.mul left right))
  | .bitAnd, .word left, .word right => some (.word (Evm.and left right))
  | .bitOr, .word left, .word right => some (.word (Evm.or left right))
  | .bitXor, .word left, .word right => some (.word (Evm.xor left right))
  | .eq, .word left, .word right => some (.bool (toBool (Evm.eq left right)))
  | .gt, .word left, .word right => some (.bool (toBool (Evm.gt left right)))
  | _, _, _ => none

/-- One lexical scope, most recent declaration first. -/
abbrev Scope := List (String × Value)

/-- Lexical scopes, innermost first. -/
abbrev Frames := List Scope

def Scope.get? : Scope → String → Option Value
  | [], _ => none
  | (bound, value) :: rest, name => if bound = name then some value else Scope.get? rest name

/-- Replace the nearest binding of `name` in one scope. -/
def Scope.set? : Scope → String → Value → Option Scope
  | [], _, _ => none
  | (bound, old) :: rest, name, value =>
      if bound = name then some ((bound, value) :: rest)
      else ((bound, old) :: ·) <$> Scope.set? rest name value

def Scope.names (scope : Scope) : List String := scope.map Prod.fst

def Frames.lookup : Frames → String → Option Value
  | [], _ => none
  | scope :: outer, name =>
      match scope.get? name with
      | some value => some value
      | none => Frames.lookup outer name

def Frames.declare : Frames → String → Value → Option Frames
  | [], _, _ => none
  | scope :: outer, name, value => some (((name, value) :: scope) :: outer)

/-- Update the nearest binding; assigning an undeclared name fails. -/
def Frames.assign : Frames → String → Value → Option Frames
  | [], _, _ => none
  | scope :: outer, name, value =>
      match scope.set? name value with
      | some scope' => some (scope' :: outer)
      | none => (scope :: ·) <$> Frames.assign outer name value

/-- The declared names of every scope; assignment never changes it. -/
def Frames.shape (frames : Frames) : List (List String) := frames.map Scope.names

/-- A decimal literal denotes a word; `word` is the only numeric local type in
this fragment. Literals of `2^256` or more have no meaning here. -/
def Expr.eval (frames : Frames) : Expr → Option Value
  | .name identifier => frames.lookup identifier
  | .number value => if value < Evm.modulus then some (.word value) else none
  | .bool value => some (.bool value)
  | .unary op operand => do op.apply (← operand.eval frames)
  | .binary op left right => do
      let leftValue ← left.eval frames
      let rightValue ← right.eval frames
      op.apply leftValue rightValue
  | .typedefRep operand => do
      match ← operand.eval frames with
      | .uint256 value => some (.word value)
      | _ => none
  | .uint256 operand => do
      match ← operand.eval frames with
      | .word value => some (.uint256 value)
      | _ => none

mutual

/-- Execute one statement. A failed lookup, type mismatch or non-Boolean
condition has no meaning (`none`). -/
def Stmt.exec : Frames → Stmt → Option Frames
  | frames, .letDecl identifier type initializer =>
      match initializer.eval frames with
      | some value => if type.admits value then frames.declare identifier value else none
      | none => none
  | frames, .assign identifier value =>
      match value.eval frames, frames.lookup identifier with
      | some new, some old => if new.sameType old then frames.assign identifier new else none
      | _, _ => none
  | frames, .ifElse condition thenBlock elseBlock =>
      match condition.eval frames with
      | some (.bool true) =>
          match Stmt.execList ([] :: frames) thenBlock with
          | some (_ :: frames') => some frames'
          | _ => none
      | some (.bool false) =>
          match Stmt.execList ([] :: frames) elseBlock with
          | some (_ :: frames') => some frames'
          | _ => none
      | _ => none

def Stmt.execList : Frames → List Stmt → Option Frames
  | frames, [] => some frames
  | frames, statement :: rest =>
      match statement.exec frames with
      | some frames' => Stmt.execList frames' rest
      | none => none

end

/-- Bind each `uint256` parameter to its ABI word, first parameter last so the
scope stays most-recent-first. -/
def Method.bindParameters : List String → List Nat → Option Scope
  | [], [] => some []
  | parameter :: parameters, argument :: arguments =>
      if argument < Evm.modulus then
        (fun scope => scope ++ [(parameter, .uint256 argument)]) <$>
          Method.bindParameters parameters arguments
      else none
  | _, _ => none

/-- Call a method with ABI words: the body runs in a block scope inside the
parameter scope, then the returned expression must be a `uint256`. -/
def Method.run (method : Method) (arguments : List Nat) : Option Nat := do
  let parameters ← Method.bindParameters method.parameters arguments
  let frames ← Stmt.execList [[], parameters] method.body
  match ← method.result.eval frames with
  | .uint256 value => some value
  | _ => none

/-- The returned ABI word of calling `method` on the file's contract. -/
def SourceFile.call (file : SourceFile) (method : String) (arguments : List Nat) :
    Option Nat :=
  if file.method.name = method then file.method.run arguments else none

theorem Stmt.execList_append (frames : Frames) (first second : List Stmt) :
    Stmt.execList frames (first ++ second) =
      (Stmt.execList frames first).bind (fun frames' => Stmt.execList frames' second) := by
  induction first generalizing frames with
  | nil => simp [Stmt.execList]
  | cons statement rest ih =>
      simp only [List.cons_append, Stmt.execList]
      cases statement.exec frames <;> simp [ih]

end Solcore.Synthesis.Source.ScalarMeaning
