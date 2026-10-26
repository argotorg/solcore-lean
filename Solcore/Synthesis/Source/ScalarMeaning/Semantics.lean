import Solcore.Synthesis.Source.ScalarMeaning.Syntax

/-! Independent meaning of the emitted Rust-dialect fragment. Words are
natural numbers below `2^256`; operators follow the EVM instruction that the
pinned standard library (`std/std.sol` and `std/opcodes.sol` at solcore-rs
`2a745e12974c373c3799fec81b48a53c7dce2ab4`) selects for `word` operands. Pairs,
`sum`, `inl` and `inr` are frontend builtins at the same revision
(`crates/hir/src/nameres/builtins.rs`); this fragment has pairs of words and
sums of two words. Locals live in a stack of lexical scopes: `let` declares in
the innermost scope, assignment updates the nearest binding, and each `if`
branch or `match` case runs in a fresh scope that is discarded afterwards; a
case scope starts with its pattern variables. A call resolves to an earlier
free function, then to an imported `std.opcodes` alias, then to `std.tobool`.
Nothing here refers to Core. -/
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

/-- Two's-complement reading of a word. -/
def toSigned (word : Nat) : Int :=
  if word < 2 ^ 255 then (word : Int) else (word : Int) - (modulus : Int)

/-- The word representing an integer modulo `2^256`. -/
def ofSigned (value : Int) : Nat := (value % (modulus : Int)).toNat

/-- `DIV`: unsigned division; a zero divisor gives zero. -/
def div (left right : Nat) : Nat := if right = 0 then 0 else left / right

/-- `MOD`: unsigned remainder; a zero divisor gives zero. -/
def mod (left right : Nat) : Nat := if right = 0 then 0 else left % right

/-- `SDIV`: signed division truncated toward zero; a zero divisor gives zero
and `-2^255 / -1` wraps to `-2^255`. -/
def sdiv (left right : Nat) : Nat :=
  if right = 0 then 0 else ofSigned (Int.tdiv (toSigned left) (toSigned right))

/-- `SMOD`: signed remainder with the sign of the dividend; a zero divisor
gives zero. -/
def smod (left right : Nat) : Nat :=
  if right = 0 then 0 else ofSigned (Int.tmod (toSigned left) (toSigned right))

/-- `SGT`: signed comparison `left > right`. -/
def sgt (left right : Nat) : Nat := if toSigned right < toSigned left then 1 else 0

/-- `SHL(shift, value)`; shifts of 256 or more give zero. -/
def shl (shift value : Nat) : Nat :=
  if shift < 256 then (value * 2 ^ shift) % modulus else 0

/-- `SHR(shift, value)`; shifts of 256 or more give zero. -/
def shr (shift value : Nat) : Nat := if shift < 256 then value / 2 ^ shift else 0

/-- `SAR(shift, value)`: floor division of the signed value; shifts of 256 or
more give zero or all ones. -/
def sar (shift value : Nat) : Nat :=
  if shift < 256 then ofSigned (toSigned value / ((2 ^ shift : Nat) : Int))
  else if toSigned value < 0 then modulus - 1 else 0

/-- `ADDMOD`: the sum is not truncated before the remainder; a zero modulus
gives zero. -/
def addmod (left right divisor : Nat) : Nat :=
  if divisor = 0 then 0 else (left + right) % divisor

/-- `MULMOD`: the product is not truncated before the remainder; a zero
modulus gives zero. -/
def mulmod (left right divisor : Nat) : Nat :=
  if divisor = 0 then 0 else (left * right) % divisor

/-- `CLZ`: leading zero bits of a 256-bit word; zero gives 256. -/
def clz (value : Nat) : Nat := if value = 0 then 256 else 255 - Nat.log2 value

/-- `BYTE(index, value)`: the byte at `index`, counted from the most
significant end; indices of 32 or more give zero. -/
def byte (index value : Nat) : Nat :=
  if index < 32 then (value / 256 ^ (31 - index)) % 256 else 0

/-- `SIGNEXTEND(index, value)`: extend the sign bit of the low `index + 1`
bytes; indices of 31 or more leave the value unchanged. -/
def signextend (index value : Nat) : Nat :=
  if index < 31 then
    let width := 8 * (index + 1)
    let low := value % 2 ^ width
    if low < 2 ^ (width - 1) then low else low + (modulus - 2 ^ width)
  else value

/-- Modular exponentiation by squaring; `exp_spec` states that it computes
`base ^ exponent mod 2^256`. -/
def powMod (base exponent : Nat) : Nat :=
  if zero : exponent = 0 then 1 % modulus
  else
    let half := powMod base (exponent / 2)
    let square := half * half % modulus
    if exponent % 2 = 0 then square else square * (base % modulus) % modulus
termination_by exponent
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)

/-- `EXP(base, exponent)`: `base ^ exponent mod 2^256`. -/
def exp (base exponent : Nat) : Nat := powMod base exponent

end Evm

/-- The standard library's `tobool`: zero is `false`, every other word is
`true`. `Eq<word>.eq` is `tobool(eq(x, y))` and `Ord<word>.gt` is
`tobool(gt(x, y))`. -/
def toBool (word : Nat) : Bool := !(word == 0)

/-- Runtime values of the fragment. `uint256` is the standard library enum
wrapping one word. `pair` is a value of type `(word, word)`; `inl` and `inr`
are the two tags of `sum<word, word>`, each with one word payload. -/
inductive Value where
  | word (value : Nat)
  | bool (value : Bool)
  | uint256 (value : Nat)
  | pair (first second : Nat)
  | inl (payload : Nat)
  | inr (payload : Nat)
  deriving Repr, BEq, DecidableEq

def LocalType.admits : LocalType → Value → Bool
  | .word, .word _ => true
  | .bool, .bool _ => true
  | .wordPair, .pair _ _ => true
  | .wordSum, .inl _ => true
  | .wordSum, .inr _ => true
  | _, _ => false

/-- Assignment keeps the type of the existing binding. Both sum tags have
type `sum<word, word>`. -/
def Value.sameType : Value → Value → Bool
  | .word _, .word _ => true
  | .bool _, .bool _ => true
  | .uint256 _, .uint256 _ => true
  | .pair _ _, .pair _ _ => true
  | .inl _, .inl _ => true
  | .inl _, .inr _ => true
  | .inr _, .inl _ => true
  | .inr _, .inr _ => true
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

/-- The `std.opcodes` wrappers pass their `word` arguments, in order, to the
EVM instruction of the same name. -/
def opcodeMeaning : String → List Value → Option Value
  | "div", [.word left, .word right] => some (.word (Evm.div left right))
  | "mod", [.word left, .word right] => some (.word (Evm.mod left right))
  | "sdiv", [.word left, .word right] => some (.word (Evm.sdiv left right))
  | "smod", [.word left, .word right] => some (.word (Evm.smod left right))
  | "sgt", [.word left, .word right] => some (.word (Evm.sgt left right))
  | "shl", [.word shift, .word value] => some (.word (Evm.shl shift value))
  | "shr", [.word shift, .word value] => some (.word (Evm.shr shift value))
  | "sar", [.word shift, .word value] => some (.word (Evm.sar shift value))
  | "addmod", [.word left, .word right, .word divisor] =>
      some (.word (Evm.addmod left right divisor))
  | "mulmod", [.word left, .word right, .word divisor] =>
      some (.word (Evm.mulmod left right divisor))
  | "clz", [.word value] => some (.word (Evm.clz value))
  | "byte", [.word index, .word value] => some (.word (Evm.byte index value))
  | "exp", [.word base, .word exponent] => some (.word (Evm.exp base exponent))
  | "signextend", [.word index, .word value] => some (.word (Evm.signextend index value))
  | _, _ => none

/-- Functions reachable through `import * from std` in this fragment. -/
def builtinMeaning : String → List Value → Option Value
  | "tobool", [.word value] => some (.bool (toBool value))
  | _, _ => none

/-- What a call can reach: the denotations of the free functions declared
so far, most recent first, and the `std.opcodes` aliases as
`(opcode, alias)` pairs. -/
structure Context where
  functions : List (String × (List Value → Option Value))
  aliases : List (String × String)

def Context.empty : Context := { functions := [], aliases := [] }

def Context.call (context : Context) (callee : String) (arguments : List Value) :
    Option Value :=
  match context.functions.find? (·.1 == callee) with
  | some (_, meaning) => meaning arguments
  | none =>
      match context.aliases.find? (·.2 == callee) with
      | some (opcode, _) => opcodeMeaning opcode arguments
      | none => builtinMeaning callee arguments

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
this fragment. Literals of `2^256` or more have no meaning. Arguments and pair
components are evaluated left to right. A pair or a sum payload must be a
word. -/
def Expr.eval (context : Context) (frames : Frames) : Expr → Option Value
  | .name identifier => frames.lookup identifier
  | .number value => if value < Evm.modulus then some (.word value) else none
  | .bool value => some (.bool value)
  | .unary op operand => do op.apply (← operand.eval context frames)
  | .binary op left right => do
      let leftValue ← left.eval context frames
      let rightValue ← right.eval context frames
      op.apply leftValue rightValue
  | .typedefRep operand => do
      match ← operand.eval context frames with
      | .uint256 value => some (.word value)
      | _ => none
  | .uint256 operand => do
      match ← operand.eval context frames with
      | .word value => some (.uint256 value)
      | _ => none
  | .call1 callee first => do
      let firstValue ← first.eval context frames
      context.call callee [firstValue]
  | .call2 callee first second => do
      let firstValue ← first.eval context frames
      let secondValue ← second.eval context frames
      context.call callee [firstValue, secondValue]
  | .call3 callee first second third => do
      let firstValue ← first.eval context frames
      let secondValue ← second.eval context frames
      let thirdValue ← third.eval context frames
      context.call callee [firstValue, secondValue, thirdValue]
  | .tuple first second => do
      let firstValue ← first.eval context frames
      let secondValue ← second.eval context frames
      match firstValue, secondValue with
      | .word left, .word right => some (.pair left right)
      | _, _ => none
  | .inl payload => do
      match ← payload.eval context frames with
      | .word value => some (.inl value)
      | _ => none
  | .inr payload => do
      match ← payload.eval context frames with
      | .word value => some (.inr value)
      | _ => none

mutual

/-- Execute one statement. A failed lookup, type mismatch, non-Boolean
condition or unmatched scrutinee has no meaning (`none`). A `match` evaluates
its scrutinee once; the selected case runs in a fresh scope binding the
pattern variables to the components or the payload, first component first. -/
def Stmt.exec (context : Context) : Frames → Stmt → Option Frames
  | frames, .letDecl identifier type initializer =>
      match initializer.eval context frames with
      | some value => if type.admits value then frames.declare identifier value else none
      | none => none
  | frames, .assign identifier value =>
      match value.eval context frames, frames.lookup identifier with
      | some new, some old => if new.sameType old then frames.assign identifier new else none
      | _, _ => none
  | frames, .ifElse condition thenBlock elseBlock =>
      match condition.eval context frames with
      | some (.bool true) =>
          match Stmt.execList context ([] :: frames) thenBlock with
          | some (_ :: frames') => some frames'
          | _ => none
      | some (.bool false) =>
          match Stmt.execList context ([] :: frames) elseBlock with
          | some (_ :: frames') => some frames'
          | _ => none
      | _ => none
  | frames, .matchPair scrutinee first second body =>
      match scrutinee.eval context frames with
      | some (.pair left right) =>
          match Stmt.execList context ([(second, .word right), (first, .word left)] :: frames)
              body with
          | some (_ :: frames') => some frames'
          | _ => none
      | _ => none
  | frames, .matchSum scrutinee left leftBody right rightBody =>
      match scrutinee.eval context frames with
      | some (.inl payload) =>
          match Stmt.execList context ([(left, .word payload)] :: frames) leftBody with
          | some (_ :: frames') => some frames'
          | _ => none
      | some (.inr payload) =>
          match Stmt.execList context ([(right, .word payload)] :: frames) rightBody with
          | some (_ :: frames') => some frames'
          | _ => none
      | _ => none

def Stmt.execList (context : Context) : Frames → List Stmt → Option Frames
  | frames, [] => some frames
  | frames, statement :: rest =>
      match statement.exec context frames with
      | some frames' => Stmt.execList context frames' rest
      | none => none

end

/-- Bind typed parameters, first parameter last so the scope stays
most-recent-first. -/
def FunctionDecl.bindParameters : List (String × LocalType) → List Value → Option Scope
  | [], [] => some []
  | (parameter, type) :: parameters, argument :: arguments =>
      if type.admits argument then
        (fun scope => scope ++ [(parameter, argument)]) <$>
          FunctionDecl.bindParameters parameters arguments
      else none
  | _, _ => none

/-- A free function's meaning: its body runs in a block scope inside its
parameter scope, and the returned value must have the declared type. -/
def FunctionDecl.denote (context : Context) (function : FunctionDecl)
    (arguments : List Value) : Option Value := do
  let parameters ← FunctionDecl.bindParameters function.parameters arguments
  let frames ← Stmt.execList context [[], parameters] function.body
  let value ← function.result.eval context frames
  if function.resultType.admits value then some value else none

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
def Method.run (context : Context) (method : Method) (arguments : List Nat) : Option Nat := do
  let parameters ← Method.bindParameters method.parameters arguments
  let frames ← Stmt.execList context [[], parameters] method.body
  match ← method.result.eval context frames with
  | .uint256 value => some value
  | _ => none

/-- The call context after the given free functions. Each function sees only
the functions declared before it; this fragment has no other calls. -/
def declareFunctions (aliases : List (String × String)) :
    List (String × (List Value → Option Value)) → List FunctionDecl →
      List (String × (List Value → Option Value))
  | functions, [] => functions
  | functions, function :: rest =>
      declareFunctions aliases
        ((function.name, function.denote { functions, aliases }) :: functions) rest

def SourceFile.context (file : SourceFile) : Context :=
  { functions := declareFunctions file.opcodeAliases [] file.functions
    aliases := file.opcodeAliases }

/-- The returned ABI word of calling `method` on the file's contract. -/
def SourceFile.call (file : SourceFile) (method : String) (arguments : List Nat) :
    Option Nat :=
  if file.method.name = method then file.method.run file.context arguments else none

theorem Stmt.execList_append (context : Context) (frames : Frames) (first second : List Stmt) :
    Stmt.execList context frames (first ++ second) =
      (Stmt.execList context frames first).bind
        (fun frames' => Stmt.execList context frames' second) := by
  induction first generalizing frames with
  | nil => simp [Stmt.execList]
  | cons statement rest ih =>
      simp only [List.cons_append, Stmt.execList]
      cases statement.exec context frames <;> simp [ih]

end Solcore.Synthesis.Source.ScalarMeaning
