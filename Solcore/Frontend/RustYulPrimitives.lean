import Solcore.Core.Renaming

/-! Pure inline-Yul operations lowered to the existing Core language.
The operation names follow solcore-rs commit
`2a745e12974c373c3799fec81b48a53c7dce2ab4`. Arguments are evaluated from
right to left, once each, before the operation. Comparisons produce EVM words.
Memory, storage, calls and termination belong to the enclosing effect lowering.
-/

set_option autoImplicit false

namespace Solcore.Frontend.RustYulPrimitives

open Core

inductive Error where
  | unknownBuiltin (name : String)
  | wrongArity (name : String) (expected actual : Nat)
  deriving Repr, BEq, DecidableEq

structure Lowered where
  type : Ty
  expression : Expr
  deriving Repr, BEq, DecidableEq

private structure Operation where
  arity : Nat
  resultType : Ty
  /-- The nearest variables contain arguments in source order. -/
  body : Expr

private def asWord (condition : Expr) : Expr :=
  .ifE condition (.word (Word.ofNatModulo 1)) (.word Word.zero)

private def binary (operation : BinaryOp) : Operation :=
  ⟨2, .word, .binary operation (.var 0) (.var 1)⟩

private def comparison (operation : BinaryOp) : Operation :=
  ⟨2, .word, asWord (.binary operation (.var 0) (.var 1))⟩

private def reversedComparison (operation : BinaryOp) : Operation :=
  ⟨2, .word, asWord (.binary operation (.var 1) (.var 0))⟩

private def shift (operation : BinaryOp) : Operation :=
  -- Yul takes (distance, value); Core takes (value, distance).
  ⟨2, .word, .binary operation (.var 1) (.var 0)⟩

private def operation? (name : String) : Option Operation :=
  match name with
  | "add" => some (binary .wordAdd)
  | "sub" => some (binary .wordSub)
  | "mul" => some (binary .wordMul)
  | "div" => some (binary .wordDiv)
  | "mod" => some (binary .wordMod)
  | "sdiv" => some (binary .wordSdiv)
  | "smod" => some (binary .wordSmod)
  | "exp" => some (binary .wordPow)
  | "signextend" => some (binary .wordSignExtend)
  | "lt" => some (reversedComparison .wordGt)
  | "gt" => some (comparison .wordGt)
  | "slt" => some (reversedComparison .wordSgt)
  | "sgt" => some (comparison .wordSgt)
  | "eq" => some (comparison .wordEq)
  | "iszero" => some ⟨1, .word, asWord (.binary .wordEq (.var 0) (.word Word.zero))⟩
  | "and" => some (binary .wordAnd)
  | "or" => some (binary .wordOr)
  | "xor" => some (binary .wordXor)
  | "not" => some ⟨1, .word, .unary .wordNot (.var 0)⟩
  | "byte" => some (binary .wordByte)
  | "shl" => some (shift .wordShl)
  | "shr" => some (shift .wordShr)
  | "sar" => some (shift .wordSar)
  | "clz" => some ⟨1, .word, .unary .wordClz (.var 0)⟩
  | "addmod" => some ⟨3, .word, .ternary .wordAddMod (.var 0) (.var 1) (.var 2)⟩
  | "mulmod" => some ⟨3, .word, .ternary .wordMulMod (.var 0) (.var 1) (.var 2)⟩
  | "pop" => some ⟨1, .unit, .unit⟩
  | _ => none

/-- Check whether a name belongs to the pure EVM operation fragment. -/
def supports (name : String) : Bool := (operation? name).isSome

private def bindArguments (resultType : Ty) (body : Expr) : Nat → List Expr → Expr
  | _, [] => body
  | depth, argument :: rest =>
      -- Typed lambda binders also require `pop`'s discarded input to be a word.
      .apply (.lambda .word resultType (bindArguments resultType body (depth + 1) rest))
        (argument.rename fun index => index + depth)

/-- Build ordinary Core code, with explicit arity and unknown-name errors.
The enclosing compiler checks the result in its lexical Core context. Every
argument is a typed word binder, including discarded `pop` arguments. -/
def compile (name : String) (arguments : List Expr) : Except Error Lowered := do
  let operation ← match operation? name with
    | some operation => pure operation
    | none => throw (.unknownBuiltin name)
  unless arguments.length = operation.arity do
    throw (.wrongArity name operation.arity arguments.length)
  pure ⟨operation.resultType,
    bindArguments operation.resultType operation.body 0 arguments.reverse⟩

end Solcore.Frontend.RustYulPrimitives
