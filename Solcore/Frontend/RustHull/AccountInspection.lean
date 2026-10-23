import Solcore.Frontend.RustHull.AccountState
import Solcore.Frontend.RustHull.Keccak

/-! External code observations run on the Core account catalog. Pending
SELFDESTRUCT does not hide code: deletion belongs to transaction finalization.
An incomplete world or an account without supplied code fails explicitly. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountInspection
open Core CodeBuilder

def definitions : DataEnvironment := AccountState.definitions
def unknownCodeReason : Word := Word.ofNatModulo 15

private def known (resultType : Core.Ty) (record : Code) (body : Code) : Code :=
  choose (part 6 9 record) body (failure resultType (constant (.word unknownCodeReason)))

/-- EXTCODESIZE evaluates its input expressions once and normalizes the target. -/
def size (worldReference complete target : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [worldReference, complete, target])) fun args =>
    bindResult .word (fun depth => AccountState.get (load (part 0 3 args) depth)
      (address (part 2 3 args) depth) (part 1 3 args depth)) fun record =>
    known .word record (success (part 5 9 record))) 0

/-- EXTCODECOPY uses a fixed packed code image. Only destination memory expands;
missing source bytes are zero and an oversized source offset cannot wrap. -/
def copy (worldReference complete memoryReference sizeReference target destination source length : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [worldReference, complete, memoryReference, sizeReference,
      target, destination, source, length])) fun args =>
    bindResult .unit (fun depth => AccountState.get (load (part 0 8 args) depth)
      (address (part 4 8 args) depth) (part 1 8 args depth)) fun record =>
    known .unit record (fun depth => Memory.copyPackedFrom
      (part 2 8 args depth) (part 3 8 args depth) (part 5 8 args depth)
      (part 4 9 record depth) (part 6 8 args depth) (part 7 8 args depth))) 0

/-- EXTCODEHASH returns zero exactly for an EIP-161 empty account. Accounts with
positive nonce or balance and no code return Keccak(empty). Code hashing itself
is ordinary Core execution and does not expand the caller's memory. -/
def hash (worldReference complete balancesReference target : Core.Expr) : Core.Expr :=
  (bind (constant (bundle [worldReference, complete, balancesReference, target])) fun args =>
    bind (address (part 3 4 args)) fun target =>
    bindResult .word (fun depth => AccountState.get (load (part 0 4 args) depth)
      (target depth) (part 1 4 args depth)) fun record =>
    known .word record <|
      bindResult .word (lookup (load (part 2 4 args)) target) fun balance =>
      let emptyAccount := choose (binary .wordEq (part 2 9 record) (number 0))
        (choose (binary .wordEq (part 5 9 record) (number 0))
          (binary .wordEq balance (number 0)) (boolean false)) (boolean false)
      choose emptyAccount (success (number 0)) <|
        bind (allocate WordMapping.type (part 4 9 record)) fun memory =>
        bind (allocate .word (number 0)) fun memorySize =>
        fun depth => Keccak.hash (memory depth) (memorySize depth)
          (number 0 depth) (part 5 9 record depth)) 0

def supports (name : String) : Bool := name ∈ ["extcodesize", "extcodecopy", "extcodehash"]

private def reference (scope : Scope) (name : String) (type : Core.Ty) : LowerM Core.Expr := do
  let (binding, index) ← scope.lookup ("$lean$evm$" ++ name)
  expectType type binding.type
  pure (.var index)

/-- Slot adapter independent of Effects, so the effect dispatcher can import
this module without a dependency cycle. Arguments are already evaluated words. -/
def lowerBuiltin (scope : Scope) (name : String) (arguments : List Core.Expr) : LowerM Lowered := do
  let world ← reference scope "world" AccountState.type
  let complete := Core.Expr.loadCell (← reference scope "worldComplete" .bool)
  match name, arguments with
  | "extcodesize", [target] => pure ⟨.word, size world complete target⟩
  | "extcodecopy", [target, destination, source, length] => pure ⟨.unit, copy world complete
      (← reference scope "memory" WordMapping.type) (← reference scope "memorySize" .word)
      target destination source length⟩
  | "extcodehash", [target] => pure ⟨.word, hash world complete
      (← reference scope "balances" WordMapping.type) target⟩
  | _, _ => fail s!"unsupported account inspection or incorrect arity: {name}"

end Solcore.Frontend.RustHull.AccountInspection
