import Solcore.Core.CallableContract

/-! A source callable view is carried by an ordinary transparent Core lambda.
The original callable identity and contract descriptor remain unchanged. Its
body contains a bounded word manifest and applies the original payload; it
allocates no cells and introduces no Core syntax or runtime evaluator.

The parser recognizes an exact wrapper shape and copied tags. It establishes
no source provenance: a caller must authenticate the returned view word and
original carrier against its own compiler metadata. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableViewWrappers
open Core

/-- After the manifest binder: original carrier is slot 2, argument is slot 1. -/
def body (view : Word) : Expr :=
  .letE (.word view) (.apply (.second (.first (.var 2))) (.var 1))

/-- Under the successful read's original-carrier binder. -/
def repack (parameter result : Ty) (view : Word) : Expr :=
  .pair (.pair (.first (.first (.var 0)))
    (.lambda parameter (LanguageResult.resultType result) (body view)))
    (.second (.var 0))

def lower (parameter result : Ty) (view : Word) (read : Expr) : Expr :=
  LanguageResult.bind (CallableContract.functionType parameter result) read
    (LanguageResult.success (repack parameter result view))

def originalValue (identity payload : Value) (contract : Word) : Value :=
  .pair (.pair identity payload) (.word contract)

def wrappedValue (parameter result : Ty) (view : Word) (identity payload : Value)
    (contract : Word) (outer : Environment) : Value :=
  .pair (.pair identity (.closure parameter (LanguageResult.resultType result) (body view)
    (originalValue identity payload contract :: outer))) (.word contract)

def bodyView? : Expr → Option Word
  | .letE (.word view) (.apply (.second (.first (.var 2))) (.var 1)) => some view
  | _ => none

/-- Exact shape only. In particular the original carrier and the complete
outer environment are retained, without traversing their captured references. -/
structure Parsed (parameter result : Ty) (value : Value) where
  view : Word
  identity : Value
  payload : Value
  contract : Word
  outer : Environment
  shape : value = wrappedValue parameter result view identity payload contract outer
  deriving Repr

def Parsed.original {parameter result : Ty} {value : Value} (parsed : Parsed parameter result value) : Value :=
  originalValue parsed.identity parsed.payload parsed.contract

def parse? (parameter result : Ty) (value : Value) : Option (Parsed parameter result value) :=
  match observed : value with
  | .pair (.pair _ (.closure _ _ code (original :: outer))) (.word _) => do
    let view ← bodyView? code
    let .pair (.pair identity payload) (.word contract) := original | none
    if shape : value = wrappedValue parameter result view identity payload contract outer then
      some ⟨view, identity, payload, contract, outer, observed.symm.trans shape⟩
    else none
  | _ => none

theorem parse_wrapped (parameter result : Ty) (view : Word) (identity payload : Value)
    (contract : Word) (outer : Environment) :
    (parse? parameter result (wrappedValue parameter result view identity payload contract outer)).isSome = true := by
  simp [parse?, wrappedValue, originalValue, bodyView?, body]

theorem Parsed.original_exact {parameter result : Ty} {value : Value}
    (parsed : Parsed parameter result value) :
    value = .pair (.pair parsed.identity
      (.closure parameter (LanguageResult.resultType result) (body parsed.view)
        (parsed.original :: parsed.outer))) (.word parsed.contract) := parsed.shape

end Solcore.Frontend.SourceCoreCallableViewWrappers
