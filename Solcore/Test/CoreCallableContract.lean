import Solcore.Core.CallableContract

set_option autoImplicit false

namespace Tests.CoreCallableContract
open Solcore Core
open CallableContract

private def w (value : Nat) : Word := (Word.ofNat? value).getD Word.zero

private def function : Expr :=
  TaggedFunction.identified (w 7)
    (.lambda .unit (LanguageResult.resultType .word)
      (.letE (.newCell (.sum .unit .unit) (.inRight .unit .unit)) (LanguageResult.success (.word (w 9)))))

private def callee : Expr :=
  .letE (.storeCell (.var 0) (.word (w 1))) (LanguageResult.success (wrap (w 11) function))

private def arguments : Expr :=
  .letE (.storeCell (.var 0) (.word (w 2))) (LanguageResult.success .unit)

private def gates (before after : Option Word) : List Gate :=
  [⟨w 5, some (w 90), some (w 91)⟩, ⟨w 11, before, after⟩]

example (before after : Option Word) :
    HasType [.cell .word] (call (gates before after) (w 99) .word callee arguments)
      (LanguageResult.resultType .word) := by
  apply call_hasType _ _ .word
  · exact .letE (.storeCell (.var rfl) .word)
      (.inRight .word (.pair
        (.pair (.inRight .unit .word)
          (.lambda .unit (.sum .word .word)
            (.letE (.newCell (.inRight .unit .unit)) (.inRight .word .word)))) .word))
  · exact .letE (.storeCell (.var rfl) .word) (.inRight .word .unit)

example : decision (gates (some (w 21)) none) .beforeArguments (w 99) (w 11) = some (w 21) := by
  decide

example : decision (gates none (some (w 22))) .beforeApplication (w 99) (w 11) = some (w 22) := by
  decide

example : decision (gates none none) .beforeArguments (w 99) (w 12) = some (w 99) := by
  decide

example {environment : Environment} {store : Store} {left right : Value} :
    Evaluates (.pair (.pair (.inRight .unit (.word (w 7))) right) (.word (w 12)) ::
      .pair (.pair (.inRight .unit (.word (w 7))) left) (.word (w 11)) :: environment)
      store equalBody (.bool true) store :=
  by simpa using (equalBody_identified (leftIdentity := w 7) (rightIdentity := w 7))

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def check (before after : Option Word) (value : Value) (store : Store) : IO Unit := do
  let expression := call (gates before after) (w 99) .word callee arguments
  assertTrue (infer? [.cell .word] expression == some (LanguageResult.resultType .word))
    "callable contract code failed checker"
  let state := State.initial expression [.cellRef .word 0] [.word (w 0)]
  let verify := fun result => do
    match result with
    | .done actual actualStore =>
        assertTrue (actual == value && actualStore == store)
          s!"callable guard order/store changed: {reprStr result}"
    | other => throw (IO.userError s!"callable guard did not complete: {reprStr other}")
  verify (runStateful 1000 state)
  match runStateful 3 state with
  | .outOfFuel checkpoint => verify (runStateful 1000 checkpoint)
  | other => throw (IO.userError s!"callable guard did not retain checkpoint: {reprStr other}")

def run : IO Unit := do
  check (some (w 21)) none (.inLeft .word (.word (w 21))) [.word (w 1)]
  check none (some (w 22)) (.inLeft .word (.word (w 22))) [.word (w 2)]
  check none none (.inRight .word (.word (w 9))) [.word (w 2), .inRight .unit .unit]
  let unknown := call [] (w 99) .word callee arguments
  assertTrue (runStateful 1000 (State.initial unknown [.cellRef .word 0] [.word (w 0)]) ==
    .done (.inLeft .word (.word (w 99))) [.word (w 1)]) "unknown descriptor bypassed guard"
  let tagged := TaggedFunction.identified (w 7) (.lambda .unit (.sum .word .unit) (.inRight .word .unit))
  let namedEqual := equal (LanguageResult.success (wrap (w 11) tagged))
    (LanguageResult.success (wrap (w 12) tagged))
  assertTrue (runStateful 1000 (State.initial namedEqual [] []) ==
    .done (.inRight .word (.bool true)) []) "descriptor changed named identity"
  let anonymous := LanguageResult.success (wrap (w 11)
    (TaggedFunction.anonymous (.lambda .unit (.sum .word .unit) (.inRight .word .unit))))
  assertTrue (runStateful 1000 (State.initial (equal anonymous anonymous) [] []) ==
    .done (.inRight .word (.bool false)) []) "anonymous wrapper compared equal"
  IO.println "ordinary callable contract dispatch/order/equality GREEN"

end Tests.CoreCallableContract
