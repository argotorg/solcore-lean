import Solcore.Frontend.SourceCoreMappingWithDefault

/-! Execute the compatibility carrier's ordinary Core code. These tests cover
transported defaults, first duplicate selection, retained raw metadata,
missing-default tokens, effects and native suspension/resume. -/

set_option autoImplicit false

namespace Tests.SourceCoreMappingWithDefault
open Solcore Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def layout : OrderedMapping.Layout := ⟨.word, .word, ⟨0⟩⟩
private def definitions : DataEnvironment := [layout.definition]
private def comparator : Expr :=
  .lambda (.product .word .word) .bool (.binary .wordEq (.first (.var 0)) (.second (.var 0)))
private def stored : Expr :=
  OrderedMapping.cons layout (.word (word 3)) (.word (word 9))
    (OrderedMapping.cons layout (.word (word 3)) (.word (word 100)) (OrderedMapping.empty layout))
private def literal (fallback : Option Nat) : Expr :=
  Frontend.SourceCoreMappingWithDefault.pack (.word (word 41))
    (match fallback with
      | none => .inLeft .word .unit
      | some value => .inRight .unit (.word (word value))) stored
private def program (type : Ty) (body : Expr) : Program := ⟨type, body, definitions⟩
private def entries : OrderedMapping.Entries :=
  [(.word (word 3), .word (word 9)), (.word (word 3), .word (word 100))]
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def completes (program : Program) (expected : Value) : IO Store := do
  assertTrue program.check "mapping default carrier failed Core checking"
  match program.runStateful 10000 with
  | .done value store =>
      assertTrue (value == expected) s!"mapping default result changed: {reprStr value}"
      pure store
  | other => throw (IO.userError s!"mapping default run did not complete: {reprStr other}")

example : layout.Registered definitions := ⟨.word, .word, rfl⟩

/-- The actual wrapper is typed using the registered ordered mapping helper. -/
example : HasType [] (Frontend.SourceCoreMappingWithDefault.lookup layout (word 1000) comparator (literal (some 77)) (.word (word 8)))
    (LanguageResult.resultType .word) definitions := by
  apply Frontend.SourceCoreMappingWithDefault.lookup_hasType (word 1000) ⟨.word, .word, rfl⟩
  · exact .lambda (.product .word .word) .bool (.binary (.first (.var rfl)) (.second (.var rfl)))
  · exact Frontend.SourceCoreMappingWithDefault.pack_hasType .word (.inRight .unit .word)
      (OrderedMapping.cons_hasType ⟨.word, .word, rfl⟩ .word .word
        (OrderedMapping.cons_hasType ⟨.word, .word, rfl⟩ .word .word
          (OrderedMapping.empty_hasType ⟨.word, .word, rfl⟩ [])))
  · exact .word

def run : IO Unit := do
  let present := program (LanguageResult.resultType .word)
    (Frontend.SourceCoreMappingWithDefault.lookup layout (word 1000) comparator (literal (some 77)) (.word (word 3)))
  let presentStore ← completes present (.inRight .word (.word (word 9)))
  assertTrue (presentStore.length == 1) "present lookup changed helper allocation count"
  let absent := program (LanguageResult.resultType .word)
    (Frontend.SourceCoreMappingWithDefault.lookup layout (word 1000) comparator (literal (some 77)) (.word (word 8)))
  let _ ← completes absent (.inRight .word (.word (word 77)))
  let missing := program (LanguageResult.resultType .word)
    (Frontend.SourceCoreMappingWithDefault.lookup layout (word 1000) comparator (literal none) (.word (word 8)))
  let _ ← completes missing (.inLeft .word (.word (word 1041)))
  let inserted := program (LanguageResult.resultType (Frontend.SourceCoreMappingWithDefault.type layout))
    (Frontend.SourceCoreMappingWithDefault.insert layout comparator (literal (some 77)) (.word (word 3)) (.word (word 12)))
  let _ ← completes inserted (.inRight .word (Frontend.SourceCoreMappingWithDefault.value (word 41) (some (.word (word 77))) layout
    [(.word (word 3), .word (word 12)), (.word (word 3), .word (word 100))]))
  let stillDefault := program (LanguageResult.resultType .word)
    (LanguageResult.bind .word inserted.body
      (Frontend.SourceCoreMappingWithDefault.lookup layout (word 1000) (comparator.weakenAt 0) (.var 0) (.word (word 8))))
  let _ ← completes stillDefault (.inRight .word (.word (word 77)))
  let once := program (.product (LanguageResult.resultType .word) .word)
    (.letE (.newCell .word (.word Word.zero))
      (.letE (Frontend.SourceCoreMappingWithDefault.lookup layout (word 1000) comparator
        (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (.word (word 1))))
          (literal (some 77))) (.word (word 8)))
        (.pair (.var 0) (.loadCell (.var 1)))))
  let onceStore ← completes once (.pair (.inRight .word (.word (word 77))) (.word (word 1)))
  assertTrue (onceStore[0]? == some (.word (word 1))) "mapping expression ran more than once"
  for fuel in List.range 64 do
    match absent.runStateful fuel with
    | .outOfFuel checkpoint =>
        match runStateful 10000 checkpoint with
        | .done value _ => assertTrue (value == .inRight .word (.word (word 77))) "mapping default resume changed"
        | _ => throw (IO.userError "mapping default resume did not complete")
    | .done value _ => assertTrue (value == .inRight .word (.word (word 77))) "mapping default finite run changed"
    | .fault error _ => throw (IO.userError s!"mapping default reached a machine fault: {reprStr error}")
  assertTrue (decide (Frontend.SourceCoreMappingWithDefault.value (word 41) none layout entries =
    .pair (.word (word 41)) (.pair (.inLeft .word .unit) (OrderedMapping.encode layout entries))))
    "mapping carrier lost its raw metadata header"
  IO.println "ordinary Core mapping metadata and transported defaults GREEN"

end Tests.SourceCoreMappingWithDefault
