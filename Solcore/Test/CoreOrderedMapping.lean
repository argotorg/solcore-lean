import Solcore.SourceSemantics.CoreLowering.OrderedMapping

/-! Generic mapping helpers use nonzero catalog identities, caller comparison,
optional lookup results, and structural/function payloads through real Core. -/

set_option autoImplicit false

namespace Tests.CoreOrderedMapping

open Solcore.Core

private def w (value : Nat) : Word := Word.ofNatModulo value
private def layout : OrderedMapping.Layout := ⟨.integer, .product .bool .word, ⟨1⟩⟩
private def definitions : DataEnvironment := [{constructorPayloadTypes := [.unit]}, layout.definition]
private def comparison : Expr := .lambda (.product .integer .integer) .bool
  (.binary .integerEq (.first (.var 0)) (.second (.var 0)))
private def pairExpr (flag : Bool) (value : Nat) : Expr := .pair (.bool flag) (.word (w value))
private def pairValue (flag : Bool) (value : Nat) : Value := .pair (.bool flag) (.word (w value))
private def entries : OrderedMapping.Entries :=
  [(.integer (-4), pairValue true 7), (.integer 2, pairValue false 9), (.integer (-4), pairValue false 11)]
private def literal : Expr :=
  OrderedMapping.cons layout (.integer (-4)) (pairExpr true 7)
    (OrderedMapping.cons layout (.integer 2) (pairExpr false 9)
      (OrderedMapping.cons layout (.integer (-4)) (pairExpr false 11) (OrderedMapping.empty layout)))
private def program (resultType : Ty) (body : Expr) : Program := ⟨resultType, body, definitions⟩

example : layout.Registered definitions := ⟨.integer, .product .bool .word, rfl⟩

/-- Ordinary application supplies the equality proof for arbitrary store state. -/
example (left right : Int) (store : Store) :
    OrderedMapping.Compares layout
      (.closure (.product .integer .integer) .bool
        (.binary .integerEq (.first (.var 0)) (.second (.var 0))) [])
      (.integer left) (.integer right) (left == right) store :=
  ⟨_, [], rfl, .binary (.first (.var rfl)) (.second (.var rfl)) rfl⟩

private def integerRel (source : Solcore.SourceSemantics.Dynamic.Value) (target : Value) : Prop :=
  ∃ value : Int, source = .integer value ∧ target = .integer value
private def integerEqual : OrderedMapping.Predicate
  | .integer left, .integer right => left == right
  | _, _ => false
private def productRel (source : Solcore.SourceSemantics.Dynamic.Value) (target : Value) : Prop :=
  ∃ flag value, source = .product (.bool flag) (.word value) ∧ target = .pair (.bool flag) (.word value)

private theorem integerEqual_correct :
    Solcore.SourceSemantics.CoreLowering.OrderedMapping.KeyEqualityCorrect integerRel integerEqual where
  equivalent := by
    rintro sourceKey sourceStored key stored ⟨left, rfl, rfl⟩ ⟨right, rfl, rfl⟩
    constructor
    · intro equivalent
      have same : left = right := of_decide_eq_true (show decide (left = right) = true from equivalent)
      subst right
      exact ⟨rfl, .integer left⟩
    · intro equivalent
      have same := Solcore.SourceSemantics.Dynamic.Value.integer.inj equivalent.1
      subst right
      simp [integerEqual]

/-- Concrete independent source update, actual comparison execution, and full
Core installation combine into a finite run with the related product value. -/
example : ∃ output finalStore required,
    Solcore.SourceSemantics.CoreLowering.OrderedMapping.ValueRel layout integerRel productRel
      [(Solcore.SourceSemantics.Dynamic.Value.integer (-4), .product (.bool false) (.word (w 42)))] output ∧
    ∀ fuel, required ≤ fuel →
      runStateful fuel (State.initial (OrderedMapping.insert layout comparison
        (OrderedMapping.cons layout (.integer (-4)) (pairExpr true 7) (OrderedMapping.empty layout))
        (.integer (-4)) (pairExpr false 42))) = .done (.inRight .word output) finalStore := by
  apply Solcore.SourceSemantics.CoreLowering.OrderedMapping.insert_run_preserves
    integerEqual_correct layout (key := .integer (-4))
    (comparator := .closure (.product .integer .integer) .bool
      (.binary .integerEq (.first (.var 0)) (.second (.var 0))) [])
  · exact ⟨-4, rfl, rfl⟩
  · exact ⟨false, w 42, rfl, rfl⟩
  · exact .cons ⟨-4, rfl, rfl⟩ ⟨true, w 7, rfl, rfl⟩ .nil
  · exact .update (.head ⟨rfl, .integer (-4)⟩)
  · exact .construct (.pair (.pair .integer (.pair .bool .word)) (.construct .unit))
  · exact .integer
  · exact .pair .bool .word
  · exact .lambda
  · intro storedKey storedValue member
    have same := List.mem_singleton.mp member
    cases same
    exact ⟨_, [], rfl, .binary (.first (.var rfl)) (.second (.var rfl)) rfl⟩

private def latestProgram : Program := program (OptionalCell.cellType layout.type)
  (.letE (OptionalCell.allocateInitialized layout.type (OrderedMapping.empty layout))
    (.letE (OrderedMapping.assign layout comparison (.var 0)
      (LanguageResult.success (.integer (-4)))
      (.letE (.storeCell (.var 0) (.inRight .unit literal))
        (LanguageResult.success (pairExpr false 42))))
      (.loadCell (.var 1))))

private def failedRhsProgram : Program := program (LanguageResult.resultType .unit)
  (.letE (OptionalCell.allocateInitialized layout.type (OrderedMapping.empty layout))
    (OrderedMapping.assign layout comparison (.var 0)
      (LanguageResult.success (.integer (-4)))
      (.letE (.storeCell (.var 0) (.inRight .unit literal))
        (LanguageResult.failure layout.valueType (.word (w 18))))))

private def functionLayout : OrderedMapping.Layout := ⟨.integer, .function .integer .integer, ⟨1⟩⟩
private def capturedFunction : Expr := .lambda .integer .integer
  (.letE (.storeCell (.var 1) (.binary .integerAdd (.loadCell (.var 1)) (.var 0))) (.loadCell (.var 2)))
private def capturedProgram : Program := {
  resultType := LanguageResult.resultType .integer
  dataDefinitions := [{constructorPayloadTypes := [.unit]}, functionLayout.definition]
  body := .letE (.newCell .integer (.integer 4))
    (LanguageResult.bind .integer
      (OrderedMapping.lookup functionLayout comparison
        (OrderedMapping.cons functionLayout (.integer 1) capturedFunction (OrderedMapping.empty functionLayout))
        (.integer 1))
      (.caseE (.var 0) (LanguageResult.failure .integer (.word (w 19)))
        (.letE (.apply (.var 0) (.integer 3))
          (LanguageResult.success (.apply (.var 1) (.integer 5))))))
}

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def completes (program : Program) (value : Value) : IO Store := do
  assertTrue program.check "generic mapping failed its registered checker"
  match program.runStateful 10000 with
  | .done result store =>
      assertTrue (result == value) s!"generic mapping result mismatch: {reprStr result}"
      return store
  | result => throw (IO.userError s!"generic mapping did not complete: {reprStr result}")

def run : IO Unit := do
  let lookupFound := program (LanguageResult.resultType layout.lookupResult)
    (OrderedMapping.lookup layout comparison literal (.integer (-4)))
  discard <| completes lookupFound (.inRight .word (.inRight .unit (pairValue true 7)))
  let lookupAbsent := program (LanguageResult.resultType layout.lookupResult)
    (OrderedMapping.lookup layout comparison literal (.integer 5))
  discard <| completes lookupAbsent (.inRight .word (.inLeft layout.valueType .unit))
  let defaulted := program (LanguageResult.resultType layout.valueType)
    (LanguageResult.bind layout.valueType lookupAbsent.body
      (.caseE (.var 0) (LanguageResult.success (pairExpr true 100)) (LanguageResult.success (.var 0))))
  discard <| completes defaulted (.inRight .word (pairValue true 100))
  let defaultFailed := program (LanguageResult.resultType layout.valueType)
    (LanguageResult.bind layout.valueType lookupAbsent.body
      (.caseE (.var 0) (LanguageResult.failure layout.valueType (.word (w 21)))
        (LanguageResult.success (.var 0))))
  discard <| completes defaultFailed (.inLeft layout.valueType (.word (w 21)))

  let updated : OrderedMapping.Entries :=
    [(.integer (-4), pairValue false 42), (.integer 2, pairValue false 9), (.integer (-4), pairValue false 11)]
  let insertion := program (LanguageResult.resultType layout.type)
    (OrderedMapping.insert layout comparison literal (.integer (-4)) (pairExpr false 42))
  let insertedStore ← completes insertion (.inRight .word (OrderedMapping.encode layout updated))
  assertTrue (insertedStore.length == 1) "recursion must share one installed self cell"
  discard <| completes (program (LanguageResult.resultType layout.type)
    (OrderedMapping.insert layout comparison literal (.integer 5) (pairExpr true 17)))
      (.inRight .word (OrderedMapping.encode layout (entries ++ [(.integer 5, pairValue true 17)])))
  let neverEqual : Expr := .lambda (.product .integer .integer) .bool (.bool false)
  discard <| completes (program (LanguageResult.resultType layout.type)
    (OrderedMapping.insert layout neverEqual literal (.integer (-4)) (pairExpr true 99)))
      (.inRight .word (OrderedMapping.encode layout (entries ++ [(.integer (-4), pairValue true 99)])))
  assertTrue (!( { lookupFound with dataDefinitions := [layout.definition] } : Program).check)
    "the actual mapping catalog identity must be checked"
  assertTrue (!(program (LanguageResult.resultType layout.lookupResult)
    (OrderedMapping.lookup layout (.lambda (.product .word .word) .bool (.bool true)) literal (.integer 0))).check)
    "the comparator must accept the precise key pair type"

  let latestStore ← completes latestProgram (.inRight .unit (OrderedMapping.encode layout updated))
  assertTrue (latestStore[0]? == some (.inRight .unit (OrderedMapping.encode layout updated)) && latestStore.length == 2)
    "generic writeback must use the root installed by the RHS"
  let failureStore ← completes failedRhsProgram (.inLeft .unit (.word (w 18)))
  assertTrue (failureStore == [.inRight .unit (OrderedMapping.encode layout entries)])
    "RHS failure must keep its root effects and skip helper allocation"
  let capturedStore ← completes capturedProgram (.inRight .word (.integer 12))
  assertTrue (capturedStore[0]? == some (.integer 12) && capturedStore.length == 2)
    "a function payload must retain the original mutable capture location"
  match latestProgram.runStateful 25 with
  | .outOfFuel checkpoint =>
      assertTrue (runStateful 10000 checkpoint == latestProgram.runStateful 10025)
        "generic mapping must resume from the actual store checkpoint"
  | result => throw (IO.userError s!"expected mapping suspension, got {reprStr result}")

end Tests.CoreOrderedMapping
