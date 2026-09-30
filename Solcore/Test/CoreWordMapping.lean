import Solcore.SourceSemantics.CoreLowering.WordMapping
import Solcore.Core.ExactFuelProperties

/-! Fixed-catalog mapping helpers execute with the actual named-data definition,
including duplicate keys, shared mutable roots, and checkpoint resumption. -/

set_option autoImplicit false

namespace Tests.CoreWordMapping

open Solcore.Core

private def w (value : Nat) : Word := Word.ofNatModulo value
private def e (value : Nat) : Expr := .word (w value)
private def v (value : Nat) : Value := .word (w value)
private def entries : WordMapping.Entries := [(w 1, w 11), (w 2, w 22), (w 1, w 33)]

private def program (type : Ty) (body : Expr) : Program := {
  resultType := type
  body := body
  dataDefinitions := WordMapping.actualDefinitions
}

private def lookupProgram (key : Nat) : Program :=
  program (LanguageResult.resultType .word) (WordMapping.lookup (WordMapping.literal entries) (e key))

private def insertProgram (key value : Nat) : Program :=
  program (LanguageResult.resultType WordMapping.type)
    (WordMapping.insert (WordMapping.literal entries) (e key) (e value))

/-- Actual helper compilation produces the independent source insertion's
structural carrier and a finite runner result, for arbitrary finite lists. -/
example (words : WordMapping.Entries) (key value : Word) :
    ∃ output finalStore required,
      Solcore.SourceSemantics.CoreLowering.WordMapping.ValueRel
        (Solcore.SourceSemantics.CoreLowering.WordMapping.sourceEntries
          (WordMapping.insertEntries key value words)) output ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial
          (WordMapping.insert (WordMapping.literal words) (.word key) (.word value))) =
          .done (.inRight .word output) finalStore :=
  Solcore.SourceSemantics.CoreLowering.WordMapping.insert_run_preserves
    (Solcore.SourceSemantics.CoreLowering.WordMapping.ValueRel.encode words)
    (Solcore.SourceSemantics.CoreLowering.WordMapping.insertEntries_source words key value)
    (WordMapping.literal_evaluates words [] []) .word .word

/-- The RHS replaces the root with two entries. Updating key 1 must preserve
its newly added key 2, which would disappear if an earlier root snapshot won. -/
private def latestRootProgram : Program := program (OptionalCell.cellType WordMapping.type)
  (.letE (OptionalCell.allocateInitialized WordMapping.type (WordMapping.literal [(w 1, w 10)]))
    (.letE (WordMapping.assign (.var 0) (LanguageResult.success (e 1))
      (.letE (.storeCell (.var 0) (.inRight .unit (WordMapping.literal [(w 1, w 20), (w 2, w 30)])))
        (LanguageResult.success (e 99))))
      (.loadCell (.var 1))))

/-- Reference, key, and RHS effects run in order: counter := 3; += 5; *= 2.
The key and value use the original environment after temporary binders. -/
private def orderProgram : Program :=
  program (.product (OptionalCell.cellType WordMapping.type) .word)
    (.letE (.newCell .word (e 0))
      (.letE (OptionalCell.allocateInitialized WordMapping.type (WordMapping.literal [(w 1, w 0)]))
        (.letE (WordMapping.assign
          (.letE (.storeCell (.var 1) (e 3)) (.var 1))
          (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (e 5)))
            (LanguageResult.success (e 1)))
          (.letE (.storeCell (.var 1) (.binary .wordMul (.loadCell (.var 1)) (e 2)))
            (LanguageResult.success (.loadCell (.var 2)))))
          (.pair (.loadCell (.var 1)) (.loadCell (.var 2))))))

private def keyFailureProgram : Program := program (LanguageResult.resultType .unit)
  (.letE (OptionalCell.allocateInitialized WordMapping.type (WordMapping.literal [(w 1, w 10)]))
    (WordMapping.assign (.var 0) (LanguageResult.failure .word (e 17))
      (.letE (.storeCell (.var 0) (.inRight .unit WordMapping.empty))
        (LanguageResult.success (e 99)))))

private def rhsFailureProgram : Program := program (LanguageResult.resultType .unit)
  (.letE (OptionalCell.allocateInitialized WordMapping.type (WordMapping.literal [(w 1, w 10)]))
    (WordMapping.assign (.var 0) (LanguageResult.success (e 1))
      (.letE (.storeCell (.var 0) (.inRight .unit (WordMapping.literal [(w 2, w 30)])))
        (LanguageResult.failure .word (e 18)))))

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def completed (program : Program) (expected : Value) : IO Store := do
  assertTrue program.check "mapping prototype failed its registered Core checker"
  match program.runStateful 6000 with
  | .done actual store =>
      assertTrue (actual == expected) s!"mapping result mismatch: {reprStr actual}"
      return store
  | other => throw (IO.userError s!"mapping prototype did not complete: {reprStr other}")

def run : IO Unit := do
  assertTrue WordMapping.actualDefinitions.isWellFormed "mapping catalog must be valid"
  assertTrue (!( { (lookupProgram 1) with dataDefinitions := [] } : Program).check)
    "named mapping data must not type-check without its actual catalog"
  assertTrue (!( { (lookupProgram 1) with dataDefinitions := [{constructorPayloadTypes := [.unit]}] } : Program).check)
    "same nominal index with wrong payloads must be rejected"

  let lookupStore ← completed (lookupProgram 1) (.inRight .word (v 11))
  assertTrue (lookupStore == WordMapping.installedStore [] WordMapping.lookupParameter .word
    WordMapping.lookupBody (.pair (WordMapping.encode entries) (v 1)) [])
    "lookup must install exactly its own shared self cell"
  discard <| completed (lookupProgram 7) (.inRight .word (v 0))
  discard <| completed (program (LanguageResult.resultType .word)
    (WordMapping.lookup WordMapping.empty (e 1))) (.inRight .word (v 0))

  let updated := [(w 1, w 99), (w 2, w 22), (w 1, w 33)]
  let updatedStore ← completed (insertProgram 1 99) (.inRight .word (WordMapping.encode updated))
  assertTrue (updatedStore.length == 1) "one helper invocation allocates one self cell"
  discard <| completed (insertProgram 3 44)
    (.inRight .word (WordMapping.encode (entries ++ [(w 3, w 44)])))
  discard <| completed (program (LanguageResult.resultType WordMapping.type)
    (WordMapping.insert WordMapping.empty (e 7) (e 8)))
      (.inRight .word (WordMapping.encode [(w 7, w 8)]))
  let maxWord := Word.ofNatModulo (wordModulus - 1)
  discard <| completed (program (LanguageResult.resultType .word)
    (WordMapping.lookup (WordMapping.literal [(maxWord, w 42), (w 0, w 13)]) (.word maxWord)))
      (.inRight .word (v 42))

  let latest := WordMapping.encode [(w 1, w 99), (w 2, w 30)]
  let latestStore ← completed latestRootProgram (.inRight .unit latest)
  assertTrue (latestStore[0]? == some (.inRight .unit latest) && latestStore.length == 2)
    "writeback must preserve the RHS's key 2 and write through the original root reference"
  let ordered := WordMapping.encode [(w 1, w 16)]
  let orderedStore ← completed orderProgram (.pair (.inRight .unit ordered) (v 16))
  assertTrue (orderedStore[0]? == some (v 16) &&
    orderedStore[1]? == some (.inRight .unit ordered) && orderedStore.length == 3)
    "reference/key/RHS must run once, in order, through the shared store"

  let keyFailedStore ← completed keyFailureProgram (.inLeft .unit (v 17))
  assertTrue (keyFailedStore == [.inRight .unit (WordMapping.encode [(w 1, w 10)])])
    "key failure must skip the RHS and helper allocation"
  let rhsFailedStore ← completed rhsFailureProgram (.inLeft .unit (v 18))
  assertTrue (rhsFailedStore == [.inRight .unit (WordMapping.encode [(w 2, w 30)])])
    "RHS failure must preserve its effects and skip the pending mapping insertion"

  match orderProgram.runStateful 30 with
  | .outOfFuel checkpoint =>
      assertTrue (runStateful 6000 checkpoint == orderProgram.runStateful 6030)
        "resuming a mapping checkpoint must preserve shared references and final stores"
  | other => throw (IO.userError s!"expected actual mapping suspension, got {reprStr other}")

end Tests.CoreWordMapping
