import Solcore.Frontend.SourceCoreDefaultValue
import Solcore.SourceSemantics.CoreLowering.DataDefaults

#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCoreDataEquality

open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }",
    "function identity(value: Word) returns (Word) { return value; }"
  ] }]
}

private def prepared (checked : SourceCoreDataCatalog.Checked) (type : TypeSystem.Ty) :
    IO (SourceCoreDataEquality.Prepared checked) :=
  match SourceCoreDataEquality.prepare 128 checked type with
  | .ok comparator => pure comparator
  | .error error => throw (IO.userError s!"comparison compilation rejected {reprStr error}")

private def runProgram (definitions : DataEnvironment) (type : Core.Ty) (expression : Expr)
    (expected : Value) (cells : Nat) : IO Unit := do
  let program : Program := ⟨type, expression, definitions⟩
  assertTrue program.check "generated comparison/default failed Core.check"
  match program.runStateful 100000 with
  | .done value store =>
    assertTrue (value == expected) s!"comparison/default mismatch: {reprStr value}"
    assertTrue (store.length == cells) "comparison allocated cells during invocation"
  | result => throw (IO.userError s!"comparison/default did not complete: {reprStr result}")

private def assertComparison (checked : SourceCoreDataCatalog.Checked) (type : TypeSystem.Ty)
    (left right : Expr) (expected : Bool) : IO Unit := do
  let comparator ← prepared checked type
  runProgram checked.catalog.definitions .bool
    (.apply comparator.expression (.pair left right)) (.bool expected) checked.catalog.entries.length
  -- The same prepared comparator is invoked twice; installation is not repeated.
  runProgram checked.catalog.definitions (.product .bool .bool)
    (.letE comparator.expression (.pair
      (.apply (.var 0) (.pair left right)) (.apply (.var 0) (.pair right left))))
    (.pair (.bool expected) (.bool expected)) checked.catalog.entries.length

private def leaf (id : DataTypeId) (value : Int) : Expr := .construct ⟨id, 0⟩ (.integer value)
private def pair (id : DataTypeId) (left right : Expr) : Expr := .construct ⟨id, 1⟩ (.pair left right)
private def tree (id : DataTypeId) : Nat → Expr
  | 0 => leaf id (-10)
  | n + 1 => pair id (leaf id (Int.ofNat n)) (tree id n)

private def rawFunction : Expr :=
  .lambda .word (LanguageResult.resultType .word) (LanguageResult.success (.var 0))

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"data equality fixture rejected {reprStr errors}")
  let signature ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some signature => pure signature
    | none => throw (IO.userError "missing Tree")
  let treeType := TypeSystem.Ty.nominal signature.id [.integer]
  let mapType := TypeSystem.Ty.mapping treeType .word
  let functionType := TypeSystem.Ty.function .word .word
  let functionTree := TypeSystem.Ty.nominal signature.id [functionType]
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 128
      [treeType, functionTree, mapType, .proxy .word, .proxy (.comptime .word), .mapping .word .word] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"data catalog rejected {reprStr error}")
  let id ← match checked.catalog.identity? treeType with
    | some id => pure id
    | none => throw (IO.userError "tree identity missing")
  assertComparison checked .unit .unit .unit true
  assertComparison checked .bool (.bool false) (.bool true) false
  assertComparison checked .bool (.bool true) (.bool true) true
  assertComparison checked .integer (.integer (-(2 ^ 300))) (.integer (-(2 ^ 300))) true
  assertComparison checked (.product .word .integer)
    (.pair (.word Word.zero) (.integer 8)) (.pair (.word Word.zero) (.integer 9)) false
  assertComparison checked treeType (tree id 12) (tree id 12) true
  assertComparison checked treeType (tree id 12) (tree id 11) false
  assertComparison checked treeType (leaf id 1) (pair id (leaf id 1) (leaf id 1)) false
  assertComparison checked treeType (leaf id 1) (leaf id 2) false
  assertComparison checked functionType (TaggedFunction.anonymous rawFunction) (TaggedFunction.anonymous rawFunction) false
  assertComparison checked functionType (TaggedFunction.identified Word.zero rawFunction)
    (TaggedFunction.identified Word.zero rawFunction) true
  assertComparison checked functionType (TaggedFunction.identified Word.zero rawFunction)
    (TaggedFunction.identified (Word.ofNatModulo 1) rawFunction) false
  assertComparison checked functionType (TaggedFunction.anonymous rawFunction)
    (TaggedFunction.identified Word.zero rawFunction) false
  assertComparison checked functionType (TaggedFunction.identified Word.zero rawFunction)
    (TaggedFunction.anonymous rawFunction) false
  -- Even a body that allocates when invoked is never invoked by equality.
  let effectfulCode := Expr.lambda .word (LanguageResult.resultType .word)
    (.letE (.newCell .word (.var 0)) (LanguageResult.success (.loadCell (.var 0))))
  assertComparison checked functionType (TaggedFunction.identified Word.zero effectfulCode)
    (TaggedFunction.identified Word.zero rawFunction) true
  let functionTreeId := (checked.catalog.identity? functionTree).getD ⟨0⟩
  assertComparison checked functionTree
    (.construct ⟨functionTreeId, 0⟩ (TaggedFunction.anonymous rawFunction))
    (.construct ⟨functionTreeId, 0⟩ (TaggedFunction.anonymous rawFunction)) false
  assertComparison checked functionTree
    (.construct ⟨functionTreeId, 0⟩ (TaggedFunction.identified Word.zero rawFunction))
    (.construct ⟨functionTreeId, 0⟩ (TaggedFunction.identified Word.zero effectfulCode)) true
  let proxyId := (checked.catalog.identity? (.proxy .word)).getD ⟨0⟩
  assertTrue (checked.catalog.identity? (.proxy .word) != checked.catalog.identity? (.proxy (.comptime .word)))
    "exact proxy staging identity collapsed"
  assertComparison checked (.proxy .word) (.construct ⟨proxyId, 0⟩ .unit) (.construct ⟨proxyId, 0⟩ .unit) true
  let mapId := (checked.catalog.identity? mapType).getD ⟨0⟩
  let mapping : Expr := .construct ⟨mapId, 0⟩ .unit
  assertComparison checked mapType mapping mapping false
  assertComparison checked (.product .unit mapType) (.pair .unit mapping) (.pair .unit mapping) false

  let comparator ← prepared checked treeType
  let layout : OrderedMapping.Layout := ⟨.namedData id, .word, mapId⟩
  let entries := OrderedMapping.cons layout (tree id 3) (.word Word.zero)
    (OrderedMapping.cons layout (tree id 2) (.word (Word.ofNatModulo 4)) (OrderedMapping.empty layout))
  let insert := OrderedMapping.insert layout (.var 0) entries (tree id 3) (.word (Word.ofNatModulo 6))
  let expected : Expr := OrderedMapping.cons layout (tree id 3) (.word (Word.ofNatModulo 6))
    (OrderedMapping.cons layout (tree id 2) (.word (Word.ofNatModulo 4)) (OrderedMapping.empty layout))
  let expectedValue ← match (Program.mk layout.type expected checked.catalog.definitions).runStateful 100000 with
    | .done value _ => pure value
    | _ => throw (IO.userError "expected mapping construction failed")
  runProgram checked.catalog.definitions (LanguageResult.resultType layout.type)
    (.letE comparator.expression insert) (.inRight .word expectedValue) (checked.catalog.entries.length + 1)

  for (type, present) in [(TypeSystem.Ty.unit, true), (.integer, true),
      (.product .bool (.proxy .word), true), (mapType, true), (functionType, false), (treeType, false)] do
    let default ← match SourceCoreDefaultValue.prepare 128 checked type with
      | .ok default => pure default
      | .error error => throw (IO.userError s!"default rejected {reprStr error}")
    let result := (Program.mk (.sum .unit default.type) default.expression checked.catalog.definitions).runStateful 1000
    match result with
    | .done (.inRight .unit _) [] => assertTrue present "unexpected present default"
    | .done (.inLeft _ .unit) [] => assertTrue (!present) "unexpected absent default"
    | _ => throw (IO.userError s!"default execution shape changed: {reprStr result}")
  IO.println "source Core data equality/default GREEN"

end Tests.SourceCoreDataEquality
