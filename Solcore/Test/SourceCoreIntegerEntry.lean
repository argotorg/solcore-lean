import Solcore.Frontend.SourceCoreBasicEntry

/-! The prepared Entry boundary validates complete Integer/product trees and
retains typed optional-cell reads and checkpoint resumption. The direct fixture
is a typed Entry; it does not claim the Basic source lowerer accepts Integer. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.Value
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCoreIntegerEntry

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceCoreBasicEntry

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"integer_entry", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reason : Core.Word := word 7

private def sourceType : TypeSystem.Ty :=
  .product .integer (.product .bool (.product .word .integer))
private def coreType : Core.Ty :=
  .product .integer (.product .bool (.product .word .integer))

private def inputs : List Input := [
  { id := binder 0, sourceType, type := coreType, comptime := false },
  { id := binder 1, sourceType := .integer, type := .integer, comptime := false },
  { id := binder 2, sourceType := .bool, type := .bool, comptime := false }
]

private def inputSource : TypedSource := {
  owner
  inputs := [
    { id := binder 0, name := "tree", scheme := .mono sourceType },
    { id := binder 1, name := "integer", scheme := .mono .integer },
    { id := binder 2, name := "flag", scheme := .mono .bool }
  ]
  roots := []
  nodes := []
}

private theorem projected :
    SourceCoreScalar.lowerType (.declaration owner) sourceType = .ok coreType := by rfl

private theorem coreTypeWF : Core.Ty.WellFormed [] coreType :=
  .product .integer (.product .bool (.product .word .integer))

private def entry : Entry := {
  key := { declaration := owner, arguments := [] }
  inputs
  sourceResultType := sourceType
  resultType := coreType
  resultProjection := projected
  faultSites := { owner, resultType := sourceType, reads := [], escapedReason := word 1 }
  body := Core.OptionalCell.read coreType (.var 2) reason
  bodyTyped := Core.OptionalCell.read_hasType reason coreTypeWF (.var rfl)
}

example : SourceCoreScalar.Value.ofCore?
    (.pair (.integer (-7)) (.pair (.bool true) (.pair (.word (word 3)) (.integer 9)))) =
    some (.product (.integer (-7)) (.product (.bool true) (.product (.word (word 3)) (.integer 9)))) := rfl

example (result : Result coreType) {value : Core.Value} {store : Core.Store}
    (success : result.observation = .succeeded value store) :
    ∃ world, Core.RuntimeStoreHasTypes world store ∧ Core.RuntimeValueHasType world value coreType :=
  result.success_typed success

example (checkpoint next : Checkpoint coreType) (spent additional : Nat)
    (exhausted : Core.runStateful spent checkpoint.state = .outOfFuel next.state) :
    (next.resume additional).observation = (checkpoint.resume (spent + additional)).observation :=
  checkpoint.resume_after_exhaustion next spent additional exhausted

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expectError {α : Type} (name : String) (result : Except SourceCoreBasicEntry.Error α)
    (accept : SourceCoreBasicEntry.Error → Bool) : IO Unit := do
  match result with
  | .error error => assertTrue (accept error) s!"{name}: wrong boundary error {reprStr error}"
  | .ok _ => throw (IO.userError s!"{name}: invalid boundary value was accepted")

private def huge : Int := (2 : Int) ^ 1024 + 17
private def deep (first last : Int) : Core.Value :=
  .pair (.integer first) (.pair (.bool true) (.pair (.word (word 11)) (.integer last)))
private def arguments : List Core.Value := [deep (-huge) huge, .integer (-3), .bool false]
private def present (value : Core.Value) : Core.Value := .inRight .unit value

private def start (values : List Core.Value) : IO (Checkpoint entry.resultType) := do
  match entry.start values with
  | .ok checkpoint => pure checkpoint
  | .error error => throw (IO.userError s!"Integer Entry.start failed: {reprStr error}")

def run : IO Unit := do
  let prepared ← match prepareInputs inputSource with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"Integer input metadata failed: {reprStr error}")
  assertTrue (prepared.map (·.id) == inputs.map (·.id) &&
    prepared.map (·.type) == [coreType, .integer, .bool])
    "Integer input projection lost source order or the deep product shape"
  let checkpoint ← start arguments
  assertTrue (checkpoint.state.store == arguments.map present)
    "Integer input cells must contain the exact arbitrary precision values"
  assertTrue (checkpoint.state.control == .eval entry.body [
    .cellRef (Core.OptionalCell.cellType .bool) 2,
    .cellRef (Core.OptionalCell.cellType .integer) 1,
    .cellRef (Core.OptionalCell.cellType coreType) 0])
    "Integer input environment lost newest-first references or payload types"
  let complete := checkpoint.resume 200
  assertTrue (complete.observation == .succeeded (deep (-huge) huge) (arguments.map present))
    "Integer optional-cell read changed its exact value or the shared store"
  let paused := checkpoint.resume 3
  let next ← match paused.checkpoint? with
    | some next => pure next
    | none => throw (IO.userError "Integer optional-cell read did not suspend at fuel three")
  assertTrue ((next.resume 197).observation == complete.observation)
    "typed Integer checkpoint/resume changed the result or store"
  let freshArguments := [deep 1 (-2), .integer huge, .bool true]
  let fresh := (← start freshArguments).resume 200
  assertTrue (fresh.observation == .succeeded (deep 1 (-2)) (freshArguments.map present))
    "reusing a prepared Integer entry reused an earlier input store"

  expectError "Integer count" (entry.start []) fun error => error matches .argumentCountMismatch 3 0
  expectError "Integer source type" (entry.start [deep 1 2, .word (word 3), .bool false])
    fun error => error matches .inputTypeMismatch 1 .integer .word
  expectError "Integer deep structural type" (entry.start [
      .pair (.integer 1) (.pair (.bool true) (.pair (.word (word 11)) (.bool false))),
      .integer 3, .bool false]) fun error => error matches .inputTypeMismatch 0 _ _
  let invalidLeaves : List Core.Value := [
    .cellRef .integer 0,
    .cellRef .integer 999999,
    .closure .unit .integer (.integer 1) [],
    .closure .unit .integer (.integer 1) [.cellRef .integer 999999],
    .hostFunction .storageRead,
    .inRight .unit (.integer 2),
    .constructed ⟨⟨0⟩, 0⟩ (.integer 2)
  ]
  for leaf in invalidLeaves do
    let forged : Core.Value := .pair (.integer 1) (.pair (.bool true) (.pair (.word (word 11)) leaf))
    expectError "deep Integer capability" (entry.start [forged, .integer 3, .bool false])
      fun error => error matches .inputShape 0 _
  expectError "Integer closure top-level" (entry.start [deep 1 2,
      .closure .unit .integer (.integer 1) [], .bool false])
    fun error => error matches .inputShape 1 .integer
  expectError "Integer supplied store" (entry.start arguments [.integer 99])
    fun error => error matches .initialStoreUnsupported 1

  let unsupported : TypedSource := { inputSource with inputs := [
    { id := binder 0, name := "function", scheme := .mono (.function .unit .integer) }
  ] }
  expectError "Integer public function parameter" (prepareInputs unsupported)
    fun error => error matches .lowering (.typeProjection { reason := .unsupportedType (.function _ _), .. })
  let foreign : TypedSource := { inputSource with inputs := [
    { id := ⟨⟨ownerModule, 1⟩, 0⟩, name := "foreign", scheme := .mono .integer }
  ] }
  expectError "Integer input metadata owner" (prepareInputs foreign)
    fun error => error matches .lowering (.ownerMismatch _ _)
  let duplicate : TypedSource := { inputSource with inputs := [
    { id := binder 0, name := "one", scheme := .mono .integer },
    { id := binder 0, name := "two", scheme := .mono .integer }
  ] }
  expectError "Integer duplicate input" (prepareInputs duplicate)
    fun error => error matches .lowering (.duplicateBinding _)

end Tests.SourceCoreIntegerEntry
