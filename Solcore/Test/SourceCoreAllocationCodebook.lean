import Solcore.Frontend.SourceCoreAllocationCodebook
import Solcore.Core.BoundedSafety

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Allocation catalog fixtures exercise actual pure preparation/emission,
renaming, suffix installation and the final Core checker. The machine fixtures
only run the generated Core to check initializer/marker/payload order. They do
not use a source evaluator or claim a source-heap export theorem. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreAllocationCodebook
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreAllocationCodebook

private def check {α : Type} [DecidableEq α] [Repr α] (label : String)
    (actual expected : Except SourceCoreAllocationCodebook.Error α) : IO Unit :=
  match actual, expected with
  | .ok actual, .ok expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected result {repr actual}")
  | .error actual, .error expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected error {repr actual}")
  | _, _ => throw (IO.userError s!"{label}: {repr actual}")

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"allocation_codebook", by decide⟩], by decide⟩⟩, 0⟩
private def key : Key := ⟨owner, []⟩
private def active : TypeSystem.Substitution := [(⟨42⟩, .word)]
private def binder (index : Nat) (type : TypeSystem.Ty) : TypedBinder := {
  id := ⟨owner, index⟩, name := "local", scheme := .mono type }
private def a := binder 0 .bool
private def b := binder 1 .word
private def c := binder 2 .integer
private def source : TypedSource := { owner, inputs := [a, b], roots := [], nodes := [] }
private def inventory : ContextInventory := {
  owner := key, active, source, bindings := [⟨a, .bool⟩, ⟨b, .word⟩, ⟨c, .integer⟩] }
private def ambient : DataEnvironment := [⟨[.unit]⟩]
private def scope : SourceCoreLocalCell.Scope := [(b.id, .word), (a.id, .bool)]
private def context : Core.Context := [.integer, OptionalCell.referenceType .word, OptionalCell.referenceType .bool]
private def request : SourceCoreSourceCells.Request := {
  source, scope, references := fun index => index + 1, binder := c, payloadType := .integer
  payload := some (.letE (.newCell .integer (.integer 8)) (.integer 9)) }

private structure Observation where
  references : List Nat
  scopes : List SourceCoreLocalCell.Scope
  definitions : DataEnvironment
  expression : Expr
  deriving Repr, DecidableEq

private def compile (request : SourceCoreSourceCells.Request) (rename : Renaming := Renaming.id)
    (context : Core.Context := context) : Except SourceCoreAllocationCodebook.Error Observation := do
  let prepared ← prepare ambient [inventory]
  let raw ← emit prepared key active request
  let result ← finalize prepared 128 context (OptionalCell.referenceType .integer) (raw.rename rename)
  pure ⟨result.entries.flatMap (·.receipt.references), result.entries.map (·.receipt.scope), result.definitions, result.expression⟩

private def captureType : Core.Ty := .product (OptionalCell.referenceType .word) (OptionalCell.referenceType .bool)
private def layout : SourceCoreHeapMarkers.Layout := ⟨⟨1⟩, captureType⟩
private def captures : Expr := .pair (.var 1) (.var 2)
private def emitted : Expr := SourceCoreHeapMarkers.allocateInitialized layout .integer captures
  (.letE (.newCell .integer (.integer 8)) (.integer 9))


private def initial : Store := [.inRight .unit (.word Word.zero), .inRight .unit (.bool true)]
private def environment : Environment := [.integer 123,
  .cellRef (OptionalCell.cellType .word) 0, .cellRef (OptionalCell.cellType .bool) 1]
private def captured : Value := .pair (.cellRef (OptionalCell.cellType .word) 0)
  (.cellRef (OptionalCell.cellType .bool) 1)

private def malformed : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let _ ← finalize prepared 32 [] .unit (.construct ⟨prepared.sentinel, 0⟩ .unit)
  pure ()

private def escapedType : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let _ ← finalize prepared 32 [] (.function .unit .unit)
    (.lambda (.namedData prepared.sentinel) .unit .unit)
  pure ()

private def unknownKey : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let _ ← decode prepared (placeholder prepared (← wordKey 17) Word.zero [] .unit .bool .unit none)
  pure ()

private def ordinaryShape : Except SourceCoreAllocationCodebook.Error (Nat × Expr) := do
  let prepared ← prepare ambient [inventory]
  let expression := .pair (.word Word.zero) (.lambda .unit .unit .unit)
  let result ← finalize prepared 32 [] (.product .word (.function .unit .unit)) expression
  pure (result.entries.length, result.expression)

private def duplicateContexts : Except SourceCoreAllocationCodebook.Error Unit := do
  let _ ← prepare ambient [inventory, inventory]
  pure ()

private def duplicateBinders : Except SourceCoreAllocationCodebook.Error Unit := do
  let _ ← prepare ambient [{ inventory with bindings := [⟨a, .bool⟩, ⟨a, .bool⟩] }]
  pure ()



private def duplicateCaptures : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let _ ← emit prepared key active { request with references := fun _ => 1 }
  pure ()

private def forgedBinder : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let _ ← emit prepared key active { request with binder := { c with comptime := true } }
  pure ()

private def wrongSubstitution : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let _ ← emit prepared key [] request
  pure ()

/-- Final checker rejection catches ill-scoped real captures; nominal-marker
recognition alone cannot authenticate the caller's Core environment. -/
private def badEnvironment : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let raw ← emit prepared key active request
  let _ ← finalize prepared 128 [] (OptionalCell.referenceType .integer) raw
  pure ()

private def overflow : Except SourceCoreAllocationCodebook.Error Unit := do
  let _ ← prepare ambient [inventory] wordModulus
  pure ()

example : wordKey wordModulus = .error (.keyOverflow wordModulus) := by simp [wordKey, Word.ofNat?]

example : runStateful 200 (.initial emitted environment initial) =
    .done (.cellRef (OptionalCell.cellType .integer) 4)
      (initial ++ [.integer 8, SourceCoreHeapMarkers.markerValue layout captured, .inRight .unit (.integer 9)]) := by cbv

private def expressionNode : ExpressionNode := {
  id := ⟨⟨owner, 0⟩⟩, span := ⟨⟨.main, "allocation.solc"⟩, 0, 1⟩,
  type := .bool, form := .reference "true" (.builtinBoolean true) }

private def viewCheck (changeForm : Bool) : Except SourceCoreAllocationCodebook.Error Unit := do
  let canonical := { source with nodes := [.expression expressionNode] }
  let changedNode := { expressionNode with
    type := .word
    form := if changeForm then .reference "false" (.builtinBoolean false) else expressionNode.form }
  let changed := { source with nodes := [.expression changedNode] }
  let prepared ← prepare ambient [{ inventory with source := canonical }]
  let _ ← emit prepared key active { request with source := changed }
  pure ()

private def distinctContexts : Except SourceCoreAllocationCodebook.Error (Word × TypeSystem.Substitution) := do
  let otherActive := [(⟨42⟩, TypeSystem.Ty.bool)]
  let prepared ← prepare ambient [inventory, { inventory with active := otherActive }]
  let emission ← emitWithReceipt prepared key otherActive request
  pure (emission.receipt.context.key, emission.receipt.context.inventory.active)

private def twoSites : Except SourceCoreAllocationCodebook.Error (List Nat) := do
  let prepared ← prepare ambient [inventory]
  let raw ← emit prepared key active { request with payload := none }
  let result ← finalize prepared 128 context (OptionalCell.referenceType .integer) (.letE raw (raw.weakenAt 0))
  pure (result.entries.map (·.layout.dataType.index))

def run : IO Unit := do
  check "initialized metadata/captures/definitions" (compile request)
    (.ok ⟨[1, 2], [scope], ambient ++ [layout.definition], emitted⟩)
  check "renamed captures" (compile request (Renaming.insertion 0) (.bool :: context))
    (.ok ⟨[2, 3], [scope], ambient ++ [layout.definition],
      SourceCoreHeapMarkers.allocateInitialized layout .integer (.pair (.var 2) (.var 3))
        (.letE (.newCell .integer (.integer 8)) (.integer 9))⟩)
  check "uninitialized allocation" (compile { request with payload := none })
    (.ok ⟨[1, 2], [scope], ambient ++ [layout.definition], SourceCoreHeapMarkers.allocate layout .integer captures⟩)
  check "malformed reserved construct" malformed (.error .malformedPlaceholder)
  check "reserved type outside marker" escapedType (.error (.invalidType (.namedData ⟨1⟩)))
  check "unknown context key" unknownKey (.error (.unknownContextKey ⟨17, by decide⟩))
  check "ordinary Core shape preserved" ordinaryShape (.ok (0, .pair (.word Word.zero) (.lambda .unit .unit .unit)))
  check "duplicate contexts" duplicateContexts (.error .duplicateContexts)
  check "duplicate binders" duplicateBinders (.error (.invalidContext Word.zero))
  check "word overflow" overflow (.error (.keyOverflow wordModulus))
  check "duplicate capture slots" duplicateCaptures (.error .duplicateReferences)
  check "changed original binder" forgedBinder (.error (.binderMismatch c.id))
  check "complete substitution key" wrongSubstitution (.error (.missingContext key []))
  check "final checker" badEnvironment (.error (.finalBodyType (OptionalCell.referenceType .integer) none))
  check "raw metadata view accepted" (viewCheck false) (.ok ())
  check "changed source form rejected" (viewCheck true) (.error (.sourceViewMismatch Word.zero))
  check "full active contexts remain distinct" distinctContexts (.ok (⟨1, by decide⟩, [(⟨42⟩, .bool)]))
  check "each emitted site indexes its definition" twoSites (.ok [1, 2])

/-- An accepted emission retains exact source/capture/binder provenance. -/
example {prepared : Prepared} {owner : Key} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {expression : Expr}
    (accepted : emit prepared owner active request = .ok expression) :
    ∃ receipt : Receipt, decode prepared expression = .ok receipt ∧
      receipt.context.inventory.owner = owner ∧ receipt.context.inventory.active = active ∧
      receipt.binding.binding.binder = request.binder ∧ receipt.scope = request.scope ∧
      receipt.captures = SourceCoreSourceCells.captures request.references request.scope := by
  obtain ⟨emission, rfl⟩ := emit_receipt accepted
  exact ⟨emission.receipt, emission.decoded, emission.ownerExact, emission.activeExact,
    emission.binderExact, emission.scopeExact, emission.capturesExact⟩

end Tests.SourceCoreAllocationCodebook
