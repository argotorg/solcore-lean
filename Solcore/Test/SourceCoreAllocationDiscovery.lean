import Solcore.Frontend.SourceCoreAllocationDiscovery

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Two-pass allocation discovery uses actual callback requests and preserved
capture layouts. Unused open metadata is accepted without projecting it; these
fixtures do not infer source semantics from a Core payload type. -/
set_option autoImplicit false
namespace Tests.SourceCoreAllocationDiscovery
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreAllocationDiscovery

private def check {α : Type} [DecidableEq α] [Repr α] (label : String)
    (actual expected : Except SourceCoreAllocationDiscovery.Error α) : IO Unit :=
  match actual, expected with
  | .ok actual, .ok expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected result {repr actual}")
  | .error actual, .error expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected error {repr actual}")
  | _, _ => throw (IO.userError s!"{label}: {repr actual}")

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"allocation_discovery", by decide⟩], by decide⟩⟩, 0⟩
private def key : Key := ⟨owner, []⟩
private def active : TypeSystem.Substitution := [(⟨99⟩, .bool)]
private def binder (index : Nat) (type : TypeSystem.Ty) : TypedBinder := {
  id := ⟨owner, index⟩, name := "allocated", scheme := .mono type }
private def outer := binder 0 (.function (.variable ⟨7⟩) (.variable ⟨7⟩))
private def unused := binder 1 (.variable ⟨88⟩)
private def allocated := binder 2 .bool
private def source : TypedSource := { owner, inputs := [outer], roots := [], nodes := [] }
private def canonical : SourceCoreAllocationDiscovery.Context := {
  owner := key, active, source, binders := [outer, unused, allocated] }
private def outerBundle : Core.Ty := .product (.function .word .word) (.function .bool .bool)
private def scope : Scope := [(outer.id, outerBundle)]
private def request : SourceCoreSourceCells.Request := {
  source, scope, references := fun index => index + 2, binder := allocated,
  payloadType := .bool, payload := some (.bool true) }
private def environment : Core.Context := [.word, .integer, OptionalCell.referenceType outerBundle]
private def layout : SourceCoreHeapMarkers.Layout := ⟨⟨0⟩, OptionalCell.referenceType outerBundle⟩
private def expectedInventory : SourceCoreAllocationCodebook.ContextInventory := {
  owner := key, active, source, bindings := [⟨outer, outerBundle⟩, ⟨allocated, .bool⟩] }

private structure Observation where
  inventories : List SourceCoreAllocationCodebook.ContextInventory
  references : List Nat
  definitions : DataEnvironment
  expression : Expr
  deriving Repr, DecidableEq

private def roundtrip : Except SourceCoreAllocationDiscovery.Error Observation := do
  let prepared ← prepare [] [canonical]
  let first ← emit prepared key active request
  let found ← discover prepared 128 first
  let second ← SourceCoreAllocationCodebook.emit found.codebook key active request
  let final ← SourceCoreAllocationCodebook.finalize found.codebook 128 environment
    (OptionalCell.referenceType .bool) second
  pure ⟨found.inventories, found.sites.flatMap (·.receipt.references), final.definitions, final.expression⟩

private def renamed : Except SourceCoreAllocationDiscovery.Error (List Nat × List Scope) := do
  let prepared ← prepare [] [canonical]
  let first ← emit prepared key active request
  let found ← discover prepared 128 (first.weakenAt 0)
  pure (found.sites.flatMap (·.receipt.references), found.sites.map (·.receipt.scope))

private def unusedMetadata : Except SourceCoreAllocationDiscovery.Error (List SourceCoreAllocationCodebook.ContextInventory) := do
  let prepared ← prepare [] [canonical]
  let found ← discover prepared 32 (.lambda .unit .unit .unit)
  pure found.inventories

private def repeated (changedPayload changedCapture : Bool) :
    Except SourceCoreAllocationDiscovery.Error (List SourceCoreAllocationCodebook.ContextInventory) := do
  let prepared ← prepare [] [canonical]
  let first ← emit prepared key active request
  let other := { request with
    payloadType := if changedPayload then .word else .bool
    scope := if changedCapture then [(outer.id, .word)] else scope
    payload := none }
  let second ← emit prepared key active other
  let found ← discover prepared 128 (.pair first second)
  pure found.inventories

private def contexts : Except SourceCoreAllocationDiscovery.Error (List SourceCoreAllocationCodebook.ContextInventory) := do
  let other := [(⟨99⟩, TypeSystem.Ty.word)]
  let prepared ← prepare [] [canonical, {canonical with active := other}]
  let first ← emit prepared key active request
  let second ← emit prepared key other { request with payloadType := .word, payload := none }
  let found ← discover prepared 128 (.pair first second)
  pure found.inventories

private def missingCapture : Except SourceCoreAllocationDiscovery.Error Unit := do
  let prepared ← prepare [] [canonical]
  let _ ← emit prepared key active { request with scope := [(⟨owner, 17⟩, .bool)] }
  pure ()

private def modifiedBinder : Except SourceCoreAllocationDiscovery.Error Unit := do
  let prepared ← prepare [] [canonical]
  let _ ← emit prepared key active { request with binder := {allocated with comptime := true} }
  pure ()

private def malformed : Except SourceCoreAllocationDiscovery.Error Unit := do
  let prepared ← prepare [] [canonical]
  let _ ← discover prepared 32 (.construct ⟨prepared.sentinel, 0⟩ .unit)
  pure ()

private def escaped : Except SourceCoreAllocationDiscovery.Error Unit := do
  let prepared ← prepare [] [canonical]
  let _ ← discover prepared 32 (.lambda (.namedData prepared.sentinel) .unit .unit)
  pure ()

private def unknownKey : Except SourceCoreAllocationDiscovery.Error Unit := do
  let prepared ← prepare [] [canonical]
  let _ ← discover prepared 32
    (placeholder prepared ⟨17, by decide⟩ Word.zero [] .unit .bool .unit none)
  pure ()

private def duplicateMetadata : Except SourceCoreAllocationDiscovery.Error Unit := do
  let _ ← prepare [] [{canonical with binders := [allocated, allocated]}]
  pure ()

private def overflow : Except SourceCoreAllocationDiscovery.Error Unit := do
  let _ ← prepare [] [canonical] wordModulus
  pure ()

private def exhausted : Except SourceCoreAllocationDiscovery.Error Unit := do
  let prepared ← prepare [] [canonical]
  let first ← emit prepared key active request
  let _ ← discover prepared 0 first
  pure ()

private def ordinary : Except SourceCoreAllocationDiscovery.Error Nat := do
  let prepared ← prepare [⟨[.unit]⟩] [canonical]
  let found ← discover prepared 32
    (.pair (.construct ⟨⟨0⟩, 0⟩ .unit) (.pair (.word Word.zero) (.lambda .unit .unit .unit)))
  pure found.sites.length

/-- Exercise the unchanged common allocation helper, then re-run that same
helper with the discovered checked allocator. Administrative result binders
are therefore introduced by the real helper rather than by the fixture. -/
private def commonHelper : Except SourceCoreAllocationDiscovery.Error (List Nat × Expr) := do
  let prepared ← prepare [] [canonical]
  let onError : SourceCoreAllocationDiscovery.Error → SourceCoreBasic.Error := fun _ =>
    .missingExpression ⟨⟨owner, 0⟩⟩
  let first ← (SourceCoreSourceCells.letInitialized (some (prepared.allocatorAt key active onError))
    source scope Renaming.id allocated .bool .bool (LanguageResult.success (.bool true))
    (LanguageResult.success (.bool false))).mapError (fun _ => .emissionMismatch)
  let found ← discover prepared 128 first
  let second ← (SourceCoreSourceCells.letInitialized (some (found.codebook.allocatorAt key active onError))
    source scope Renaming.id allocated .bool .bool (LanguageResult.success (.bool true))
    (LanguageResult.success (.bool false))).mapError (fun _ => .emissionMismatch)
  let final ← SourceCoreAllocationCodebook.finalize found.codebook 128
    [OptionalCell.referenceType outerBundle] (LanguageResult.resultType .bool) second
  pure (found.sites.flatMap (·.receipt.references), final.expression)

def run : IO Unit := do
  check "two-pass inventory and final checker" roundtrip
    (.ok ⟨[expectedInventory], [2], [layout.definition],
      SourceCoreHeapMarkers.allocateInitialized layout .bool (.var 2) (.bool true)⟩)
  check "renaming keeps actual captures" renamed (.ok ([3], [scope]))
  check "unused open metadata not projected" unusedMetadata (.ok [{expectedInventory with bindings := []}])
  check "same binder agrees across occurrences" (repeated false false) (.ok [expectedInventory])
  check "allocated payload disagreement" (repeated true false)
    (.error (.payloadMismatch allocated.id .bool .word))
  check "captured outer bundle disagreement" (repeated false true)
    (.error (.payloadMismatch outer.id outerBundle .word))
  check "full contexts have distinct discovered types" contexts
    (.ok [expectedInventory, {expectedInventory with
      active := [(⟨99⟩, .word)], bindings := [⟨outer, outerBundle⟩, ⟨allocated, .word⟩]}])
  check "unknown capture metadata" missingCapture (.error (.missingBinder Word.zero ⟨owner, 17⟩))
  check "original binder metadata exact" modifiedBinder (.error (.binderMismatch allocated.id))
  check "malformed reserved shape" malformed (.error .malformedPlaceholder)
  check "reserved type outside annotation" escaped (.error (.invalidType (.namedData ⟨0⟩)))
  check "unknown context key" unknownKey (.error (.unknownContextKey ⟨17, by decide⟩))
  check "duplicate original binder" duplicateMetadata (.error (.invalidContext Word.zero))
  check "Word key overflow" overflow (.error (.keyOverflow wordModulus))
  check "discovery exhaustion" exhausted (.error .traversalExhausted)
  check "ordinary nominal/lambda/word shape" ordinary (.ok 0)
  check "common source allocation helper" commonHelper
    (.ok ([1], LanguageResult.bind .bool (LanguageResult.success (.bool true))
      (.letE (SourceCoreHeapMarkers.allocateInitialized layout .bool (.var 1) (.var 0))
        ((LanguageResult.success (.bool false)).weakenAt 1))))

example {prepared : Prepared} {owner : Key} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {expression : Expr}
    (accepted : emit prepared owner active request = .ok expression) :
    ∃ emission : Emission prepared owner active request, emission.expression = expression :=
  emit_receipt accepted

example {prepared : Prepared} {fuel : Nat} {expression : Expr}
    (found : Discovered prepared fuel expression) :
    SourceCoreAllocationCodebook.prepare prepared.ambient found.inventories = .ok found.codebook :=
  found.checked

end Tests.SourceCoreAllocationDiscovery
