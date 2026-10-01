import Solcore.Frontend.SourceCoreAllocationLayouts
import Solcore.Core.BoundedSafety

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreAllocationLayouts.Prepared.mk

/-! Fixed artifact layouts survive different capture embeddings and initial
payload expressions. Syntactic clones share a nominal definition but generated
Core still appends distinct marker/payload pairs on every execution. -/
set_option autoImplicit false
namespace Tests.SourceCoreAllocationLayouts
open Solcore Solcore.Core Solcore.Frontend SourceInference
open SourceCoreAllocationLayouts

private def check {α : Type} [DecidableEq α] [Repr α] (label : String)
    (actual expected : Except SourceCoreAllocationLayouts.Error α) : IO Unit :=
  match actual, expected with
  | .ok actual, .ok expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected result {repr actual}")
  | .error actual, .error expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected error {repr actual}")
  | _, _ => throw (IO.userError s!"{label}: {repr actual}")

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"allocation_layouts", by decide⟩], by decide⟩⟩, 0⟩
private def key : SourceSpecialization.SpecializationKey := ⟨owner, []⟩
private def active : TypeSystem.Substitution := [(⟨42⟩, .bool)]
private def binder (index : Nat) (type : TypeSystem.Ty) : TypedBinder := {
  id := ⟨owner, index⟩, name := "local", scheme := .mono type }
private def capturedBinder := binder 0 .word
private def allocatedBinder := binder 1 .bool
private def source : TypedSource := { owner, inputs := [capturedBinder], roots := [], nodes := [] }
private def metadata : SourceCoreAllocationDiscovery.Context := {
  owner := key, active, source, binders := [capturedBinder, allocatedBinder] }
private def ambient : DataEnvironment := [⟨[.unit]⟩]
private def scope : SourceCoreLocalCell.Scope := [(capturedBinder.id, .word)]
private def request : SourceCoreSourceCells.Request := {
  source, scope, references := fun index => index + 1, binder := allocatedBinder,
  payloadType := .bool, payload := some (.bool true) }
private def layout : SourceCoreHeapMarkers.Layout := ⟨⟨1⟩, OptionalCell.referenceType .word⟩

private def fixture (includeUninitialized : Bool := false) : Except SourceCoreAllocationLayouts.Error Prepared := do
  let prepared ← (SourceCoreAllocationDiscovery.prepare ambient [metadata]).mapError Error.authentication
  let first ← (SourceCoreAllocationDiscovery.emit prepared key active request).mapError Error.authentication
  let repeated := .letE first (first.weakenAt 0)
  let expression ← if includeUninitialized then do
      let absent ← (SourceCoreAllocationDiscovery.emit prepared key active {request with payload := none})
        |>.mapError Error.authentication
      pure (.pair repeated absent)
    else pure repeated
  let discovered ← (SourceCoreAllocationDiscovery.discover prepared 128 expression).mapError Error.authentication
  prepare discovered

private def staticLayouts (includeUninitialized : Bool) :
    Except SourceCoreAllocationLayouts.Error (List Nat × DataEnvironment) := do
  let fixed ← fixture includeUninitialized
  pure (fixed.entries.map (·.layout.dataType.index), fixed.definitions)

private def differentEmbedding : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with references := fun index => index + 5, payload := some (.bool false)}

private def unobservedScope : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with scope := [], references := Renaming.id}

private def unobservedInitialization : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with payload := none}

private def initializedVariant : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture true
  allocate fixed key active {request with payload := none}

private def missingBinder : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with binder := binder 17 .bool}

private def mismatchPayload : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with payloadType := .word, payload := none}

private def duplicateCapture : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with scope := scope ++ scope}

private def mismatchMetadata : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with binder := {allocatedBinder with comptime := true}}

private def wrongContext : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key [] request

private structure RunObservation where
  value : Value
  store : Store
  definitions : DataEnvironment
  deriving Repr, DecidableEq

private def runTwice : Except SourceCoreAllocationLayouts.Error RunObservation := do
  let fixed ← fixture
  let first ← allocate fixed key active request
  let second ← allocate fixed key active {request with
    references := fun index => index + 2
    payload := some (.bool false)}
  let code := .letE first second
  unless Core.infer? [.integer, OptionalCell.referenceType .word] code fixed.definitions =
      some (OptionalCell.referenceType .bool) do throw .invalidDefinitions
  match Core.runStateful 200 (.initial code
      [.integer 123, .cellRef (OptionalCell.cellType .word) 0]
      [.inRight .unit (.word (Word.ofNatModulo 9))]) with
  | .done value store => pure ⟨value, store, fixed.definitions⟩
  | _ => throw .invalidDefinitions

private def emptyCatalog : Except SourceCoreAllocationLayouts.Error (List Nat × DataEnvironment) := do
  let prepared ← (SourceCoreAllocationDiscovery.prepare ambient [metadata]).mapError Error.authentication
  let discovered ← (SourceCoreAllocationDiscovery.discover prepared 32 (.lambda .unit .unit .unit)).mapError Error.authentication
  let fixed ← prepare discovered
  pure (fixed.entries.map (·.layout.dataType.index), fixed.definitions)

private def contextSpecific : Except SourceCoreAllocationLayouts.Error (List Nat) := do
  let other := [(⟨42⟩, TypeSystem.Ty.word)]
  let prepared ← (SourceCoreAllocationDiscovery.prepare ambient [metadata, {metadata with active := other}])
    |>.mapError Error.authentication
  let first ← (SourceCoreAllocationDiscovery.emit prepared key active request).mapError Error.authentication
  let second ← (SourceCoreAllocationDiscovery.emit prepared key other request).mapError Error.authentication
  let discovered ← (SourceCoreAllocationDiscovery.discover prepared 128 (.pair first second)).mapError Error.authentication
  let fixed ← prepare discovered
  pure (fixed.entries.map (·.layout.dataType.index))

private def malformed : Except SourceCoreAllocationLayouts.Error Unit := do
  let prepared ← (SourceCoreAllocationDiscovery.prepare ambient [metadata]).mapError Error.authentication
  let discovered ← (SourceCoreAllocationDiscovery.discover prepared 32 (.construct ⟨prepared.sentinel, 1⟩ .unit))
    |>.mapError Error.authentication
  let _ ← prepare discovered
  pure ()

private def overflow : Except SourceCoreAllocationLayouts.Error Unit := do
  let _ ← (SourceCoreAllocationDiscovery.prepare ambient [metadata] wordModulus).mapError Error.authentication
  pure ()

def run : IO Unit := do
  check "cloned site shares one fixed definition" (staticLayouts false) (.ok ([1], ambient ++ [layout.definition]))
  check "initialized form is part of static key" (staticLayouts true)
    (.ok ([1, 2], ambient ++ [layout.definition, layout.definition]))
  check "actual captures and initializer are request-specific" differentEmbedding
    (.ok (SourceCoreHeapMarkers.allocateInitialized layout .bool (.var 5) (.bool false)))
  check "unobserved lexical scope rejected" unobservedScope
    (.error (.unobservedLayout (Key.ofRequest key active {request with scope := [], references := Renaming.id})))
  check "unobserved initialized form rejected" unobservedInitialization
    (.error (.unobservedLayout (Key.ofRequest key active {request with payload := none})))
  check "registered uninitialized variant" initializedVariant
    (.ok (SourceCoreHeapMarkers.allocate ⟨⟨2⟩, OptionalCell.referenceType .word⟩ .bool (.var 1)))
  check "unknown original binder rejected before selection" missingBinder
    (.error (.authentication (.missingBinder Word.zero (binder 17 .bool).id)))
  check "payload type reauthenticated" mismatchPayload
    (.error (.authentication (.payloadMismatch allocatedBinder.id .bool .word)))
  check "duplicate source capture rejected" duplicateCapture (.error (.authentication .duplicateScope))
  check "binder flags reauthenticated" mismatchMetadata (.error (.authentication (.binderMismatch allocatedBinder.id)))
  check "full context reauthenticated" wrongContext (.error (.authentication (.missingContext key [])))
  let captured := .cellRef (OptionalCell.cellType .word) 0
  check "shared layout still allocates two distinct runtime pairs" runTwice
    (.ok ⟨.cellRef (OptionalCell.cellType .bool) 4,
      [.inRight .unit (.word (Word.ofNatModulo 9)), SourceCoreHeapMarkers.markerValue layout captured,
        .inRight .unit (.bool true), SourceCoreHeapMarkers.markerValue layout captured, .inRight .unit (.bool false)],
      ambient ++ [layout.definition]⟩)
  check "no sites preserves only ambient catalog" emptyCatalog (.ok ([], ambient))
  check "full contextual identities never share layout" contextSpecific (.ok [1, 2])
  check "malformed initial discovery refused" malformed (.error (.authentication .malformedPlaceholder))
  check "metadata Word overflow never wraps" overflow (.error (.authentication (.keyOverflow wordModulus)))

example {prepared : Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    (receipt : Allocation prepared owner active request) :
    ∃ site ∈ prepared.origin.discovered.sites, Key.ofReceipt site.receipt = Key.ofRequest owner active request :=
  receipt.observed

example {prepared : Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    (receipt : Allocation prepared owner active request) : receipt.entry.layout.Registered prepared.definitions :=
  receipt.registered

end Tests.SourceCoreAllocationLayouts
