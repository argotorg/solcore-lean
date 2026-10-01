import Solcore.Frontend.SourceCoreAllocationLedger

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreAllocationLedger.Ledger.mk

/-! Actual fixed discovery layouts are scanned with opaque initial source
cells, administrative cells, aliases, pending allocations and cyclic payloads.
These tests certify the ledger boundary, not arbitrary store provenance or a
source execution corresponding to each hand-constructed native store. -/
set_option autoImplicit false
namespace Tests.SourceCoreAllocationLedger
open Solcore Solcore.Core Solcore.Frontend SourceInference
open SourceCoreAllocationLedger

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"allocation_ledger", by decide⟩], by decide⟩⟩, 0⟩
private def key : SourceSpecialization.SpecializationKey := ⟨owner, []⟩
private def active : TypeSystem.Substitution := [(⟨42⟩, .word)]
private def binder (index : Nat) (type : TypeSystem.Ty) : TypedBinder := {
  id := ⟨owner, index⟩, name := "local", scheme := .mono type }
private def a := binder 0 .word
private def b := binder 1 .word
private def c := binder 2 .bool
private def f := binder 3 (.function .unit .unit)
private def d := binder 4 .word
private def source : TypedSource := { owner, inputs := [], roots := [], nodes := [] }
private def metadata : SourceCoreAllocationDiscovery.Context := {
  owner := key, active, source, binders := [a, b, c, f, d] }
private def ambient : DataEnvironment := [⟨[.unit]⟩]
private def wordScope : Scope := [(a.id, .word)]
private def aliasScope : Scope := [(a.id, .word), (b.id, .word)]
private def functionType : Ty := .function .unit .unit
private def functionScope : Scope := [(f.id, functionType)]
private def request (allocated : TypedBinder) (type : Ty) (scope : Scope) : SourceCoreSourceCells.Request := {
  source, scope, references := Renaming.id, binder := allocated, payloadType := type, payload := none }
private def requests : List SourceCoreSourceCells.Request :=
  [request a .word [], request b .word wordScope, request c .bool aliasScope,
   request f functionType [], request d .word functionScope]

private def fixture : Except String Layouts := do
  let prepared ← (SourceCoreAllocationDiscovery.prepare ambient [metadata]).mapError reprStr
  let emitted ← requests.mapM (fun request =>
    (SourceCoreAllocationDiscovery.emit prepared key active request).mapError reprStr)
  let discovered ← (SourceCoreAllocationDiscovery.discover prepared 512
    (emitted.foldr Expr.pair .unit)).mapError reprStr
  (SourceCoreAllocationLayouts.prepare discovered).mapError reprStr

private def layout (id : Nat) (scope : Scope) : SourceCoreHeapMarkers.Layout :=
  ⟨⟨id⟩, SourceCoreSourceCells.captureType scope⟩
private def marker (id : Nat) (scope : Scope) (captures : Value) : Value :=
  SourceCoreHeapMarkers.markerValue (layout id scope) captures
private def reference (type : Ty) (index : Nat) : Value := .cellRef (OptionalCell.cellType type) index
private def word (value : Nat) : Value := .word (Word.ofNatModulo value)
private def present (value : Value) : Value := .inRight .unit value

/-- Deliberately invalid and unreachable legacy cells are retained verbatim.
The scan must not inspect their type, body, capture references or metadata. -/
private def initial : SourceHeap := [
  { type := .error, value := some (.closure [] .unit [] source key [(a.id, ⟨999⟩)] []) },
  { type := .word, value := some (.proxy (.comptime .bool)) }]

private def store : Store := [word 99,
  marker 1 [] .unit, present (word 9),
  marker 2 wordScope (reference .word 2), present (word 10),
  marker 3 aliasScope (.pair (reference .word 2) (reference .word 2)), present (.bool true),
  .closure .unit .unit .unit [], .constructed ⟨⟨0⟩, 0⟩ .unit]

private structure Observation where
  locations : List LocationEntry
  environments : List SourceEnvironment
  payloads : List (Option Value)
  pending : Bool
  next : SourceLocation
  deriving Repr, DecidableEq

private def observe (layouts : Layouts) (initial : SourceHeap) (store : Store) : Except SourceCoreAllocationLedger.Error Observation := do
  let ledger ← scan layouts initial store
  pure ⟨ledger.locations, ledger.rows.map (·.environment), ledger.rows.map (·.payload),
    ledger.pending.isSome, ledger.nextSourceLocation⟩

private def check {α : Type} [DecidableEq α] [Repr α] (label : String)
    (actual expected : Except SourceCoreAllocationLedger.Error α) : IO Unit :=
  match actual, expected with
  | .ok actual, .ok expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected result {repr actual}")
  | .error actual, .error expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected error {repr actual}")
  | _, _ => throw (IO.userError s!"{label}: {repr actual}")

private def expected : Observation := ⟨
  [⟨2, ⟨2⟩, .word⟩, ⟨4, ⟨3⟩, .word⟩, ⟨6, ⟨4⟩, .bool⟩],
  [[], [(a.id, ⟨2⟩)], [(a.id, ⟨2⟩), (b.id, ⟨2⟩)]],
  [some (word 9), some (word 10), some (.bool true)], false, ⟨5⟩⟩

private def prefixExport (layouts : Layouts) : Except SourceCoreAllocationLedger.Error (String × String × Nat) := do
  let ledger ← scan layouts initial store
  let exported ← ledger.exportHeap (fun _ => Except.ok ({type := .unit, value := some .unit} : SourceTypedRuntime.Cell))
  pure (reprStr ledger.initialHeap, reprStr (exported.take initial.length), exported.length)

private def recursiveValue : Value :=
  .closure .unit .unit .unit [reference functionType 1]
private def recursiveStore : Store := [marker 4 [] .unit, present recursiveValue,
  marker 5 functionScope (reference functionType 1), present (word 7)]

private def recursiveWorld : StoreTyping :=
  [.namedData ⟨4⟩, OptionalCell.cellType functionType, .namedData ⟨5⟩, OptionalCell.cellType .word]

/-- A closure may capture the very optional cell which contains it. Runtime
typing checks the finite world, without recursively unfolding the heap. -/
private theorem recursiveValue_typed {definitions : DataEnvironment} {world : StoreTyping}
    (self : world[1]? = some (OptionalCell.cellType functionType)) :
    RuntimeValueHasType world recursiveValue functionType definitions :=
  .closure (.cons (.cellRef self) .nil) .unit

private theorem recursiveStore_typed {definitions : DataEnvironment}
    (first : (layout 4 []).Registered definitions)
    (second : (layout 5 functionScope).Registered definitions) :
    RuntimeStoreHasTypes recursiveWorld recursiveStore definitions := by
  have contents : RuntimeEnvironmentHasTypes recursiveWorld recursiveStore recursiveWorld definitions :=
    .cons (.constructed first.payloadLookup .unit)
      (.cons (.inRight (recursiveValue_typed rfl))
        (.cons (.constructed second.payloadLookup (.cellRef rfl))
          (.cons (.inRight .word) .nil)))
  exact ⟨rfl, fun found => contents.lookup found⟩

private def typedCyclic (layouts : Layouts) : Except SourceCoreAllocationLedger.Error (List LocationEntry) := do
  if first : layouts.definitions[4]? = some (layout 4 []).definition then
    if second : layouts.definitions[5]? = some (layout 5 functionScope).definition then
      let firstRegistered : (layout 4 []).Registered layouts.definitions := ⟨.unit, first⟩
      let secondRegistered : (layout 5 functionScope).Registered layouts.definitions :=
        ⟨.cell (.sum .unit (.function .unit .unit)), second⟩
      let certified ← scanTyped layouts [] recursiveWorld recursiveStore
        (recursiveStore_typed firstRegistered secondRegistered)
      pure certified.ledger.locations
    else throw .invalidLedgerOrder
  else throw .invalidLedgerOrder

def run : IO Unit := do
  let layouts ← match fixture with
    | .ok layouts => pure layouts
    | .error error => throw (IO.userError error)
  check "opaque prefix, admin cells and aliased captured source locations"
    (observe layouts initial store) (.ok expected)
  check "opaque prefix is never decoded or validated" (prefixExport layouts)
    (.ok (reprStr initial, reprStr initial, 5))
  let pending := store.take 4
  check "marker-only tail reserves no source location" (observe layouts initial pending)
    (.ok ⟨[⟨2, ⟨2⟩, .word⟩], [[]], [some (word 9)], true, ⟨3⟩⟩)
  check "resume completes payload with stable earlier locations" (observe layouts initial (store.take 5))
    (.ok ⟨[⟨2, ⟨2⟩, .word⟩, ⟨4, ⟨3⟩, .word⟩], [[], [(a.id, ⟨2⟩)]],
      [some (word 9), some (word 10)], false, ⟨4⟩⟩)
  check "initialization flag describes allocation, not later payload contents"
    (observe layouts [] [marker 1 [] .unit, .inLeft .word .unit])
    (.ok ⟨[⟨1, ⟨0⟩, .word⟩], [[]], [none], false, ⟨1⟩⟩)
  check "pending first marker with opaque prefix" (observe layouts initial [marker 1 [] .unit])
    (.ok ⟨[], [], [], true, ⟨2⟩⟩)
  check "unrelated store append preserves completed ledger" (observe layouts initial
      (store ++ [.integer 100, .cellRef .integer 77, .inRight .unit (word 4)])) (.ok expected)
  check "admin frame changes do not affect source mapping" (observe layouts initial
      ([.integer (-123)] ++ store.drop 1)) (.ok expected)
  check "recursive payload is finite and capture references share completed cells"
    (observe layouts [] recursiveStore)
    (.ok ⟨[⟨1, ⟨0⟩, functionType⟩, ⟨3, ⟨1⟩, .word⟩], [[], [(f.id, ⟨0⟩)]],
      [some recursiveValue, some (word 7)], false, ⟨2⟩⟩)
  check "finite runtime world types the whole cyclic store and typed scan"
    (typedCyclic layouts) (.ok [⟨1, ⟨0⟩, functionType⟩, ⟨3, ⟨1⟩, .word⟩])
  let first := store.take 3
  check "capture must reference a completed source cell" (observe layouts []
    (first ++ [marker 2 wordScope (reference .word 0), present (word 1)]))
    (.error (.unknownCaptureLocation 0))
  check "capture cannot reference the future payload" (observe layouts []
    [marker 2 wordScope (reference .word 1), present (word 1)])
    (.error (.unknownCaptureLocation 1))
  check "capture annotation is checked" (observe layouts []
    (first ++ [marker 2 wordScope (.cellRef .word 2), present (word 1)]))
    (.error (.invalidReferenceType .word (OptionalCell.cellType .word)))
  check "actual captured cell payload type is checked" (observe layouts []
    (first ++ [marker 5 functionScope (reference functionType 2), present (word 1)]))
    (.error (.capturePayloadMismatch 2 .word functionType))
  check "capture product pack must match the exact scope" (observe layouts []
    (first ++ [marker 3 aliasScope (reference .word 2), present (.bool true)]))
    (.error .invalidCaptureShape)
  check "empty scope still requires unit capture" (observe layouts []
    [marker 1 [] (.bool false), present (word 1)]) (.error .invalidCaptureShape)
  check "known owner with wrong constructor is rejected" (observe layouts []
    [.constructed ⟨⟨1⟩, 1⟩ .unit, present (word 1)])
    (.error (.invalidKnownConstructor 0 ⟨⟨1⟩, 1⟩ ⟨⟨1⟩, 0⟩))
  check "interleaved known marker cannot stand in for payload" (observe layouts []
    [marker 1 [] .unit, marker 1 [] .unit]) (.error (.invalidOptionalPayload 1 .word))
  check "absent payload annotation must match native payload type" (observe layouts []
    [marker 1 [] .unit, .inLeft .bool .unit]) (.error (.invalidOptionalPayload 1 .word))
  check "present payload must match native payload type" (observe layouts []
    [marker 1 [] .unit, present (.bool true)]) (.error (.invalidOptionalPayload 1 .word))
  check "empty native store preserves opaque source prefix" (observe layouts initial [])
    (.ok ⟨[], [], [], false, ⟨2⟩⟩)

example {layouts : Layouts} {store : Store} (row : Row layouts store) {world : StoreTyping}
    (typed : RuntimeStoreHasTypes world store layouts.definitions) :
    RuntimeValueHasType world row.captures row.entry.layout.captureType layouts.definitions :=
  row.captures_typed typed

example {layouts : Layouts} {initial : SourceHeap} {store : Store} (ledger : Ledger layouts initial store)
    (index : Fin ledger.rows.length) :
    (ledger.rows[index]).environment.map Prod.fst = (ledger.rows[index]).entry.key.scope.map Prod.fst :=
  (ledger.capture_prior_exact index).binders_exact

example {layouts : Layouts} {initial : SourceHeap} {store : Store} (ledger : Ledger layouts initial store)
    (decode : Row layouts store → Except SourceCoreAllocationLedger.Error SourceTypedRuntime.Cell) {heap : SourceHeap}
    (exported : ledger.exportHeap decode = .ok heap) : heap.take initial.length = initial :=
  ledger.exportHeap_prefix decode exported

end Tests.SourceCoreAllocationLedger
