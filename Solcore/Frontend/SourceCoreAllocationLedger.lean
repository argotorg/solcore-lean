import Solcore.Frontend.SourceCoreAllocationLayouts
import Solcore.Frontend.SourceRuntimeValues
import Solcore.Core.Safety

/-! Source-visible allocation locations and captures observed in a Core store.
Only completed adjacent marker/optional-payload pairs produce rows. Unrelated
administrative cells are skipped and a marker-only tail remains pending.

The initial source heap is an opaque retained prefix; no value or closure in
that prefix is inspected or imported into Core. Payload interpretation, closure
code provenance and source-execution correspondence are later boundaries.
Typing a store alone does not establish its compilation or execution history. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreAllocationLedger
open SourceInference Core
abbrev SourceLocation := SourceTypedRuntime.Location
abbrev SourceEnvironment := SourceTypedRuntime.Environment
abbrev SourceHeap := List SourceTypedRuntime.Cell
abbrev Layouts := SourceCoreAllocationLayouts.Prepared
abbrev LayoutEntry (layouts : Layouts) := SourceCoreAllocationLayouts.Entry layouts.origin
abbrev Scope := SourceCoreLocalCell.Scope

inductive Error where
  | exhausted
  | invalidKnownConstructor (location : Nat) (actual expected : ConstructorId)
  | invalidCaptureShape
  | invalidReferenceType (actual expected : Ty)
  | unknownCaptureLocation (location : Nat)
  | capturePayloadMismatch (location : Nat) (actual expected : Ty)
  | invalidOptionalPayload (location : Nat) (expected : Ty)
  | invalidLedgerOrder
  deriving Repr, DecidableEq

structure LocationEntry where
  core : Core.Location
  source : SourceLocation
  payloadType : Ty
  deriving Repr, DecidableEq

inductive Reference (prior : List LocationEntry) (type : Ty) : Value → SourceLocation → Prop where
  | intro {entry : LocationEntry} (member : entry ∈ prior) (typeExact : entry.payloadType = type) :
      Reference prior type (.cellRef (OptionalCell.cellType type) entry.core) entry.source

inductive Captures (prior : List LocationEntry) : Scope → Value → SourceEnvironment → Prop where
  | nil : Captures prior [] .unit []
  | one {id : Resolved.LocalId} {type : Ty} {value : Value} {location : SourceLocation}
      (reference : Reference prior type value location) :
      Captures prior [(id, type)] value [(id, location)]
  | cons {id : Resolved.LocalId} {type : Ty} {next : Resolved.LocalId × Ty} {rest : Scope}
      {head tail : Value} {location : SourceLocation} {environment : SourceEnvironment}
      (reference : Reference prior type head location)
      (following : Captures prior (next :: rest) tail environment) :
      Captures prior ((id, type) :: next :: rest) (.pair head tail) ((id, location) :: environment)

theorem Reference.type_eq {prior : List LocationEntry} {type : Ty} {value : Value} {location : SourceLocation}
    (related : Reference prior type value location) : value.type = OptionalCell.referenceType type := by
  cases related
  rfl

theorem Captures.type_eq {prior : List LocationEntry} {scope : Scope} {value : Value} {environment : SourceEnvironment}
    (related : Captures prior scope value environment) : value.type = SourceCoreSourceCells.captureType scope := by
  induction related with
  | nil => rfl
  | one reference => exact reference.type_eq
  | cons reference following ih =>
    simpa only [Value.type, SourceCoreSourceCells.captureType, reference.type_eq] using congrArg (Ty.product _) ih

theorem Captures.binders_exact {prior : List LocationEntry} {scope : Scope} {value : Value} {environment : SourceEnvironment}
    (related : Captures prior scope value environment) : environment.map Prod.fst = scope.map Prod.fst := by
  induction related with
  | nil | one => rfl
  | cons reference following ih => simp only [List.map_cons, ih]

structure ReferenceReceipt (prior : List LocationEntry) (type : Ty) (value : Value) where
  location : SourceLocation
  related : Reference prior type value location

private def resolveReference (prior : List LocationEntry) (type : Ty) :
    (value : Value) → Except Error (ReferenceReceipt prior type value)
  | .cellRef element location =>
    if elementEq : element = OptionalCell.cellType type then
      match found : prior.find? (fun entry => decide (entry.core = location)) with
      | none => .error (.unknownCaptureLocation location)
      | some entry =>
        if typeEq : entry.payloadType = type then
          .ok ⟨entry.source, by
            have located : entry.core = location := by
              have tested := List.find?_some found
              exact of_decide_eq_true tested
            rw [elementEq, ← located]
            exact .intro (List.mem_of_find?_eq_some found) typeEq⟩
        else .error (.capturePayloadMismatch location entry.payloadType type)
    else .error (.invalidReferenceType element (OptionalCell.cellType type))
  | _ => .error .invalidCaptureShape

structure CaptureReceipt (prior : List LocationEntry) (scope : Scope) (value : Value) where
  environment : SourceEnvironment
  related : Captures prior scope value environment

def captureEnvironment (prior : List LocationEntry) :
    (scope : Scope) → (value : Value) → Except Error (CaptureReceipt prior scope value)
  | [], .unit => .ok ⟨[], .nil⟩
  | [], _ => .error .invalidCaptureShape
  | [(id, type)], value => do
    let found ← resolveReference prior type value
    pure ⟨[(id, found.location)], .one found.related⟩
  | (id, type) :: next :: rest, .pair head tail => do
    let found ← resolveReference prior type head
    let following ← captureEnvironment prior (next :: rest) tail
    pure ⟨(id, found.location) :: following.environment, .cons found.related following.related⟩
  | _ :: _ :: _, _ => .error .invalidCaptureShape

def optionalValue (type : Ty) : Option Value → Value
  | none => .inLeft type .unit
  | some value => .inRight .unit value

structure PayloadReceipt (type : Ty) (optional : Value) where
  payload : Option Value
  shape : optional = optionalValue type payload
  typeExact : optional.type = OptionalCell.cellType type

private def decodePayload (location : Nat) (type : Ty) :
    (optional : Value) → Except Error (PayloadReceipt type optional)
  | .inLeft annotation .unit =>
    if equal : annotation = type then .ok ⟨none, by simp [optionalValue, equal], by simp [Value.type, OptionalCell.cellType, equal]⟩
    else .error (.invalidOptionalPayload location type)
  | .inRight .unit value =>
    if typed : value.type = type then .ok ⟨some value, rfl, by simp [Value.type, OptionalCell.cellType, typed]⟩
    else .error (.invalidOptionalPayload location type)
  | _ => .error (.invalidOptionalPayload location type)

structure Row (layouts : Layouts) (store : Store) where
  entry : LayoutEntry layouts
  member : entry ∈ layouts.entries
  markerIndex : Nat
  sourceLocation : SourceLocation
  captures : Value
  optional : Value
  payload : Option Value
  environment : SourceEnvironment
  prior : List LocationEntry
  markerFound : store[markerIndex]? = some (SourceCoreHeapMarkers.markerValue entry.layout captures)
  payloadFound : store[markerIndex + 1]? = some optional
  payloadShape : optional = optionalValue entry.key.payloadType payload
  payloadType : optional.type = OptionalCell.cellType entry.key.payloadType
  captured : Captures prior entry.key.scope captures environment
  deriving Repr

def Row.coreLocation {layouts : Layouts} {store : Store} (row : Row layouts store) : Core.Location := row.markerIndex + 1

def Row.location {layouts : Layouts} {store : Store} (row : Row layouts store) : LocationEntry :=
  ⟨row.coreLocation, row.sourceLocation, row.entry.key.payloadType⟩

structure Pending (layouts : Layouts) (store : Store) where
  entry : LayoutEntry layouts
  member : entry ∈ layouts.entries
  markerIndex : Nat
  captures : Value
  environment : SourceEnvironment
  prior : List LocationEntry
  markerFound : store[markerIndex]? = some (SourceCoreHeapMarkers.markerValue entry.layout captures)
  payloadMissing : store[markerIndex + 1]? = none
  captured : Captures prior entry.key.scope captures environment
  deriving Repr

theorem Pending.is_tail {layouts : Layouts} {store : Store} (pending : Pending layouts store) :
    pending.markerIndex + 1 = store.length := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp pending.markerFound
  have ending := List.getElem?_eq_none_iff.mp pending.payloadMissing
  omega

structure Result (layouts : Layouts) (store : Store) where
  rows : List (Row layouts store)
  pending : Option (Pending layouts store)
  deriving Repr

private def scanFrom (layouts : Layouts) (initial : SourceHeap) (store : Store) :
    Nat → Nat → List (Row layouts store) → Except Error (Result layouts store)
  | 0, _, _ => .error .exhausted
  | fuel + 1, index, rows => do
    match current : store[index]? with
    | none => pure ⟨rows, none⟩
    | some value =>
      match valueEq : value with
      | .constructed constructor captures =>
        match found : layouts.entries.find? (fun entry => decide (entry.layout.dataType = constructor.owner)) with
        | none => scanFrom layouts initial store fuel (index + 1) rows
        | some entry =>
          if exactConstructor : constructor = entry.layout.constructor then
            let prior := rows.map Row.location
            let captured ← captureEnvironment prior entry.key.scope captures
            have marker : store[index]? = some (SourceCoreHeapMarkers.markerValue entry.layout captures) := by
              simpa only [SourceCoreHeapMarkers.markerValue, valueEq, exactConstructor] using current
            match payloadFound : store[index + 1]? with
            | none =>
              pure ⟨rows, some ⟨entry, List.mem_of_find?_eq_some found, index, captures,
                captured.environment, prior, marker, payloadFound, captured.related⟩⟩
            | some optional =>
              let payload ← decodePayload (index + 1) entry.key.payloadType optional
              let row : Row layouts store := {
                entry, member := List.mem_of_find?_eq_some found
                markerIndex := index
                sourceLocation := ⟨initial.length + rows.length⟩
                captures, optional, payload := payload.payload
                environment := captured.environment, prior
                markerFound := marker, payloadFound
                payloadShape := payload.shape, payloadType := payload.typeExact
                captured := captured.related }
              scanFrom layouts initial store fuel (index + 2) (rows ++ [row])
          else throw (.invalidKnownConstructor index constructor entry.layout.constructor)
      | _ => scanFrom layouts initial store fuel (index + 1) rows

/-- Independent finite checks connect every capture to exactly the preceding
completed rows and place source locations after the untouched initial prefix. -/
def RowsAligned {layouts : Layouts} {store : Store} (initial : SourceHeap) (rows : List (Row layouts store)) : Prop :=
  ∀ index : Fin rows.length,
    (rows[index]).sourceLocation.index = initial.length + index.val ∧
    (rows[index]).prior = (rows.take index.val).map Row.location ∧
    (rows.take index.val).all (fun previous => decide (previous.coreLocation < (rows[index]).markerIndex)) = true

def PendingAligned {layouts : Layouts} {store : Store} (rows : List (Row layouts store)) : Option (Pending layouts store) → Prop
  | none => True
  | some pending => pending.prior = rows.map Row.location ∧
      rows.all (fun row => decide (row.coreLocation < pending.markerIndex)) = true

instance {layouts : Layouts} {store : Store} (initial : SourceHeap) (rows : List (Row layouts store)) :
    Decidable (RowsAligned initial rows) := inferInstanceAs (Decidable (∀ _ : Fin rows.length, _ ∧ _ ∧ _))
instance {layouts : Layouts} {store : Store} (rows : List (Row layouts store)) (pending : Option (Pending layouts store)) :
    Decidable (PendingAligned rows pending) := by
  cases pending <;> unfold PendingAligned <;> infer_instance

structure Ledger (layouts : Layouts) (initial : SourceHeap) (store : Store) where private mk ::
  rows : List (Row layouts store)
  pending : Option (Pending layouts store)
  aligned : RowsAligned initial rows
  pendingAligned : PendingAligned rows pending
  deriving Repr

def scan (layouts : Layouts) (initial : SourceHeap) (store : Store) : Except Error (Ledger layouts initial store) := do
  let result ← scanFrom layouts initial store (store.length + 1) 0 []
  if aligned : RowsAligned initial result.rows then
    if pendingAligned : PendingAligned result.rows result.pending then
      pure ⟨result.rows, result.pending, aligned, pendingAligned⟩
    else throw .invalidLedgerOrder
  else throw .invalidLedgerOrder

def Ledger.initialHeap {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (_ledger : Ledger layouts initial store) : SourceHeap := initial

def Ledger.locations {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) : List LocationEntry := ledger.rows.map Row.location

def Ledger.locationAt? {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) (location : Core.Location) : Option LocationEntry :=
  ledger.locations.find? (fun entry => decide (entry.core = location))

def Ledger.nextSourceLocation {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) : SourceLocation := ⟨initial.length + ledger.rows.length⟩

/-- Cell interpretation is supplied by the later value decoder. The prefix
is retained verbatim and is never sent through that decoder. -/
def Ledger.exportHeap {layouts : Layouts} {initial : SourceHeap} {store : Store} {ε : Type}
    (ledger : Ledger layouts initial store) (decode : Row layouts store → Except ε SourceTypedRuntime.Cell) : Except ε SourceHeap := do
  pure (initial ++ (← ledger.rows.mapM decode))

theorem Ledger.exportHeap_prefix {layouts : Layouts} {initial : SourceHeap} {store : Store} {ε : Type}
    (ledger : Ledger layouts initial store) (decode : Row layouts store → Except ε SourceTypedRuntime.Cell)
    {heap : SourceHeap} (exported : ledger.exportHeap decode = .ok heap) : heap.take initial.length = initial := by
  cases decoded : ledger.rows.mapM decode with
  | error error => simp [exportHeap, decoded, Functor.map, Except.map] at exported
  | ok cells =>
    simp [exportHeap, decoded, Functor.map, Except.map] at exported
    subst heap
    simp

theorem Ledger.sourceLocation_exact {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) (index : Fin ledger.rows.length) :
    (ledger.rows[index]).sourceLocation.index = initial.length + index.val := (ledger.aligned index).1

theorem Ledger.sourceLocation_injective {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) :
    Function.Injective (fun index : Fin ledger.rows.length => (ledger.rows[index]).sourceLocation) := by
  intro left right equal
  apply Fin.ext
  have same := congrArg (fun location : SourceLocation => location.index) equal
  rw [ledger.sourceLocation_exact left, ledger.sourceLocation_exact right] at same
  omega

theorem Ledger.locationAt?_found {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) {location : Core.Location} {entry : LocationEntry}
    (found : ledger.locationAt? location = some entry) :
    entry ∈ ledger.locations ∧ entry.core = location := by
  have tested := List.find?_some found
  exact ⟨List.mem_of_find?_eq_some found, of_decide_eq_true tested⟩

theorem Ledger.capture_prior_exact {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) (index : Fin ledger.rows.length) :
    Captures ((ledger.rows.take index.val).map Row.location) (ledger.rows[index]).entry.key.scope
      (ledger.rows[index]).captures (ledger.rows[index]).environment := by
  rw [← (ledger.aligned index).2.1]
  exact (ledger.rows[index]).captured

private theorem value_typed_at {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typed : RuntimeStoreHasTypes world store definitions) {index : Nat} {value : Value}
    (found : store[index]? = some value) : RuntimeValueHasType world value value.type definitions := by
  have worldFound : world[index]? = some value.type := by
    rw [typed.world_eq]
    simp only [List.getElem?_map, found, Option.map_some]
  obtain ⟨actual, read, valueTyped⟩ := typed.read worldFound
  have same : actual = value := by
    have read : store[index]? = some actual := read
    exact Option.some.inj (read.symm.trans found)
  subst actual
  exact valueTyped

theorem Row.optional_typed {layouts : Layouts} {store : Store} (row : Row layouts store)
    {world : StoreTyping} (typed : RuntimeStoreHasTypes world store layouts.definitions) :
    RuntimeValueHasType world row.optional (OptionalCell.cellType row.entry.key.payloadType) layouts.definitions := by
  rw [← row.payloadType]
  exact value_typed_at typed row.payloadFound

theorem Row.captures_typed {layouts : Layouts} {store : Store} (row : Row layouts store)
    {world : StoreTyping} (typed : RuntimeStoreHasTypes world store layouts.definitions) :
    RuntimeValueHasType world row.captures row.entry.layout.captureType layouts.definitions := by
  have markerTyped := value_typed_at typed row.markerFound
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp row.member
  have registered := layouts.entry_registered found
  cases markerTyped with
  | constructed payloadFound capturesTyped =>
    rw [registered.payloadLookup] at payloadFound
    cases payloadFound
    exact capturesTyped

theorem Row.payload_typed {layouts : Layouts} {store : Store} (row : Row layouts store)
    {world : StoreTyping} (typed : RuntimeStoreHasTypes world store layouts.definitions)
    {value : Value} (present : row.payload = some value) :
    RuntimeValueHasType world value row.entry.key.payloadType layouts.definitions := by
  have valueTyped := row.optional_typed typed
  rw [row.payloadShape, present] at valueTyped
  cases valueTyped with
  | inRight payloadTyped => exact payloadTyped

structure TypedLedger (layouts : Layouts) (initial : SourceHeap) (world : StoreTyping) (store : Store) where
  ledger : Ledger layouts initial store
  typed : RuntimeStoreHasTypes world store layouts.definitions
  deriving Repr

def scanTyped (layouts : Layouts) (initial : SourceHeap) (world : StoreTyping) (store : Store)
    (typed : RuntimeStoreHasTypes world store layouts.definitions) : Except Error (TypedLedger layouts initial world store) :=
  (scan layouts initial store).map (fun ledger => ⟨ledger, typed⟩)

end Solcore.Frontend.SourceCoreAllocationLedger
