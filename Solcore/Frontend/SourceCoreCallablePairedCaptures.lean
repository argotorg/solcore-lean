import Solcore.Frontend.SourceCoreCallablePairedTemplates
import Solcore.Frontend.SourceCoreCallablePairedLedger

/-! Captured native references are joined to the actual allocation ledger by
physical Core location first. Binder identity, native payload type, owner,
complete native allocated context and contextual binder metadata are then
checked. Source metadata substitutions remain separate from these native
context checks; the source principal can have a different active context.
Repeated recursive allocations of the same binder remain different rows.

A produced receipt retains the owning completion and an exact successful
observation. Subvalue paths cover result data only, never closure environments.
The join preserves ordered source locations after the opaque prefix. It does
not reconstruct source lambda bodies or derive ancestry history from words.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedCaptures
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallablePairedPrograms.Prepared
abbrev Cache {checked : Checked} (prepared : Prepared checked) := SourceCoreCallablePairedTemplates.Cache prepared
abbrev Template := SourceCoreCallablePairedTemplates.Template
abbrev Capture := SourceCoreCallablePairedTemplates.Capture
abbrev Authenticated {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (world : StoreTyping) (store : Store) (value : Value) := SourceCoreCallablePairedTemplates.Authenticated cache world store value
abbrev Completion {checked : Checked} (prepared : Prepared checked) := SourceCoreCallablePairedPrograms.Completion prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev SourceEnvironment := SourceCoreAllocationLedger.SourceEnvironment
abbrev TypedLedger := SourceCoreAllocationLedger.TypedLedger
abbrev Row := SourceCoreAllocationLedger.Row

abbrev Subvalue (value : Value) := SourceCoreCallableNativeSlots.Subvalue value

structure Produced {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (completion : Completion prepared) (world : StoreTyping) (store : Store) (value : Value) where private mk ::
  authenticated : Authenticated cache world store value
  result : Value
  observation : completion.result.native.observation = .succeeded result store
  subvalue : Subvalue value result

def Produced.of_success {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value result : Value}
    (authenticated : Authenticated cache world store value)
    (observation : completion.result.native.observation = .succeeded result store)
    (subvalue : Subvalue value result) : Produced cache completion world store value :=
  ⟨authenticated, result, observation, subvalue⟩

/-- Composition can update older replacements; a literal list prefix would
incorrectly reject a completed flexible parent substitution. Domain order and
full composition, including every binding, are checked instead. -/
def ContextExtends (allocated selected : TypeSystem.Substitution) : Prop :=
  allocated.domain.IsPrefix selected.domain ∧ selected.compose allocated = selected
instance (allocated selected : TypeSystem.Substitution) : Decidable (ContextExtends allocated selected) :=
  inferInstanceAs (Decidable (_ ∧ _))

inductive Error where
  | unknownLocation (location : Nat)
  | binderMismatch (location : Nat) (expected actual : Resolved.LocalId)
  | payloadMismatch (location : Nat) (expected actual : Ty)
  | ownerMismatch (location : Nat)
  | contextMismatch (location : Nat)
  | unknownAllocatedContext (location : Nat)
  | allocatedBinderMismatch (location : Nat)
  | unknownExpectedBinder (id : Resolved.LocalId)
  | contextualBinderMismatch (location : Nat)
  deriving Repr

structure Slot {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) (capture : Capture template environment world) where private mk ::
  ordinal : Fin ledger.ledger.rows.length
  locationExact : (ledger.ledger.rows[ordinal]).coreLocation = capture.location
  binderExact : (ledger.ledger.rows[ordinal]).entry.key.binder.id = capture.binder
  payloadExact : (ledger.ledger.rows[ordinal]).entry.key.payloadType = capture.payloadType
  ownerExact : (ledger.ledger.rows[ordinal]).entry.key.owner = template.source.lambda.owner
  activeExtends : ContextExtends (ledger.ledger.rows[ordinal]).entry.key.active template.source.lambda.active
  allocated : SourceCoreAllocationContexts.Certified prepared.base.plan prepared.base.contexts
  allocatedMember : allocated ∈ prepared.contexts.rows
  allocatedOwner : allocated.context.owner = (ledger.ledger.rows[ordinal]).entry.key.owner
  allocatedActive : allocated.context.active = (ledger.ledger.rows[ordinal]).entry.key.active
  allocatedBinder : (ledger.ledger.rows[ordinal]).entry.key.binder ∈ allocated.context.binders
  expected : SourceCoreAllocationCodebook.IndexedBinding
  expectedFound : template.source.lambda.context.bindingAt? capture.binder = some expected
  expectedIdentity : expected.binding.binder.id = capture.binder
  contextualBinder : (ledger.ledger.rows[ordinal]).entry.key.binder.applySubstitution template.source.lambda.active = expected.binding.binder

def Slot.row {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} {capture : Capture template environment world}
    (slot : Slot ledger capture) : Row prepared.layouts store := ledger.ledger.rows[slot.ordinal]

def Slot.sourceLocation {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} {capture : Capture template environment world}
    (slot : Slot ledger capture) : SourceTypedRuntime.Location := slot.row.sourceLocation

theorem Slot.prefixOffset {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} {capture : Capture template environment world}
    (slot : Slot ledger capture) : slot.sourceLocation.index = initial.length + slot.ordinal.val :=
  ledger.ledger.sourceLocation_exact slot.ordinal

theorem Slot.nativeReference {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} {capture : Capture template environment world}
    (slot : Slot ledger capture) :
    SourceCoreAllocationLedger.Reference ledger.ledger.locations capture.payloadType
      (.cellRef (OptionalCell.cellType capture.payloadType) capture.location) slot.sourceLocation := by
  rw [← slot.locationExact]
  apply SourceCoreAllocationLedger.Reference.intro (entry := slot.row.location)
  · exact List.mem_map_of_mem (by exact List.getElem_mem slot.ordinal.isLt)
  · exact slot.payloadExact

/-- The full contextual source binder comes from the actual cached allocation
inventory, rather than from a native reference's Core type. -/
theorem Slot.binderOrigin {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} {capture : Capture template environment world}
    (slot : Slot ledger capture) :
    SourceCoreAllocationContexts.BinderOrigin slot.allocated.context.source slot.row.entry.key.binder :=
  slot.allocated.binder_origin slot.allocatedBinder

private theorem ledger_core_injective {checked : Checked} {prepared : Prepared checked}
    {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) :
    Function.Injective (fun ordinal : Fin ledger.ledger.rows.length => (ledger.ledger.rows[ordinal]).coreLocation) := by
  have ordered : ∀ left right : Fin ledger.ledger.rows.length, left.val < right.val →
      (ledger.ledger.rows[left]).coreLocation < (ledger.ledger.rows[right]).coreLocation := by
    intro left right before
    have member : ledger.ledger.rows[left] ∈ ledger.ledger.rows.take right.val := by
      rw [List.mem_take_iff_getElem]
      exact ⟨left.val, by omega, rfl⟩
    have previous := List.all_eq_true.mp (ledger.ledger.aligned right).2.2 _ member
    have previous := of_decide_eq_true previous
    simp only [SourceCoreAllocationLedger.Row.coreLocation] at previous ⊢
    exact Nat.lt_trans previous (Nat.lt_succ_self _)
  intro left right same
  change (ledger.ledger.rows[left]).coreLocation = (ledger.ledger.rows[right]).coreLocation at same
  apply Fin.ext
  rcases Nat.lt_trichotomy left.val right.val with before | sameIndex | after
  · have tooSmall := ordered left right before
    rw [same] at tooSmall
    exact False.elim (Nat.lt_irrefl _ tooSmall)
  · exact sameIndex
  · have tooSmall := ordered right left after
    rw [same] at tooSmall
    exact False.elim (Nat.lt_irrefl _ tooSmall)

/-- Aliasing is determined by physical location, even when binder IDs recur. -/
theorem Slot.alias {checked : Checked} {prepared : Prepared checked}
    {leftTemplate rightTemplate : Template} {leftEnvironment rightEnvironment : Environment}
    {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store}
    {left : Capture leftTemplate leftEnvironment world} {right : Capture rightTemplate rightEnvironment world}
    (leftSlot : Slot ledger left) (rightSlot : Slot ledger right)
    (same : left.location = right.location) : leftSlot.sourceLocation = rightSlot.sourceLocation := by
  have ordinals : leftSlot.ordinal = rightSlot.ordinal :=
    ledger_core_injective ledger (leftSlot.locationExact.trans (same.trans rightSlot.locationExact.symm))
  exact congrArg (fun (ordinal : Fin ledger.ledger.rows.length) =>
    (ledger.ledger.rows[ordinal]).sourceLocation) ordinals

/-- Distinct native source cells remain distinct after prefix reindexing. -/
theorem Slot.alias_iff {checked : Checked} {prepared : Prepared checked}
    {leftTemplate rightTemplate : Template} {leftEnvironment rightEnvironment : Environment}
    {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store}
    {left : Capture leftTemplate leftEnvironment world} {right : Capture rightTemplate rightEnvironment world}
    (leftSlot : Slot ledger left) (rightSlot : Slot ledger right) :
    leftSlot.sourceLocation = rightSlot.sourceLocation ↔ left.location = right.location := by
  constructor
  · intro same
    have ordinals : leftSlot.ordinal = rightSlot.ordinal := ledger.ledger.sourceLocation_injective same
    exact leftSlot.locationExact.symm.trans
      ((congrArg (fun (ordinal : Fin ledger.ledger.rows.length) =>
        (ledger.ledger.rows[ordinal]).coreLocation) ordinals).trans rightSlot.locationExact)
  · exact leftSlot.alias rightSlot


private def joinSlot {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) (capture : Capture template environment world) :
    Except Error (Slot ledger capture) := do
  let ordinal ← match (List.finRange ledger.ledger.rows.length).find? (fun ordinal =>
      decide ((ledger.ledger.rows[ordinal]).coreLocation = capture.location)) with
    | none => throw (.unknownLocation capture.location)
    | some ordinal => pure ordinal
  let row := ledger.ledger.rows[ordinal]
  if locationExact : row.coreLocation = capture.location then
    if binderExact : row.entry.key.binder.id = capture.binder then
      if payloadExact : row.entry.key.payloadType = capture.payloadType then
        if ownerExact : row.entry.key.owner = template.source.lambda.owner then
          if activeExtends : ContextExtends row.entry.key.active template.source.lambda.active then
            let allocated ← match prepared.contexts.rows.attach.find? (fun context => decide
                (context.val.context.owner = row.entry.key.owner ∧ context.val.context.active = row.entry.key.active)) with
              | none => throw (.unknownAllocatedContext capture.location)
              | some context => pure context
            if allocatedExact : allocated.val.context.owner = row.entry.key.owner ∧ allocated.val.context.active = row.entry.key.active then
              if allocatedBinder : row.entry.key.binder ∈ allocated.val.context.binders then
                match expectedFound : template.source.lambda.context.bindingAt? capture.binder with
                | none => throw (.unknownExpectedBinder capture.binder)
                | some expected =>
                  if expectedIdentity : expected.binding.binder.id = capture.binder then
                    if contextualBinder : row.entry.key.binder.applySubstitution template.source.lambda.active = expected.binding.binder then
                      pure ⟨ordinal, locationExact, binderExact, payloadExact, ownerExact, activeExtends,
                        allocated.val, allocated.property, allocatedExact.1, allocatedExact.2, allocatedBinder,
                        expected, expectedFound, expectedIdentity, contextualBinder⟩
                    else throw (.contextualBinderMismatch capture.location)
                  else throw (.unknownExpectedBinder capture.binder)
              else throw (.allocatedBinderMismatch capture.location)
            else throw (.unknownAllocatedContext capture.location)
          else throw (.contextMismatch capture.location)
        else throw (.ownerMismatch capture.location)
      else throw (.payloadMismatch capture.location capture.payloadType row.entry.key.payloadType)
    else throw (.binderMismatch capture.location capture.binder row.entry.key.binder.id)
  else throw (.unknownLocation capture.location)

inductive CaptureSourceEnv {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) :
    List (Capture template environment world) → SourceEnvironment → Prop where
  | nil : CaptureSourceEnv ledger [] []
  | cons {capture : Capture template environment world} {tail : List (Capture template environment world)}
      {sourceTail : SourceEnvironment} (slot : Slot ledger capture)
      (following : CaptureSourceEnv ledger tail sourceTail) :
      CaptureSourceEnv ledger (capture :: tail) ((capture.binder, slot.sourceLocation) :: sourceTail)

namespace CaptureSourceEnv
variable {checked : Checked} {prepared : Prepared checked} {template : Template}
  {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
  {ledger : TypedLedger prepared.layouts initial world store}
  {captures : List (Capture template environment world)} {source : SourceEnvironment}

theorem length (related : CaptureSourceEnv ledger captures source) : source.length = captures.length := by
  induction related with
  | nil => rfl
  | cons slot following ih => simp only [List.length_cons, ih]

theorem binders (related : CaptureSourceEnv ledger captures source) :
    source.map Prod.fst = captures.map (·.binder) := by
  induction related with
  | nil => rfl
  | cons slot following ih => simp only [List.map_cons, ih]

theorem lookup (related : CaptureSourceEnv ledger captures source) {index : Nat} {binder : Resolved.LocalId}
    {location : SourceTypedRuntime.Location} (found : source[index]? = some (binder, location)) :
    ∃ capture, captures[index]? = some capture ∧ capture.binder = binder ∧
      ∃ slot : Slot ledger capture, slot.sourceLocation = location := by
  induction related generalizing index with
  | nil => simp at found
  | cons slot following ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
      exact ⟨_, rfl, found.1, slot, found.2⟩
    | succ index =>
      obtain ⟨capture, captured, binderExact, slot, located⟩ := ih (by simpa using found)
      exact ⟨capture, by simpa using captured, binderExact, slot, located⟩

end CaptureSourceEnv

private structure EnvironmentReceipt {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) (captures : List (Capture template environment world)) where
  source : SourceEnvironment
  related : CaptureSourceEnv ledger captures source

private def joinEnvironment {checked : Checked} {prepared : Prepared checked} {template : Template}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) :
    (captures : List (Capture template environment world)) → Except Error (EnvironmentReceipt ledger captures)
  | [] => .ok ⟨[], .nil⟩
  | capture :: tail => do
    let slot ← joinSlot ledger capture
    let following ← joinEnvironment ledger tail
    pure ⟨(capture.binder, slot.sourceLocation) :: following.source, .cons slot following.related⟩

/-- A metadata/location relation alone. Execution provenance is supplied by
`Produced` or `Stored`, and is deliberately not inferred from this receipt. -/
structure Captured {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  environment : SourceEnvironment
  related : CaptureSourceEnv ledger authenticated.sourceCaptures environment

def joinAuthenticated {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) : Except Error (Captured authenticated ledger) := do
  let receipt ← joinEnvironment ledger authenticated.sourceCaptures
  pure ⟨receipt.source, receipt.related⟩

abbrev Receipt {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value : Value}
    (produced : Produced cache completion world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) := Captured produced.authenticated ledger

def join {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value : Value}
    (produced : Produced cache completion world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) : Except Error (Receipt produced ledger) :=
  joinAuthenticated produced.authenticated ledger

/-- Heap payload provenance also covers failed and suspended invocations.
Only source ledger payloads are traversed, never an arbitrary closure's saved
Core environment or a compiler-only administrative cell. -/
structure Stored {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (completion : Completion prepared) {world : StoreTyping} {store : Store} (value : Value)
    {initial : SourceHeap} (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  authenticated : Authenticated cache world store value
  observation : SourceCoreCallablePairedLedger.store completion = store
  ordinal : Fin ledger.ledger.rows.length
  payload : Value
  payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload
  subvalue : Subvalue value payload

def Stored.of_payload {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value payload : Value}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (authenticated : Authenticated cache world store value)
    (observation : SourceCoreCallablePairedLedger.store completion = store)
    (ordinal : Fin ledger.ledger.rows.length)
    (payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload)
    (subvalue : Subvalue value payload) : Stored cache completion value ledger :=
  ⟨authenticated, observation, ordinal, payload, payloadFound, subvalue⟩

def joinStored {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value : Value}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (stored : Stored cache completion value ledger) : Except Error (Captured stored.authenticated ledger) :=
  joinAuthenticated stored.authenticated ledger

namespace Captured
variable {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
  {world : StoreTyping} {store : Store} {value : Value}
  {authenticated : Authenticated cache world store value} {initial : SourceHeap}
  {ledger : TypedLedger prepared.layouts initial world store}

theorem length (receipt : Captured authenticated ledger) :
    receipt.environment.length = authenticated.template.source.scope.length :=
  receipt.related.length.trans authenticated.capturesComplete

theorem binders (receipt : Captured authenticated ledger) :
    receipt.environment.map Prod.fst = authenticated.template.source.scope.map Prod.fst := by
  have lengths := congrArg List.length authenticated.capturesExact
  simp only [List.length_map, List.length_zip, authenticated.capturesComplete] at lengths
  have enough : authenticated.template.source.scope.length ≤ authenticated.template.references.length := by omega
  have exact := congrArg (List.map (fun entry : Nat × (Resolved.LocalId × Ty) => entry.2.1))
    authenticated.capturesExact
  have captureOrder : authenticated.sourceCaptures.map (·.binder) =
      authenticated.template.source.scope.map Prod.fst := by
    have zipped : (authenticated.template.references.zip authenticated.template.source.scope).map
        (fun entry => entry.2.1) = authenticated.template.source.scope.map Prod.fst := by
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) (List.map_snd_zip enough)
    simpa only [List.map_map, Function.comp_def] using exact.trans zipped
  exact receipt.related.binders.trans captureOrder

theorem lookup (receipt : Captured authenticated ledger) {index : Nat} {binder : Resolved.LocalId}
    {location : SourceTypedRuntime.Location} (found : receipt.environment[index]? = some (binder, location)) :
    ∃ capture, authenticated.sourceCaptures[index]? = some capture ∧ capture.binder = binder ∧
      ∃ slot : Slot ledger capture, slot.sourceLocation = location := receipt.related.lookup found

theorem outsidePrefix (receipt : Captured authenticated ledger) {index : Nat} {binder : Resolved.LocalId}
    {location : SourceTypedRuntime.Location} (found : receipt.environment[index]? = some (binder, location)) :
    initial.length ≤ location.index := by
  obtain ⟨_, _, _, slot, same⟩ := receipt.lookup found
  rw [← same, slot.prefixOffset]
  omega

end Captured
end Solcore.Frontend.SourceCoreCallablePairedCaptures
