import Solcore.Frontend.SourceCoreAllocationDiscovery

/-! Fixed allocation layouts for all entries of one compiled artifact. The
first discovery AST determines a finite set of metadata keys. A later allocator
reauthenticates each real request against that discovery's checked codebook,
then emits an existing nominal marker layout directly. Capture positions and
initializer expressions remain request-specific and are not part of the key.

Sharing a layout shares only its static definition: each evaluation still
allocates its own marker followed by its own optional payload cell. Historical
source compilation provenance belongs to the integrating factory; this module
retains the actual discovery scan receipt and accepts no undefined site key. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreAllocationLayouts
open SourceInference Core

structure Key where
  owner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  binder : TypedBinder
  scope : SourceCoreLocalCell.Scope
  payloadType : Core.Ty
  initialized : Bool
  deriving Repr, DecidableEq

def Key.ofReceipt (receipt : SourceCoreAllocationDiscovery.Receipt) : Key :=
  ⟨receipt.context.inventory.owner, receipt.context.inventory.active, receipt.binding.binding.binder,
    receipt.scope, receipt.payloadType, receipt.payload.isSome⟩

def Key.ofRequest (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (request : SourceCoreSourceCells.Request) : Key :=
  ⟨owner, active, request.binder, request.scope, request.payloadType, request.payload.isSome⟩

structure Origin where
  prepared : SourceCoreAllocationDiscovery.Prepared
  fuel : Nat
  expression : Expr
  discovered : SourceCoreAllocationDiscovery.Discovered prepared fuel expression
  deriving Repr

def Origin.codebook (origin : Origin) : SourceCoreAllocationCodebook.Prepared := origin.discovered.codebook
def Origin.keys (origin : Origin) : List Key := origin.discovered.sites.map (fun site => Key.ofReceipt site.receipt)

structure Entry (origin : Origin) where
  key : Key
  observed : key ∈ origin.keys
  ordinal : Nat
  deriving Repr

def Entry.layout {origin : Origin} (entry : Entry origin) : SourceCoreHeapMarkers.Layout :=
  ⟨⟨origin.codebook.ambient.length + entry.ordinal⟩, SourceCoreSourceCells.captureType entry.key.scope⟩

private def enumerate (origin : Origin) : List (Entry origin) :=
  origin.keys.eraseDups.attach.zipIdx.map fun (key, index) =>
    ⟨key.val, List.mem_eraseDups.mp key.property, index⟩

private abbrev indexed (origin : Origin) (entries : List (Entry origin)) : Prop :=
  entries.map (fun entry => entry.layout.dataType.index) =
    (List.range entries.length).map (origin.codebook.ambient.length + ·)

inductive Error where
  | authentication (error : SourceCoreAllocationCodebook.Error)
  | duplicateLayouts
  | invalidIndices
  | invalidDefinitions
  | unobservedLayout (key : Key)
  deriving Repr, DecidableEq

structure Prepared where private mk ::
  origin : Origin
  entries : List (Entry origin)
  enumerated : entries = enumerate origin
  unique : (entries.map (·.key)).Nodup
  indices : indexed origin entries
  definitionsTyped : (origin.codebook.ambient ++ entries.map (·.layout.definition)).WellFormed
  deriving Repr

def Prepared.codebook (prepared : Prepared) : SourceCoreAllocationCodebook.Prepared := prepared.origin.codebook

def Prepared.definitions (prepared : Prepared) : DataEnvironment :=
  prepared.codebook.ambient ++ prepared.entries.map (·.layout.definition)

def prepare {initial : SourceCoreAllocationDiscovery.Prepared} {fuel : Nat} {expression : Expr}
    (discovered : SourceCoreAllocationDiscovery.Discovered initial fuel expression) : Except Error Prepared := do
  let origin : Origin := ⟨initial, fuel, expression, discovered⟩
  let entries := enumerate origin
  if unique : (entries.map (·.key)).Nodup then
    if indices : indexed origin entries then
      if valid : (origin.codebook.ambient ++ entries.map (·.layout.definition)).isWellFormed = true then
        pure ⟨origin, entries, rfl, unique, indices, DataEnvironment.isWellFormed_sound valid⟩
      else throw .invalidDefinitions
    else throw .invalidIndices
  else throw .duplicateLayouts

/-- A static layout determines no capture positions or payload expression. -/
def allocation {origin : Origin} (entry : Entry origin) (request : SourceCoreSourceCells.Request) : Expr :=
  let captures := SourceCoreSourceCells.captures request.references request.scope
  match request.payload with
  | none => SourceCoreHeapMarkers.allocate entry.layout request.payloadType captures
  | some initializer => SourceCoreHeapMarkers.allocateInitialized entry.layout request.payloadType captures initializer

structure Allocation (prepared : Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (request : SourceCoreSourceCells.Request) where
  authentication : SourceCoreAllocationCodebook.Emission prepared.codebook owner active request
  entry : Entry prepared.origin
  member : entry ∈ prepared.entries
  keyExact : entry.key = Key.ofRequest owner active request
  expression : Expr
  expressionExact : expression = allocation entry request

def allocateWithReceipt (prepared : Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (request : SourceCoreSourceCells.Request) :
    Except Error (Allocation prepared owner active request) := do
  let authenticated ← (SourceCoreAllocationCodebook.emitWithReceipt prepared.codebook owner active request)
    |>.mapError Error.authentication
  match found : prepared.entries.find? (fun entry : Entry prepared.origin => decide (entry.key = Key.ofRequest owner active request)) with
  | none => throw (.unobservedLayout (Key.ofRequest owner active request))
  | some entry =>
    have keyExact : entry.key = Key.ofRequest owner active request := by
      have tested := List.find?_some found
      exact of_decide_eq_true tested
    pure ⟨authenticated, entry, List.mem_of_find?_eq_some found,
      keyExact, allocation entry request, rfl⟩

def allocate (prepared : Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (request : SourceCoreSourceCells.Request) : Except Error Expr :=
  (allocateWithReceipt prepared owner active request).map (·.expression)

def Prepared.allocatorAt (prepared : Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (onError : Error → SourceCoreBasic.Error) : SourceCoreSourceCells.Allocator :=
  fun request => (allocate prepared owner active request).mapError onError

theorem allocate_receipt {prepared : Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request} {expression : Expr}
    (accepted : allocate prepared owner active request = .ok expression) :
    ∃ receipt : Allocation prepared owner active request, receipt.expression = expression := by
  cases allocated : allocateWithReceipt prepared owner active request with
  | error error => simp [allocate, allocated, Except.map] at accepted
  | ok receipt =>
    simp only [allocate, allocated, Except.map, Except.ok.injEq] at accepted
    exact ⟨receipt, accepted⟩

/-- Every selected key occurs in the authenticated first scan. This is a
static discovery statement, not provenance of an arbitrary external AST. -/
theorem Allocation.observed {prepared : Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    (receipt : Allocation prepared owner active request) :
    ∃ site ∈ prepared.origin.discovered.sites, Key.ofReceipt site.receipt = Key.ofRequest owner active request := by
  have observed := receipt.entry.observed
  rw [receipt.keyExact] at observed
  exact List.mem_map.mp observed

@[simp] theorem Prepared.ambient_prefix (prepared : Prepared) :
    prepared.definitions.take prepared.codebook.ambient.length = prepared.codebook.ambient := by
  simp [Prepared.definitions]

theorem Prepared.entry_index (prepared : Prepared) {index : Nat} {entry : Entry prepared.origin}
    (found : prepared.entries[index]? = some entry) :
    entry.layout.dataType.index = prepared.codebook.ambient.length + index := by
  change entry.layout.dataType.index = prepared.origin.codebook.ambient.length + index
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  have atIndex := congrArg (fun indices : List Nat => indices[index]?) prepared.indices
  simpa only [List.getElem?_map, found, List.getElem?_range bound, Option.map_some, Option.some.injEq] using atIndex

theorem Prepared.entry_definition (prepared : Prepared) {index : Nat} {entry : Entry prepared.origin}
    (found : prepared.entries[index]? = some entry) :
    prepared.definitions[entry.layout.dataType.index]? = some entry.layout.definition := by
  rw [prepared.entry_index found]
  simp only [Prepared.definitions, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_map, found, Option.map_some]

theorem Prepared.entry_registered (prepared : Prepared) {index : Nat} {entry : Entry prepared.origin}
    (found : prepared.entries[index]? = some entry) : entry.layout.Registered prepared.definitions := by
  refine ⟨?_, prepared.entry_definition found⟩
  apply prepared.definitionsTyped.constructorPayloadType_wellFormed (constructor := entry.layout.constructor)
  change prepared.definitions.lookupConstructorPayloadType? entry.layout.constructor = some entry.layout.captureType
  simp only [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?,
    SourceCoreHeapMarkers.Layout.constructor]
  rw [prepared.entry_definition found]
  rfl

theorem Allocation.registered {prepared : Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    (receipt : Allocation prepared owner active request) : receipt.entry.layout.Registered prepared.definitions := by
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp receipt.member
  exact prepared.entry_registered found

theorem Allocation.hasType {prepared : Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    (receipt : Allocation prepared owner active request) {context : Core.Context}
    (payloadWellFormed : Ty.WellFormed prepared.definitions request.payloadType)
    (capturesTyped : HasType context (SourceCoreSourceCells.captures request.references request.scope)
      (SourceCoreSourceCells.captureType request.scope) prepared.definitions)
    (initializerTyped : ∀ expression, request.payload = some expression →
      HasType context expression request.payloadType prepared.definitions) :
    HasType context receipt.expression (OptionalCell.referenceType request.payloadType) prepared.definitions := by
  have captureType : receipt.entry.layout.captureType = SourceCoreSourceCells.captureType request.scope := by
    change SourceCoreSourceCells.captureType receipt.entry.key.scope = SourceCoreSourceCells.captureType request.scope
    rw [receipt.keyExact]
    rfl
  have capturesTyped : HasType context (SourceCoreSourceCells.captures request.references request.scope)
      receipt.entry.layout.captureType prepared.definitions := by
    rw [captureType]
    exact capturesTyped
  rw [receipt.expressionExact]
  cases payload : request.payload with
  | none =>
    simpa only [allocation, payload] using
      SourceCoreHeapMarkers.allocate_hasType receipt.registered capturesTyped payloadWellFormed
  | some initializer =>
    simpa only [allocation, payload] using SourceCoreHeapMarkers.allocateInitialized_hasType
      receipt.registered capturesTyped (initializerTyped initializer payload)

end Solcore.Frontend.SourceCoreAllocationLayouts
