import Solcore.Frontend.SourceCoreCallableNativeSnapshotScanner
import Solcore.Frontend.SourceCoreCallableNativeSlots
import Solcore.Frontend.SourceCoreAllocationContexts
import Solcore.Frontend.SourceCoreAllocationLedger

/-! Profile-independent typed reference collection and source ledger joins.
Physical Core locations select rows before exact binder/type/owner/native
context checks. This library proves order, alias and opaque-prefix laws; it
does not authenticate native closure code or infer execution provenance.
Owned profile caches and Produced/Stored receipts supply those boundaries. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableNativeCaptureJoin
open SourceInference Core
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Layouts := SourceCoreAllocationLayouts.Prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev SourceEnvironment := SourceCoreAllocationLedger.SourceEnvironment
abbrev TypedLedger := SourceCoreAllocationLedger.TypedLedger
abbrev Row := SourceCoreAllocationLedger.Row

structure Spec where
  source : SourceCoreLambdaTemplates.Receipt
  references : List Nat
  referenceExact : references = source.references.map (· + 1)

def ofTemplate {profile : SourceCoreCallableNativeSnapshotScanner.Profile}
    (template : SourceCoreCallableNativeSnapshotScanner.Template profile) : Spec :=
  ⟨template.source, template.references, template.referenceExact⟩

structure Capture (spec : Spec) (environment : Core.Environment) (world : StoreTyping) where private mk ::
  binder : Resolved.LocalId
  payloadType : Ty
  environmentIndex : Nat
  location : Nat
  sourceReference : (environmentIndex, (binder, payloadType)) ∈ spec.references.zip spec.source.scope
  sourceSlot : (binder, payloadType) ∈ spec.source.scope
  referenceSlot : environmentIndex ∈ spec.references
  exact : environment[environmentIndex]? = some (.cellRef (OptionalCell.cellType payloadType) location)
  worldExact : world[location]? = some (OptionalCell.cellType payloadType)

inductive CollectionError where
  | native (error : SourceCoreCallableNativeSlots.Error)
  | countMismatch
  | orderMismatch
  deriving Repr

structure Collected (spec : Spec) (environment : Environment) (world : StoreTyping) where private mk ::
  captures : List (Capture spec environment world)
  exact : captures.map (fun capture => (capture.environmentIndex, (capture.binder, capture.payloadType))) =
    spec.references.zip spec.source.scope
  complete : captures.length = spec.source.scope.length

def collect (spec : Spec) (environment : Environment) (world : StoreTyping) :
    Except CollectionError (Collected spec environment world) := do
  let captures ← (spec.references.zip spec.source.scope).attach.mapM fun ⟨(index, (binder, type)), member⟩ => do
    let native ← (SourceCoreCallableNativeSlots.reference environment world index type).mapError CollectionError.native
    pure (Capture.mk binder type index native.location member (List.of_mem_zip member).2
      (List.of_mem_zip member).1 native.exact native.worldExact)
  if order : captures.map (fun capture => (capture.environmentIndex, (capture.binder, capture.payloadType))) =
      spec.references.zip spec.source.scope then
    if complete : captures.length = spec.source.scope.length then
      pure ⟨captures, order, complete⟩
    else throw .countMismatch
  else throw .orderMismatch

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

structure Slot {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger layouts initial world store) (capture : Capture spec environment world) where private mk ::
  ordinal : Fin ledger.ledger.rows.length
  locationExact : (ledger.ledger.rows[ordinal]).coreLocation = capture.location
  binderExact : (ledger.ledger.rows[ordinal]).entry.key.binder.id = capture.binder
  payloadExact : (ledger.ledger.rows[ordinal]).entry.key.payloadType = capture.payloadType
  ownerExact : (ledger.ledger.rows[ordinal]).entry.key.owner = spec.source.lambda.owner
  activeExtends : ContextExtends (ledger.ledger.rows[ordinal]).entry.key.active spec.source.lambda.active
  allocated : SourceCoreAllocationContexts.Certified plan parents
  allocatedMember : allocated ∈ contexts.rows
  allocatedOwner : allocated.context.owner = (ledger.ledger.rows[ordinal]).entry.key.owner
  allocatedActive : allocated.context.active = (ledger.ledger.rows[ordinal]).entry.key.active
  allocatedBinder : (ledger.ledger.rows[ordinal]).entry.key.binder ∈ allocated.context.binders
  expected : SourceCoreAllocationCodebook.IndexedBinding
  expectedFound : spec.source.lambda.context.bindingAt? capture.binder = some expected
  expectedIdentity : expected.binding.binder.id = capture.binder
  contextualBinder : (ledger.ledger.rows[ordinal]).entry.key.binder.applySubstitution spec.source.lambda.active = expected.binding.binder

def Slot.row {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store} {capture : Capture spec environment world}
    (slot : Slot (contexts := contexts) ledger capture) : Row layouts store := ledger.ledger.rows[slot.ordinal]

def Slot.sourceLocation {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store} {capture : Capture spec environment world}
    (slot : Slot (contexts := contexts) ledger capture) : SourceTypedRuntime.Location := slot.row.sourceLocation

theorem Slot.prefixOffset {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store} {capture : Capture spec environment world}
    (slot : Slot (contexts := contexts) ledger capture) : slot.sourceLocation.index = initial.length + slot.ordinal.val :=
  ledger.ledger.sourceLocation_exact slot.ordinal

theorem Slot.nativeReference {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store} {capture : Capture spec environment world}
    (slot : Slot (contexts := contexts) ledger capture) :
    SourceCoreAllocationLedger.Reference ledger.ledger.locations capture.payloadType
      (.cellRef (OptionalCell.cellType capture.payloadType) capture.location) slot.sourceLocation := by
  rw [← slot.locationExact]
  apply SourceCoreAllocationLedger.Reference.intro (entry := slot.row.location)
  · exact List.mem_map_of_mem (by exact List.getElem_mem slot.ordinal.isLt)
  · exact slot.payloadExact

/-- The full contextual source binder comes from the actual cached allocation
inventory, rather than from a native reference's Core type. -/
theorem Slot.binderOrigin {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store} {capture : Capture spec environment world}
    (slot : Slot (contexts := contexts) ledger capture) :
    SourceCoreAllocationContexts.BinderOrigin slot.allocated.context.source slot.row.entry.key.binder :=
  slot.allocated.binder_origin slot.allocatedBinder

theorem ledger_core_injective {layouts : Layouts}
    {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger layouts initial world store) :
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
theorem Slot.alias {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents}
    {leftTemplate rightTemplate : Spec} {leftEnvironment rightEnvironment : Environment}
    {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store}
    {left : Capture leftTemplate leftEnvironment world} {right : Capture rightTemplate rightEnvironment world}
    (leftSlot : Slot (contexts := contexts) ledger left) (rightSlot : Slot (contexts := contexts) ledger right)
    (same : left.location = right.location) : leftSlot.sourceLocation = rightSlot.sourceLocation := by
  have ordinals : leftSlot.ordinal = rightSlot.ordinal :=
    ledger_core_injective ledger (leftSlot.locationExact.trans (same.trans rightSlot.locationExact.symm))
  exact congrArg (fun (ordinal : Fin ledger.ledger.rows.length) =>
    (ledger.ledger.rows[ordinal]).sourceLocation) ordinals

/-- Distinct native source cells remain distinct after prefix reindexing. -/
theorem Slot.alias_iff {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents}
    {leftTemplate rightTemplate : Spec} {leftEnvironment rightEnvironment : Environment}
    {world : StoreTyping} {store : Store} {initial : SourceHeap}
    {ledger : TypedLedger layouts initial world store}
    {left : Capture leftTemplate leftEnvironment world} {right : Capture rightTemplate rightEnvironment world}
    (leftSlot : Slot (contexts := contexts) ledger left) (rightSlot : Slot (contexts := contexts) ledger right) :
    leftSlot.sourceLocation = rightSlot.sourceLocation ↔ left.location = right.location := by
  constructor
  · intro same
    have ordinals : leftSlot.ordinal = rightSlot.ordinal := ledger.ledger.sourceLocation_injective same
    exact leftSlot.locationExact.symm.trans
      ((congrArg (fun (ordinal : Fin ledger.ledger.rows.length) =>
        (ledger.ledger.rows[ordinal]).coreLocation) ordinals).trans rightSlot.locationExact)
  · exact leftSlot.alias rightSlot


def joinSlot {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger layouts initial world store) (capture : Capture spec environment world) :
    Except Error (Slot (contexts := contexts) ledger capture) :=
  letI : BEq TypedBinder := instBEqOfDecidableEq
  do
    let ordinal ← match (List.finRange ledger.ledger.rows.length).find? (fun ordinal =>
        decide ((ledger.ledger.rows[ordinal]).coreLocation = capture.location)) with
      | none => throw (.unknownLocation capture.location)
      | some ordinal => pure ordinal
    let row := ledger.ledger.rows[ordinal]
    if locationExact : row.coreLocation = capture.location then
      if binderExact : row.entry.key.binder.id = capture.binder then
        if payloadExact : row.entry.key.payloadType = capture.payloadType then
          if ownerExact : row.entry.key.owner = spec.source.lambda.owner then
            if activeExtends : ContextExtends row.entry.key.active spec.source.lambda.active then
              let allocated : { certified : SourceCoreAllocationContexts.Certified plan parents // certified ∈ contexts.rows } ← match contexts.rows.attach.find? (fun context => decide
                  (context.val.context.owner = row.entry.key.owner ∧ context.val.context.active = row.entry.key.active)) with
                | none => throw (.unknownAllocatedContext capture.location)
                | some context => pure context
              if allocatedExact : allocated.val.context.owner = row.entry.key.owner ∧ allocated.val.context.active = row.entry.key.active then
                if allocatedBinder : (row.entry.key.binder : TypedBinder) ∈ (allocated.val.context.binders : List TypedBinder) then
                  match expectedFound : spec.source.lambda.context.bindingAt? capture.binder with
                  | none => throw (.unknownExpectedBinder capture.binder)
                  | some expected =>
                    if expectedIdentity : expected.binding.binder.id = capture.binder then
                      if contextualBinder : row.entry.key.binder.applySubstitution spec.source.lambda.active = expected.binding.binder then
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

inductive CaptureSourceEnv {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger layouts initial world store) :
    List (Capture spec environment world) → SourceEnvironment → Prop where
  | nil : CaptureSourceEnv (contexts := contexts) ledger [] []
  | cons {capture : Capture spec environment world} {tail : List (Capture spec environment world)}
      {sourceTail : SourceEnvironment} (slot : Slot (contexts := contexts) ledger capture)
      (following : CaptureSourceEnv (contexts := contexts) ledger tail sourceTail) :
      CaptureSourceEnv (contexts := contexts) ledger (capture :: tail) ((capture.binder, slot.sourceLocation) :: sourceTail)

namespace CaptureSourceEnv
variable {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
  {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
  {ledger : TypedLedger layouts initial world store}
  {captures : List (Capture spec environment world)} {source : SourceEnvironment}

theorem length (related : CaptureSourceEnv (contexts := contexts) ledger captures source) : source.length = captures.length := by
  induction related with
  | nil => rfl
  | cons slot following ih => simp only [List.length_cons, ih]

theorem binders (related : CaptureSourceEnv (contexts := contexts) ledger captures source) :
    source.map Prod.fst = captures.map (·.binder) := by
  induction related with
  | nil => rfl
  | cons slot following ih => simp only [List.map_cons, ih]

theorem lookup (related : CaptureSourceEnv (contexts := contexts) ledger captures source) {index : Nat} {binder : Resolved.LocalId}
    {location : SourceTypedRuntime.Location} (found : source[index]? = some (binder, location)) :
    ∃ capture, captures[index]? = some capture ∧ capture.binder = binder ∧
      ∃ slot : Slot (contexts := contexts) ledger capture, slot.sourceLocation = location := by
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

structure Joined {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger layouts initial world store) (captures : List (Capture spec environment world)) where
  source : SourceEnvironment
  related : CaptureSourceEnv (contexts := contexts) ledger captures source

def join {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} {layouts : Layouts}
    {contexts : SourceCoreAllocationContexts.Inventory plan parents} {spec : Spec}
    {environment : Environment} {world : StoreTyping} {store : Store} {initial : SourceHeap}
    (ledger : TypedLedger layouts initial world store) :
    (captures : List (Capture spec environment world)) → Except Error (Joined (contexts := contexts) ledger captures)
  | [] => .ok ⟨[], .nil⟩
  | capture :: tail => do
    let slot ← joinSlot (contexts := contexts) ledger capture
    let following ← join (contexts := contexts) ledger tail
    pure ⟨(capture.binder, slot.sourceLocation) :: following.source, .cons slot following.related⟩


end Solcore.Frontend.SourceCoreCallableNativeCaptureJoin
