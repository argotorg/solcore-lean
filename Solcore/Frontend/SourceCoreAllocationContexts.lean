import Solcore.Frontend.SourceCoreAllocationDiscovery
import Solcore.Frontend.SourceCoreStageCodebook
import Solcore.Frontend.SourceCoreDataPlaces
import Solcore.Frontend.SourceCoreRawMetadata

/-! Canonical allocation metadata from the actual executable plan and sealed
contextual evidence receipts. All declared binders, including principal generic
lambda metadata, are retained. No source type is projected into Core here.

Match scrutinee cells use exactly the metadata constructed by the compatible
match lowerer. Each retained binder has a declaration or hidden-scrutinee
receipt. Equal owner/full-context keys may share a row only when source views
and complete ordered binder metadata agree. Payload representations are later
obtained from actual allocator requests by AllocationDiscovery. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreAllocationContexts
open SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Context := SourceCoreAllocationDiscovery.Context

inductive Error where
  | contexts (error : SourceCoreStageCodebook.Error)
  | metadata (error : SourceCoreBasic.Error)
  | conflictingContext (owner : Key) (active : TypeSystem.Substitution)
  deriving Repr

def hiddenBinder (statement : StatementNode) (resolution : MatchResolution)
    (scrutinee : ExpressionNode) : TypedBinder := {
  id := resolution.hiddenScrutinee
  name := ""
  scheme := ⟨[], SourceCoreRawMetadata.runtimeType scrutinee.type⟩
  span := some statement.span
}

inductive BinderOrigin (source : TypedSource) : TypedBinder → Prop where
  | declared {binder : TypedBinder} (member : binder ∈ SourceCoreDataPlaces.declaredBinders source) :
      BinderOrigin source binder
  | hidden {statement : StatementNode} {resolution : MatchResolution} {scrutinee : ExpressionNode}
      (member : .statement statement ∈ source.nodes)
      (form : statement.form = .matchWith resolution)
      (found : source.lookupExpression? resolution.scrutinee = some scrutinee) :
      BinderOrigin source (hiddenBinder statement resolution scrutinee)

structure BinderReceipt (source : TypedSource) where
  binder : TypedBinder
  origin : BinderOrigin source binder

private def hiddenReceipts (source : TypedSource) : Except Error (List (BinderReceipt source)) := do
  let nested ← source.nodes.attach.mapM fun item => do
    match nodeEq : item.val with
    | .expression _ => pure []
    | .statement statement =>
      match form : statement.form with
      | .matchWith resolution =>
        if resolution.scrutinee.occurrence.owner ≠ source.owner then
          throw (.metadata (.ownerMismatch source.owner resolution.scrutinee.occurrence.owner))
        match found : source.lookupExpression? resolution.scrutinee with
        | none => throw (.metadata (.missingExpression resolution.scrutinee))
        | some scrutinee =>
          pure [⟨hiddenBinder statement resolution scrutinee,
            .hidden (by simpa [nodeEq] using item.property) form found⟩]
      | _ => pure []
  pure nested.flatten

def binders (source : TypedSource) : Except Error (List (BinderReceipt source)) := do
  let declared := (SourceCoreDataPlaces.declaredBinders source).attach.map fun item =>
    (⟨item.val, .declared item.property⟩ : BinderReceipt source)
  pure (declared ++ (← hiddenReceipts source))

/-- Provenance is membership in the actual supplied plan/receipt lists, not
an arbitrary Core type or an inferred source function identity. -/
inductive Origin (plan : Plan) (parents : List SourceCoreLocalEvidence.Prepared) where
  | root (specialized : SourceSpecialization.SpecializedFunction) (member : specialized ∈ plan.specializations)
  | contextual (prepared : SourceCoreLocalEvidence.Prepared) (member : prepared ∈ parents)

def Origin.owner {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} : Origin plan parents → Key
  | .root specialized _ => specialized.key
  | .contextual prepared _ => prepared.caller.key

def Origin.active {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} :
    Origin plan parents → TypeSystem.Substitution
  | .root _ _ => []
  | .contextual prepared _ => prepared.substitution

def Origin.source {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} : Origin plan parents → TypedSource
  | .root specialized _ => specialized.function.typedBody
  | .contextual prepared _ => prepared.source

structure Certified (plan : Plan) (parents : List SourceCoreLocalEvidence.Prepared) where
  origin : Origin plan parents
  context : Context
  ownerExact : context.owner = origin.owner
  activeExact : context.active = origin.active
  sourceExact : context.source = origin.source
  receipts : List (BinderReceipt context.source)
  collected : binders context.source = .ok receipts
  bindersExact : context.binders = receipts.map (·.binder)
  sourceOwner : context.source.owner = context.owner.declaration
  distinct : (context.binders.map (·.id)).Nodup
  binderOwners : ∀ binder ∈ context.binders, binder.id.owner = context.source.owner

def certify {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} (origin : Origin plan parents) :
    Except Error (Certified plan parents) := do
  let owner := origin.owner
  let source := origin.source
  if sourceOwner : source.owner = owner.declaration then
    match collected : binders source with
    | .error error => throw error
    | .ok receipts =>
      let declared := receipts.map (·.binder)
      if distinct : (declared.map (·.id)).Nodup then
        if owned : declared.all (fun binder => decide (binder.id.owner = source.owner)) = true then
          pure {
            origin
            context := ⟨owner, origin.active, source, declared⟩
            ownerExact := rfl, activeExact := rfl, sourceExact := rfl
            receipts, collected, bindersExact := rfl, sourceOwner, distinct
            binderOwners := fun binder member => of_decide_eq_true (List.all_eq_true.mp owned binder member)
          }
        else
          match declared.find? (fun binder => decide (binder.id.owner ≠ source.owner)) with
          | some binder => throw (.metadata (.ownerMismatch source.owner binder.id.owner))
          | none => throw (.metadata (.ownerMismatch source.owner owner.declaration))
      else
        match declared.find? (fun binder => (declared.filter (fun other => decide (binder.id = other.id))).length > 1) with
        | some binder => throw (.metadata (.duplicateBinding binder.id))
        | none => throw (.metadata (.ownerMismatch source.owner owner.declaration))
  else throw (.metadata (.ownerMismatch owner.declaration source.owner))

/-- Reuse permits the raw/evidence expression views already accepted by the
emitter, while retaining exact forms, statements and ordered binder metadata. -/
def sameContext (left right : Context) : Prop :=
  left.owner = right.owner ∧ left.active = right.active ∧
  SourceCoreAllocationCodebook.sourceView left.source = SourceCoreAllocationCodebook.sourceView right.source ∧
  left.binders = right.binders

instance (left right : Context) : Decidable (sameContext left right) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def insert {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (rows : List (Certified plan parents)) (candidate : Certified plan parents) : Except Error (List (Certified plan parents)) :=
  match rows.find? (fun row => decide (row.context.owner = candidate.context.owner ∧ row.context.active = candidate.context.active)) with
  | none => .ok (rows ++ [candidate])
  | some row =>
      if sameContext row.context candidate.context then .ok rows
      else .error (.conflictingContext candidate.context.owner candidate.context.active)

theorem insert_reuses {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    {rows : List (Certified plan parents)} {candidate existing : Certified plan parents}
    (found : rows.find? (fun row => decide
      (row.context.owner = candidate.context.owner ∧ row.context.active = candidate.context.active)) = some existing)
    (same : sameContext existing.context candidate.context) :
    insert rows candidate = .ok rows := by
  simp only [insert, found, if_pos same]

structure Inventory (plan : Plan) (parents : List SourceCoreLocalEvidence.Prepared) where
  rows : List (Certified plan parents)
  unique : (rows.map (fun row => (row.context.owner, row.context.active))).Nodup

def Inventory.contexts {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (inventory : Inventory plan parents) : List Context := inventory.rows.map (·.context)

def fromPrepared (plan : Plan) (parents : List SourceCoreLocalEvidence.Prepared) : Except Error (Inventory plan parents) := do
  let origins : List (Origin plan parents) :=
    (plan.specializations.attach.map (fun row => .root row.val row.property)) ++
    (parents.attach.map (fun row => .contextual row.val row.property))
  let candidates ← origins.mapM certify
  let rows ← candidates.foldlM insert []
  if unique : (rows.map (fun row => (row.context.owner, row.context.active))).Nodup then
    pure ⟨rows, unique⟩
  else
    match rows with
    | row :: _ => throw (.conflictingContext row.context.owner row.context.active)
    | [] => throw (.contexts .duplicateId)

structure Prepared (program : CheckedProgram) (plan : Plan) (candidates : List SourceCoreLocalPolymorphism.Instance) where
  parents : List SourceCoreLocalEvidence.Prepared
  authenticated : SourceCoreStageCodebook.prepareContexts program plan candidates = .ok parents
  inventory : Inventory plan parents

def prepare (program : CheckedProgram) (plan : Plan) (candidates : List SourceCoreLocalPolymorphism.Instance) :
    Except Error (Prepared program plan candidates) :=
  match authenticated : SourceCoreStageCodebook.prepareContexts program plan candidates with
  | .error error => .error (.contexts error)
  | .ok parents => (fromPrepared plan parents).map (fun inventory => ⟨parents, authenticated, inventory⟩)

theorem binders_declared {source : TypedSource} {receipts : List (BinderReceipt source)}
    (accepted : binders source = .ok receipts) {binder : TypedBinder}
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders source) :
    binder ∈ receipts.map (·.binder) := by
  cases hidden : hiddenReceipts source with
  | error error => simp [binders, hidden, Functor.map, Except.map] at accepted
  | ok extra =>
    simp [binders, hidden, Functor.map, Except.map] at accepted
    subst receipts
    simp only [List.map_append, List.mem_append]
    left
    simpa using member

/-- The inventory keeps every original declaration, even when its type is
open or the compiler later emits no allocation for that binder. -/
theorem Certified.declared_mem {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (row : Certified plan parents) {binder : TypedBinder}
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders row.context.source) :
    binder ∈ row.context.binders := by
  rw [row.bindersExact]
  exact binders_declared row.collected member

theorem Certified.binder_origin {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (row : Certified plan parents) {binder : TypedBinder} (member : binder ∈ row.context.binders) :
    BinderOrigin row.context.source binder := by
  rw [row.bindersExact] at member
  obtain ⟨receipt, _, equal⟩ := List.mem_map.mp member
  subst binder
  exact receipt.origin

theorem Certified.source_owned {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (row : Certified plan parents) : row.context.source.owner = row.origin.owner.declaration := by
  rw [← row.ownerExact]
  exact row.sourceOwner

theorem Inventory.contexts_unique {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (inventory : Inventory plan parents) :
    (inventory.contexts.map (fun context => (context.owner, context.active))).Nodup := by
  simpa only [Inventory.contexts, List.map_map, Function.comp_def] using inventory.unique

end Solcore.Frontend.SourceCoreAllocationContexts
