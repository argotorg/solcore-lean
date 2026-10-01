import Solcore.Frontend.SourceCoreCallableAncestryCache
import Solcore.Frontend.SourceCoreCallableAncestryLedger

/-! Principal closure headers are prepared for every supplied graph state.
Preparation validates the owned principal inventory and exact lambda form.
Runtime restoration selects a cached header by state index and the complete
allocation key, and retains the ledger's ordered source locations.

This module does not certify the graph's reachable-state closure or runtime
history. Its caller must supply the owning graph preparation receipt and the
actual allocation-frame lookup. No source body is evaluated or traversed while
restoring a value. A Unit native instance bundle still has a source principal.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders
open SourceInference TypeSystem
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallableAncestryPrograms.Prepared
abbrev Table := SourceCoreCallableAncestryCache.Table
abbrev Principal {checked : Checked} (program : Program checked) :=
  SourceCoreCallablePrincipals.Entry program.base.sourceProgram program.base.plan program.base.contexts
abbrev AllocationKey := SourceCoreAllocationLayouts.Key
abbrev SourceValue := SourceTypedRuntime.Value

def eraseRequirements (source : TypedSource) : TypedSource :=
  {source with nodes := source.nodes.map fun
    | .expression node => .expression {node with requirements := []}
    | .statement node => .statement node}

inductive Error where
  | sourceMismatch (index : Nat) (binder : Resolved.LocalId)
  | missingLambda (index : Nat) (initializer : ExpressionId)
  | lambdaMismatch (index : Nat) (initializer : ExpressionId)
  | missingHeader (index : Nat) (binder : Resolved.LocalId)
  | allocationMismatch (index : Nat) (binder : Resolved.LocalId)
  | absentPrincipal (binder : Resolved.LocalId)
  | snapshot (error : SourceCoreAncestryAllocationFrames.Error)
  | frameUnavailable (binder : Resolved.LocalId)
  deriving Repr

structure Header {checked : Checked} (program : Program checked) (table : Table) where private mk ::
  position : Fin table.states.length
  principal : Principal program
  owned : principal ∈ program.ancestry.principals.entries
  owner : (table.states[position]).owner = principal.context.owner
  active : (table.states[position]).active = principal.context.active
  sourceExact : eraseRequirements (table.states[position]).source = eraseRequirements principal.context.source
  node : ExpressionNode
  found : (table.states[position]).source.lookupExpression? principal.principal.declaration.initializer = some node
  form : node.form = .lambda principal.principal.parameters principal.principal.resultType principal.principal.body

def Header.state {checked : Checked} {program : Program checked} {table : Table}
    (header : Header program table) : SourceCoreCallableAncestryCache.State := table.states[header.position]

def Header.matches {checked : Checked} {program : Program checked} {table : Table}
    (header : Header program table) (key : AllocationKey) : Prop := header.principal.matchesLayout key
instance {checked : Checked} {program : Program checked} {table : Table}
    (header : Header program table) (key : AllocationKey) : Decidable (header.matches key) :=
  inferInstanceAs (Decidable (header.principal.matchesLayout key))

private def prepareHeader {checked : Checked} (program : Program checked) (table : Table)
    (position : Fin table.states.length) (principal : Principal program)
    (owned : principal ∈ program.ancestry.principals.entries)
    (owner : (table.states[position]).owner = principal.context.owner)
    (active : (table.states[position]).active = principal.context.active) : Except Error (Header program table) := do
  if sourceExact : eraseRequirements (table.states[position]).source = eraseRequirements principal.context.source then
    match found : (table.states[position]).source.lookupExpression? principal.principal.declaration.initializer with
    | none => throw (.missingLambda position.val principal.principal.declaration.initializer)
    | some node =>
      if form : node.form = .lambda principal.principal.parameters principal.principal.resultType principal.principal.body then
        pure ⟨position, principal, owned, owner, active, sourceExact, node, found, form⟩
      else throw (.lambdaMismatch position.val principal.principal.declaration.initializer)
  else throw (.sourceMismatch position.val principal.principal.binder.id)

private def headersAt {checked : Checked} (program : Program checked) (table : Table)
    (position : Fin table.states.length) : Except Error (List (Header program table)) := do
  let candidates ← program.ancestry.principals.entries.attach.mapM fun principal => do
    if owner : (table.states[position]).owner = principal.val.context.owner then
      if active : (table.states[position]).active = principal.val.context.active then
        let header ← prepareHeader program table position principal.val principal.property owner active
        pure [header]
      else pure []
    else pure []
  pure candidates.flatten

structure Prepared {checked : Checked} (program : Program checked) (table : Table) where private mk ::
  headers : List (Header program table)
  private collected : ∃ groups, (List.finRange table.states.length).mapM (headersAt program table) = .ok groups ∧
    headers = groups.flatten

def prepare {checked : Checked} (program : Program checked) (table : Table) : Except Error (Prepared program table) :=
  match collected : (List.finRange table.states.length).mapM (headersAt program table) with
  | .error error => .error error
  | .ok groups => .ok ⟨groups.flatten, ⟨groups, collected, rfl⟩⟩

def Prepared.headerAt? {checked : Checked} {program : Program checked} {table : Table}
    (prepared : Prepared program table) (position : Nat) (binder : Resolved.LocalId) : Option (Header program table) :=
  prepared.headers.find? fun header => decide (header.position.val = position ∧ header.principal.principal.binder.id = binder)

structure Restored {checked : Checked} {program : Program checked} {table : Table}
    (prepared : Prepared program table) (position : Nat) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  header : Header program table
  selected : prepared.headerAt? position row.entry.key.binder.id = some header
  layoutMatches : header.matches row.entry.key
  value : SourceValue
  exact : value = .closure header.principal.principal.parameters header.principal.principal.resultType
    header.principal.principal.body header.state.source header.state.owner row.environment header.principal.context.evidence

/-- The state index must come from the separately owned graph lookup of the
actual allocation snapshot. This operation only selects prepared metadata. -/
def restoreAt {checked : Checked} {program : Program checked} {table : Table}
    (prepared : Prepared program table) (position : Nat) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) : Except Error (Restored prepared position row) := do
  match selected : prepared.headerAt? position row.entry.key.binder.id with
  | none => throw (.missingHeader position row.entry.key.binder.id)
  | some header =>
    if layoutMatches : header.matches row.entry.key then
      pure ⟨header, selected, layoutMatches,
        .closure header.principal.principal.parameters header.principal.principal.resultType header.principal.principal.body
          header.state.source header.state.owner row.environment header.principal.context.evidence, rfl⟩
    else throw (.allocationMismatch position row.entry.key.binder.id)

theorem Restored.position_exact {checked : Checked} {program : Program checked} {table : Table}
    {prepared : Prepared program table} {position : Nat} {store : Core.Store}
    {row : SourceCoreAllocationLedger.Row program.layouts store} (restored : Restored prepared position row) :
    restored.header.position.val = position := by
  have selected := restored.selected
  simp only [Prepared.headerAt?] at selected
  have tested := List.find?_some selected
  exact (of_decide_eq_true tested).1

theorem Restored.binder_exact {checked : Checked} {program : Program checked} {table : Table}
    {prepared : Prepared program table} {position : Nat} {store : Core.Store}
    {row : SourceCoreAllocationLedger.Row program.layouts store} (restored : Restored prepared position row) :
    row.entry.key.binder = restored.header.principal.principal.binder := restored.layoutMatches.2.2

theorem Restored.binder_origin {checked : Checked} {program : Program checked} {table : Table}
    {prepared : Prepared program table} {position : Nat} {store : Core.Store}
    {row : SourceCoreAllocationLedger.Row program.layouts store} (restored : Restored prepared position row) :
    SourceCoreAllocationContexts.BinderOrigin restored.header.principal.context.compilerSource row.entry.key.binder :=
  restored.header.principal.layout_binder_origin restored.layoutMatches

theorem Restored.capture_order {checked : Checked} {program : Program checked} {table : Table}
    {prepared : Prepared program table} {position : Nat} {store : Core.Store}
    {row : SourceCoreAllocationLedger.Row program.layouts store} (_restored : Restored prepared position row) :
    row.environment.map Prod.fst = row.entry.key.scope.map Prod.fst := row.captured.binders_exact

structure AllocationRestored {checked : Checked} {program : Program checked} {table : Table}
    (prepared : Prepared program table) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  payload : Core.Value
  present : row.payload = some payload
  snapshot : SourceCoreAncestryAllocationFrames.Snapshot program.ancestry.layout.frame row
  position : Nat
  selected : table.lookupIndex? snapshot.frame = some (some position)
  restored : Restored prepared position row

/-- The actual recorded frame determines the selected metadata state. An
absent optional payload is retained as absent by the heap decoder, so this
principal constructor requires an initialized allocation. -/
def restoreAllocation {checked : Checked} {program : Program checked} {table : Table}
    (prepared : Prepared program table) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) : Except Error (AllocationRestored prepared row) := do
  match present : row.payload with
  | none => throw (.absentPrincipal row.entry.key.binder.id)
  | some payload =>
    let snapshot ← (SourceCoreAncestryAllocationFrames.snapshot program.ancestry.layout.frame row).mapError Error.snapshot
    match selected : table.lookupIndex? snapshot.frame with
    | some (some position) =>
      let restored ← restoreAt prepared position row
      pure ⟨payload, present, snapshot, position, selected, restored⟩
    | _ => throw (.frameUnavailable row.entry.key.binder.id)

end Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders
