import Solcore.Frontend.SourceCoreCallablePairedHeaders
import Solcore.Frontend.SourceCoreCallablePairedLedger
import Solcore.Frontend.SourceCoreCallablePairedAllocationFrames

/-! Raw source-cell declarations are cached separately from compiler binders.
A paired state can omit unrelated native substitution bindings. This cache
therefore collects actual source binders from each reached lexical source once,
then joins them to the owning compiler context by stable binder identity.

Runtime selection uses the allocation snapshot, state index, compiler owner,
complete native context and binder ID. It performs no source graph traversal.
Payload decoding and emitted-snapshot history remain separate obligations.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedCellHeaders
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallablePairedPrograms.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Context {checked : Checked} (program : Program checked) := SourceCoreAllocationContexts.Certified program.base.plan program.base.contexts
abbrev Binding := SourceCoreAllocationContexts.BinderReceipt

inductive Error where
  | metadata (error : SourceCoreAllocationContexts.Error)
  | missingContext (position : Nat)
  | missingBinder (position : Nat) (binder : Resolved.LocalId)
  | snapshot (error : SourceCoreCallablePairedAllocationFrames.Error)
  | frameUnavailable (binder : Resolved.LocalId)
  | headerUnavailable (position : Nat) (binder : Resolved.LocalId)
  deriving Repr

structure Header {checked : Checked} {program : Program checked} (graph : Graph program.base) where private mk ::
  position : Fin graph.table.states.length
  context : Context program
  owned : context ∈ program.contexts.rows
  selected : context.context.owner = (graph.table.states[position]).metadata.owner ∧
    context.context.active = (graph.table.states[position]).nativeActive
  bindings : List (Binding (graph.table.states[position]).metadata.source)
  collected : SourceCoreAllocationContexts.binders (graph.table.states[position]).metadata.source = .ok bindings
  nativeBinder : TypedBinder
  nativeOwned : nativeBinder ∈ context.context.binders
  raw : Binding (graph.table.states[position]).metadata.source
  rawOwned : raw ∈ bindings
  identity : raw.binder.id = nativeBinder.id

private def headerForBinding {checked : Checked} {program : Program checked} (graph : Graph program.base)
    (position : Fin graph.table.states.length) (context : Context program) (owned : context ∈ program.contexts.rows)
    (selected : context.context.owner = (graph.table.states[position]).metadata.owner ∧
      context.context.active = (graph.table.states[position]).nativeActive)
    (bindings : List (Binding (graph.table.states[position]).metadata.source))
    (collected : SourceCoreAllocationContexts.binders (graph.table.states[position]).metadata.source = .ok bindings)
    (native : TypedBinder) (nativeOwned : native ∈ context.context.binders) :
    Except Error (Header (program := program) graph) := by
  cases rawFound : bindings.find? (fun (raw : Binding (graph.table.states[position]).metadata.source) => decide (raw.binder.id = native.id)) with
  | none => exact .error (.missingBinder position.val native.id)
  | some raw =>
    have identity : raw.binder.id = native.id := of_decide_eq_true (List.find?_some (p := fun (candidate : Binding (graph.table.states[position]).metadata.source) => decide (candidate.binder.id = native.id)) rawFound)
    exact .ok ⟨position, context, owned, selected, bindings, collected, native, nativeOwned, raw,
      List.mem_of_find?_eq_some rawFound, identity⟩

private def headersAt {checked : Checked} {program : Program checked} (graph : Graph program.base)
    (position : Fin graph.table.states.length) : Except Error (List (Header (program := program) graph)) := by
  cases found : program.contexts.rows.attach.find? (fun (context : {context : Context program // context ∈ program.contexts.rows}) => decide
      (context.val.context.owner = (graph.table.states[position]).metadata.owner ∧
        context.val.context.active = (graph.table.states[position]).nativeActive)) with
  | none => exact .error (.missingContext position.val)
  | some context =>
    have selected : context.val.context.owner = (graph.table.states[position]).metadata.owner ∧
        context.val.context.active = (graph.table.states[position]).nativeActive :=
      of_decide_eq_true (List.find?_some (p := fun (candidate : {candidate : Context program // candidate ∈ program.contexts.rows}) => decide
        (candidate.val.context.owner = (graph.table.states[position]).metadata.owner ∧
          candidate.val.context.active = (graph.table.states[position]).nativeActive)) found)
    cases collected : SourceCoreAllocationContexts.binders (graph.table.states[position]).metadata.source with
    | error error => exact .error (Error.metadata error)
    | ok bindings =>
      exact context.val.context.binders.attach.mapM fun (native : {native : TypedBinder // native ∈ context.val.context.binders}) =>
        headerForBinding (program := program) graph position context.val context.property selected bindings collected native.val native.property

structure Prepared {checked : Checked} {program : Program checked} (graph : Graph program.base) where private mk ::
  headers : List (Header (program := program) graph)
  groups : List (List (Header (program := program) graph))
  collected : (List.finRange graph.table.states.length).mapM (headersAt (program := program) graph) = .ok groups
  flattened : headers = groups.flatten

def prepare {checked : Checked} {program : Program checked} (graph : Graph program.base) : Except Error (Prepared (program := program) graph) :=
  match collected : (List.finRange graph.table.states.length).mapM (headersAt (program := program) graph) with
  | .error error => .error error
  | .ok groups => .ok ⟨groups.flatten, groups, collected, rfl⟩

def Prepared.at? {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (prepared : Prepared (program := program) graph) (position : Nat) (key : SourceCoreAllocationLayouts.Key) : Option (Header (program := program) graph) :=
  prepared.headers.find? fun header => decide (header.position.val = position ∧
    header.context.context.owner = key.owner ∧ header.context.context.active = key.active ∧ header.nativeBinder = key.binder)

structure Selected {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (prepared : Prepared (program := program) graph) {store : Core.Store} (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  snapshot : SourceCoreCallablePairedAllocationFrames.Snapshot program.ancestry.layout.frame row
  position : Nat
  lookup : graph.table.lookupIndex? snapshot.frame = some (some position)
  header : Header (program := program) graph
  selected : prepared.at? position row.entry.key = some header

def select {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (prepared : Prepared (program := program) graph) {store : Core.Store} (row : SourceCoreAllocationLedger.Row program.layouts store) :
    Except Error (Selected prepared row) := do
  let snapshot ← (SourceCoreCallablePairedAllocationFrames.snapshot program.ancestry.layout.frame row).mapError Error.snapshot
  match lookup : graph.table.lookupIndex? snapshot.frame with
  | some (some position) =>
    match selected : prepared.at? position row.entry.key with
    | none => throw (.headerUnavailable position row.entry.key.binder.id)
    | some header => pure ⟨snapshot, position, lookup, header, selected⟩
  | _ => throw (.frameUnavailable row.entry.key.binder.id)

theorem Selected.binder_identity {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {prepared : Prepared (program := program) graph} {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (selected : Selected prepared row) : selected.header.raw.binder.id = row.entry.key.binder.id := by
  have tested := List.find?_some selected.selected
  have native : selected.header.nativeBinder = row.entry.key.binder := (of_decide_eq_true tested).2.2.2
  exact selected.header.identity.trans (congrArg TypedBinder.id native)

end Solcore.Frontend.SourceCoreCallablePairedCellHeaders
