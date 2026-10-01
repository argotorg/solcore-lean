import Solcore.Frontend.SourceCoreCallablePairedHeaders

/-! Raw source declarations cached for the finite prepared metadata graph.
Compiler and source substitution contexts remain distinct. Each raw binder
is joined to its actual compiler inventory by stable identity before execution.
Snapshot decoding and execution history are supplied by runner adapters. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableNativeCellHeaders
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Inventory {checked : Checked} (base : Base checked) := SourceCoreAllocationContexts.Inventory base.plan base.contexts
abbrev Context {checked : Checked} (base : Base checked) := SourceCoreAllocationContexts.Certified base.plan base.contexts
abbrev Binding := SourceCoreAllocationContexts.BinderReceipt

inductive Error where
  | metadata (error : SourceCoreAllocationContexts.Error)
  | missingContext (position : Nat)
  | missingBinder (position : Nat) (binder : Resolved.LocalId)
  deriving Repr

structure Header {checked : Checked} {base : Base checked} (graph : Graph base) (inventory : Inventory base) where private mk ::
  position : Fin graph.table.states.length
  context : Context base
  owned : context ∈ inventory.rows
  selected : context.context.owner = (graph.table.states[position]).metadata.owner ∧
    context.context.active = (graph.table.states[position]).nativeActive
  bindings : List (Binding (graph.table.states[position]).metadata.source)
  collected : SourceCoreAllocationContexts.binders (graph.table.states[position]).metadata.source = .ok bindings
  nativeBinder : TypedBinder
  nativeOwned : nativeBinder ∈ context.context.binders
  raw : Binding (graph.table.states[position]).metadata.source
  rawOwned : raw ∈ bindings
  identity : raw.binder.id = nativeBinder.id

private def headerForBinding {checked : Checked} {base : Base checked} (graph : Graph base) (inventory : Inventory base)
    (position : Fin graph.table.states.length) (context : Context base) (owned : context ∈ inventory.rows)
    (selected : context.context.owner = (graph.table.states[position]).metadata.owner ∧
      context.context.active = (graph.table.states[position]).nativeActive)
    (bindings : List (Binding (graph.table.states[position]).metadata.source))
    (collected : SourceCoreAllocationContexts.binders (graph.table.states[position]).metadata.source = .ok bindings)
    (native : TypedBinder) (nativeOwned : native ∈ context.context.binders) :
    Except Error (Header graph inventory) := by
  cases rawFound : bindings.find? (fun (raw : Binding (graph.table.states[position]).metadata.source) => decide (raw.binder.id = native.id)) with
  | none => exact .error (.missingBinder position.val native.id)
  | some raw =>
    have identity : raw.binder.id = native.id := of_decide_eq_true (List.find?_some (p := fun (candidate : Binding (graph.table.states[position]).metadata.source) => decide (candidate.binder.id = native.id)) rawFound)
    exact .ok ⟨position, context, owned, selected, bindings, collected, native, nativeOwned, raw,
      List.mem_of_find?_eq_some rawFound, identity⟩

private def headersAt {checked : Checked} {base : Base checked} (graph : Graph base) (inventory : Inventory base)
    (position : Fin graph.table.states.length) : Except Error (List (Header graph inventory)) := by
  cases found : inventory.rows.attach.find? (fun (context : {context : Context base // context ∈ inventory.rows}) => decide
      (context.val.context.owner = (graph.table.states[position]).metadata.owner ∧
        context.val.context.active = (graph.table.states[position]).nativeActive)) with
  | none => exact .error (.missingContext position.val)
  | some context =>
    have selected : context.val.context.owner = (graph.table.states[position]).metadata.owner ∧
        context.val.context.active = (graph.table.states[position]).nativeActive :=
      of_decide_eq_true (List.find?_some (p := fun (candidate : {candidate : Context base // candidate ∈ inventory.rows}) => decide
        (candidate.val.context.owner = (graph.table.states[position]).metadata.owner ∧
          candidate.val.context.active = (graph.table.states[position]).nativeActive)) found)
    cases collected : SourceCoreAllocationContexts.binders (graph.table.states[position]).metadata.source with
    | error error => exact .error (Error.metadata error)
    | ok bindings =>
      exact context.val.context.binders.attach.mapM fun (native : {native : TypedBinder // native ∈ context.val.context.binders}) =>
        headerForBinding graph inventory position context.val context.property selected bindings collected native.val native.property

structure Prepared {checked : Checked} {base : Base checked} (graph : Graph base) (inventory : Inventory base) where private mk ::
  headers : List (Header graph inventory)
  groups : List (List (Header graph inventory))
  collected : (List.finRange graph.table.states.length).mapM (headersAt graph inventory) = .ok groups
  flattened : headers = groups.flatten

def prepare {checked : Checked} {base : Base checked} (graph : Graph base) (inventory : Inventory base) : Except Error (Prepared graph inventory) :=
  match collected : (List.finRange graph.table.states.length).mapM (headersAt graph inventory) with
  | .error error => .error error
  | .ok groups => .ok ⟨groups.flatten, groups, collected, rfl⟩

def Prepared.at? {checked : Checked} {base : Base checked} {graph : Graph base} {inventory : Inventory base}
    (prepared : Prepared graph inventory) (position : Nat) (key : SourceCoreAllocationLayouts.Key) : Option (Header graph inventory) :=
  prepared.headers.find? fun header => decide (header.position.val = position ∧
    header.context.context.owner = key.owner ∧ header.context.context.active = key.active ∧ header.nativeBinder = key.binder)

theorem Prepared.binder_identity {checked : Checked} {base : Base checked}
    {graph : Graph base} {inventory : Inventory base} (prepared : Prepared graph inventory)
    {position : Nat} {key : SourceCoreAllocationLayouts.Key} {header : Header graph inventory}
    (selected : prepared.at? position key = some header) : header.raw.binder.id = key.binder.id := by
  have tested := List.find?_some selected
  have native : header.nativeBinder = key.binder := (of_decide_eq_true tested).2.2.2
  exact header.identity.trans (congrArg TypedBinder.id native)

end Solcore.Frontend.SourceCoreCallableNativeCellHeaders
