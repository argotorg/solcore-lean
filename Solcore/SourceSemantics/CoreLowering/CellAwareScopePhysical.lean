import Solcore.SourceSemantics.CoreLowering.CellAwareScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceFrames
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.SourceSemantics.CoreLowering.GeneralHeapFrame
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning

/-! Physical evidence for one actual named body. Stored generalized entries
retain their original descriptor typing and the exact shared frame reference.
This package is supplied by real parameter entry and declaration allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalLocatedRows GeneralizedLocalBundleContexts CallableIndexedHistory

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function} {context : SourceSemantics.Context}

inductive Entry (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (context : SourceSemantics.Context)
    (frameLocation : Core.Location) (id : Resolved.LocalId) (location : Dynamic.Location)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) : Prop where
  | ordinary {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads heap location cell)
      (descriptor : cell.generalized = none) :
      Entry compiled named context frameLocation id location mapping world heap store
  | generalized {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
      {lexical : Substitution}
      (located : Located (GeneralizedLocalInstanceValues.model compiled.indexed)
        function binding lexical location mapping world heap store)
      (owner : binding.caller = named.signature.key) (binder : binding.binder.id = id)
      (lexicalContext : ContextExtension lexical [])
      (frames : located.Frames frameLocation)
      (fields : Dynamic.RuntimeContextFields function.definitionContext context)
      (requirements : context.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements) :
      Entry compiled named context frameLocation id location mapping world heap store

theorem Entry.transport {frameLocation id location mapping world heap store nextMap nextWorld after finalStore}
    (entry : Entry compiled named context frameLocation id location mapping world heap store)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world heap store nextMap nextWorld after finalStore) :
    Entry compiled named context frameLocation id location nextMap nextWorld after finalStore := by
  cases entry with
  | ordinary read descriptor =>
    obtain ⟨cell, updated, _, same⟩ := effect.metadata _ _ read
    exact .ordinary updated (same.trans descriptor)
  | generalized located owner binder lexical frames fields requirements =>
    obtain ⟨next, same⟩ := effect.retains_values located
    exact .generalized next owner binder lexical
      (frames.transport effect.maps effect.worlds same) fields requirements

theorem Entry.authority {frameLocation id location mapping world heap store}
    (entry : Entry compiled named context frameLocation id location mapping world heap store) :
    CellAwareScopeAuthority.Entry (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] id location mapping world heap store := by
  cases entry with
  | ordinary read descriptor => exact .ordinary read descriptor
  | generalized located owner binder lexical _ _ _ => exact .generalized owner binder lexical ⟨located⟩

structure Physical (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (canonical : Core.Environment)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (environment : Dynamic.Environment) where
  native : NativeFrame
  id : Word
  selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some id
  carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    native (.named id) (some (CallableIndexedNamedGeneration.state named))
  declarations : CompatibleExpressionReads.ScopeDeclarations
    (CallableIndexedNamedGeneration.source named) scope context
  ownership : LocalIdentityOwnership (CallableIndexedNamedGeneration.source named)
  sourceDeclarations : CellAwareScopeDeclarations.Full (CallableIndexedNamedGeneration.source named) scope context
  location : Core.Location
  reference : canonical[scope.length + 1 + compiled.indexed.base.globals.length]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type location)
  read : store.read? location =
    some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native)
  unmapped : location ∉ mapping
  entries : ∀ {id sourceLocation}, Dynamic.Environment.LooksUp environment id sourceLocation →
    Entry compiled named context location id sourceLocation mapping world heap store


abbrev Physical.ghost {scope canonical mapping world heap store environment}
    (physical : Physical compiled named context scope canonical mapping world heap store environment) : GhostFrame :=
  .named physical.id

def Physical.transport {scope canonical mapping world heap store environment nextMap nextWorld after finalStore}
    (physical : Physical compiled named context scope canonical mapping world heap store environment)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world heap store nextMap nextWorld after finalStore)
    (preserved : AdministrativePreserved mapping store nextMap finalStore) :
    Physical compiled named context scope canonical nextMap nextWorld after finalStore environment :=
  { native := physical.native
    id := physical.id
    selected := physical.selected
    carried := physical.carried
    declarations := physical.declarations
    ownership := physical.ownership
    sourceDeclarations := physical.sourceDeclarations
    location := physical.location
    reference := physical.reference
    read := ((preserved physical.location physical.unmapped
      (List.getElem?_eq_some_iff.mp physical.read).1).2).trans physical.read
    unmapped := (preserved physical.location physical.unmapped
      (List.getElem?_eq_some_iff.mp physical.read).1).1
    entries := fun lookup => (physical.entries lookup).transport effect }

@[simp] theorem Physical.transport_location {scope canonical mapping world heap store environment nextMap nextWorld after finalStore}
    (physical : Physical compiled named context scope canonical mapping world heap store environment)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world heap store nextMap nextWorld after finalStore)
    (preserved : AdministrativePreserved mapping store nextMap finalStore) :
    (physical.transport effect preserved).location = physical.location := rfl

@[simp] theorem Physical.transport_native {scope canonical mapping world heap store environment nextMap nextWorld after finalStore}
    (physical : Physical compiled named context scope canonical mapping world heap store environment)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world heap store nextMap nextWorld after finalStore)
    (preserved : AdministrativePreserved mapping store nextMap finalStore) :
    (physical.transport effect preserved).native = physical.native := rfl

theorem Physical.generalized {scope canonical mapping world heap store environment id location cell function}
    (physical : Physical compiled named context scope canonical mapping world heap store environment)
    (lookup : Dynamic.Environment.LooksUp environment id location)
    (read : Dynamic.Heap.Reads heap location cell) (descriptor : cell.generalized = some function) :
    ∃ binding lexical, ∃ located : Located (GeneralizedLocalInstanceValues.model compiled.indexed)
        function binding lexical location mapping world heap store,
      binding.caller = named.signature.key ∧ binding.binder.id = id ∧ ContextExtension lexical [] ∧
      located.Frames physical.location ∧ Dynamic.RuntimeContextFields function.definitionContext context ∧
      context.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements := by
  cases physical.entries lookup with
  | ordinary previous empty =>
    have same := read.functional previous
    rw [same, empty] at descriptor
    cases descriptor
  | generalized located owner binder lexical frames fields requirements =>
    have same := read.functional located.sourceRead
    have functionEq := Option.some.inj
      (descriptor.symm.trans ((congrArg Dynamic.Cell.generalized same).trans located.descriptor))
    cases functionEq
    exact ⟨_, _, located, owner, binder, lexical, frames, fields, requirements⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical
