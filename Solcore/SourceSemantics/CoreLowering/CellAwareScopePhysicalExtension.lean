import Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical

/-! Real monomorphic parameters initialize the named physical scope. Each
subsequent lexical declaration extends only the original binder context and
retains the same selected frame and caller key. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalLocatedRows GeneralizedLocalBundleContexts CallableIndexedHistory

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function} {context nextContext : SourceSemantics.Context}

theorem Entry.recontext {frameLocation id location mapping world heap store binder}
    {sourceOwner : Resolved.DeclarationId}
    (entry : Entry compiled named context frameLocation id location mapping world heap store)
    (extended : BinderExtends sourceOwner context binder nextContext)
    (different : binder.id ≠ id) :
    Entry compiled named nextContext frameLocation id location mapping world heap store := by
  cases entry with
  | ordinary read descriptor => exact .ordinary read descriptor
  | generalized located owner binderId lexical frames fields requirements =>
    refine .generalized located owner binderId lexical frames
      (fields.trans (.ofBinderExtends extended)) ?_
    cases extended
    exact .tail (by simpa only [located.attachment.binder, binderId] using different) requirements

private theorem monomorphic_entries {frameLocation mapping world heap store environment scope}
    (agrees : Dynamic.EnvironmentAgrees heap scope environment)
    (typed : Dynamic.HeapWellTyped context heap)
    (monomorphic : ∀ id scheme, (id, scheme) ∈ scope → scheme.quantified = []) :
    ∀ {id location}, Dynamic.Environment.LooksUp environment id location →
      Entry compiled named context frameLocation id location mapping world heap store := by
  induction agrees with
  | nil => intro id location lookup; cases lookup
  | @cons scope environment headId scheme headLocation cell read _ storage tail ih =>
    intro id location lookup
    cases lookup with
    | head =>
      cases storage with
      | ordinary _ empty => exact .ordinary read empty
      | generalized descriptor _ binderScheme =>
        have principal := ((typed cell read.member).generalized_inv descriptor).2.code.polymorphic
        exact False.elim (principal (binderScheme ▸ monomorphic headId scheme (by simp)))
    | tail _ next =>
      exact ih (fun child childScheme member => monomorphic child childScheme (List.mem_cons_of_mem _ member)) next

def Physical.of_monomorphic {scope canonical mapping world heap store environment}
    (native : NativeFrame) (id : Word)
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some id)
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      native (.named id) (some (CallableIndexedNamedGeneration.state named)))
    (declarations : CompatibleExpressionReads.ScopeDeclarations (CallableIndexedNamedGeneration.source named) scope context)
    (ownership : LocalIdentityOwnership (CallableIndexedNamedGeneration.source named))
    (sourceDeclarations : CellAwareScopeDeclarations.Full (CallableIndexedNamedGeneration.source named) scope context)
    (location : Core.Location)
    (reference : canonical[scope.length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : location ∉ mapping)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (typed : Dynamic.HeapWellTyped context heap)
    (monomorphic : ∀ id scheme, (id, scheme) ∈ context.locals → scheme.quantified = []) :
    Physical compiled named context scope canonical mapping world heap store environment :=
  ⟨native, id, selected, carried, declarations, ownership, sourceDeclarations, location, reference, read, unmapped,
    monomorphic_entries locals typed monomorphic⟩

def Physical.cons {scope canonical mapping world heap store environment binder payload sourceLocation}
    (physical : Physical compiled named context scope canonical mapping world heap store environment)
    (extended : BinderExtends (CallableIndexedNamedGeneration.source named).owner context binder nextContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (CallableIndexedNamedGeneration.source named)
      ((binder.id, payload) :: scope) nextContext)
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders (CallableIndexedNamedGeneration.source named))
    (reference : Core.Value)
    (head : Entry compiled named nextContext physical.location binder.id sourceLocation mapping world heap store) :
    Physical compiled named nextContext ((binder.id, payload) :: scope) (reference :: canonical)
      mapping world heap store ((binder.id, sourceLocation) :: environment) := by
  refine ⟨physical.native, physical.id, physical.selected, physical.carried, declarations, physical.ownership,
    CellAwareScopeDeclarations.scope_bind payload member physical.sourceDeclarations extended, physical.location, ?_, physical.read, physical.unmapped, ?_⟩
  · change (reference :: canonical)[scope.length + 1 + 1 + compiled.indexed.base.globals.length]? = _
    rw [show scope.length + 1 + 1 + compiled.indexed.base.globals.length =
      (scope.length + 1 + compiled.indexed.base.globals.length) + 1 by omega]
    exact physical.reference
  · intro id location lookup
    cases lookup with
    | head => exact head
    | tail different previous => exact (physical.entries previous).recontext extended different

end Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical
