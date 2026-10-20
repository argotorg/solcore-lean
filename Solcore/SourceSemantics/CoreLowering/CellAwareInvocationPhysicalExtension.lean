import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical

/-! Real monomorphic parameters initialize the actual body physical scope. Each
subsequent lexical declaration extends only the original binder context and
retains the same selected frame and caller key. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalLocatedRows GeneralizedLocalBundleContexts CallableIndexedHistory

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {index : ActualBodyInvocation.Index compiled} {context nextContext : SourceSemantics.Context}

theorem Entry.recontext {frameLocation id location mapping world heap store binder}
    {sourceOwner : Resolved.DeclarationId}
    (entry : Entry compiled index context frameLocation id location mapping world heap store)
    (extended : BinderExtends sourceOwner context binder nextContext)
    (different : binder.id ≠ id) :
    Entry compiled index nextContext frameLocation id location mapping world heap store := by
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
      Entry compiled index context frameLocation id location mapping world heap store := by
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
    (frame : ActualBodyInvocation.Frame index)
    (declarations : CompatibleExpressionReads.ScopeDeclarations index.source scope context)
    (ownership : LocalIdentityOwnership index.source)
    (sourceDeclarations : CellAwareScopeDeclarations.Full index.source scope context)
    (location : Core.Location)
    (reference : canonical[scope.length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame frame.native))
    (unmapped : location ∉ mapping)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (typed : Dynamic.HeapWellTyped context heap)
    (monomorphic : ∀ id scheme, (id, scheme) ∈ context.locals → scheme.quantified = []) :
    Physical compiled index context scope canonical mapping world heap store environment :=
  ⟨frame, declarations, ownership, sourceDeclarations, location, reference, read, unmapped,
    monomorphic_entries locals typed monomorphic⟩

def Physical.cons {scope canonical mapping world heap store environment binder payload sourceLocation}
    (physical : Physical compiled index context scope canonical mapping world heap store environment)
    (extended : BinderExtends index.source.owner context binder nextContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations index.source
      ((binder.id, payload) :: scope) nextContext)
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
    (reference : Core.Value)
    (head : Entry compiled index nextContext physical.location binder.id sourceLocation mapping world heap store) :
    Physical compiled index nextContext ((binder.id, payload) :: scope) (reference :: canonical)
      mapping world heap store ((binder.id, sourceLocation) :: environment) := by
  refine ⟨physical.frame, declarations, physical.ownership,
    CellAwareScopeDeclarations.scope_bind payload member physical.sourceDeclarations extended, physical.location, ?_, physical.read, physical.unmapped, ?_⟩
  · change (reference :: canonical)[scope.length + 1 + 1 + compiled.indexed.base.globals.length]? = _
    rw [show scope.length + 1 + 1 + compiled.indexed.base.globals.length =
      (scope.length + 1 + compiled.indexed.base.globals.length) + 1 by omega]
    exact physical.reference
  · intro id location lookup
    cases lookup with
    | head => exact head
    | tail different previous => exact (physical.entries previous).recontext extended different

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
