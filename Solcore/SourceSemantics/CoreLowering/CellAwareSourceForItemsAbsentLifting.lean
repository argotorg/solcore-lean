import Solcore.SourceSemantics.CoreLowering.CellAwareScopeExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedAbsentPrefix
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsSourceInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping

/-! An original uninitialized declaration lifts through its actual absent
cell allocation. The independently executed suffix starts at that exact heap,
with every earlier generalized descriptor still retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsAbsentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForLiftBounds (ItemsLifts)
open TypedLexicalControl (absentRequest)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}


include registered in
theorem absent {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {binder : TypedBinder} {rest : List ForItemForm}
    {payload : Ty} {body : Expr} {administrative : Core.Context}
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders (source named))
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends (source named).owner context binder nextContext)
    (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : projects binder.scheme.body payload)
    (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
      (absentRequest (source named) scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
      whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
      (absentRequest (source named) scope binder payload))
    (same : annotation.original = allocation.expression)
    (sourceEq : invocation.source = source named)
    (remaining : ItemsLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := nextContext) (scope := ((binder.id, payload) :: scope)) bridge producer rest) :
    ItemsLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer (.letDecl binder none :: rest) := by
  intro size environment canonical actual actualContext embedding before after reachedReady finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    current, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  obtain ⟨tailSize, location, bound, _smaller, allocated, tail⟩ :=
    SelectedCompilationStageForItemsSourceInversion.absent mono
      (by simpa only [sourceEq] using extended) trace
  obtain ⟨marker, _agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      _preserved, _allocationEffect, nextAuthority, reachedState, _related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
    CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
      projection environments heaps locals agrees actualTyped current admitted authority physical
      (ready current physical.read) allocated body
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, tailAdapted⟩ :=
    remaining ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      runtime.transport (.ofBinderExtends extended),
      (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers,
      (Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger,
      reachedState, nextAdmitted, nextAuthority, nextPhysical, owner, sameLocation.trans locationEq.symm, nextReady⟩ tail
  exact ⟨resultContext, resultOutcome, resultHeap,
    .absent mono (by simpa only [sourceEq] using extended) allocated stagedTail, tailAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForItemsAbsentLifting
