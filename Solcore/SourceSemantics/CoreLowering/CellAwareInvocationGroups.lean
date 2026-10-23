import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareStagedGroupBounds

/-! Group evaluation runs its actual child in the same invocation. The child
keeps every stored attachment and returns the same exact heap effect. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGroups
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedGroupBounds (Group)
open CellAwareStagedGroupBounds (source_group_inv child_typed)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- The Source group rule adds one genuine step above its executed child.
The child theorem carries either fault tag and the exact reached state. -/
theorem group_preserves
    (unique : NodeOccurrencesUnique invocation.source) (budget : Nat)
    (childMeaning : CellAwareInvocationExpressionBounds.PreservesBelow
      (attachment := attachment) bridge context model index registry invocation children faults budget) :
    ∀ size, size ≤ budget → CellAwareInvocationExpressionBounds.PreservesAt
      (attachment := attachment) bridge context model index registry invocation (Group compiled.compatible.checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  cases certified with
  | actual metadata form innerFound sourceType child =>
      have same := Option.some.inj (found.symm.trans metadata.found)
      cases same
      obtain ⟨childSize, sizeEq, childTrace⟩ := source_group_inv unique metadata.found form trace
      have smaller : childSize < budget := by
        rw [sizeEq] at within
        exact Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
        childMeaning childSize smaller child innerFound
          (child_typed metadata form innerFound unique typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childTrace
      refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, ?_⟩
      · simpa only [sourceType] using represented
      · simpa only [sourceType] using post

/-- The native group is literally the child code. Its structural child IH
uses the SAME grade; this theorem requests no strict native inequality. -/
theorem group_reflects
    (unique : NodeOccurrencesUnique invocation.source) (size : Nat)
    (childMeaning : CellAwareInvocationExpressionBounds.ReflectsAt
      (attachment := attachment) bridge context model index registry invocation children faults size) :
    CellAwareInvocationExpressionBounds.ReflectsAt
      (attachment := attachment) bridge context model index registry invocation (Group compiled.compatible.checked invocation.source children) faults size := by
  intro scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame completed
  cases certified with
  | actual metadata form innerFound sourceType child =>
      have same := Option.some.inj (found.symm.trans metadata.found)
      cases same
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
        childMeaning child innerFound (child_typed metadata form innerFound unique typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame completed
      have occurrence : Staging.Recursive.Occurrence invocation id (.group _) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome, after, finalMap, finalWorld,
        .group occurrence trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata, effect,
        reached, related, ?_⟩
      · simpa only [sourceType] using represented
      · simpa only [sourceType] using post

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGroups
