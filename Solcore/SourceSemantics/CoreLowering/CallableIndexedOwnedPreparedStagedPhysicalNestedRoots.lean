import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNestedCanonicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds

/-! Physical recursive expression results restore the same original named
packet using their actual returned frame. The pool and all reached records
remain the witnesses returned by that expression. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNestedRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPhysicalNestedCanonicalState
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep} {size : Nat}
local notation "canonicalBridge" =>
  CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) 1)
local notation "nestedBridge" => bridge (headers := headers) owner caller

theorem preserves_at (meaning : PreservesAt canonicalBridge context model stages invocation certificate faults size) :
    PreservesAt nestedBridge context model stages invocation certificate faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome afterHeap environments heaps locals agrees nativeTyped initial admitted trace
  have originalAdmission : CallableIndexedOwnedSourceAdmission.Admission canonicalBridge context
      (CallableIndexedOwnedPhysicalNestedCanonicalState.canonical owner caller initial) := ⟨admitted.heap, admitted.rows⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds,
      frame, metadata, reached, related, post⟩ :=
    meaning certified found typed environments heaps locals agrees nativeTyped
      (CallableIndexedOwnedPhysicalNestedCanonicalState.canonical owner caller initial) originalAdmission trace
  let returned := after owner caller initial reached frame
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps,
    maps, worlds, frame, metadata, returned, related, ?_⟩
  cases outcome with
  | value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

theorem reflects_at (meaning : ReflectsAt canonicalBridge context model stages invocation certificate faults size) :
    ReflectsAt nestedBridge context model stages invocation certificate faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  have originalAdmission : CallableIndexedOwnedSourceAdmission.Admission canonicalBridge context
      (CallableIndexedOwnedPhysicalNestedCanonicalState.canonical owner caller initial) := ⟨admitted.heap, admitted.rows⟩
  obtain ⟨sourceSize, outcome, afterHeap, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds,
      frame, metadata, reached, related, post⟩ :=
    meaning certified found typed environments heaps locals agrees nativeTyped
      (CallableIndexedOwnedPhysicalNestedCanonicalState.canonical owner caller initial) originalAdmission completed
  let returned := after owner caller initial reached frame
  refine ⟨sourceSize, outcome, afterHeap, finalMap, finalWorld, trace, result, finalHeaps,
    maps, worlds, frame, metadata, returned, related, ?_⟩
  cases outcome with
  | value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic => exact ⟨post.rows, post.successful⟩
    | stage => exact post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNestedRoots
