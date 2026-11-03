import Solcore.SourceSemantics.CoreLowering.CaptureCopyIndexedTyping
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates
import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotCode

/-! Native typing of a generalized declaration's snapshot code. Inverting the
copies types the bundle initializer in the original scope, and the descriptor
allocation fixes the type of the cell the continuation binds. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotTyping
open Core Frontend SourceInference
open CellAwareGeneralizedSnapshotCode (snapshotInner snapshotSequence)

/-- A scope slot holds a cell of its payload type in the scope's own context. -/
theorem scope_cell {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {index : Nat} {id : Resolved.LocalId} {payload : Ty} (found : scope[index]? = some (id, payload)) :
    (SourceCoreLocalCell.coreContext scope ++ administrative)[index]? = some (.cell (OptionalCell.cellType payload)) := by
  rw [List.getElem?_append_left (by simpa [SourceCoreLocalCell.coreContext] using (List.getElem?_eq_some_iff.mp found).1)]
  simp [SourceCoreLocalCell.coreContext, found]

/-- A typed snapshot declaration types its bundle initializer in the original
context and its continuation below the descriptor cell. -/
theorem snapshot_children {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) request)
    (same : annotation.original = allocation.expression)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {payload type result : Ty}
    {initializer captured body : Expr} {definitions : DataEnvironment} {context : Core.Context}
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      source scope (fun index => index) (snapshotInner payload initializer annotation.expression) = .ok captured)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (cellPayload : Ty), scope[index]? = some (id, cellPayload) →
      context[index]? = some (.cell (OptionalCell.cellType cellPayload)))
    (typed : HasType context (snapshotSequence type captured body) result definitions) :
    (∃ initializerType, HasType context initializer initializerType definitions) ∧
      HasType (OptionalCell.referenceType request.payloadType :: context) body result definitions := by
  unfold snapshotSequence LanguageResult.bind at typed
  cases typed with
  | caseE capturedTyped _ next =>
    have inner := CaptureCopyTyping.copyScopeIndexed_body_hasType copied slots capturedTyped
    unfold snapshotInner LanguageResult.bind LanguageResult.success at inner
    cases inner with
    | caseE initializerTyped _ allocated =>
      cases allocated with
      | inRight _ allocationTyped =>
        have resultType := TypedLexicalWhile.Native.annotated_result allocation annotation same allocationTyped
        subst resultType
        exact ⟨⟨_, initializerTyped⟩, next⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotTyping
