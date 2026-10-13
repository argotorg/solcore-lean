import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadBounds

/-! Ordinary reads preserve their actual Source cell and lazy mapping writes.
Only the selected occurrence and its input heap are used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionReads

theorem read_preserved
    {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel values source scope id reason code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {value : Dynamic.Value} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    (read : Dynamic.Heap.Reads before location cell)
    (ordinary : cell.generalized = none)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heap : Dynamic.HeapWellTyped context before)
    (typing : ExpressionHasType source context id type)
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    Dynamic.ExpressionEvaluationPreserved context before after value type := by
  have same_node : ∀ {node}, ContainsExpression source id node → node = certificate.node := by
    intro node contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans certificate.metadata.found)
  have same_cell : ∀ {otherLocation otherCell},
      Dynamic.Environment.LooksUp environment certificate.binder otherLocation →
      Dynamic.Heap.Reads before otherLocation otherCell → otherCell = cell := by
    intro otherLocation otherCell otherLookup otherRead
    cases otherLookup.functional lookup
    exact otherRead.functional read
  cases typing with
  | @intro _ _ node rawType plan contains formTyped rawEq rawWF typeWF requirements =>
    cases same_node contains
    have path := requirements.outputPath
    rw [certificate.metadata.coercions] at path
    cases path
    cases trace with
    | intro otherContains raw coercions =>
      cases same_node otherContains
      rw [certificate.metadata.coercions] at coercions
      cases coercions
      rw [certificate.form] at raw formTyped
      obtain ⟨typed, afterTyped, extension⟩ := raw.referencePreserves locals heap formTyped
      exact ⟨typed, afterTyped, extension⟩
    | generalizedLocal otherContains form _ otherLookup otherRead descriptor _ _ _ =>
      cases same_node otherContains
      rw [certificate.form] at form
      cases form
      cases same_cell otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadAdmission
