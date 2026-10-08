import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralMeaning
import Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts

/-! The existing literal meanings exclude faults at their real certificates.
Finite projections retain their values and add the vacuous success post. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ReachedLiteralOutcomePorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ExpressionFailurePostContracts

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
  {solved : List SolvedRequirement} (program : Program) (context : SourceSemantics.Context)
  (evidence : Dynamic.EvidenceEnvironment) {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {post : ExpressionFaultPost}

theorem preserves_of_fault_free
    (meaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate (fun _ _ => False)) :
    Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults post := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ outcome after environments heaps locals agrees trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found environments heaps locals agrees trace
  cases represented with
  | value related =>
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .value related,
      finalHeaps, maps, worlds, frame, metadata, trivial⟩
  | fault impossible => exact False.elim impossible

theorem reflects_of_fault_free
    (meaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate (fun _ _ => False)) :
    Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults post := by
  intro scope id lowered generated node found mapping world administrative environment canonical actual
    before store ξ value finalStore environments heaps locals agrees evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found environments heaps locals agrees evaluated
  cases represented with
  | value related =>
    exact ⟨_, after, finalMap, finalWorld, trace, .value related,
      finalHeaps, maps, worlds, frame, metadata, trivial⟩
  | fault impossible => exact False.elim impossible

theorem preserves_with_evidence
    (receipts : ∀ scope id lowered, certificate scope id lowered →
      ∃ node, source.lookupExpression? id = some node ∧
        CompatibleExpressionLiterals.Literal solved node lowered.type lowered.expression ∧
        CompatibleExpressionLiterals.NumericEvidence context evidence node)
    (unique : NodeOccurrencesUnique source) :
    Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults post :=
  preserves_of_fault_free functions program context evidence
    (CompatibleExpressionLiterals.preserves_with_evidence functions program context evidence
      receipts unique (fun _ _ => False))

theorem reflects_with_evidence
    (receipts : ∀ scope id lowered, certificate scope id lowered →
      ∃ node, source.lookupExpression? id = some node ∧
        CompatibleExpressionLiterals.Literal solved node lowered.type lowered.expression ∧
        CompatibleExpressionLiterals.NumericEvidence context evidence node) :
    Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults post :=
  reflects_of_fault_free functions program context evidence
    (CompatibleExpressionLiterals.reflects_with_evidence functions program context evidence source
      receipts (fun _ _ => False))

theorem preserves (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source) :
    Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun _ id lowered => CompatibleExpressionLiterals.Certificate solved source id lowered)
      faults post :=
  preserves_of_fault_free functions program context evidence
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique (fun _ _ => False))

theorem reflects (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) :
    Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun _ id lowered => CompatibleExpressionLiterals.Certificate solved source id lowered)
      faults post :=
  reflects_of_fault_free functions program context evidence
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source (fun _ _ => False))

end Solcore.SourceSemantics.CoreLowering.ReachedLiteralOutcomePorts
