import Solcore.SourceSemantics.CoreLowering.GenericAssignmentUnaryDiagnostics
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingPreparationCoverage

/-! Projected unary sites reuse the actual unary occurrence grammar. Their
owning statement supplies the same place diagnostic inventory as compilation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProjectedBitNotDiagnosticOrigins
open Core Frontend SourceInference

abbrev Occurs := GenericAssignmentUnaryDiagnostics.UnaryOccurs
abbrev OccursFor := GenericAssignmentUnaryDiagnostics.UnaryOccursFor
abbrev HeaderOriginFor := AssignmentDiagnosticOrigins.HeaderOriginFor
abbrev ForOriginFor := AssignmentDiagnosticOrigins.ForOriginFor

/-- Statement and header sites retain the authentic parent and target. -/
theorem owning_target {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} (origin : Occurs source site assignment) :
    ∃ node, .statement node ∈ source.nodes ∧ site = .occurrence node.id.occurrence ∧
      assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node := by
  cases origin with
  | statement found form =>
    refine ⟨_, (lookupStatement?_sound found).1, ?_, ?_⟩
    · exact (congrArg (fun id : StatementId => SourceCoreElaboration.ErrorSite.occurrence id.occurrence)
        (lookupStatement?_sound found).2).symm
    · simp only [CompatiblePlaceMissingPreparationCoverage.targets, form, List.mem_singleton]
  | header found form member =>
    refine ⟨_, (lookupStatement?_sound found).1, ?_, ?_⟩
    · exact (congrArg (fun id : StatementId => SourceCoreElaboration.ErrorSite.occurrence id.occurrence)
        (lookupStatement?_sound found).2).symm
    · rw [CompatiblePlaceMissingPreparationCoverage.targets, form]
      exact List.mem_filterMap.mpr ⟨_, member, rfl⟩

end Solcore.SourceSemantics.CoreLowering.ProjectedBitNotDiagnosticOrigins
