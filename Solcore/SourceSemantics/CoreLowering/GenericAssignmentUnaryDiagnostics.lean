import Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticOrigins

/-! Bit-not assignments retain their own original unary diagnostic category.
The prepared source table supplies the exact token at a statement or for-header
occurrence; no value-assignment operand relation is widened. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentUnaryDiagnostics
open Core Frontend SourceInference SourceCoreAssignmentFaultSites

/-- Only an authentic decoded bit-not entry represents this unary fault. -/
def UnaryRep (table : Table) : FunctionCalls.FaultRep
  | .invalidUnaryOperand .bitNot, token => ∃ diagnostic,
      table.diagnostic? token = some diagnostic ∧
      diagnostic.error = .invalidUnaryOperand .bitNot none
  | _, _ => False

def unaryToken (table : Table) (site : SourceCoreElaboration.ErrorSite)
    (root : Resolved.LocalId) : Word := table.reasonAt site root .bitNot

/-- Header unary statements retain their actual owning for occurrence. -/
inductive UnaryOccurs (source : TypedSource) :
    SourceCoreElaboration.ErrorSite → AssignmentResolution → Prop where
  | statement {id node assignment}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .assignBitNot assignment) :
      UnaryOccurs source (.occurrence id.occurrence) assignment
  | header {id node initializer condition post body assignment}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .forLoop initializer condition post body)
      (member : .assignBitNot assignment ∈ initializer ++ post) :
      UnaryOccurs source (.occurrence id.occurrence) assignment

abbrev UnaryOccursFor (tracked : Bool) (source : TypedSource)
    (site : SourceCoreElaboration.ErrorSite) (assignment : AssignmentResolution) : Prop :=
  if tracked then UnaryOccurs source site assignment else True

theorem UnaryOccursFor.statement {tracked : Bool} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment) :
    UnaryOccursFor tracked source (.occurrence id.occurrence) assignment := by
  cases tracked with
  | false => trivial
  | true => exact UnaryOccurs.statement found form

/-- The existing table traversal includes actual unary statement and header sites. -/
theorem prepared_unary_at {source : TypedSource} {first : Nat} {table : Table}
    {node : StatementNode} {assignment : AssignmentResolution}
    (prepared : prepare source first = .ok table) (member : Node.statement node ∈ source.nodes)
    (occurs : Certificates.UnaryAt node assignment)
    (rawWord : assignment.target.type = .word) :
    UnaryRep table (.invalidUnaryOperand .bitNot)
      (unaryToken table (.occurrence node.id.occurrence) assignment.target.root) := by
  obtain ⟨site, _, _, _, kind, reason, diagnostic⟩ :=
    Certificates.prepare_unary prepared member occurs (.inl rawWord)
  refine ⟨site.diagnostic, ?_, ?_⟩
  · simpa only [unaryToken, reason] using diagnostic
  · simp only [Site.diagnostic, kind]

theorem prepared_unary {source : TypedSource} {first : Nat} {table : Table}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    (prepared : prepare source first = .ok table)
    (origin : UnaryOccurs source site assignment) (rawWord : assignment.target.type = .word) :
    UnaryRep table (.invalidUnaryOperand .bitNot) (unaryToken table site assignment.target.root) := by
  cases origin with
  | statement found form =>
    have present := lookupStatement?_sound found
    rw [← present.2]
    exact prepared_unary_at prepared present.1 (.statement form) rawWord
  | header found form member =>
    have present := lookupStatement?_sound found
    rw [← present.2]
    exact prepared_unary_at prepared present.1 (.header form member) rawWord

/-- The receiving relation gets only the actual prepared unary entry. -/
theorem prepared_unary_included {source : TypedSource} {first : Nat} {table : Table}
    {faults : FunctionCalls.FaultRep}
    (prepared : prepare source first = .ok table)
    (included : ∀ reason token, UnaryRep table reason token → faults reason token)
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    (origin : UnaryOccurs source site assignment) (rawWord : assignment.target.type = .word) :
    faults (.invalidUnaryOperand .bitNot) (unaryToken table site assignment.target.root) :=
  included _ _ (prepared_unary prepared origin rawWord)

end Solcore.SourceSemantics.CoreLowering.GenericAssignmentUnaryDiagnostics

namespace Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticOrigins
open Core Frontend SourceInference GenericAssignmentUnaryDiagnostics

/-- The current unary header item retains the original owning occurrence. -/
theorem HeaderOriginFor.unary {tracked : Bool} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution} {items : List ForItemForm}
    (origin : HeaderOriginFor tracked source site (.assignBitNot assignment :: items)) :
    UnaryOccursFor tracked source site assignment := by
  cases tracked with
  | false => trivial
  | true =>
    rcases origin with ⟨id, node, initializer, condition, post, body, found, form, rfl, suffix⟩ |
      ⟨id, node, initializer, condition, post, body, found, form, rfl, suffix⟩
    · obtain ⟨beforeItems, same⟩ := suffix
      apply UnaryOccurs.header found form
      apply List.mem_append_left
      rw [← same]
      exact List.mem_append_right _ List.mem_cons_self
    · obtain ⟨beforeItems, same⟩ := suffix
      apply UnaryOccurs.header found form
      apply List.mem_append_right
      rw [← same]
      exact List.mem_append_right _ List.mem_cons_self

end Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticOrigins
