import Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
import Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission

/-! The actual compiler certificate retains an arm/default request for every
original body. Static request origins recover typing for all retained children. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchCertificates GenericMatchChildren

theorem scrutinee_found {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {expressions : ExpressionCertificate}
    {requests : List Request} {code : Expr}
    (certificate : Certificate compilation source scope id resolution result reason
      expressions (Occurs requests) code) :
    ∃ node, source.lookupExpression? resolution.scrutinee = some node := by
  cases certificate with
  | matchWith _ _ _ _ _ _ _ found _ _ _ _ _ _ _ => exact ⟨_, found⟩

private theorem arms_request {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {id : StatementId} {scope : Scope} {type : TypeSystem.Ty}
    {requests : List Request} {cases : List TypedMatchCase} {native : List (Pattern × Expr)}
    {arm : TypedMatchCase}
    (certificate : Arms compilation source id scope type (Occurs requests) cases native)
    (member : arm ∈ cases) : ∃ request ∈ requests, request.statements = arm.body := by
  induction certificate with
  | nil => cases member
  | cons pattern typed body tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, body, rfl⟩
    · exact ih member

theorem arm_request {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {expressions : ExpressionCertificate}
    {requests : List Request} {code : Expr} {arm : TypedMatchCase}
    (certificate : Certificate compilation source scope id resolution result reason
      expressions (Occurs requests) code)
    (member : arm ∈ resolution.cases) : ∃ request ∈ requests, request.statements = arm.body := by
  cases certificate with
  | matchWith _ _ _ _ _ _ _ _ _ _ _ arms _ _ _ => exact arms_request arms member

theorem default_request {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {expressions : ExpressionCertificate}
    {requests : List Request} {code : Expr} {statements : List StatementId}
    (certificate : Certificate compilation source scope id resolution result reason
      expressions (Occurs requests) code)
    (present : resolution.defaultBody = some statements) :
    ∃ request ∈ requests, request.statements = statements := by
  cases certificate with
  | matchWith _ _ _ _ _ _ _ _ _ _ _ _ fallback _ _ =>
    rw [present] at fallback
    cases fallback with
    | some body => exact ⟨_, body, rfl⟩

/-- A request may share its statement list with another arm. Its original
membership supplies a genuine context without identifying distinct scopes. -/
theorem original_context {source : TypedSource} {control : ControlContext}
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {cases : List TypedMatchCase} {facts : List BodyFacts}
    {fallback : Option (List StatementId)} {request : Request}
    (typed : MatchCasesHaveType source control context type cases facts)
    (defaultTyped : ∀ statements, fallback = some statements →
      ∃ final bodyFacts, StatementsHaveType source control context statements final bodyFacts)
    (original : (∃ arm ∈ cases, request.statements = arm.body) ∨ fallback = some request.statements) :
    ∃ child final bodyFacts,
      ContextFor source context type cases fallback request child ∧
      StatementsHaveType source control child request.statements final bodyFacts := by
  rcases original with ⟨arm, member, same⟩ | present
  · obtain ⟨binders, arity, child, final, bodyFacts, pattern, extended, body⟩ := case_typing typed member
    exact ⟨child, final, bodyFacts, .arm member same pattern extended, same ▸ body⟩
  · obtain ⟨final, bodyFacts, body⟩ := defaultTyped _ present
    exact ⟨context, final, bodyFacts, .default present, body⟩

/-- The original statement and its actual finite compiler children construct
the scan. Ownership supplies the hidden and pattern input-exclusion facts. -/
theorem matching_scan {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {scrutinee : ExpressionNode}
    {result : Ty} {reason : Word} {expressions : ExpressionCertificate}
    {requests : List Request} {code : Expr} {approved : ExpressionId → Prop}
    {expected : TypeSystem.Ty} {mode : Bool} {rest : List StatementId}
    (certificate : Certificate compilation source scope id resolution result reason
      expressions (Occurs requests) code)
    (ownership : LocalIdentityOwnership source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutinee)
    (value : approved resolution.scrutinee)
    (children : ∀ request ∈ requests,
      ScopedSourceBodyAdmission.Scan source approved expected false request.statements)
    (remaining : ScopedSourceBodyAdmission.Scan source approved expected mode rest) :
    ScopedSourceBodyAdmission.Scan source approved expected mode (id :: rest) := by
  obtain ⟨hiddenOrdinary, armsOrdinary⟩ := ordinary_bindings ownership found form
  apply ScopedSourceBodyAdmission.Scan.matching found form scrutineeFound value hiddenOrdinary armsOrdinary
  · intro arm member
    obtain ⟨request, present, same⟩ := arm_request certificate member
    exact same ▸ children request present
  · intro statements present
    obtain ⟨request, member, same⟩ := default_request certificate present
    exact same ▸ children request member
  · exact remaining

end Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
