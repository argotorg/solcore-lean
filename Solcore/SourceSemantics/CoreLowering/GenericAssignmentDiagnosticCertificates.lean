import Solcore.SourceSemantics.CoreLowering.AssignmentFaultTableCertificates
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentReachableDiagnostics
import Solcore.Frontend.SourceCoreCompatibleDataMatches

/-! The real loop-policy callback supplies the exact operand token. The table
relation describes only operand diagnostics; clients explicitly include it in
their whole fault relation. Missing/default and uninitialized place laws remain
separate. No native projection supplies raw scalar eligibility. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnostics
open Core Frontend SourceInference
open SourceCoreAssignmentFaultSites
open Certificates (OperandAt)

/-- A concrete relation for actual table diagnostics, with no invented entry
for plain assignment and no claim about another fault category. -/
def OperandRep (table : Table) : FunctionCalls.FaultRep
  | .invalidAssignmentOperands operator, token => ∃ diagnostic rawType,
      table.diagnostic? token = some diagnostic ∧
      diagnostic.error = .invalidAssignmentOperands operator none (some rawType)
  | _, _ => False

def token (table : Table) (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (operator : Syntax.ValueAssignOp) : Word :=
  if operator = .equal then .zero else table.reasonAt site root (.value operator)

theorem prepared_operands {source : TypedSource} {first : Nat} {table : Table}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    (prepared : prepare source first = .ok table) (member : Node.statement node ∈ source.nodes)
    (occurs : OperandAt node assignment operator)
    (rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer) :
    AssignmentOperandDiagnostics.OperandsLaw (OperandRep table) operator
      (token table (.occurrence node.id.occurrence) assignment.target.root operator) := by
  apply AssignmentOperandDiagnostics.of_not_equal
  intro different
  have scalar : assignment.target.type = .word ∨ assignment.target.type = .integer := by
    rcases rawProfile with equal | scalar
    · exact (different equal).elim
    · exact scalar
  obtain ⟨site, _, _, _, kind, reason, diagnostic⟩ := Certificates.prepare_operand prepared member occurs different scalar
  refine ⟨site.diagnostic, site.rhsType, ?_, ?_⟩
  · simpa only [token, if_neg different, reason] using diagnostic
  · simp only [Site.diagnostic, kind]

/-- Relating operand diagnostics to a larger fault inventory is explicit. -/
theorem prepared_operands_included {source : TypedSource} {first : Nat} {table : Table}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    {faults : FunctionCalls.FaultRep}
    (included : ∀ reason word, OperandRep table reason word → faults reason word)
    (prepared : prepare source first = .ok table) (member : Node.statement node ∈ source.nodes)
    (occurs : OperandAt node assignment operator)
    (rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer) :
    AssignmentOperandDiagnostics.OperandsLaw faults operator
      (token table (.occurrence node.id.occurrence) assignment.target.root operator) := by
  intro previous right invalid
  exact included _ _ (prepared_operands prepared member occurs rawProfile previous right invalid)

/-- Both ordinary statements and for-header items select this same real
callback. Equal uses zero; compound operators use the actual table lookup. -/
theorem policy_assignment (values : SourceCoreCompatibleValues.Context)
    (solved : List SolvedRequirement) (table : Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (owner : SourceSpecialization.SpecializationKey) (expression : SourceCoreFunctions.ExpressionLowerer)
    (sourceCells : Option SourceCoreSourceCells.Allocator) (definitions : Option DataEnvironment)
    (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (site : SourceCoreElaboration.ErrorSite) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (output : Ty) (next : Expr) (reasonAt : ExpressionId → Word) :
    SourceCoreLoops.assignValue (SourceCoreCompatibleDataMatches.loopPolicy values solved table diagnostics owner expression sourceCells definitions)
      fuel source scope site assignment operator rhs output next reasonAt =
    SourceCoreCompatibleDataPlaces.lower values values.checked.signatures expression fuel source scope site assignment operator
      (some rhs) output next reasonAt (diagnostics.placeReason owner site assignment.target.root none)
      (token table site assignment.target.root operator)
      (fun type => diagnostics.placeReason owner site assignment.target.root (some type)) := by
  cases operator <;> rfl

end Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnostics

namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open GenericAssignmentDiagnostics

theorem Head.reachable_of_token
    {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
    {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
    {definitions : DataEnvironment} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    {table : SourceCoreAssignmentFaultSites.Table} {first : Nat} {node : StatementNode}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (same : head.invalid = token table (.occurrence node.id.occurrence) assignment.target.root operator)
    (included : ∀ reason word, OperandRep table reason word → faults reason word)
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (member : Node.statement node ∈ source.nodes)
    (occurs : SourceCoreAssignmentFaultSites.Certificates.OperandAt node assignment operator)
    (rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer)
    (missing : ∀ {root resolved reason word count},
      CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason word count → faults reason word)
    (uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection) :
    head.ReachableErrors registry faults :=
  ⟨missing, uninitialized, same.symm ▸ prepared_operands_included included prepared member occurs rawProfile⟩

/-- One compiler traversal supplies both the emitted expression and its exact
operand token, then the actual prepared table supplies the reachable law. -/
theorem Head.of_prepared_policy
    {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
    {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : SourceCoreFunctions.ExpressionLowerer} {fuel : Nat} {node : StatementNode}
    {next code : Expr} {output result : Ty}
    {solved : List SolvedRequirement} {table : SourceCoreAssignmentFaultSites.Table} {first : Nat}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {owner : SourceSpecialization.SpecializationKey}
    {sourceCells : Option SourceCoreSourceCells.Allocator} {ambientDefinitions : Option DataEnvironment}
    {faults : FunctionCalls.FaultRep}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer)
    (extract : ∀ id lowered, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered → ∃ child,
      source.lookupExpression? id = some child ∧ certificate scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (member : Node.statement node ∈ source.nodes)
    (occurs : SourceCoreAssignmentFaultSites.Certificates.OperandAt node assignment operator)
    (included : ∀ reason word, OperandRep table reason word → faults reason word)
    (accepted : SourceCoreLoops.assignValue
      (SourceCoreCompatibleDataMatches.loopPolicy values solved table diagnostics owner expression sourceCells ambientDefinitions)
      fuel source scope (.occurrence node.id.occurrence) assignment operator rhs output next reasonAt = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output ∧
      head.invalid = token table (.occurrence node.id.occurrence) assignment.target.root operator ∧
      AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid := by
  rw [policy_assignment] at accepted
  have profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer := by
    rcases rawProfile with equal | word | integer
    · exact .inl equal
    · exact .inr (.inl (by rw [word]; rfl))
    · exact .inr (.inr (by rw [integer]; rfl))
  obtain ⟨head, emitted, same⟩ := Head.of_lower_with_token unique signatures sourceTyped writable rightTyped profile extract accepted typed
  exact ⟨head, emitted, same, same.symm ▸ prepared_operands_included included prepared member occurs rawProfile⟩

end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
