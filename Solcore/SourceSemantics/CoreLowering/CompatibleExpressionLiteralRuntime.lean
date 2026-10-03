import Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts

/-! Atomic literal receipts retain actual numeric implementation evidence.
The old literal and ordinary-context APIs are unchanged. Runtime ledger validity
is consumed only at the selected numeric row; all unused rows stay present.
No source or native execution law is stored in this static certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionLiterals

/-- The primitive implementation is fixed by the actual compiler's numeric
target branch. Other atomic forms have no selected numeric evidence. -/
def NumericSelected (solved : List SolvedRequirement) (node : ExpressionNode) : Prop :=
  ∀ literal resolution, node.form = .integerLiteral literal resolution →
    NumericLiteralEvidenceReceipts.Selected solved resolution
      (.builtin (if node.type = .integer then .intInteger else .intWord))

/-- The ordinary literal metadata and the full actual numeric row receipt.
Neither the complete runtime ledger nor a semantic execution law is a field. -/
def Certificate (solved : List SolvedRequirement) (source : TypedSource)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ node, source.lookupExpression? id = some node ∧
    Literal solved node lowered.type lowered.expression ∧ NumericSelected solved node

theorem Certificate.forget {solved source id lowered}
    (receipt : Certificate solved source id lowered) :
    CompatibleExpressionLiterals.Certificate solved source id lowered := by
  obtain ⟨node, found, literal, _⟩ := receipt
  exact ⟨node, found, literal⟩

private theorem selected_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    NumericSelected context.solvedRequirements node := by
  intro literal resolution form
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
        bind, Except.bind, pure, Except.pure] at accepted
      have bypass := special (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) context childSource childScope childId childReasonAt) (fuel + 1)
      cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
      all_goals try rw [bypass] at accepted
      all_goals
        simp only [form] at accepted
        by_cases target : node.type = .integer
        · simp only [target, ↓reduceIte] at accepted ⊢
          cases validated : SourceCoreElaboration.validateNativeIntegerLiteral context.solvedRequirements node literal resolution with
          | error error => simp [validated, Except.mapError] at accepted
          | ok output => exact NumericLiteralEvidenceReceipts.integer validated
        · simp only [target, ↓reduceIte] at accepted ⊢
          cases validated : SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements node literal resolution with
          | error error => simp [validated, Except.mapError] at accepted
          | ok output => exact NumericLiteralEvidenceReceipts.word validated
    · simp [owner, bind, Except.bind] at accepted

/-- Successful actual function lowering supplies both old metadata and the
stronger selected-row receipt. The original override bypass is explicit. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {context : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (atomic : Atomic node.form) (unitType : node.form = .tuple [] → node.type = .unit)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Certificate context.solvedRequirements source id lowered := by
  obtain ⟨other, otherFound, literal⟩ := CompatibleExpressionLiterals.of_functions found atomic unitType special readPolicy leafPolicy accepted
  have same := Option.some.inj (otherFound.symm.trans found)
  subst other
  exact ⟨node, found, literal, selected_of_functions found special accepted⟩

/-- Only the authenticated row is checked against the complete runtime ledger.
No covering dictionary or ordinary validity of unused rows is required. -/
theorem NumericSelected.evidence {solved : List SolvedRequirement} {node : ExpressionNode}
    (selected : NumericSelected solved node) {context : SourceSemantics.Context}
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context) (evidence : Dynamic.EvidenceEnvironment) :
    NumericEvidence context evidence node := by
  intro literal resolution form
  exact ⟨(selected literal resolution form).proves sameLedger runtime,
    (selected literal resolution form).safe sameLedger runtime evidence⟩

/-- The complete atomic family uses the shared literal preservation proof.
Its extra static evidence comes from actual numeric acceptance only. -/
theorem preserves {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {solved : List SolvedRequirement} (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context) {source : TypedSource}
    (unique : NodeOccurrencesUnique source) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun _ id lowered => Certificate solved source id lowered) faults := by
  refine CompatibleExpressionLiterals.preserves_with_evidence (registry := registry) (solved := solved)
    functions program context evidence (certificate := fun _ id lowered => Certificate solved source id lowered) ?_ unique faults
  intro scope id lowered receipt
  obtain ⟨node, found, literal, selected⟩ := receipt
  exact ⟨node, found, literal, selected.evidence sameLedger runtime evidence⟩

/-- Reflection uses the same static receipt and original native completion;
no preservation law or prior independent source execution is an input. -/
theorem reflects {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    {solved : List SolvedRequirement} (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context) (source : TypedSource) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (fun _ id lowered => Certificate solved source id lowered) faults := by
  refine CompatibleExpressionLiterals.reflects_with_evidence (registry := registry) (solved := solved)
    functions program context evidence source (certificate := fun _ id lowered => Certificate solved source id lowered) ?_ faults
  intro scope id lowered receipt
  obtain ⟨node, found, literal, selected⟩ := receipt
  exact ⟨node, found, literal, selected.evidence sameLedger runtime evidence⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
