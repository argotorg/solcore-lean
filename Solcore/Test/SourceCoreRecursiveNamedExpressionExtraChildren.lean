import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallCertificates

/-! Actual predecessor-fuel receipts feed the existing compiler fold. These
formal consumers retain callee-first order and duplicate arguments. Static
source typing and the indirect head receipt remain separate obligations;
no source execution, stage acceptance or called-body meaning is inferred. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedExpressionExtraChildren
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCallSelectionCertificates
open RecursiveNamedExpressionCompilerCertificates CallableIndirectCallCertificates

/-- Only actual indirect child positions use the new extra admission field. -/
def indirectForm : ExpressionForm → Prop
  | .call _ _ (.indirect _) => True
  | _ => False

def indirectChildren : ExpressionForm → List ExpressionId
  | .call callee arguments (.indirect _) => callee :: arguments
  | _ => []

section ActualReceipt
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreBasic.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered)

/-- The parent uses the successor; all actual vector entries use exactly its
predecessor, including repeated argument IDs and the leading callee. -/
theorem actual_predecessor_fuel :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id reasonAt = .ok lowered ∧
    ∀ child code, (child, code) ∈ receipt.entries →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt = .ok code :=
  ⟨receipt.accepted, receipt.ordered_children.2⟩

theorem actual_ordered_positions : receipt.entries.map Prod.fst = callee :: arguments := by
  have count := receipt.ordered_children.1
  simp only [Receipt.entries, List.map_cons, List.map_fst_zip (Nat.le_of_eq count)]

/-- Full original metadata and policy-read metadata stay distinct. -/
theorem actual_metadata :
    source.lookupExpression? id = some receipt.original ∧
    receipt.original.form = .call callee arguments (.indirect metadata) ∧
    policy.readExpression source id = .ok (receipt.node, receipt.type) ∧
    metadata.argumentCoercions = [] :=
  ⟨receipt.found, receipt.originalForm, receipt.read, receipt.argumentCoercions⟩

theorem actual_branch_receipt {context : SourceSemantics.Context}
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (head : calls (CompatibleExpressionCalls.Entries scope receipt.entries) scope id lowered)
    (sourceTypes : ∀ child code, (child, code) ∈ receipt.entries → ∃ childNode,
      source.lookupExpression? child = some childNode ∧ ExpressionHasType source context child childNode.type) :
    ∃ entries : List (ExpressionId × SourceCoreBasic.LoweredExpr),
      calls (CompatibleExpressionCalls.Entries scope entries) scope id lowered ∧
      entries.map Prod.fst = indirectChildren receipt.original.form ∧
      ∀ child code, (child, code) ∈ entries → ∃ childNode,
        source.lookupExpression? child = some childNode ∧
        ExpressionHasType source context child childNode.type ∧
        SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt = .ok code := by
  refine ⟨receipt.entries, head, ?_, ?_⟩
  · rw [receipt.originalForm]
    exact actual_ordered_positions receipt
  · intro child code member
    obtain ⟨childNode, found, typed⟩ := sourceTypes child code member
    exact ⟨childNode, found, typed, receipt.ordered_children.2 child code member⟩

/-- Actual repeated argument IDs remain three physical ordered vector slots. -/
theorem actual_repeated_positions (argument : ExpressionId) (repeated : arguments = [argument, argument]) :
    receipt.entries.map Prod.fst = [callee, argument, argument] ∧ receipt.entries.length = 3 := by
  constructor
  · rw [actual_ordered_positions receipt, repeated]
  · have count := congrArg List.length (actual_ordered_positions receipt)
    simpa only [List.length_map, repeated, List.length_cons, List.length_nil] using count

/-- Empty arguments retain the actual callee compiler result as the one child. -/
theorem actual_empty_arguments (empty : arguments = []) :
    receipt.entries = [(callee, receipt.calleeCode)] := by
  cases empty
  rfl

theorem actual_admitted_entries {admitted : ExpressionId → Prop}
    (admission : AdmissionWith indirectForm indirectChildren source admitted) (allowed : admitted id) :
    ∀ child code, (child, code) ∈ receipt.entries → admitted child := by
  intro child code member
  have form : indirectForm receipt.original.form := by rw [receipt.originalForm]; trivial
  apply admission.extra_children id receipt.original allowed receipt.found form child
  rw [← (show receipt.entries.map Prod.fst = indirectChildren receipt.original.form from by
    rw [receipt.originalForm]; exact actual_ordered_positions receipt)]
  exact List.mem_map.mpr ⟨(child, code), member, rfl⟩
end ActualReceipt

section Fold
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}

theorem tree_of_actual_indirect_children
    {source : TypedSource} {context : SourceSemantics.Context}
    (callerEvidence : Option Dynamic.EvidenceEnvironment)
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (includeCall : ∀ {children scope id lowered},
      RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context children scope id lowered →
      calls children scope id lowered)
    (projectedCall : ∀ {children scope id lowered node}, calls children scope id lowered →
      source.lookupExpression? id = some node → values.checked.catalog.project node.type = .ok lowered.type)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {admitted : ExpressionId → Prop}
    (admission : AdmissionWith indirectForm indirectChildren source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes headers context)
    (emptyEvidence : SelectedEmptyEvidence headers compilation source admitted)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source context admitted)
    (policyFor : PolicyForWith (headers := headers) callerEvidence policy compilation readFuel values source context scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    (extraReceipts : ∀ childFuel id node lowered, admitted id → source.lookupExpression? id = some node →
      indirectForm node.form → ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (childFuel + 1) compilation source scope id reasonAt = .ok lowered →
      ∃ callee arguments metadata,
        ∃ receipt : Receipt policy body childFuel compilation source scope id callee arguments metadata reasonAt lowered,
          calls (CompatibleExpressionCalls.Entries scope receipt.entries) scope id lowered ∧
          ∀ child code, (child, code) ∈ receipt.entries → ∃ childNode,
            source.lookupExpression? child = some childNode ∧ ExpressionHasType source context child childNode.type)
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered) :
    RuntimeExpressionsFor calls readFuel values source context compilation.solvedRequirements reasonAt scope id lowered := by
  apply tree_of_functions_at_runtime_with_children callerEvidence calls includeCall projectedCall
    indirectForm indirectChildren admission coverage sourceTypes emptyEvidence order unique declarations signatures
    constructorValid fragmentValid selectedValid policyFor native active profile fragmentCoercions coercions
    _ allowed found typed accepted
  intro childFuel child childNode childLowered childAllowed childFound form childTyped childAccepted
  obtain ⟨callee, arguments, metadata, receipt, head, types⟩ :=
    extraReceipts childFuel child childNode childLowered childAllowed childFound form childTyped childAccepted
  have same : receipt.original = childNode := Option.some.inj (receipt.found.symm.trans childFound)
  simpa only [same] using actual_branch_receipt receipt calls head types
end Fold

section Boundaries
variable (callee argument : ExpressionId) (metadata : IndirectCallResolution)
  (calleeCode first second : SourceCoreBasic.LoweredExpr)

/-- Physical vector order retains repeated IDs without sorting or deduplication. -/
theorem repeated_order :
    ([(callee, calleeCode), (argument, first), (argument, second)] :
      List (ExpressionId × SourceCoreBasic.LoweredExpr)).map Prod.fst = [callee, argument, argument] := rfl

theorem callee_first : indirectChildren (.call callee [argument, argument] (.indirect metadata)) =
    [callee, argument, argument] := rfl

/-- The ordinary public child definition remains unchanged. -/
theorem old_indirect_children : evaluationChildren (.call callee [argument, argument] (.indirect metadata)) = [] := rfl

theorem old_empty_admission {extra : ExpressionForm → Prop} {source : TypedSource}
    {admitted : ExpressionId → Prop} (admission : AdmissionFor extra source admitted) :
    AdmissionWith extra (fun _ => []) source admitted := admission.with_empty

abbrev old_compiler := @tree_of_functions_at_runtime_with_calls
abbrev original_arity := @tree_of_functions_at_runtime_with_calls._proof_1_33
end Boundaries
end Tests.SourceCoreRecursiveNamedExpressionExtraChildren
