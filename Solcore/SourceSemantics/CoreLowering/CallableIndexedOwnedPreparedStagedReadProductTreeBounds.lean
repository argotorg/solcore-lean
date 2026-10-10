import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedProductTreeBounds

/-! One accepted compiler extraction retains the actual finite literal/read/
group/pair tree and its selected literal sites. Structural recursion constructs
every staged child meaning internally, including ordinary local reads and lazy
mapping initialization at the actual reached state. Source and native grades
remain independent: transparent group reflection uses the same native grade,
while evaluated pair binds use their real strict child grades. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

/-- The original compiler tree and LiteralSites are paired at the same code,
Source context and read fuel. Only static receipts are retained. -/
abbrev Certificate (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate :=
  CompatibleExpressionProducts.Tree.WithLiterals (fuel := readFuel) (values := values)
    (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
    (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved source id lowered)

private theorem selected_literals {policy body context values source scope reasonAt} :
    CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt
      (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate context.solvedRequirements source id lowered) := by
  intro id node fuel lowered found atomic unitType special readPolicy leafPolicy accepted
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType
    special readPolicy leafPolicy accepted
  exact ⟨receipt.forget, receipt⟩

/-- The genuine accepted action extracts this exact supported tree once. Raw
Source typing and compiler policy facts are independent static inputs. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (policyFor : CompatibleExpressionProducts.PolicyFor policy compilation readFuel values source scope reasonAt)
    (coercions : ∀ id node, CompatibleExpressionProducts.Syntax source id →
      source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : CompatibleExpressionProducts.Syntax source id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Certificate readFuel values source context compilation.solvedRequirements reasonAt scope id lowered := by
  exact CompatibleExpressionProducts.tree_of_functions_with_literals
    (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate compilation.solvedRequirements source id code)
    selected_literals unique declarations policyFor coercions syntaxTree found typed accepted

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  {semanticFaults : FunctionCalls.FaultRep}
  (faults : RecursiveStageMeaning.FaultRep)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "trees" => Certificate readFuel
  (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
  invocation.source context solved reasonAt

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues
      (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include extension sameLedger runtimeLedger uninitialized semantic unique wellFormed runtime covers in
/-- LiteralSites recursion proves each actual Source child internally. A read
uses its genuine local certificate; no read or whole-child meaning is supplied. -/
theorem preserves (size : Nat) :
    PreservesAt bridge context valueModel registry invocation trees faults size := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites generalizing size with
  | literal _ receipt =>
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedLiteralGroupBounds.literal_preserves
        functions bridge sameLedger runtimeLedger unique wellFormed runtime covers faults size receipt
  | read receipt =>
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedReadBounds.preserves bridge functions extension
        uninitialized semantic unique wellFormed runtime covers size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
      have children : PreservesBelow bridge context valueModel registry invocation
          (Point scope inner lowered) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih childSize
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size children
        size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
      have children : PreservesBelow bridge context valueModel registry invocation
          (Two scope left right first second) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, alternative⟩ := point
        cases alternative with
        | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize
        | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedPairBounds.pair_preserves bridge unique wellFormed
        runtime covers (product_values functions) size children size (Nat.le_refl _)
        (.actual metadata form leftFound rightFound sourceType
          ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

include extension sameLedger runtimeLedger uninitialized semantic unique wellFormed runtime covers in
/-- Reflection follows the same finite sites at independent native grades.
Grouping recurses at the same grade; actual pair binds supply strict children. -/
theorem reflects (size : Nat) :
    ReflectsAt bridge context valueModel registry invocation trees faults size := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites generalizing size with
  | literal _ receipt =>
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedLiteralGroupBounds.literal_reflects
        functions bridge sameLedger runtimeLedger wellFormed runtime covers faults size receipt
  | read receipt =>
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedReadBounds.reflects bridge functions extension
        uninitialized semantic unique wellFormed runtime covers size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
      have children : ReflectsAt bridge context valueModel registry invocation
          (Point scope inner lowered) faults size := by
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih size
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size children
        (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
      have children : ReflectsBelow bridge context valueModel registry invocation
          (Two scope left right first second) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, alternative⟩ := point
        cases alternative with
        | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize
        | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedPairBounds.pair_reflects bridge unique wellFormed
        runtime covers (product_values functions) size children size (Nat.le_refl _)
        (.actual metadata form leftFound rightFound sourceType
          ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds
