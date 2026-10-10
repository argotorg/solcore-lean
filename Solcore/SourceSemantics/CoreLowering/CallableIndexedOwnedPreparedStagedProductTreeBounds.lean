import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLiteralGroupBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPairBounds

/-! The actual accepted compiler extracts the finite pure product fragment.
The selected literal sites and exact grouped/product children are retained
through one canonical extraction. Structural recursion constructs the staged
meaning of every child. Native grouping keeps the same size; executed pair
children descend strictly. Source and native sizes remain independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedProductTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

/-- A finite syntax restriction, with actual lookup and form fields only. -/
inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | literal {id node} (found : source.lookupExpression? id = some node)
      (atomic : CompatibleExpressionLiterals.Atomic node.form) : Syntax source id
  | group {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .group inner) (child : Syntax source inner) : Syntax source id
  | pair {id node left right} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple [left, right])
      (first : Syntax source left) (second : Syntax source right) : Syntax source id

theorem Syntax.to_canonical {source : TypedSource} {id : ExpressionId}
    (syntaxTree : Syntax source id) : CompatibleExpressionProducts.Syntax source id := by
  induction syntaxTree with
  | literal found atomic => exact .literal found atomic
  | group found form child ih => exact .group found form ih
  | pair found form first second firstIH secondIH => exact .pair found form firstIH secondIH

/-- Every retained child is the literal native child from the same compiler
extraction. Source product types are independent raw typing identities. -/
inductive Tree (checked : SourceCoreCompatibleCatalog.Checked) (solved : List SolvedRequirement)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | literal {id lowered}
      (receipt : CompatibleExpressionLiteralRuntime.Certificate solved source id lowered) :
      Tree checked solved source scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : CompatibleExpressionReads.Metadata checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Tree checked solved source scope inner lowered) :
      Tree checked solved source scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : CompatibleExpressionReads.Metadata checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (leftTree : Tree checked solved source scope left first)
      (rightTree : Tree checked solved source scope right second) :
      Tree checked solved source scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩

/-- Translation follows actual LiteralSites, including their authentic
compound fields. The pure syntax rules rule out a local-read leaf. -/
theorem Tree.of_literal_sites
    {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered}
    (sites : tree.LiteralSites
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code))
    (syntaxTree : Syntax source id) : Tree values.checked solved source scope id lowered := by
  induction sites with
  | literal _ receipt => exact .literal receipt
  | read receipt =>
      obtain ⟨actual, _type, _binding⟩ := receipt
      cases syntaxTree with
      | literal found atomic =>
          cases Option.some.inj (found.symm.trans actual.metadata.found)
          rw [actual.form] at atomic
          cases atomic
      | group found form child =>
          cases Option.some.inj (found.symm.trans actual.metadata.found)
          simp [actual.form] at form
      | pair found form first second =>
          cases Option.some.inj (found.symm.trans actual.metadata.found)
          simp [actual.form] at form
  | group metadata form innerFound sourceType child childSites ih =>
      cases syntaxTree with
      | literal found atomic =>
          cases Option.some.inj (found.symm.trans metadata.found)
          rw [form] at atomic
          cases atomic
      | group found actualForm childSyntax =>
          cases Option.some.inj (found.symm.trans metadata.found)
          cases ExpressionForm.group.inj (actualForm.symm.trans form)
          exact .group metadata form innerFound sourceType (ih childSyntax)
      | pair found actualForm first second =>
          cases Option.some.inj (found.symm.trans metadata.found)
          simp [form] at actualForm
  | pair metadata form leftFound rightFound sourceType first second firstSites secondSites firstIH secondIH =>
      cases syntaxTree with
      | literal found atomic =>
          cases Option.some.inj (found.symm.trans metadata.found)
          rw [form] at atomic
          cases atomic
      | group found actualForm child =>
          cases Option.some.inj (found.symm.trans metadata.found)
          simp [form] at actualForm
      | pair found actualForm leftSyntax rightSyntax =>
          cases Option.some.inj (found.symm.trans metadata.found)
          have ids := ExpressionForm.tuple.inj (actualForm.symm.trans form)
          cases (List.cons.inj ids).1
          cases (List.cons.inj (List.cons.inj ids).2).1
          exact .pair metadata form leftFound rightFound sourceType
            (firstIH leftSyntax) (secondIH rightSyntax)

/-- The selected numeric literal producer runs at the exact accepted leaf
action. It supplies both canonical membership and the stronger runtime leaf. -/
private theorem selected_literals {policy body context values source scope reasonAt} :
    CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt
      (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate context.solvedRequirements source id lowered) := by
  intro id node fuel lowered found atomic unitType special readPolicy leafPolicy accepted
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType
    special readPolicy leafPolicy accepted
  exact ⟨receipt.forget, receipt⟩

/-- One canonical static extraction constructs the finite runtime tree.
Only authentic syntax, raw typing and policy/compiler facts are inputs. -/
theorem Tree.of_functions
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
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Tree values.checked compilation.solvedRequirements source scope id lowered := by
  obtain ⟨tree, sites⟩ := CompatibleExpressionProducts.tree_of_functions_with_literals
    (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate compilation.solvedRequirements source id code)
    selected_literals unique declarations policyFor coercions syntaxTree.to_canonical found typed accepted
  exact Tree.of_literal_sites sites syntaxTree

variable {checked : SourceCoreCompatibleCatalog.Checked} {rawRegistry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)
  (faults : RecursiveStageMeaning.FaultRep)

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues
      (model := CompatibleAmbientHeap.payloadModel checked rawRegistry functions) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include sameLedger runtimeLedger unique wellFormed runtime covers in
/-- Finite structural recursion constructs all child preservation proofs.
Each actual Source child has its own strictly smaller Source grade. -/
theorem preserves (size : Nat) :
    PreservesAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (Tree checked solved invocation.source) faults size := by
  intro scope id lowered tree
  induction tree generalizing size with
  | literal receipt =>
      exact CallableIndexedOwnedPreparedStagedLiteralGroupBounds.literal_preserves
        functions bridge sameLedger runtimeLedger unique wellFormed runtime covers faults size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
      have children : PreservesBelow bridge context
          (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) registry invocation
          (Point scope inner lowered) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih childSize
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size children
        size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
      have children : PreservesBelow bridge context
          (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) registry invocation
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

include sameLedger runtimeLedger unique wellFormed runtime covers in
/-- LiteralSites structural recursion permits group reflection at the SAME
native size. Only actual pair bind children use strict native descent. -/
theorem reflects (size : Nat) :
    ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (Tree checked solved invocation.source) faults size := by
  intro scope id lowered tree
  induction tree generalizing size with
  | literal receipt =>
      exact CallableIndexedOwnedPreparedStagedLiteralGroupBounds.literal_reflects
        functions bridge sameLedger runtimeLedger wellFormed runtime covers faults size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
      have children : ReflectsAt bridge context
          (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) registry invocation
          (Point scope inner lowered) faults size := by
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih size
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size children
        (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
      have children : ReflectsBelow bridge context
          (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) registry invocation
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedProductTreeBounds
