import Solcore.SourceSemantics.CoreLowering.ScalarConstructorFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberTree

/-! Member fault transport retains the selected parent, child and layout. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ScalarMemberFaultPostContracts
open Core Frontend SourceInference CompatibleExpressionReads CompatibleExpressionMembers ExpressionFailurePostContracts

structure Joins (post : ExpressionFaultPost) (values : CompatibleExpressionReads.ValuesContext)
    (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) : Prop where
  base : ∀ {id node child childNode name index identity branches result childType
      environment before reason after token mapping world store},
    Metadata values.checked source id node result →
    Metadata values.checked source child childNode childType →
    node.form = .member child name index →
    Layout values.checked (.occurrence id.occurrence) childNode.type node.type index identity branches result →
    Dynamic.ExpressionFaults program context evidence source environment before child reason after →
    post program context evidence source environment before child reason after token mapping world store →
    post program context evidence source environment before id reason after token mapping world store

theorem trivial_joins (values : CompatibleExpressionReads.ValuesContext) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    Joins TrivialExpressionPost values program context evidence source where
  base := by intros; trivial

theorem base_fault_outcome {post : ExpressionFaultPost} {values : CompatibleExpressionReads.ValuesContext}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} (joins : Joins post values program context evidence source)
    {id child : ExpressionId} {node childNode : ExpressionNode} {name : String} {index : Nat}
    {identity : DataTypeId} {branches : List Expr} {result childType : Ty}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {token : Word} {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {store : Store}
    (metadata : Metadata values.checked source id node result)
    (baseMetadata : Metadata values.checked source child childNode childType)
    (form : node.form = .member child name index)
    (layout : Layout values.checked (.occurrence id.occurrence) childNode.type node.type index identity branches result)
    (failed : Dynamic.ExpressionFaults program context evidence source environment before child reason after)
    (retained : OutcomePost post program context evidence source environment before child childType
      (.fault reason) after (.inLeft childType (.word token)) mapping world store) :
    OutcomePost post program context evidence source environment before id result
      (.fault reason) after (.inLeft result (.word token)) mapping world store :=
  ⟨token, rfl, joins.base metadata baseMetadata form layout failed (OutcomePost.fault retained)⟩

end Solcore.SourceSemantics.CoreLowering.ScalarMemberFaultPostContracts
