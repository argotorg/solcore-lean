import Solcore.SourceSemantics.CoreLowering.RecursiveStageTupleMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingReadMeaning

/-! Concrete staged tuples may contain ordinary supported primitive leaves or
actual mapping reads. The common ordered tuple proof closes the leaf meanings
internally, including lazy initialization and the first failure. Arbitrary
callable expressions and generalized cells remain independent families. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingTupleMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}

/-- Both alternatives retain their actual compiler receipts and source binding. -/
def Leaves (fuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate := fun scope id code =>
  RecursiveStageTupleMeaning.PrimitiveCertificate fuel values source context solved reasonAt scope id code ∨
    RecursiveStageMappingReadMeaning.Supported (fuel := fuel) (values := values) (source := source)
      (context := context) (reasonAt := reasonAt) scope id code

def Certificate (fuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate :=
  RecursiveStageTupleMeaning.CertificateFor values source (Leaves fuel values source context solved reasonAt)

/-- A mapping leaf enters the finite tree from its exact static read receipt. -/
theorem mapping {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (receipt : RecursiveStageMappingReadMeaning.Supported (fuel := fuel) (values := values) (source := source)
      (context := context) (reasonAt := reasonAt) scope id code) :
    Certificate fuel values source context solved reasonAt scope id code := .leaf (.inr receipt)

/-- The original primitive family preserves its whole static tree. -/
theorem primitive {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (receipt : RecursiveStageTupleMeaning.PrimitiveCertificate fuel values source context solved reasonAt scope id code) :
    Certificate fuel values source context solved reasonAt scope id code := .leaf (.inl receipt)

section Meaning
variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = solved)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include sameSource sameLedger extension runtime uninitialized in
private theorem leaf_reflects :
    RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Leaves fuel values source context solved reasonAt)
      (RecursiveStageTupleMeaning.FaultRep faults) := by
  intro scope id code receipt
  intro node found mapping world admin environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  have result : ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expression program stages invocation context environment before id outcome after ∧
      RecursiveStagePrimitiveMeaning.Result functions (registry := registry) finalMap finalWorld
        node.type code.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
    rcases receipt with ordinary | selected
    · obtain ⟨tree, sites⟩ := ordinary
      exact RecursiveStagePrimitiveMeaning.reflects functions program stages invocation sameSource uninitialized
        sameLedger runtime sites found environments heaps locals agrees evaluated
    · exact RecursiveStageMappingReadMeaning.reflects functions program stages invocation sameSource extension
        selected found environments heaps locals agrees evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ := result
  refine ⟨outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds, frame, metadata⟩
  cases represented with
  | value payload => exact .value payload
  | fault matched => exact .fault matched

include sameSource sameLedger extension runtime uninitialized in
private theorem leaf_preserves (unique : NodeOccurrencesUnique source) :
    RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Leaves fuel values source context solved reasonAt)
      (RecursiveStageTupleMeaning.FaultRep faults) := by
  intro scope id code receipt
  intro node found mapping world admin environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  have result : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.expression.rename ξ) value finalStore ∧
      RecursiveStagePrimitiveMeaning.Result functions (registry := registry) finalMap finalWorld
        node.type code.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
    rcases receipt with ordinary | selected
    · obtain ⟨tree, sites⟩ := ordinary
      exact RecursiveStagePrimitiveMeaning.preserves functions program stages invocation sameSource unique uninitialized
        extension sameLedger runtime sites found environments heaps locals agrees trace
    · exact RecursiveStageMappingReadMeaning.preserves functions program stages invocation sameSource extension unique
        uninitialized selected found environments heaps locals agrees trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ := result
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, metadata⟩
  cases represented with
  | value payload => exact .value payload
  | fault matched => exact .fault matched

include sameSource sameLedger extension runtime uninitialized in
/-- Reflection starts with the original ordered Core pack. Each reached read
retains its own raw type and initializes the same cell at the same position. -/
theorem reflects :
    RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Certificate fuel values source context solved reasonAt)
      (RecursiveStageTupleMeaning.FaultRep faults) := by
  cases sameSource
  exact RecursiveStageTupleMeaning.reflects_with_leaves functions program stages invocation
    (leaf_reflects functions program stages invocation rfl sameLedger extension runtime uninitialized)

include sameSource sameLedger extension runtime uninitialized in
/-- Preservation closes the concrete leaf laws inside the common tuple proof.
No external execution law or preceding native completion is an input. -/
theorem preserves (unique : NodeOccurrencesUnique source) :
    RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Certificate fuel values source context solved reasonAt)
      (RecursiveStageTupleMeaning.FaultRep faults) := by
  cases sameSource
  exact RecursiveStageTupleMeaning.preserves_with_leaves functions program stages invocation unique
    (leaf_preserves functions program stages invocation rfl sameLedger extension runtime uninitialized unique)
end Meaning

/-- The actual function lowerer supplies the original ordered child vector.
Only static receipts from the reached child acceptances are required. -/
theorem of_functions {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {budget : Nat} {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {ids : List ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .tuple ids) (typed : ExpressionHasType source context id node.type)
    (special : ∀ child remaining, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child remaining source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (budget + 1) compilation source scope id reasonAt = .ok lowered)
    (extract : ∀ child, child ∈ ids → ∀ childNode code, source.lookupExpression? child = some childNode →
      ExpressionHasType source context child childNode.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope child reasonAt = .ok code →
      Certificate fuel values source context compilation.solvedRequirements reasonAt scope child code) :
    Certificate fuel values source context compilation.solvedRequirements reasonAt scope id lowered :=
  RecursiveStageTupleMeaning.of_functions_with_leaves
    (Leaves fuel values source context compilation.solvedRequirements reasonAt)
    unique found form typed special readPolicy leaf accepted extract

end Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingTupleMeaning
