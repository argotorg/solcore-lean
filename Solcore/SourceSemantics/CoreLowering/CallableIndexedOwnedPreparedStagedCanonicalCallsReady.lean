import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerRawTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopeCallPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds

/-! Static call authority for one genuine root at the canonical invocation of
the same actual Code. The certificate retains every callee and argument row,
including duplicate occurrences. Original typing supplies each reached raw
parent type; the retained policy supplies its exact compiler callbacks. Global
metadata and original source attribution remain genuine static inputs.
This endpoint covers the canonical invocation. Other selected guard frames
require their own actual coherence proof. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalCallsReady
open Core Frontend SourceInference
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls Syntax)

private theorem literal_syntax {solved : List SolvedRequirement}
    {source : TypedSource} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionLiterals.Certificate solved source id lowered) :
    CompatibleExpressionProducts.Syntax source id := by
  rcases lowered with ⟨type, expression⟩
  obtain ⟨node, found, literal⟩ := receipt
  refine .literal found ?_
  cases literal with
  | unit form _type _requirements _coercions =>
    rw [form]
    exact .unit
  | bool value form _type _requirements _coercions =>
    rw [form]
    exact .bool _ value
  | word value form _type _requirements _coercions _meaning =>
    rw [form]
    exact .word _
  | resolvedWord form _metadata | resolvedInteger form _metadata =>
    rw [form]
    exact .integer _ _

private theorem product_syntax {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered) :
    CompatibleExpressionProducts.Syntax source id := by
  induction tree with
  | literal receipt => exact literal_syntax receipt
  | read receipt =>
    obtain ⟨certificate, _type, _binding⟩ := receipt
    exact .read certificate.metadata.found certificate.form
  | group metadata form _found _sourceType _child ih =>
    exact .group metadata.found form ih
  | pair metadata form _leftFound _rightFound _sourceType _first _second firstIH secondIH =>
    exact .pair metadata.found form firstIH secondIH

private theorem sequence_length {source : TypedSource}
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope ids types codes) :
    ids.length = codes.length := by
  induction tree with
  | nil => rfl
  | single _found _generated => rfl
  | cons _found _generated _tail ih => exact congrArg Nat.succ ih

private theorem zip_member {α β : Type} {xs : List α} {ys : List β}
    (same : xs.length = ys.length) {x : α} (member : x ∈ xs) :
    ∃ y, (x, y) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => cases member
  | cons head rest ih =>
    cases ys with
    | nil => cases same
    | cons first tail =>
      have remaining : rest.length = tail.length := Nat.succ.inj same
      rcases List.mem_cons.mp member with equal | inside
      · subst x
        refine ⟨first, ?_⟩
        change (head, first) ∈ (head, first) :: rest.zip tail
        exact List.mem_cons_self
      · obtain ⟨y, paired⟩ := ih remaining inside
        refine ⟨y, ?_⟩
        change (x, y) ∈ (head, first) :: rest.zip tail
        exact List.mem_cons_of_mem _ paired

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}

/-- Every actual certificate reconstructs its supported original grammar.
The physical argument rows are retained; no occurrence set replaces them. -/
theorem certificate_syntax {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Certificate policy body compilation readFuel values source context reasonAt scope id lowered) :
    Syntax source id := by
  induction tree with
  | leaf tree =>
    obtain ⟨product, _literalSites⟩ := tree
    exact .leaf (product_syntax product)
  | group metadata form _found _sourceType _child ih =>
    exact .group metadata.found form ih
  | @tuple id node ids types codes header sequence children ih =>
    refine .tuple header.metadata.found header.form ?_
    intro child member
    obtain ⟨code, paired⟩ := zip_member (sequence_length sequence) member
    exact ih child code paired
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
    refine .call compiler.found compiler.originalForm ?_ ?_
    · apply ih callee compiler.calleeCode
      change (callee, compiler.calleeCode) ∈ (callee, compiler.calleeCode) :: ids.zip compiler.codes
      exact List.mem_cons_self
    · intro child member
      obtain ⟨code, paired⟩ := zip_member (sequence_length sequence) member
      apply ih child code
      change (child, code) ∈ (callee, compiler.calleeCode) :: ids.zip compiler.codes
      exact List.mem_cons_of_mem _ paired

/-- Grammar at a reached call comes from its literal Calls path and certificate,
including the leading callee and ordered argument entries. -/
theorem calls_syntax {callFuel : Nat} {callScope : SourceCoreLocalCell.Scope}
    {callId callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {lowered : SourceCoreBasic.LoweredExpr}
    {compiler : CallableIndirectCallCertificates.Receipt policy body callFuel compilation
      source callScope callId callee ids metadata reasonAt lowered}
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    {root : Certificate policy body compilation readFuel values source context
      reasonAt rootScope rootId rootCode}
    (path : Calls compiler root) : Syntax source callId := by
  induction path with
  | here sequence children => exact certificate_syntax (.call compiler sequence children)
  | group _inside ih => exact ih
  | tuple_child _member _inside ih => exact ih
  | call_child _member _inside ih => exact ih

/-- One actual sidecar is chosen outside the universal static call proof.
Each Port comes from the same successful prepareSidecar action, so its sidecar
is identified by constructor injectivity. No execution or body law is used. -/
theorem canonical_calls_ready
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : CallableIndexedNamedGeneration.Named}
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function parameterScope administrative)
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      compiled.indexed named function.source)
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr} {rootType : TypeSystem.Ty}
    (typed : ExpressionHasType function.source context rootId rootType)
    (root : Certificate code.policy code.lowerBody code.compilation compiled.indexed.fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      function.source context code.reasonAt rootScope rootId rootCode) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan code.compilation.owner = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar code.active function) ∧
      CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
        (compiled := compiled) (invocation := RecursiveStageRegistry.scope sidecar code.active function) root := by
  obtain ⟨sidecar, issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code sourceReceipt unique
  refine ⟨sidecar, issued, selected, ?_⟩
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  have syntaxTree := calls_syntax path
  have profile := CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.retained_policy_for
    retained metadata callScope code.reasonAt
  have parentTyped := CallableIndexedOwnedPreparedStagedRecursiveCallerRawTyping.parent_typed
    compiler unique typed path
  obtain ⟨actualSidecar, actualIssued, _actualSelected, port⟩ :=
    CallableIndexedOwnedPreparedStagedCanonicalScopeCallPorts.canonical_scope_port
      code profile syntaxTree compiler parentTyped sourceReceipt unique
  have same : actualSidecar = sidecar := Except.ok.inj (actualIssued.symm.trans issued)
  cases same
  exact port

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalCallsReady
