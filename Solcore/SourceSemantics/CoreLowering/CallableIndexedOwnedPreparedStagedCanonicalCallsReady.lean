import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax
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
open CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax (syntax_child syntax_not_direct)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls Syntax)

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}

/-- The shared certificate admits the complete supported grammar, including
actual direct declaration calls. -/
theorem certificate_syntax {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Certificate policy body compilation readFuel values source context reasonAt scope id lowered) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.OrdinarySyntax compilation.plan source id :=
  CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.certificate_syntax tree

/-- The legacy grammar at a reached call follows its exact original child
path from authentic legacy syntax at the root. Shared certificates alone also
include direct calls, so they do not imply this restricted grammar. -/
theorem calls_syntax {callFuel : Nat} {callScope : SourceCoreLocalCell.Scope}
    {callId callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {lowered : SourceCoreBasic.LoweredExpr}
    {compiler : CallableIndirectCallCertificates.Receipt policy body callFuel compilation
      source callScope callId callee ids metadata reasonAt lowered}
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    {root : Certificate policy body compilation readFuel values source context
      reasonAt rootScope rootId rootCode}
    (path : Calls compiler root) (tree : Syntax source rootId) : Syntax source callId := by
  induction path with
  | here sequence children => exact tree
  | @group scope id node inner innerNode code actual form found sourceType child inside ih =>
    exact ih (syntax_child tree actual.found (by simp [form, ExpressionForm.references]))
  | @tuple_child scope id node tupleIds types codes header sequence children child childCode member inside ih =>
    exact ih (syntax_child tree header.metadata.found (by
      simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @constructor_child scope id node instantiation constructorIds tag headerWord codes header form admissible ranges count nodes sequence children child childCode member inside ih =>
    exact ih (syntax_child tree header.metadata.found (by
      simp [form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @builtin_child scope id otherCallee otherIds function otherFuel code outer calleeTyped sourceType nativeTypes sequence children child childCode member inside ih =>
    exact ih (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.syntax_child tree outer.metadata.found (by
      simp [outer.form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @direct_child scope id otherCallee otherIds instantiation otherFuel code types outer calleeTyped application sequence children child childCode member inside ih =>
    exact False.elim (syntax_not_direct tree outer.metadata.found outer.form)
  | @call_child scope id otherCallee otherIds metadata otherFuel code types outer sequence children child childCode member inside ih =>
    apply ih
    apply syntax_child tree outer.found
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      simp [outer.originalForm, ExpressionForm.references]
    · simp [outer.originalForm, ExpressionForm.references, (List.of_mem_zip remaining).1]
  | @unary_child scope id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType profile child inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @binary_left scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile first second inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @binary_right scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile first second inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @conditional_condition scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @conditional_then scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @conditional_else scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))

  | @index_base scope id node base key baseNode keyNode layout comparison first second header keyFound form sourceType scalar firstTree secondTree inside ih
  | @index_key scope id node base key baseNode keyNode layout comparison first second header keyFound form sourceType scalar firstTree secondTree inside ih =>
    exact False.elim (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.syntax_not_index tree header.metadata.found form)

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
      function.source context code.reasonAt rootScope rootId rootCode)
    (tree : Syntax function.source rootId) :
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
  have syntaxTree := calls_syntax path tree
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
