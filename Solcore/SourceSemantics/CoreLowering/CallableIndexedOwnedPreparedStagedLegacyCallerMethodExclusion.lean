import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax

/-! Legacy policy hooks decline operator methods at the actual reached Source
occurrences. These facts are derived from compiler receipts, not execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}

private theorem method_calls_legacy_syntax {callFuel : Nat} {callScope : SourceCoreLocalCell.Scope}
    {callId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt policy body callFuel compilation
      values source callScope callId reasonAt lowered}
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    {root : Certificate policy body compilation readFuel values source context
      reasonAt rootScope rootId rootCode}
    (path : MethodCalls compiler root) (tree : Syntax source rootId) : Syntax source callId := by
  induction path with
  | here sequence children => exact tree
  | @method_child scope id otherFuel code types outer sequence children child childCode member inside ih =>
    exact ih (syntax_child tree outer.metadata.found (outer.argument_references (List.of_mem_zip member).1))
  | @group scope id node inner innerNode code actual form found sourceType child inside ih =>
    exact ih (syntax_child tree actual.found (by simp [form, ExpressionForm.references]))
  | @tuple_child scope id node tupleIds types codes header sequence children child childCode member inside ih =>
    exact ih (syntax_child tree header.metadata.found (by
      simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @constructor_child scope id node instantiation constructorIds tag headerWord codes header form admissible ranges count nodes sequence children child childCode member inside ih =>
    exact ih (syntax_child tree header.metadata.found (by
      simp [form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @builtin_child scope id otherCallee otherIds function otherFuel code outer calleeTyped sourceType nativeTypes sequence children child childCode member inside ih =>
    exact ih (syntax_child tree outer.metadata.found (by
      simp [outer.form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @direct_child scope id otherCallee otherIds instantiation otherFuel code types outer calleeTyped application sequence children child childCode member inside ih =>
    exact False.elim (no_direct_of_syntax _ tree outer (.here calleeTyped application sequence children))
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
    exact False.elim (no_indexes_of_syntax _ tree header keyFound form sourceType scalar (.here firstTree secondTree))


theorem no_methods_of_policy_on {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel values source context reasonAt scope id lowered)
    (tree : Syntax source id) {roots : List NodeId}
    (reached : CallableLambdaBodyReachability.Reaches source roots (.expression id))
    (profile : PolicyOn policy compilation readFuel values source scope reasonAt
      (fun child => CallableLambdaBodyReachability.Reaches source roots (.expression child))) : NoMethods root := by
  intro fuel callScope callId callCode compiler path
  have syntaxTree := method_calls_legacy_syntax path tree
  have scopeEq := method_calls_scope path
  have bypass := profile.special callId (method_calls_reached path reached) syntaxTree
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation) (fuel + 1)
  rw [← scopeEq] at bypass
  have impossible := compiler.special.symm.trans bypass
  cases impossible

theorem no_methods_of_policy {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel values source context reasonAt scope id lowered)
    (tree : Syntax source id)
    (profile : PolicyFor policy compilation readFuel values source scope reasonAt) : NoMethods root :=
  no_methods_of_policy_on root tree (.root (by simp))
    (profile.on (fun child => CallableLambdaBodyReachability.Reaches source [.expression id] (.expression child)))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax
