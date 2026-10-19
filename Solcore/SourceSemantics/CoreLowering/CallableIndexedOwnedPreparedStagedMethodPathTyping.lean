import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerRawTyping
/-! Recover original method-parent typing along an authentic certificate path. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodPathTyping
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate MethodCalls)

private theorem typed_at_lookup {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) :
    ExpressionHasType source context id node.type := by
  obtain ⟨actual, contains, stored⟩ := typed.stored_type
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst actual
  exact stored ▸ typed

private theorem row_member {source : TypedSource} {context : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes source context ids types)
    {id : ExpressionId} (member : id ∈ ids) :
    ∃ type, ExpressionHasType source context id type := by
  induction ids generalizing types with
  | nil => cases member
  | cons head tail ih =>
    cases typed with
    | cons headTyped tailTyped =>
      rcases List.mem_cons.mp member with same | remaining
      · subst id; exact ⟨_, headTyped⟩
      · exact ih tailTyped remaining

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
  {callFuel : Nat} {callScope : SourceCoreLocalCell.Scope}
  {callId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
    policy body callFuel compilation values source callScope callId reasonAt lowered)

theorem parent_typed
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    {root : Certificate policy body compilation readFuel values source context
      reasonAt rootScope rootId rootCode}
    {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context rootId type)
    (path : MethodCalls compiler root) :
    ExpressionHasType source context callId compiler.node.type := by
  induction path generalizing type with
  | here sequence children =>
    exact typed_at_lookup unique compiler.metadata.found typed
  | @method_child scope id otherFuel code types outer sequence children child childCode member inside ih =>
    have originalTyped := typed_at_lookup unique outer.metadata.found typed
    obtain ⟨rawTypes, childrenTyped⟩ := outer.arguments_typed unique originalTyped
    obtain ⟨childType, childTyped⟩ := row_member childrenTyped (List.of_mem_zip member).1
    exact ih childTyped
  | @group scope id node inner innerNode code actual form found sourceType child inside ih =>
    have originalTyped := typed_at_lookup unique actual.found typed
    obtain ⟨actualInner, childFound, sameType, childTyped⟩ :=
      CompatibleExpressionProducts.group_source_types
        unique actual.found form actual.coercions originalTyped
    exact ih childTyped
  | @tuple_child scope id node tupleIds types codes header sequence children
      child childCode member inside ih =>
    have originalTyped := typed_at_lookup unique header.metadata.found typed
    obtain ⟨rawTypes, childrenTyped, sameType⟩ :=
      CompatibleExpressionTuples.source_types unique header.metadata.found
        header.form header.metadata.coercions originalTyped
    obtain ⟨childType, childTyped⟩ :=
      row_member childrenTyped (List.of_mem_zip member).1
    exact ih childTyped
  | @constructor_child scope id node instantiation constructorIds tag headerWord codes header form admissible ranges count nodes sequence children child childCode member inside ih =>
    have originalTyped := typed_at_lookup unique header.metadata.found typed
    obtain ⟨_admissible, childrenTyped, _sameType⟩ :=
      CompatibleExpressionConstructors.constructor_source_types unique header.metadata.found
        form header.metadata.coercions originalTyped
    obtain ⟨childType, childTyped⟩ := row_member childrenTyped (List.of_mem_zip member).1
    exact ih childTyped
  | @builtin_child scope id otherCallee otherIds function otherFuel code
      outer calleeTyped sourceType nativeTypes sequence children child childCode member inside ih =>
    have originalTyped := typed_at_lookup unique outer.metadata.found typed
    obtain ⟨_callee, argumentsTyped, _sourceType⟩ :=
      CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.source_types
        unique outer.metadata.found outer.form outer.metadata.coercions originalTyped
    obtain ⟨childType, childTyped⟩ := row_member argumentsTyped (List.of_mem_zip member).1
    exact ih childTyped
  | @direct_child scope id otherCallee otherIds otherInstantiation otherFuel code types
      outer calleeTyped application sequence children child childCode member inside ih =>
    have originalTyped := typed_at_lookup unique outer.metadata.found typed
    obtain ⟨rawTypes, _callee, _application, argumentsTyped⟩ :=
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types
        unique outer.metadata.found outer.form outer.metadata.coercions originalTyped
    obtain ⟨childType, childTyped⟩ := row_member argumentsTyped (List.of_mem_zip member).1
    exact ih childTyped
  | @call_child scope id otherCallee otherIds otherMetadata otherFuel code types
      outer sequence children child childCode member inside ih =>
    obtain ⟨parameter, result, rawTypes, calleeTyped, argumentsTyped, application⟩ :=
      CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts
        unique outer.found outer.originalForm typed
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      exact ih calleeTyped
    · obtain ⟨childType, childTyped⟩ :=
        row_member argumentsTyped (List.of_mem_zip remaining).1
      exact ih childTyped

  | @unary_child scope id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType profile child inside ih =>
    have originalTyped := typed_at_lookup unique metadata.found typed
    obtain ⟨actualChild, actualCore, childFound, childTyped, actualProfile⟩ :=
      CompatibleExpressionPrimitives.unary_source_types unique metadata.found form
        metadata.coercions metadata.requirements originalTyped
    exact ih childTyped
  | @binary_left scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile first second inside ih =>
    have originalTyped := typed_at_lookup unique metadata.found typed
    obtain ⟨actualLeft, actualRight, actualMode, firstFound, secondFound, sameType, leftTyped, rightTyped, actualProfile⟩ :=
      CompatibleExpressionPrimitives.binary_source_types unique metadata.found form
        metadata.coercions metadata.requirements originalTyped
    exact ih leftTyped
  | @binary_right scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile first second inside ih =>
    have originalTyped := typed_at_lookup unique metadata.found typed
    obtain ⟨actualLeft, actualRight, actualMode, firstFound, secondFound, sameType, leftTyped, rightTyped, actualProfile⟩ :=
      CompatibleExpressionPrimitives.binary_source_types unique metadata.found form
        metadata.coercions metadata.requirements originalTyped
    exact ih rightTyped
  | @conditional_condition scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    have originalTyped := typed_at_lookup unique metadata.found typed
    obtain ⟨actualCondition, actualThen, actualElse, firstFound, secondFound, thirdFound,
        firstType, secondType, thirdType, conditionTyped, thenTyped, elseTyped⟩ :=
      CompatibleExpressionConditionals.conditional_source_types unique metadata.found form
        metadata.coercions originalTyped
    exact ih conditionTyped
  | @conditional_then scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    have originalTyped := typed_at_lookup unique metadata.found typed
    obtain ⟨actualCondition, actualThen, actualElse, firstFound, secondFound, thirdFound,
        firstType, secondType, thirdType, conditionTyped, thenTyped, elseTyped⟩ :=
      CompatibleExpressionConditionals.conditional_source_types unique metadata.found form
        metadata.coercions originalTyped
    exact ih thenTyped
  | @conditional_else scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    have originalTyped := typed_at_lookup unique metadata.found typed
    obtain ⟨actualCondition, actualThen, actualElse, firstFound, secondFound, thirdFound,
        firstType, secondType, thirdType, conditionTyped, thenTyped, elseTyped⟩ :=
      CompatibleExpressionConditionals.conditional_source_types unique metadata.found form
        metadata.coercions originalTyped
    exact ih elseTyped

  | @index_base scope id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree inside ih =>
    have originalTyped := typed_at_lookup unique header.metadata.found typed
    obtain ⟨keyType, baseTyped, keyTyped⟩ := CompatibleExpressionIndices.index_source_types
      unique header.metadata.found form header.metadata.coercions originalTyped
    exact ih baseTyped
  | @index_key scope id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree inside ih =>
    have originalTyped := typed_at_lookup unique header.metadata.found typed
    obtain ⟨keyType, baseTyped, keyTyped⟩ := CompatibleExpressionIndices.index_source_types
      unique header.metadata.found form header.metadata.coercions originalTyped
    exact ih keyTyped

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodPathTyping
