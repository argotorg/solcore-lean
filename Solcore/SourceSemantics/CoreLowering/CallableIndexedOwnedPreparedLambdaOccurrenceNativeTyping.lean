import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
import Solcore.SourceSemantics.CoreLowering.ActualCallablePolicy

/-! Native inversion at an actual emitted compiler occurrence initially gives
an existential result type. The genuine lambda hook and callable decoration fix
that type through their literal annotations. This normalization retains the
original accepted certificate and native context; it constructs no Source
lookup, Source typing, selected implementation or body execution law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping
open Core Frontend SourceInference
open CallableIndexedLambdaCertificates

private theorem descriptor_exists (table : SourceCoreStageCodebook.Table)
    {origin : SourceCoreStageCodebook.Origin} {id : Word}
    (selected : table.idAt? origin = some id) :
    Nonempty (SourceCoreCallableContracts.Descriptor table origin) := by
  cases accepted : SourceCoreCallableContracts.descriptor table origin with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at accepted
    split at accepted
    · rename_i absent
      rw [selected] at absent
      cases absent
    · cases accepted
  | ok descriptor => exact ⟨descriptor⟩

/-- The selected snapshot has literal lambda annotations. Any typing of that
same expression fixes its result; no second expected typing is assumed. -/
theorem snapshot_result {definitions : DataEnvironment} {context : Core.Context}
    (table : SourceCoreCallableIndexedDispatch.Table) (layout : SourceCoreCallableIndexedFrames.Layout)
    (origin : Word) (referenceIndex : Nat) (parameter result : Ty) (body : Expr)
    {nativeType : Ty}
    (typed : HasType context
      (SourceCoreCallableIndexedAncestry.snapshotLambda table layout origin referenceIndex parameter result body)
      nativeType definitions) :
    nativeType = .function parameter (LanguageResult.resultType result) := by
  cases typed with
  | letE _ closure =>
    cases closure
    rfl

/-- The actual anonymous identity and descriptor word remain in their
original product order. Constructor inversion fixes the full result type. -/
theorem decorated_snapshot_result {definitions : DataEnvironment} {context : Core.Context}
    {table : SourceCoreStageCodebook.Table} {origin : SourceCoreStageCodebook.Origin}
    (descriptor : SourceCoreCallableContracts.Descriptor table origin)
    (dispatch : SourceCoreCallableIndexedDispatch.Table) (layout : SourceCoreCallableIndexedFrames.Layout)
    (selected : Word) (referenceIndex : Nat) (parameter result : Ty) (body : Expr)
    {nativeType : Ty}
    (typed : HasType context
      (LanguageResult.success (descriptor.wrap (TaggedFunction.anonymous
        (SourceCoreCallableIndexedAncestry.snapshotLambda dispatch layout selected referenceIndex parameter result body))))
      nativeType definitions) :
    nativeType = LanguageResult.resultType (CallableContract.functionType parameter result) := by
  cases typed with
  | inRight _ wrapped =>
    cases wrapped with
    | pair tagged contract =>
      cases contract
      cases tagged with
      | pair identity closure =>
        cases identity with
        | inLeft _ unit =>
          cases unit
          have same := snapshot_result dispatch layout selected referenceIndex parameter result body closure
          cases same
          rfl

/-- One authentic compiler lambda certificate normalizes the raw child
typing obtained from its actual enclosing body. Descriptor existence is derived
from that hook's selected codebook row, before any Code/Site is constructed. -/
theorem certificate_native {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered)
    (found : view.lookupExpression? id = some node)
    (expressionHook : policy.rawLambdaExpression =
      SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry compilation.owner [])
    (callables : policy.callables =
      SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    {nativeContext : Core.Context} {nativeType : Ty}
    (typed : HasType nativeContext lowered.expression nativeType prepared.layouts.definitions) :
    HasType nativeContext lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions := by
  obtain ⟨origin, body, selected, _raw, _owner, _globals, _source, emitted⟩ :=
    CallableIndexedFormation.expressionHook_receipt prepared.ancestry (expressionHook ▸ receipt.expressionHook)
  rw [(lookupExpression?_sound found).2] at selected
  obtain ⟨descriptor⟩ := descriptor_exists _ selected
  have decorated := receipt.decoration
  rw [callables, ActualCallablePolicy.lambda_decoration _ [] compilation view node id
    receipt.parameterCore receipt.resultCore _ descriptor] at decorated
  have sameExpression := Except.ok.inj decorated
  have rawTyped : HasType nativeContext receipt.expression nativeType prepared.layouts.definitions := by
    simpa only [receipt.emitted] using typed
  rw [← sameExpression, emitted] at rawTyped
  have exactType := decorated_snapshot_result descriptor prepared.ancestry.graph.table prepared.ancestry.layout.frame
    origin (SourceCoreCallableIndexedAncestry.creationReferenceIndex compilation scope)
    receipt.parameterCore receipt.resultCore body rawTyped
  have checkedType := receipt.checked
  rw [callables] at checkedType
  unfold SourceCoreBasic.ensureType at checkedType
  split at checkedType
  · rename_i reportedType
    change reported = CallableContract.functionType receipt.parameterCore receipt.resultCore at reportedType
    have expected : nativeType = LanguageResult.resultType lowered.type := by
      simpa only [receipt.emitted, reportedType] using exactType
    exact expected ▸ typed
  · cases checkedType

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping
