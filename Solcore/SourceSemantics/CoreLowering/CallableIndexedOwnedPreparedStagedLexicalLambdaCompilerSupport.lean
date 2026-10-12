import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaBodyNativeInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalContextCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBodyViewEdits
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBodyTree

/-! Actual closure flow compilation supplies each child at its genuine lexical
context. Reached-only metadata transports the same allocations and native code
back to original Source. Child factories receive compiler and typing facts only. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Lexical LexicalSupport parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedLexicalContextCertificates

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
  {stages : Staging.Recursive.Registry} (choice : Choice code (stages := stages))

/-- Static declarations are insensitive to the exact allowed metadata edit. -/
theorem scope_declarations {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    (declared : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations view scope context := by
  intro binder original index type found root
  exact declared binder original index type found (by simpa only [rootBinder metadata] using root)

include frame in
/-- Native typing is inverted from the actual lambda once. Each expression
factory sees its original typed node, accepted view callback and real context. -/
theorem tree
    (view : CallableIndexedOwnedContextualLambdaProvenance.BodyView code)
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context)
    (sourceSignatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (syntaxTree : GenericLexicalStatements.Syntax function.source expressionSyntax
      inputs.context true function.body function.resultType)
    (children : ∀ context, Dynamic.RuntimeContextFields inputs.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations function.source scope context →
      expressionSyntax id → Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      function.source.lookupExpression? id = some node → ExpressionHasType function.source context id node.type →
      choice.packet.policy.lowerExpression fuel code.view scope id choice.packet.reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType compiled.indexed.layouts.definitions → certificates context scope id lowered) :
    GenericLexicalStatements.Tree compiled.indexed.layouts choice.packet.allocationOwner choice.packet.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length choice.packet.onError
      (.initial compiled.compatible.checked) function.source
      (TypedCertificate function.source certificates)
      inputs.context (parameterScope code) true function.body function.resultType code.receipt.resultCore choice.packet.flow := by
  let changed := CallableIndexedLambdaBodyViewEdits.changed function.source code.view
  have edited : LocalView function.source code.view changed := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have avoids := CallableIndexedLambdaBodyViewEdits.avoids view
  have unique := frame.code.graph.nodeOccurrencesUnique
  have viewedSyntax := CallableLambdaViewSourceTyping.lexical_syntax_with edited avoids unique
    (fun _ _ original => original) syntaxTree
    (fun id member => Reaches.root (List.mem_map.mpr ⟨id, member, rfl⟩))
  have reverse : LocalView code.view function.source changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  have native := CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native code
  rw [choice.packet.emitted] at native
  obtain ⟨nativeType, native⟩ := TypedLexicalWhile.Native.finished_flow native
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_parameters (values := .initial compiled.compatible.checked) code inputs frame captured
  have extracted := CallableIndexedOwnedPreparedNativeLexicalCollectors.tree_of_typed_flow_with_residual true
    (values := .initial compiled.compatible.checked)
    choice.readPolicy choice.binderPolicy choice.allocationPolicy
    (certificates := fun context scope id lowered => Dynamic.RuntimeContextFields inputs.context context →
      Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      TypedCertificate function.source certificates context scope id lowered)
    (fun context _closed _residual _signatures scope fuel id node lowered declarations syntaxValue found typed accepted nativeType childTyped fields reached => by
      have originalFound : function.source.lookupExpression? id = some node :=
        (expression_lookup edited avoids reached).trans found
      have originalTyped := CallableLambdaViewStaticTyping.expression_original edited avoids unique typed reached
      exact ⟨node, originalFound, originalTyped,
        children context fields (scope_declarations code.viewOfSource.symm declarations)
          syntaxValue reached originalFound originalTyped accepted childTyped⟩)
    viewedSyntax runtime.variables_closed runtime.residual_variables_open sourceSignatures
    (scope_declarations code.viewOfSource declarations) projection choice.packet.accepted native
  have discharged := Tree.discharge_context extracted (.refl _)
  exact CallableLambdaViewBodyTree.body reverse (avoids.view edited.metadata)
    (fun _ _ id _ reached child => child (reached.metadata edited.metadata.symm)) discharged

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerSupport
