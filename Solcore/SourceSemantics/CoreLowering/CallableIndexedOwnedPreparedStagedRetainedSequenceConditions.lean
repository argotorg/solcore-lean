import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBodyViewEdits
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaOriginalConditions

/-! Retained compiler policies and reached body metadata supply the actual
sequence conditions. Source declarations and diagnostic attribution are static
facts; body admission comes from the original closure frame and parameter
extension. No execution or called-body law is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRetainedSequenceConditions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableLambdaBodyReachability
open CallableIndexedOwnedContextualLambdaProvenance (BodyView)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor MetadataOn retained_policy_for retained_policy_on)
open CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories (Choice Conditions)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {named : CallableIndexedNamedGeneration.Named} {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (code : Code compiled.indexed function scope administrative)
  (body : CallableIndexedLambdaStaticBodySupport.BodyWith
    (values := .initial compiled.compatible.checked) expressionSyntax certificates code
    (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)

/-- Every proof refers to the same original Code, full Source and entry context. -/
def conditions_on
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (bodyView : BodyView code)
    (original : MetadataFor compiled.indexed named function.source)
    (viewed : MetadataOn compiled.indexed named code.view
      (fun id => Reaches code.view (function.body.map NodeId.statement) (.expression id)))
    (treeSyntax : ∀ id, Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      Syntax code.view id)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      scope function.context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (uninitialized : ∀ current id lowered,
      CompatibleExpressionReads.LoweredRead compiled.indexed.fuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        function.source body.context code.reasonAt current id lowered →
      Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      ∀ location, semanticFaults (.uninitializedLocation location) (code.reasonAt id))
    (choice : Choice code (stages := stages)) : Conditions code body choice where
  readFuel := compiled.indexed.fuel
  changed := CallableIndexedLambdaBodyViewEdits.changed function.source code.view
  edited := by
    intro child selected
    rw [stages.source selected]
    exact CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  avoids := by
    intro child selected
    rw [stages.source selected]
    exact CallableIndexedLambdaBodyViewEdits.avoids bodyView
  sourceProfile := by
    intro child selected
    rw [stages.source selected]
    exact (retained_policy_for retained original _ _).on _
  viewProfile := retained_policy_on retained viewed _ _
  syntaxTree := by
    intro expression child used
    exact treeSyntax expression
      (CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.children_reached
        choice.packet.receipt.tree code.viewOfSource expression child used)
  original := by
    intro child selected
    exact CallableIndexedOwnedPreparedStagedLambdaOriginalConditions.at_selected_scope_on
      code body declarations (fun id node tree found => original.coercions id tree node found)
        wellFormed selected
      (by simpa only [stages.source selected, choice.reason] using uninitialized)

/-- Legacy global metadata and faults specialize to the actual body. -/
def conditions
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (bodyView : BodyView code)
    (original : MetadataFor compiled.indexed named function.source)
    (viewed : MetadataFor compiled.indexed named code.view)
    (treeSyntax : ∀ id, Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      Syntax code.view id)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      scope function.context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (uninitialized : ∀ current id lowered,
      CompatibleExpressionReads.LoweredRead compiled.indexed.fuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        function.source body.context code.reasonAt current id lowered →
      ∀ location, semanticFaults (.uninitializedLocation location) (code.reasonAt id))
    (choice : Choice code (stages := stages)) : Conditions code body choice :=
  conditions_on code body retained bodyView original (viewed.on _)
    treeSyntax declarations wellFormed
    (fun current id lowered receipt _reached => uninitialized current id lowered receipt) choice

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRetainedSequenceConditions
