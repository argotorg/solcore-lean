import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaBodyNativeInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBodyViewEdits

/-! Original typed closure syntax and the retained compiler callback produce
a branching packet for the same Code. Every child keeps the current lexical
context, exact accepted callback and native typing. No execution law is stored. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching BranchingSupport parameterScope)
open CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
  {stages : Staging.Recursive.Registry} (choice : Choice code (stages := stages))

include frame in
/-- The complete native body supplies local typing; authentic metadata views
and binder receipts recover the original Source tree without changing code. -/
theorem collected
    (view : CallableIndexedOwnedContextualLambdaProvenance.BodyView code)
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context)
    (sourceSignatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (hidden : GenericImperativeMatch.MatchHiddenFresh function.source)
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
    (ledger : inputs.context.solvedRequirements = code.compilation.solvedRequirements)
    (projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {faults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs function.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator
        (choice.invalidOperand site assignment.target.root operator))
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (syntaxTree : GenericImperativeMatch.Syntax function.source expressionSyntax
      inputs.context (.statements true function.body) function.resultType)
    (children : ∀ context, Dynamic.RuntimeContextFields inputs.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations function.source scope context →
      expressionSyntax id → Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      function.source.lookupExpression? id = some node → ExpressionHasType function.source context id node.type →
      choice.packet.policy.lowerExpression fuel code.view scope id choice.packet.reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType compiled.indexed.layouts.definitions → certificates context scope id lowered) :
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected (faults := faults) compiled.indexed.layouts choice.packet.allocationOwner choice.packet.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length choice.packet.onError
      (.initial compiled.compatible.checked) function.source expressionSyntax
      (TypedCertificate function.source certificates) compiled.indexed.layouts.definitions administrative
      inputs.context (parameterScope code) (.statements true function.body) function.resultType code.receipt.resultCore choice.packet.flow := by
  let changed := CallableIndexedLambdaBodyViewEdits.changed function.source code.view
  have edited : LocalView function.source code.view changed := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have native := CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native code
  rw [choice.packet.emitted] at native
  obtain ⟨nativeType, native⟩ := TypedLexicalWhile.Native.finished_flow native
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_parameters (values := .initial compiled.compatible.checked) code inputs frame captured
  exact CallableIndexedOwnedPreparedNativeBranchingCollectors.collected edited
    (CallableIndexedLambdaBodyViewEdits.avoids view) frame.code.graph.nodeOccurrencesUnique
    choice.readPolicy choice.binderPolicy choice.allocationPolicy choice.assignments operands
    choice.matchPolicy choice.matchValues choice.matchDefinitions choice.matchAllocator hidden catalog
    (ledger.trans choice.matchLedger.symm) children
    syntaxTree rfl choice.packet.shape (.refl _) runtime.variables_closed runtime.residual_variables_open sourceSignatures
    declarations (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩)) projection choice.packet.accepted native

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport
