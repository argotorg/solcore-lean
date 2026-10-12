import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRetainedSequenceConditions
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadMetadata
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics

/-! The actual four-node captured-read factory supplies the whole sequence
family member at any authentic Code. Its compiler policy, view and declarations
are retained static receipts; only the real read diagnostic is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadSequence
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaProvenance (BodyView)
open CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)
open CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds (OrdinarySequence)
open CallableIndexedOwnedPreparedStagedSingleReadMetadata

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  (code : Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))

/-- Full policy/profile and per-scope conditions are constructed from the actual
Source nodes. No caller supplies a child certificate, execution, or body law. -/
def sequence
    (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension
      completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {read lambda : ExpressionNode} {inner outer : StatementNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {name : String} {binder : Resolved.LocalId}
    (nodes : function.source.nodes = [.expression read, .statement inner, .expression lambda, .statement outer])
    (lambdaForm : lambda.form = .lambda parameters result statements)
    (bodyShape : function.body = [inner.id])
    (innerFound : function.source.lookupStatement? inner.id = some inner)
    (innerForm : inner.form = .returnStmt (some read.id))
    (readFound : function.source.lookupExpression? read.id = some read)
    (readForm : read.form = .reference name (.local binder))
    (requirements : read.requirements = []) (coercions : read.coercions = [])
    (locals : compiled.indexed.base.locals.bindings = [])
    (signature : ProgramFunctionSignature)
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (sourceOwner : function.source.owner = signature.id) :
    OrdinarySequence stagePrepared support.caller.named code support.body := by
  let body := support.body
  have retained := provenance.policy_recipe
  have bodyView := provenance.body_view
  have declarations := provenance.scope_declarations
  have reached : Reaches function.source (function.body.map NodeId.statement) (.expression read.id) := by
    rw [bodyShape]
    exact .statement (.root (by simp)) innerFound (by simp [innerForm, StatementForm.references])
  have viewedRead : code.view.lookupExpression? read.id = some read :=
    (bodyView read.id reached).symm.trans readFound
  let original := metadata compiled.indexed support.caller.named (LambdaMetadataViews.MetadataView.refl function.source)
    nodes lambdaForm readFound readForm requirements coercions locals
  let viewed := metadata compiled.indexed support.caller.named code.viewOfSource
    nodes lambdaForm viewedRead readForm requirements coercions locals
  have treeSyntax : ∀ id, Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      Syntax code.view id := by
    intro id actual
    rw [bodyShape] at actual
    have only := reached_node readFound readForm innerFound innerForm actual
    rcases only with impossible | identity
    · cases impossible
    · cases identity
      exact .leaf (.read viewedRead readForm)
  have faults : ∀ current id lowered,
      CompatibleExpressionReads.LoweredRead compiled.indexed.fuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        function.source body.context code.reasonAt current id lowered →
      ∀ location, CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
        (.uninitializedLocation location) (code.reasonAt id) := by
    intro current id lowered receipt location
    have identity := lowered_read_id nodes lambdaForm receipt
    exact CallableIndexedOwnedContextualLambdaReadDiagnostics.uninitialized support
      provenance.body_reasons receiver (identity.symm ▸ reached) receipt location
  exact {
    shape := by
      rw [bodyShape]
      exact .terminal (.returning [] (code.viewOfSource.symm.statement innerFound) innerForm)
    conditions := CallableIndexedOwnedPreparedStagedRetainedSequenceConditions.conditions
      code body retained bodyView original viewed treeSyntax declarations wellFormed faults
    readFuel := fun _ => rfl
    retained := retained
    metadata := original
    signature := signature
    signatureMember := signatureMember
    sourceOwner := sourceOwner }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadSequence
