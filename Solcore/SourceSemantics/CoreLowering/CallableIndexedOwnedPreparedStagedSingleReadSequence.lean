import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRetainedSequenceConditions
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadMetadata
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics

/-! A captured-read body supplies its sequence family member at any authentic
Code. Outer Source expressions may contain other reads; compiler-view metadata
and diagnostics are used only for actual body references. The original Source
policy exclusions remain explicit static facts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadSequence
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaProvenance (BodyView)
open CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor MetadataOn)
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
def sequence_on
    (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension
      completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (original : MetadataFor compiled.indexed support.caller.named function.source)
    {read : ExpressionNode} {inner : StatementNode}
    {name : String} {binder : Resolved.LocalId}
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
  have only_read : ∀ id, Reaches code.view (function.body.map NodeId.statement) (.expression id) →
      id = read.id := by
    intro id path
    have originalPath := path.metadata code.viewOfSource.symm
    rw [bodyShape] at originalPath
    rcases reached_node readFound readForm innerFound innerForm originalPath with impossible | identity
    · cases impossible
    · exact NodeId.expression.inj identity
  let viewed : MetadataOn compiled.indexed support.caller.named code.view
      (fun id => Reaches code.view (function.body.map NodeId.statement) (.expression id)) := {
    requirements := by
      intro id admitted _tree node found
      have same := Option.some.inj (found.symm.trans ((only_read id admitted).symm ▸ viewedRead))
      exact same.symm ▸ requirements
    coercions := by
      intro id admitted _tree node found
      have same := Option.some.inj (found.symm.trans ((only_read id admitted).symm ▸ viewedRead))
      exact same.symm ▸ coercions
    initializer := by intro id admitted tree; simp only [locals, List.find?_nil]
    arguments := by
      intro id admitted _tree node found callee ids actual form
      have same := Option.some.inj (found.symm.trans ((only_read id admitted).symm ▸ viewedRead))
      subst node
      rw [readForm] at form
      cases form
    localRead := by intro id admitted tree node found name binder form; simp only [locals, List.any_nil] }
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
      Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      ∀ location, CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
        (.uninitializedLocation location) (code.reasonAt id) := by
    intro current id lowered receipt actual location
    exact CallableIndexedOwnedContextualLambdaReadDiagnostics.uninitialized support
      provenance.body_reasons receiver actual receipt location
  exact {
    shape := by
      rw [bodyShape]
      exact .terminal (.returning [] (code.viewOfSource.symm.statement innerFound) innerForm)
    conditions := CallableIndexedOwnedPreparedStagedRetainedSequenceConditions.conditions_on
      code body retained bodyView original viewed treeSyntax declarations wellFormed faults
    readFuel := fun _ => rfl
    retained := retained
    metadata := original
    signature := signature
    signatureMember := signatureMember
    sourceOwner := sourceOwner }

/-- The earlier four-node producer specializes the reached-body construction. -/
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
    OrdinarySequence stagePrepared support.caller.named code support.body :=
  sequence_on stagePrepared code support provenance receiver wellFormed
    (metadata compiled.indexed support.caller.named (LambdaMetadataViews.MetadataView.refl function.source)
      nodes lambdaForm readFound readForm requirements coercions locals)
    bodyShape innerFound innerForm readFound readForm requirements coercions locals
    signature signatureMember sourceOwner

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadSequence
