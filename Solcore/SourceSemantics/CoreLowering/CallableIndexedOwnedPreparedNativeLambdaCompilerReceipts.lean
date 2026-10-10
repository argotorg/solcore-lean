import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCompilerChildren
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalCaptureReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts

/-! One actual raw compiler lambda occurrence produces its native-aware body.
The literal accepted Certificate and independently typed Source row are retained.
Raw enclosing native typing is normalized by the emitted callable constructors;
one Site is then built at the actual Named entry prefix. Its static shell builds
one JointBody through the native compiler traversal, with no separately typed
body or assignment supplier. Ordinary and selected-method callers use their
real Named compilation and evidence. Existing broad collected bodies do not
acquire this receipt. The concrete issuer/static shell producer remains open. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedNativeCompilerChildren
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
  {statements : List StatementId} {reported : Ty} {childFuel : Nat}
  (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
    (context compiled.indexed named) (source named) scope id node parameters result statements reported rootReasonAt lowered)

/-- This positive packet contains the actual chosen Site and one native-aware
body under Type. It is produced only from a literal accepted compiler occurrence. -/
structure Receipt where
  site : Site compiled.indexed named parameters result statements sourceContext evidence []
    scope («prefix» (compiled := compiled) named)
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  policy : site.code.policy = root.selected.policy
  lowerBody : site.code.lowerBody = root.selected.lowerBody
  fuel : site.code.fuel = childFuel
  view : site.code.view = source named
  reason : site.code.reasonAt = rootReasonAt
  sourceNodeEq : site.code.sourceNode = node
  nodeEq : site.code.node = node
  certificateEq : HEq site.code.receipt certificate
  binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy named site.code
  shell : SiteShell (compilation := compilation) expressionSyntax site
  body : JointBody compilation site.code (Program.ofChecked compiled.sourceProgram)
    expressionSyntax (certificates root expressionSyntax («prefix» (compiled := compiled) named)) shell.diagnosticPolicy
    shell.issued.invalidOperand shell.issued.invalidUnary shell.issued.invalidProjection shell.issued.missingDefault
  entry : body.toContext = shell.entry
  readFuel : body.readFuel = shell.readFuel
  sourceFacts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts
    (closure named parameters result statements sourceContext evidence []) id node

/-- The same occurrence builds its literal prefix Site and native JointBody.
The shell callback supplies only actual Source/issuance/policy metadata for the
Site just generated. It cannot supply body typing or any execution theorem. -/
theorem of_certificate
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source named))
    (covers : evidence.Covers sourceContext)
    (found : (source named).lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (sourceTyped : ExpressionHasType (source named) sourceContext id node.type)
    (coercions : node.coercions = [])
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (context compiled.indexed named) (source named) scope id rootReasonAt = .ok lowered)
    {nativeType : Ty}
    (raw : HasType (SourceCoreLocalCell.coreContext scope ++ «prefix» (compiled := compiled) named)
      lowered.expression nativeType compiled.indexed.layouts.definitions)
    (shells : ∀ site : Site compiled.indexed named parameters result statements sourceContext evidence []
        scope («prefix» (compiled := compiled) named),
      site.code.id = id → site.code.lowered = lowered → site.code.policy = root.selected.policy →
      site.code.lowerBody = root.selected.lowerBody → site.code.fuel = childFuel →
      site.code.view = source named → site.code.reasonAt = rootReasonAt →
      Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
        (closure named parameters result statements sourceContext evidence []) →
      Nonempty (SiteShell (compilation := compilation) expressionSyntax site)) :
    Nonempty (Receipt root expressionSyntax certificate
      (sourceContext := sourceContext) (evidence := evidence)) := by
  have native := CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping.certificate_native
    compiled.indexed certificate found root.rawLambdaExpression root.callables raw
  obtain ⟨site, identifier, emitted, policy, lowerBody, fuel, view, reason,
      sourceNode, actualNode, sameCertificate⟩ :=
    CallableIndexedLambdaGeneration.of_certificate compiled.indexed sourceContext evidence [] certificate accepted
      profile (LambdaMetadataViews.MetadataView.refl _) found form found rfl
      root.sourceCells root.rawLambdaBody root.rawLambdaExpression root.callables root.projectType native
  have facts := CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
    (function := closure named parameters result statements sourceContext evidence [])
    runtime.graph.nodeOccurrencesUnique found form sourceTyped coercions
  obtain ⟨shell⟩ := shells site identifier emitted policy lowerBody fuel view reason (facts.frame runtime covers)
  obtain ⟨body, entry, readFuel⟩ :=
    SiteShell.joint root expressionSyntax site shell policy lowerBody reason
  have binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy named site.code :=
    (congrArg SourceCoreFunctions.Policy.lowerBinder policy).trans root.selected.binder
  exact ⟨⟨site, identifier, emitted, policy, lowerBody, fuel, view, reason,
    sourceNode, actualNode, sameCertificate, binderPolicy, shell, body, entry, readFuel, facts⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts
