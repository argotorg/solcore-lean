import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaFormation

/-! One accepted contextual compiler call chooses the ordinary lambda Site.
Its dependent static inputs build the joint body at that same Site and factory.
The runtime prefix and public population of these static inputs remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedOrdinaryLambdaFormation
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericImperativeMatch

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The finite contextual inversion retains the actual policy and body lowerer.
It does not select a Site or certify execution of the body. -/
structure ContextualPolicyReceipt (named : Named)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (fuel : Nat) (view : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
    (context compiled.indexed named) view scope id reasonAt = .ok lowered
  binder : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
    ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.locals named.signature.key []
  recipe : lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
    ((representation compiled.indexed).atContext named.signature.key [])
    (context compiled.indexed named).solvedRequirements compilation.own.assignments diagnostics
    (context compiled.indexed named).owner
    (SourceCoreGeneralFunctions.contextualBinder
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.locals named.signature.key [])

/-- Only the original contextual bind is eliminated; the recursive compiler
callback and its minimum budget stay inside the selected policy. -/
theorem ContextualPolicyReceipt.of_accepted
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered) :
    Nonempty (ContextualPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation fuel view scope id reasonAt lowered) := by
  rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  dsimp only at accepted
  change (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key |>.mapError SourceCoreBasic.Error.callPreparation) >>= _ = .ok lowered at accepted
  rw [record] at accepted
  simp only [Except.mapError, bind, Except.bind] at accepted
  exact ⟨⟨_, _, accepted, rfl, rfl⟩⟩

section ChosenSite
variable (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- Every static field is indexed by this literal chosen Produced value.
There is no completed joint body or formation semantics among these inputs. -/
structure SiteInputs
    (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered) where
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  entry : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) produced.site.code
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
    (closure caller.named parameters result statements sourceContext evidence [])
  readFuel : Nat
  changed : List ExpressionId
  edited : LocalView (source caller.named) produced.site.code.view changed
  avoids : Avoids (source caller.named) (statements.map NodeId.statement) changed
  unique : NodeOccurrencesUnique (source caller.named)
  sameLedger : sourceContext.solvedRequirements = produced.site.code.compilation.solvedRequirements
  syntaxTransport : ∀ id, Reaches (source caller.named) (statements.map NodeId.statement) (.expression id) →
    expressionSyntax produced.site.code.view id → expressionSyntax (source caller.named) id
  expressions : ∀ context scope id lowered,
    Reaches (source caller.named) (statements.map NodeId.statement) (.expression id) →
    certificates readFuel produced.site.code.view context scope id lowered →
    certificates readFuel (source caller.named) context scope id lowered
  syntaxTree : Syntax (source caller.named) (expressionSyntax (source caller.named))
    entry.context (.statements true statements) result
  viewSyntax : Syntax produced.site.code.view (expressionSyntax produced.site.code.view)
    entry.context (.statements true statements) result
  projection : compiled.compatible.checked.catalog.project result = .ok produced.site.code.receipt.resultCore
  residualMode : Bool
  static : ExtractionInputs (layouts := compiled.indexed.layouts) (owner := produced.site.code.compilation.owner)
    (active := produced.site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
    (globals := compiled.indexed.base.globals.length) (onError := produced.site.code.allocationError)
    (values := .initial compiled.compatible.checked) (source := produced.site.code.view)
    (expressionSyntax := expressionSyntax produced.site.code.view) (certificates := certificates readFuel produced.site.code.view)
    (reasonAt := produced.site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions)
    (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    (invalidOperand := issued.invalidOperand) (invalidUnary := issued.invalidUnary)
    (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
    residualMode (bodyPolicy produced.compilation produced.site.code) entry.context
    (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
  nativeTyped : HasType (SourceCoreLocalCell.coreContext
      (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    produced.site.code.receipt.body (LanguageResult.resultType produced.site.code.receipt.resultCore)
    compiled.indexed.layouts.definitions

/-- The genuine Source lookup fixes the selected raw node. No erased Code
field is recovered from an equality between certificate proofs. -/
theorem Produced.source_node {sourceNode : ExpressionNode}
    (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)
    (found : (source caller.named).lookupExpression? id = some sourceNode) :
    produced.site.code.sourceNode = sourceNode := by
  have actual : (source caller.named).lookupExpression? id = some produced.site.code.sourceNode := by
    simpa only [produced.identifier, CallableIndexedLambdaGeneration.closure] using produced.site.code.sourceFound
  exact Option.some.inj (actual.symm.trans found)

/-- The chosen formation keeps the input named compilation as well as the
chosen Site's factory. These equalities are literal constructor receipts. -/
structure Receipt (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation compiled.indexed caller.named diagnostics namedCode)
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  formation : Formation caller sourceContext evidence scope id lowered
  diagnostics_eq : formation.produced.diagnostics = diagnostics
  namedCode_eq : formation.produced.namedCode = namedCode
  compilation_eq : HEq formation.produced.compilation compilation

/-- One actual contextual producer chooses the Site. Its dependent inputs
then run the existing static collector and canonical transport at that Site. -/
theorem receipt_of_contextual
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed caller.named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan caller.named.signature.key = .ok caller.named.specialized)
    {fuel : Nat} {view : TypedSource} {sourceNode node : ExpressionNode} {reported : Ty}
    {reasonAt : ExpressionId → Word}
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source caller.named) view)
    (sourceFound : (source caller.named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result statements)
    (rawType : sourceNode.type = FunctionValues.sourceType
      (closure caller.named parameters result statements sourceContext evidence []))
    (rawOrdinary : Dynamic.OrdinaryRequirementLayout sourceNode.requirements sourceNode.coercions [])
    (rawCoercions : sourceNode.coercions = [])
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext caller.named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed caller.named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      lowered.expression (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions)
    (siteInputs : ∀ produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered,
      produced.diagnostics = diagnostics → produced.namedCode = namedCode → HEq produced.compilation compilation →
      Nonempty (SiteInputs caller produced)) :
    Nonempty (Receipt caller diagnostics namedCode compilation sourceContext evidence scope id lowered) := by
  obtain ⟨site, identifier, emitted, binderPolicy, recipe⟩ := CallableIndexedLambdaGeneration.of_contextual_with_body_recipe
    compiled.indexed compilation record sourceContext evidence [] profile viewOfSource sourceFound sourceForm
    found form owner requirements coercions ordinary read accepted typed
  let produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered :=
    ⟨diagnostics, namedCode, compilation, site, identifier, emitted, binderPolicy, recipe⟩
  obtain ⟨inputs⟩ := siteInputs produced rfl rfl (HEq.refl compilation)
  obtain ⟨body, _entry, _readFuel⟩ := at_site produced.compilation produced.site produced.recipe
    (Program.ofChecked compiled.sourceProgram) inputs.entry inputs.frame inputs.expressionSyntax inputs.certificates
    inputs.readFuel inputs.diagnosticPolicy inputs.issued.invalidOperand inputs.issued.invalidUnary
    inputs.issued.invalidProjection inputs.issued.missingDefault inputs.edited inputs.avoids inputs.unique
    inputs.sameLedger inputs.syntaxTransport inputs.expressions inputs.syntaxTree inputs.viewSyntax inputs.projection
    inputs.static inputs.nativeTyped
  have nodeEq := Produced.source_node caller produced sourceFound
  let formation : Formation caller sourceContext evidence scope id lowered := {
    parameters := parameters, result := result, statements := statements, produced := produced
    expressionSyntax := inputs.expressionSyntax, certificates := inputs.certificates, issued := inputs.issued
    diagnosticPolicy := inputs.diagnosticPolicy, body := body
    sourceType := nodeEq ▸ rawType, ordinary := nodeEq ▸ rawOrdinary, coercions := nodeEq ▸ rawCoercions }
  exact ⟨⟨formation, rfl, rfl, HEq.refl compilation⟩⟩

/-- A finite projection forgets only the input compilation identities. -/
theorem formation_of_receipt
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
    (receipt : Receipt caller diagnostics namedCode compilation sourceContext evidence scope id lowered) :
    Nonempty (Formation caller sourceContext evidence scope id lowered) := ⟨receipt.formation⟩

end ChosenSite
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
