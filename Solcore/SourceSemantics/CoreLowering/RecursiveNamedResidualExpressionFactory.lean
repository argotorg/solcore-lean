import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedRows

/-! Real declaration scopes keep their residual flag. Full closed raw ranges
supply only source instantiation validity; actual compiler receipts supply the
existing recursive expression Tree. Static source admission, full inventory
coverage, source typing and diagnostic interpretation remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedResidualExpressionFactory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates
open CompatibleExpressionInstantiationLaws
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

section Expressions
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}

/-- SourceTypes depends on signature rows, not lexical bindings or the residual
flag. Raw parameter/result identities and retained evidence are unchanged. -/
theorem sourceTypes_at {initial target : SourceSemantics.Context}
    (same : target.signatures = initial.signatures) (types : SourceTypes headers initial) :
    SourceTypes headers target := by
  refine ⟨?_, ?_, types.projections, types.evidence⟩
  · intro header member signature declared selected
    exact types.parameters header member signature (same ▸ declared) selected
  · intro header member signature declared selected
    exact types.result header member signature (same ▸ declared) selected

theorem tree_of_contextual_of_ranges
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : SourceCoreGeneralFunctions.CallableContext}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    {caller : SourceSpecialization.SpecializedFunction}
    (admission : Admission source admitted) (coverage : Coverage headers compilation)
    (sourceTypes : SourceTypes headers sourceContext)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary source locals compilation.owner admitted)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (unique : NodeOccurrencesUnique source)
    (lexical : sourceContext.typeVariables = [])
    (constructorRanges : ConstructorRanges source
      (fun id => admitted id ∨ CompatibleExpressionBuiltins.Syntax source id))
    (declarationRanges : DeclarationRanges source admitted)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (sourceSignatures : sourceContext.signatures = values.checked.signatures)
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures locals parents assignments
      diagnostics compilation (some native) none skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source sourceContext compilation.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_contextual_with_validity
    (checkedProgram := checkedProgram)
    (representation := representation)
    (signatures := signatures)
    (locals := locals)
    (parents := parents)
    (assignments := assignments)
    (diagnostics := diagnostics)
    (native := native)
    (skipInitializer := skipInitializer)
    (fuel := fuel)
    (readFuel := readFuel)
    (source := source)
    (scope := scope)
    (id := id)
    (node := node)
    (reasonAt := reasonAt)
    (lowered := lowered)
    (sourceContext := sourceContext)
    (admitted := admitted)
    (caller := caller)
    (admission := admission)
    (coverage := coverage)
    (sourceTypes := sourceTypes)
    (order := order)
    (ordinary := ordinary)
    (callerSelected := callerSelected)
    (callerClosed := callerClosed)
    (unique := unique)
    (declarations := declarations)
    (sourceSignatures := sourceSignatures)
    (allowed := allowed)
    (found := found)
    (typed := typed)
    (readPolicy := readPolicy)
    (lowerPolicy := lowerPolicy)
    (leafPolicy := leafPolicy)
    (accepted := accepted)
    (constructorValid := ConstructorLaw.of_ranges lexical (constructorRanges.restrict (fun _ allowed => Or.inl allowed)))
    (fragmentValid := ConstructorLaw.of_ranges lexical (constructorRanges.restrict (fun _ allowed => Or.inr allowed)))
    (declarationValid := DeclarationLaw.of_ranges lexical declarationRanges)

end Expressions

variable (cached : SourceCoreUnifiedCompilation.Compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare cached = .ok recipe)
  (rows : List LambdaRow)
  (cachedRows : cached.indexed.secondPass.closures = rows.map LambdaRow.expression)
  (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
    cached.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
  (member : nativeEntry ∈ cached.indexed.entries)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (definitions : ambient.definitions = cached.indexed.layouts.definitions)
  {headers : Inventory cached.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {header : Header cached.indexed.ancestry values ambient.definitions program}
  (sameCache : header.compiled.closures = cached.indexed.secondPass.closures)
  (complete : Complete headers) (globals : header.globals = cached.indexed.base.globals.length)
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)


variable {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}


/-- The same actual contextual compiler is used at every lexical child scope.
Only signature-dependent source rows move between scopes. The original ledger,
raw instantiations, admission domains and stored node identities remain fixed. -/
theorem expressions
    {checkedProgram : CheckedProgram} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignmentTable : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {skipInitializer : Option ExpressionId}
    {caller : SourceSpecialization.SpecializedFunction}
    (policyExpression : header.policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      checkedProgram header.representation signatures locals parents assignmentTable diagnostics compilation
      (some native) none skipInitializer)
    (sameLedger : compilation.solvedRequirements = header.solved)
    (admission : Admission header.function.source expressionSyntax)
    (coverage : Coverage headers compilation) (sourceTypes : SourceTypes headers header.context)
    (order : ∀ id callee arguments instantiation node, expressionSyntax id →
      header.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary header.function.source locals compilation.owner expressionSyntax)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (constructorRanges : ConstructorRanges header.function.source
      (fun id => expressionSyntax id ∨ CompatibleExpressionBuiltins.Syntax header.function.source id))
    (declarationRanges : DeclarationRanges header.function.source expressionSyntax)
    (expressionRead : header.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (expressionLower : header.representation.expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead header.readFuel values)
    (expressionLeaf : header.representation.expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (sourceSignatures : header.context.signatures = values.checked.signatures) :
∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered := by
  intro sourceContext lexical _residual childSignatures scope fuel id node lowered declarations allowed found typed generated
  rw [policyExpression] at generated
  have tree := tree_of_contextual_of_ranges admission coverage
    (sourceTypes_at (childSignatures.trans sourceSignatures.symm) sourceTypes) order ordinary
    callerSelected callerClosed header.unique lexical constructorRanges declarationRanges declarations
    childSignatures allowed found typed expressionRead expressionLower expressionLeaf generated
  simpa only [sameLedger] using tree

include member definitions sameCache complete globals recipeAccepted cachedRows ordered entry in
/-- Actual cached typing and support still feed the unique statement traversal.
There is no external expression/body meaning or arbitrary child native typing
premise. Full raw closed ranges and independent source admission remain explicit. -/
theorem extract (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    {checkedProgram : CheckedProgram} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignmentTable : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {skipInitializer : Option ExpressionId}
    {caller : SourceSpecialization.SpecializedFunction}
    (policyExpression : header.policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      checkedProgram header.representation signatures locals parents assignmentTable diagnostics compilation
      (some native) none skipInitializer)
    (sameLedger : compilation.solvedRequirements = header.solved)
    (admission : Admission header.function.source expressionSyntax)
    (coverage : Coverage headers compilation) (sourceTypes : SourceTypes headers header.context)
    (order : ∀ id callee arguments instantiation node, expressionSyntax id →
      header.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary header.function.source locals compilation.owner expressionSyntax)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (constructorRanges : ConstructorRanges header.function.source
      (fun id => expressionSyntax id ∨ CompatibleExpressionBuiltins.Syntax header.function.source id))
    (declarationRanges : DeclarationRanges header.function.source expressionSyntax)
    (expressionRead : header.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (expressionLower : header.representation.expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead header.readFuel values)
    (expressionLeaf : header.representation.expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  apply RecursiveNamedCachedSupport.extract_source cached recipeAccepted rows cachedRows ordered
    member definitions sameCache complete globals entry diagnosticPolicy registered prefixEq factory
    readPolicy binderPolicy allocationPolicy
    (expressions (cached := cached) policyExpression sameLedger admission coverage sourceTypes order ordinary callerSelected callerClosed
      constructorRanges declarationRanges expressionRead expressionLower expressionLeaf sourceSignatures)
    assignments unaryPolicy syntaxTree sourceSignatures declarations projection accepted

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedResidualExpressionFactory
