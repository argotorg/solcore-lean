import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionNativeTyping
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfileFactory

/-! Actual entry reference slots supply native typing for the existing
assignment-child callback. Source expression certificates remain independent;
no runtime expression/body law or new compiler traversal is introduced. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedAssignmentNativeCertificates
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory
open RecursiveNamedExpressionNativeTyping NativeExpressionContextSupport
open CompatibleExpressionScalarNativeTyping

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {header : Header prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}

/-- The administrative context is recovered from real canonical values and
its own typing derivation. All later lexical scopes prepend before these slots. -/
theorem entry_slots (prefixEq : compilation.administrativePrefix = 1)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    Slots headers compilation (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) := by
  intro target member
  have found := entry.catalog.globals target member
  have types := entry.environments.runtime_hasTypes.type_tags
  change entry.canonical.map Value.type = SourceCoreLocalCell.coreContext (bodyScope header) ++
    SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative at types
  have typed : (SourceCoreLocalCell.coreContext (bodyScope header) ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)[(bodyScope header).length + (0 + 1) + target.slot]? = some target.named.signature.referenceType := by
    rw [← types]
    simpa [bodyScope, List.getElem?_map, found, Value.type, SourceCoreCalls.Signature.referenceType, OptionalCell.referenceType] using
      congrArg (Option.map Value.type) found
  simpa [SourceCoreLocalCell.coreContext, List.getElem?_append, List.length_map,
    prefixEq, Nat.add_assoc] using typed

private theorem key_typed {source : TypedSource} {context : SourceSemantics.Context}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    (typed : SourceProjectionsHaveType source context root projections leaf)
    {id : ExpressionId} (member : id ∈ DataPlaceKeyOrder.sourceKeys projections) :
    ∃ type, ExpressionHasType source context id type := by
  induction projections generalizing root leaf with
  | nil => cases typed; cases member
  | cons projection projections ih =>
    cases typed with
    | index head rest =>
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨_, head⟩
      · exact ih rest tail
    | member _ rest => exact ih rest member

/-- Only RHS and real ordered-key members are selected from source typing. -/
theorem assignment_child_source {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs id : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    (member : id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections) :
    ∃ node, source.lookupExpression? id = some node ∧ ExpressionHasType source context id node.type := by
  have child : ∃ type, ExpressionHasType source context id type := by
    cases typed with
    | equal target right _ | wordCompound _ target right _ =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, right⟩
      · cases target with
        | intro _ path _ => exact key_typed path member
  obtain ⟨type, typed⟩ := child
  obtain ⟨node, contains, same⟩ := typed.stored_type
  exact ⟨node, lookupExpression?_complete unique contains, same.symm ▸ typed⟩

variable {source : TypedSource} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {readFuel fuel : Nat}

/-- This finite callback types the actual RHS/key compiler outputs. Duplicate
key occurrences remain members of the original list, with no deduplication. -/
theorem assignment_children
    (shaped : CompatibleCatalogNominalCoverage.Shapes values.checked.signatures values.checked.catalog)
    (complete : CompatibleCatalogNominalCoverage.Complete values.checked.catalog)
    (slots : Slots headers compilation administrative)
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : SourceCoreLoops.ExpressionLowerer}
    (unique : NodeOccurrencesUnique source)
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    (expressions : ∀ id, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      ∀ node lowered, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      expression fuel source scope id reasonAt = .ok lowered →
      Expressions headers compilation readFuel source context solved reasonAt scope id lowered) :
    ∀ id lowered, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧
      Expressions headers compilation readFuel source context solved reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) ambient.definitions := by
  intro id lowered member generated
  obtain ⟨node, found, sourceTyped⟩ := assignment_child_source unique typed member
  have tree := expressions id member node lowered found sourceTyped generated
  exact ⟨node, found, tree, (tree_native_at shaped complete slots ambient.basePrefix tree).2⟩

variable {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

theorem extract_with_residual (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (closed : header.context.typeVariables = []) (residual : header.context.residualTypeVariables = residualMode)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    {suffix : Core.Context}
    (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions)
    (support : supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
    (complete : Complete headers) (globals : header.globals = base.globals.length)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  have shaped := CompatibleCatalogNominalCoverage.prepare_shapes registered
  rw [← SourceCoreCompatibleCatalog.prepare_signatures registered] at shaped
  have completeCatalog := CompatibleCatalogNominalCoverage.prepare_complete registered
  have slots := entry_slots prefixEq entry
  apply RecursiveNamedCatalogProfileFactory.extract_with_residual residualMode diagnosticPolicy factory readPolicy binderPolicy allocationPolicy
    expressions assignments unaryPolicy ?_ syntaxTree closed residual sourceSignatures declarations projection accepted
    cachedTyped support complete globals entry
  intro sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated
  have tree := expressions sourceContext closed residual signatures declarations syntaxTree found typed generated
  exact ⟨tree, (tree_native_at shaped completeCatalog slots ambient.basePrefix tree).2⟩

/-- Compatibility entry for the former closed residual scope. -/
theorem extract (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (closed : header.context.typeVariables = []) (residual : header.context.residualTypeVariables = false)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    {suffix : Core.Context}
    (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions)
    (support : supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
    (complete : Complete headers) (globals : header.globals = base.globals.length)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  exact extract_with_residual false (diagnosticPolicy := diagnosticPolicy) (catalogSignatures := catalogSignatures)
    (catalogFuel := catalogFuel) (catalogTypes := catalogTypes) (metadata := metadata) (limits := limits)
    (contracts := contracts) (registered := registered) (prefixEq := prefixEq) (tracked := tracked) (factory := factory)
    (readPolicy := readPolicy) (binderPolicy := binderPolicy) (allocationPolicy := allocationPolicy)
    (expressions := expressions) (assignments := assignments) (unaryPolicy := unaryPolicy) (syntaxTree := syntaxTree)
    (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations)
    (projection := projection) (accepted := accepted) (suffix := suffix) (cachedTyped := cachedTyped)
    (support := support) (complete := complete) (globals := globals) (entry := entry)

/-- Use the real source declaration context; its residual flag is derived
from structural instantiation and the actual monomorphic parameters. -/
theorem extract_source (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    {suffix : Core.Context}
    (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions)
    (support : supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
    (complete : Complete headers) (globals : header.globals = base.globals.length)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  exact extract_with_residual true (diagnosticPolicy := diagnosticPolicy) (catalogSignatures := catalogSignatures)
    (catalogFuel := catalogFuel) (catalogTypes := catalogTypes) (metadata := metadata) (limits := limits)
    (contracts := contracts) (registered := registered) (prefixEq := prefixEq) (tracked := tracked) (factory := factory)
    (readPolicy := readPolicy) (binderPolicy := binderPolicy) (allocationPolicy := allocationPolicy)
    (expressions := expressions) (assignments := assignments) (unaryPolicy := unaryPolicy) (syntaxTree := syntaxTree)
    (closed := RecursiveNamedSourceContextFacts.header_typeVariables header)
    (residual := RecursiveNamedSourceContextFacts.header_residual header) (sourceSignatures := sourceSignatures)
    (declarations := declarations) (projection := projection) (accepted := accepted) (suffix := suffix)
    (cachedTyped := cachedTyped) (support := support) (complete := complete) (globals := globals) (entry := entry)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedAssignmentNativeCertificates
