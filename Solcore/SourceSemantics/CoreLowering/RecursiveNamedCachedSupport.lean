import Solcore.SourceSemantics.CoreLowering.NativeExpressionRenamingSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInitialization
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedAssignmentNativeCertificates

/-! Actual accepted initialization stores each cached closure with exactly
the global references, the frame reference and its installer Unit prefix.
Native type preservation bounds the stored body; syntactic renaming reflection
removes the installer prefix. No source authority or execution law is inferred
from this bound. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory
open NativeExpressionContextSupport RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

theorem environment_length (signatures : List Signature) (layout : SourceCoreCallableIndexedFrames.Layout) :
    (initialEnvironment signatures layout).length = signatures.length + 1 := by
  rw [initialEnvironment, reserved_environment]
  simp

theorem captured_length {world : StoreTyping} {context : Core.Context} {definitions : DataEnvironment}
    (signatures : List Signature) (layout : SourceCoreCallableIndexedFrames.Layout) (slot : Nat)
    (typed : RuntimeEnvironmentHasTypes world
      (List.replicate slot .unit ++ initialEnvironment signatures layout) context definitions) :
    context.length = slot + signatures.length + 1 := by
  have lengths := congrArg List.length typed.type_tags
  simp only [List.length_map, List.length_append, List.length_replicate, environment_length] at lengths
  omega

/-- Only the actual body typing obtained from the stored closure is needed.
Parameter/result well-formedness is not separately assumed to rebuild a lambda
typing derivation. -/
theorem row_supported {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (rows : List LambdaRow) (cached : compiled.indexed.secondPass.closures = rows.map LambdaRow.expression)
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      compiled.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
    {slot : Nat} {row : LambdaRow} (found : rows[slot]? = some row) :
    supported row.expression (compiled.indexed.base.globals.length + 1) = true := by
  obtain ⟨world, typed⟩ := stored accepted rows cached ordered
  have read := RecursiveNamedCatalogInitialization.closure_read compiled.indexed.base.globals rows
    compiled.indexed.ancestry.layout.frame ordered found
  obtain ⟨context, capturedTyped, bodyTyped⟩ := stored_closure typed read
  have length := captured_length compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame slot capturedTyped
  have bodySupport := of_typing bodyTyped
  have renamed : supported (row.expression.rename (shift slot))
      (compiled.indexed.base.globals.length + 1 + slot) = true := by
    simpa only [LambdaRow.expression, Expr.rename, supported, List.length_cons, length,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bodySupport
  exact NativeExpressionRenamingSupport.shift row.expression slot _ renamed

theorem cached_supported {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (rows : List LambdaRow) (cached : compiled.indexed.secondPass.closures = rows.map LambdaRow.expression)
    (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
      compiled.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
    {slot : Nat} {parameter result : Ty} {body : Expr}
    (selected : compiled.indexed.secondPass.closures[slot]? = some (.lambda parameter result body)) :
    supported (.lambda parameter result body) (compiled.indexed.base.globals.length + 1) = true := by
  rw [cached] at selected
  exact row_supported accepted rows cached ordered (RecursiveNamedCatalogInitialization.row_of_cached selected)

variable (cached : SourceCoreUnifiedCompilation.Compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare cached = .ok recipe)
  (rows : List LambdaRow)
  (cachedRows : cached.indexed.secondPass.closures = rows.map LambdaRow.expression)
  (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
    cached.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
  (member : nativeEntry ∈ cached.indexed.entries)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
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

include recipeAccepted cachedRows ordered sameCache in
/-- This is the same selected full cached lambda used by native extraction. -/
theorem header_supported :
    supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code)
      (cached.indexed.base.globals.length + 1) = true := by
  apply cached_supported recipeAccepted rows cachedRows ordered
  rw [← sameCache]
  exact header.cached

include member definitions sameCache in
private theorem original_cached :
    HasType (cached.indexed.base.globals.map (·.referenceType) ++ .cell cached.indexed.ancestry.layout.frame.type ::
      SourceCoreGeneralEntry.nativeInputContext nativeEntry.native.inputTypes)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions := by
  have selected := header.cached
  rw [sameCache] at selected
  have typed := CallableIndexedCachedNativeTyping.prepared_native_closure cached.indexedPrepared member selected
    (CallableIndexedPreparedInventories.cached_global_at cached header.selected)
  simpa only [← definitions] using typed

include member definitions sameCache complete globals recipeAccepted cachedRows ordered entry in
theorem canonical_body :
    HasType (SourceCoreLocalCell.coreContext (bodyScope header) ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      header.body (LanguageResult.resultType header.output) ambient.definitions :=
  canonical_cached complete globals (original_cached cached member definitions sameCache) (header_supported cached recipeAccepted rows cachedRows ordered sameCache) entry

variable {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

include member definitions sameCache complete globals recipeAccepted cachedRows ordered entry in
/-- This consumer feeds the real prepared root's native proof into the single
compiler traversal, without requesting body/loop HasType at actual Γ. -/
theorem extract_with_residual (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
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
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :=
  RecursiveNamedAssignmentNativeCertificates.extract_with_residual residualMode diagnosticPolicy registered prefixEq factory readPolicy binderPolicy allocationPolicy
    expressions assignments unaryPolicy syntaxTree closed residual sourceSignatures declarations
    projection accepted (original_cached cached member definitions sameCache) (header_supported cached recipeAccepted rows cachedRows ordered sameCache) complete globals entry

include member definitions sameCache complete globals recipeAccepted cachedRows ordered entry in
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
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
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
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  exact extract_with_residual false (cached := cached) (rows := rows) (member := member) (definitions := definitions)
    (sameCache := sameCache) (complete := complete) (globals := globals) (recipeAccepted := recipeAccepted)
    (cachedRows := cachedRows) (ordered := ordered) (entry := entry) (diagnosticPolicy := diagnosticPolicy)
    (catalogSignatures := catalogSignatures) (catalogFuel := catalogFuel) (catalogTypes := catalogTypes)
    (metadata := metadata) (limits := limits) (contracts := contracts) (registered := registered) (prefixEq := prefixEq)
    (tracked := tracked) (factory := factory) (readPolicy := readPolicy) (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy) (expressions := expressions) (assignments := assignments)
    (unaryPolicy := unaryPolicy) (syntaxTree := syntaxTree) (closed := closed) (residual := residual)
    (sourceSignatures := sourceSignatures) (declarations := declarations) (projection := projection)
    (accepted := accepted)

include member definitions sameCache complete globals recipeAccepted cachedRows ordered entry in
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
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
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
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  exact extract_with_residual true (cached := cached) (rows := rows) (member := member) (definitions := definitions)
    (sameCache := sameCache) (complete := complete) (globals := globals) (recipeAccepted := recipeAccepted)
    (cachedRows := cachedRows) (ordered := ordered) (entry := entry) (diagnosticPolicy := diagnosticPolicy)
    (catalogSignatures := catalogSignatures) (catalogFuel := catalogFuel) (catalogTypes := catalogTypes)
    (metadata := metadata) (limits := limits) (contracts := contracts) (registered := registered) (prefixEq := prefixEq)
    (tracked := tracked) (factory := factory) (readPolicy := readPolicy) (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy) (expressions := expressions) (assignments := assignments)
    (unaryPolicy := unaryPolicy) (syntaxTree := syntaxTree)
    (closed := RecursiveNamedSourceContextFacts.header_typeVariables header)
    (residual := RecursiveNamedSourceContextFacts.header_residual header) (sourceSignatures := sourceSignatures)
    (declarations := declarations) (projection := projection) (accepted := accepted)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedSupport
