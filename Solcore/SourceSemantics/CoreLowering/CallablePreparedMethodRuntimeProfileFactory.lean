import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogHookMeaning
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations

/-! Static profiles retain the actual cached method, source-selected dictionary,
ordered parameters and accepted body callback. The compiler extractor is used
once at that same source and native body. Its own diagnostic receipt supplies
the sites; no expression or body execution law is stored in a profile. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallablePreparedMethodSelection CallableCoercionMethodInstantiation
open CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogHookMeaning

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

/-- The real retained method's declared callable type agrees with its raw input
binders before and after structural substitution. No packed arity is inverted. -/
theorem callable_shape {program : CheckedProgram} {method : ExecutableImplMethods.CheckedMethod}
    (receipt : CallableCoercionBodyProvenance.Certificate program method)
    (wellFormed : ProgramWellFormed (Program.ofChecked program)) :
    method.specialized.function.type = .function
      (TypeSystem.Ty.productMany (method.specialized.function.typedBody.inputs.map (fun b => b.scheme.body)))
      method.specialized.function.inferredBodyType := by
  have valid := wellFormed.methods_valid (MethodDefinition.ofChecked receipt.retained)
    (List.mem_map.mpr ⟨receipt.retained, receipt.retainedMember, rfl⟩)
  cases valid with
  | intro _ _ _ _ _ _ _ _ _ body =>
    cases body with
    | intro _ _ _ _ shape result _ _ _ extended _ _ _ _ _ _ =>
      have inputs := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      change receipt.retained.checked.typedBody.inputs.map (fun b => b.scheme.body) = _ at inputs
      have genericShape : receipt.retained.checked.type = .function
          (TypeSystem.Ty.productMany (receipt.retained.checked.typedBody.inputs.map (fun b => b.scheme.body)))
          receipt.retained.checked.inferredBodyType := by
        rw [inputs]
        exact shape.trans (congrArg (TypeSystem.Ty.function _) result.symm)
      rw [receipt.result.2, genericShape]
      simp only [TypeSystem.ParameterSubstitution.apply]
      rw [← receipt.result.1, StructuralSubstitution.apply_productMany, receipt.inputs]
      simp only [List.map_map, Function.comp_def, StructuralSubstitution.applyBinder, StructuralSubstitution.applyScheme]

private theorem project_productMany {catalog : SourceCoreCompatibleCatalog.Catalog}
    {types : List TypeSystem.Ty} {native : List Core.Ty}
    (projected : types.mapM catalog.project = .ok native) :
    catalog.project (TypeSystem.Ty.productMany types) = .ok (SourceCoreCompatibleCatalog.packTypes native) := by
  induction types generalizing native with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projected
    subst native
    rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at projected
    obtain ⟨first, firstProjected, projected⟩ := bind_ok projected
    obtain ⟨rest, restProjected, projected⟩ := bind_ok projected
    cases projected
    cases tail with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at restProjected
      subst rest
      exact firstProjected
    | cons next suffix =>
      have remaining := ih restProjected
      rw [List.mapM_cons] at restProjected
      obtain ⟨nextNative, _, restProjected⟩ := bind_ok restProjected
      obtain ⟨suffixNative, _, restProjected⟩ := bind_ok restProjected
      cases restProjected
      change (do pure (Ty.product (← catalog.project head)
        (← catalog.project (TypeSystem.Ty.productMany (next :: suffix))))) = _
      rw [firstProjected, remaining]
      rfl

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (cached : Cached compiled method.specialized)

theorem parameters : (bodyInstance compiled.sourceProgram method).source.inputs = cached.named.inputs.map Prod.fst := by
  obtain ⟨row, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled cached.selected
  have fields := SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted
  rw [← fields.1, cached.same] at fields
  exact fields.2.1.symm

theorem parameter_pack
    (receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    cached.named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) := by
  obtain ⟨row, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled cached.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  have shape := callable_shape receipt wellFormed
  have inputs := parameters cached
  change method.specialized.function.typedBody.inputs = _ at inputs
  rw [inputs] at shape
  have actualShape : row.function.type = .function
      (TypeSystem.Ty.productMany (cached.named.inputs.map (fun b => b.1.scheme.body)))
      row.function.inferredBodyType := by
    rw [← same, cached.same]
    simpa only [List.map_map, Function.comp_def] using shape
  have projected := CompatibleExpressionReads.projectType_of_accepted
    (RecursiveNamedHeaderParameterProjections.prepared_parameter accepted actualShape)
  have vector := project_productMany
    (RecursiveNamedPreparedParameterProjections.cached_projected compiled cached.selected)
  exact Except.ok.inj (projected.symm.trans vector)

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem prepared_outputs {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {specialized : SourceSpecialization.SpecializedFunction} {named : SourceCoreGeneralFunctions.Function}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named) :
    named.signature.key = specialized.key ∧
      representation.expressions.projectType (.declaration specialized.key.declaration)
        specialized.function.inferredBodyType = .ok named.signature.resultType := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (specialized.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged] at accepted
    cases shape : specialized.function.type <;>
      simp only [shape, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted <;>
      try contradiction
    rename_i parameter result
    by_cases mismatch : result ≠ specialized.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨parameterType, _, accepted⟩ := bind_ok accepted
      obtain ⟨resultType, projected, accepted⟩ := bind_ok accepted
      obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
      cases accepted
      have resultEq : result = specialized.function.inferredBodyType := Classical.byContradiction mismatch
      exact ⟨rfl, by simpa only [resultEq] using mapError_ok projected⟩


theorem result_projection : compiled.compatible.checked.catalog.project
    (bodyInstance compiled.sourceProgram method).resultType = .ok cached.named.signature.resultType := by
  obtain ⟨row, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled cached.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  have projected := CompatibleExpressionReads.projectType_of_accepted (prepared_outputs accepted).2
  rw [← same, cached.same] at projected
  exact projected


section Static
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)

abbrev policy := CompatibleNamedBody.bodyPolicy
  ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
  prepared.base.sourceProgram prepared.base.sourceProgram.signatures prepared.base.locals compilation.parents
  compilation.own.assignments diagnostics (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext

abbrev scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))

/-- Actual source attribution and full runtime validity at the real parameter context. -/
structure SourceAt (values : SourceCoreCompatibleValues.Context)
    (sourceBody : Dynamic.BodyInstance) (dictionary : Dynamic.EvidenceEnvironment) where
  sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named
  parameters : sourceBody.source.inputs = named.inputs.map Prod.fst
  frame : CallableCoercionMethodFrame.Frame sourceBody (methodFunction compilation sourceBody dictionary)
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  extended : MonoBindersExtend sourceBody.source.owner sourceBody.context sourceBody.source.inputs types context
  valid : CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary
  closed : context.typeVariables = []
  residual : context.residualTypeVariables = true
  signatures : context.signatures = values.checked.signatures
  projection : values.checked.catalog.project sourceBody.resultType = .ok named.signature.resultType
  parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd)
  unique : NodeOccurrencesUnique sourceBody.source

variable {values : SourceCoreCompatibleValues.Context} {sourceBody : Dynamic.BodyInstance}
  {dictionary : Dynamic.EvidenceEnvironment}

/-- The accepted body action is the same actual policy, source and statement vector. -/
theorem SourceAt.accepted (source : SourceAt compilation values sourceBody dictionary) :
    SourceCoreLoops.lowerStatementsWithPolicy (policy compilation) prepared.fuel sourceBody.source (scope (named := named))
      compilation.statements named.signature.resultType (diagnostics.reasonAt named.signature.key)
      compilation.own.fellThroughReason compilation.own.table.escapedReason = .ok compilation.body := by
  rw [source.sameSource]
  exact CallableCoercionMethodBody.loops_accepted compilation

private theorem reversed_scope (bindings : List (TypedBinder × Core.Ty)) (scope : SourceCoreLocalCell.Scope) :
    bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) scope =
      bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons binding rest ih => simp only [List.foldl_cons, ih, List.reverse_cons, List.map_append,
      List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

theorem SourceAt.declarations (source : SourceAt compilation values sourceBody dictionary) :
    CompatibleExpressionReads.ScopeDeclarations sourceBody.source (scope (named := named)) source.context := by
  have members : ∀ binding, binding ∈ named.inputs →
      binding.1 ∈ SourceCoreDataPlaces.declaredBinders sourceBody.source := by
    intro binding member
    apply List.mem_append_left
    rw [source.parameters]
    exact List.mem_map.mpr ⟨binding, member, rfl⟩
  have extended := source.extended
  rw [source.parameters] at extended
  have initial : CompatibleExpressionReads.ScopeDeclarations sourceBody.source [] sourceBody.context := by
    intro _ _ _ _ selected _
    cases selected
  have final := RecursiveNamedHeaderScopeDeclarations.parameters members extended initial
  simpa only [reversed_scope, List.append_nil, scope] using final

end Static

/-- Independent whole-program validity and this exact source selection create
runtime context validity; the actual cache supplies ordered parameters and projections. -/
theorem source_at {values : SourceCoreCompatibleValues.Context}
    (sameChecked : values.checked = compiled.compatible.checked)
    (receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {context : SourceSemantics.Context} {callerEvidence dictionary : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      traitName methodName requirements (bodyInstance compiled.sourceProgram method) dictionary)
    (unique : NodeOccurrencesUnique (bodyInstance compiled.sourceProgram method).source)
    (signatures : compiled.sourceProgram.signatures = values.checked.signatures) :
    Nonempty (SourceAt cached.compilation values (bodyInstance compiled.sourceProgram method) dictionary) := by
  obtain ⟨types, lexical, facts, typed, valid⟩ := selected_typed selected wellFormed
  have fields := RecursiveNamedInitialContextValidity.mono_fields typed.typing.inputs_extend
  refine ⟨⟨?_, parameters cached, cached.frame selected, lexical, types, typed.typing.inputs_extend,
    ?_, fields.typeVariables.trans typed.type_variables_empty,
    fields.residualTypeVariables.trans typed.residual_type_variables_open,
    fields.signatures.trans (typed.signatures_eq.trans signatures), ?_, parameter_pack cached receipt wellFormed, unique⟩⟩
  · simp only [CallableIndexedNamedGeneration.source, cached.same, bodyInstance]
  · change CompatibleRuntimeContextValidity.Valid method.specialized.function.solvedRequirements lexical dictionary at valid
    simpa only [cached.same] using valid
  · rw [sameChecked]
    exact result_projection cached


/-- The exact cached lambda fixes this compilation's native body type. -/
theorem cached_body_native
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts} (member : entry ∈ compiled.indexed.entries) :
    HasType (SourceCoreLocalCell.coreContext (scope (named := cached.named)) ++
      cached.named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
      .cell compiled.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      cached.compilation.body (LanguageResult.resultType cached.named.signature.resultType) compiled.indexed.layouts.definitions := by
  have typed := CallableIndexedCachedNativeTyping.prepared_native_closure compiled.indexedPrepared member cached.cached
    (CallableIndexedPreparedInventories.cached_global_at compiled cached.selected)
  rw [cached.compilation.emitted] at typed
  cases typed with
  | lambda _ _ body =>
    simpa only [scope, List.append_assoc, List.cons_append] using CallableIndexedParameterNativeInversion.body_native cached.compilation body

/-- Only the used native prefix must agree. Unused administrative suffixes stay arbitrary. -/
theorem canonical_native {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts} (member : entry ∈ compiled.indexed.entries)
    {bound : Nat} {administrative : Core.Context}
    (support : NativeExpressionContextSupport.supported cached.compilation.body bound = true)
    (agrees : NativeExpressionContextSupport.Agrees bound
      (SourceCoreLocalCell.coreContext (scope (named := cached.named)) ++
        cached.named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
        .cell compiled.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      (SourceCoreLocalCell.coreContext (scope (named := cached.named)) ++
        SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) :: administrative)) :
    HasType (SourceCoreLocalCell.coreContext (scope (named := cached.named)) ++
      SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) :: administrative)
      cached.compilation.body (LanguageResult.resultType cached.named.signature.resultType) ambient.definitions := by
  have typed := NativeExpressionContextSupport.typing (cached_body_native cached member) support agrees
  rwa [definitions] at typed

section Extract
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  (source : SourceAt compilation values sourceBody dictionary)
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {administrative : Core.Context} {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}

/-- Admission of the reached static children in this actual callback.
The source context, projections, parameters and body acceptance come from SourceAt. -/
structure Inputs (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context) where
  matchCompilation : SourceCoreCompatibleDataMatches.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word
  invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy sourceBody.source invalidOperand
  matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess (policy compilation) matchCompilation
  matchValues : matchCompilation.values = values
  matchDefinitions : matchCompilation.definitions = ambient.definitions
  matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame prepared.base.globals.length
    (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error))))
  matchLedger : matchCompilation.solvedRequirements = named.specialized.function.solvedRequirements
  matchChildStatic : GenericImperativeMatch.MatchChildStatic matchCompilation sourceBody.source
    certificates
    ambient.definitions administrative
  readPolicy : (policy compilation).readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    (policy compilation).lowerBinder sourceBody.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked sourceBody.source scope binder
  allocationPolicy : (policy compilation).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame prepared.base.globals.length
    (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error))))
  expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = values.checked.signatures →
    ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations sourceBody.source scope sourceContext → expressionSyntax id →
    sourceBody.source.lookupExpression? id = some node → ExpressionHasType sourceBody.source sourceContext id node.type →
    (policy compilation).lowerExpression fuel sourceBody.source scope id (diagnostics.reasonAt named.signature.key) = .ok lowered →
    certificates sourceContext scope id lowered
  assignments : CompatibleAssignmentStatements.AssignmentPolicy (policy compilation) values invalidProjection invalidOperand missingDefault
  unaryPolicy : CompatibleBitNotStatements.Policy (policy compilation) values invalidProjection invalidUnary missingDefault
  assignmentExpressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = values.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations sourceBody.source scope sourceContext →
    expressionSyntax id → ∀ node, sourceBody.source.lookupExpression? id = some node →
    ExpressionHasType sourceBody.source sourceContext id node.type →
    (policy compilation).lowerExpression fuel sourceBody.source scope id (diagnostics.reasonAt named.signature.key) = .ok lowered →
      certificates sourceContext scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) ambient.definitions
  syntaxTree : GenericImperativeMatch.Syntax sourceBody.source expressionSyntax source.context
    (.statements true compilation.statements) sourceBody.resultType


/-- This extraction is indexed by the actual compiled body and actual dictionary.
Only its own diagnostics can materialize its same Tree and sites. -/
structure Receipt (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (diagnosticPolicy : AssignmentDiagnosticPolicy) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context) where
  flow : Expr
  extracted : GenericImperativeMatch.ExtractionFor diagnosticPolicy prepared.layouts named.signature.key []
    prepared.ancestry.layout.frame prepared.base.globals.length (fun error => .sourceAllocation (reprStr error))
    values sourceBody.source expressionSyntax certificates ambient.definitions administrative
    named.specialized.function.solvedRequirements source.context (scope (named := named))
    (.statements true compilation.statements) sourceBody.resultType named.signature.resultType flow
  emitted : compilation.body = CompatibleStatements.finish named.signature.resultType flow
    compilation.own.fellThroughReason compilation.own.table.escapedReason

/-- The common extractor traverses the actual body once. No semantic callback is needed. -/
theorem extract (inputs : Inputs source (ambient := ambient) certificates tracked diagnosticPolicy expressionSyntax administrative)
    (typed : HasType (SourceCoreLocalCell.coreContext (scope (named := named)) ++ administrative)
      compilation.body (LanguageResult.resultType named.signature.resultType) ambient.definitions) :
    Nonempty (Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax administrative) := by
  obtain ⟨flow, generated, extracted, emitted⟩ := GenericImperativeMatch.extraction_of_typed_body_with_lowering true diagnosticPolicy
    inputs.factory inputs.matchPolicy inputs.matchValues inputs.matchDefinitions inputs.matchAllocator inputs.matchChildStatic
    inputs.readPolicy inputs.binderPolicy inputs.allocationPolicy inputs.expressions inputs.assignments inputs.unaryPolicy
    source.unique inputs.assignmentExpressions inputs.syntaxTree source.closed source.residual source.signatures
    (source.declarations compilation) source.projection (source.accepted compilation) typed
  rw [inputs.matchLedger] at extracted
  exact ⟨⟨flow, extracted, emitted⟩⟩

/-- The good returned receipt constructs the existing same-dictionary profile. -/
def Receipt.profile
    (receipt : Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative))
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (definitions : prepared.layouts.definitions = ambient.definitions)
    (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (interpreted : receipt.extracted.diagnostics registry faults) :
    ProfileFor compilation values ambient sourceBody dictionary administrative registry faults
      expressionSyntax certificates
      (fun context => CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)
      diagnosticPolicy := by
  have sites : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults receipt.extracted.tree := by
    obtain ⟨errors, ledgers⟩ := receipt.extracted.materialize registry faults interpreted
    exact RecursiveNamedCatalogRuntimeProfileFactory.catalog_sites catalog ledgers source.valid.ledger source.signatures
  exact {
    sameSource := source.sameSource
    parameters := source.parameters
    sourceFrame := source.frame
    context := source.context
    types := source.types
    extended := source.extended
    body := {
      flow := receipt.flow
      tree := receipt.extracted.tree
      sites := sites
      initialValid := source.valid
      projection := source.projection
      unique := source.unique
      emitted := receipt.emitted }
    definitions := definitions
    registered := registered
    parameterType := source.parameterType }

end Extract


/-- Actual cached native typing supplies the only whole-body typing premise.
The remaining inputs concern syntax, used slots and reached static children. -/
theorem extract_cached {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {dictionary : Dynamic.EvidenceEnvironment}
    (source : SourceAt cached.compilation values (bodyInstance compiled.sourceProgram method) dictionary)
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy} {administrative : Core.Context}
    (inputs : Inputs source (ambient := ambient) certificates tracked diagnosticPolicy expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) :: administrative))
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts} (member : entry ∈ compiled.indexed.entries)
    {bound : Nat} (support : NativeExpressionContextSupport.supported cached.compilation.body bound = true)
    (agrees : NativeExpressionContextSupport.Agrees bound
      (SourceCoreLocalCell.coreContext (scope (named := cached.named)) ++
        cached.named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
        .cell compiled.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      (SourceCoreLocalCell.coreContext (scope (named := cached.named)) ++
        SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) :: administrative)) :
    Nonempty (Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) :: administrative)) :=
  extract source inputs (canonical_native cached definitions member support agrees)

/-- Interpretation belongs to this exact returned receipt, not every possible
receipt. Witness selection stays inside the proposition. -/
theorem profile_of_interpreted {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {dictionary : Dynamic.EvidenceEnvironment}
    (source : SourceAt cached.compilation values (bodyInstance compiled.sourceProgram method) dictionary)
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {diagnosticPolicy : AssignmentDiagnosticPolicy} {administrative : Core.Context}
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (good : ∃ receipt : Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) :: administrative),
      receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor cached.compilation values ambient (bodyInstance compiled.sourceProgram method) dictionary
      administrative registry faults expressionSyntax certificates
      (fun context => CompatibleRuntimeContextValidity.Valid cached.named.specialized.function.solvedRequirements context dictionary)
      diagnosticPolicy) := by
  obtain ⟨receipt, interpreted⟩ := good
  exact ⟨receipt.profile source catalog definitions registered interpreted⟩

end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory
