import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaMeaning

/-! Ordinary lambda generation under a real named entry. Compiler callbacks
fix the source owner and empty native parent; the named seed fixes the complete
source graph. Source context, evidence and capture locations are the actual
formation inputs. Generalized bundles, applied views and whole traversal
coverage remain separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedNamedGeneration CallableIndexedLambdaValues

/-- The source closure stores the exact generation inputs, without deriving
source context or evidence from the native frame. -/
def closure (named : Named) (parameters : List TypedBinder) (result : TypeSystem.Ty) (body : List StatementId)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment) : Dynamic.Closure :=
  ⟨parameters, result, body, source named, captured, context, evidence⟩

private theorem evidence_lambda (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (compilation : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {view : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : view.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller compilation child fuel view scope id reasonAt callables = .ok none := by
  have owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, found, form, owned, requirements, coercions,
    bind, Except.bind, pure, Except.pure]

/-- Successful execution of the actual ordinary callback yields its lambda
branch receipt and all production hook profiles. No lambda-body execution is
an input. Excluding the generalized-initializer override is a static condition. -/
theorem contextual_certificate_with_binder {checked : SourceCoreCompatibleCatalog.Checked} (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : view.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered) :
    ∃ (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer),
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) (context prepared named)
        view scope id reasonAt = .ok lowered ∧
      Nonempty (CallableIndexedLambdaCertificates.Certificate policy lowerBody fuel (context prepared named)
        view scope id node parameters result body reported reasonAt lowered) ∧
      policy.sourceCells = some (allocator prepared named) ∧
      policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [] ∧
      policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [] ∧
      policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [] ∧
      policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked ∧
      policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
        ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [] := by
  rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  dsimp only at accepted
  change (SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key |>.mapError SourceCoreBasic.Error.callPreparation) >>= _ = .ok lowered at accepted
  rw [record] at accepted
  simp only [Except.mapError, bind, Except.bind] at accepted
  refine ⟨_, _, accepted, ?_, rfl, rfl, rfl, ?_, rfl, rfl⟩
  · apply CallableIndexedLambdaCertificates.of_accepted (owner := owner) (found := found) (form := form) (accepted := accepted)
    · change (do
        let actualSource ← SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram prepared.base.plan
          prepared.base.locals named.signature.key none view id
        _) = .ok none
      have unchanged : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram prepared.base.plan
          prepared.base.locals named.signature.key none view id = .ok view := by
        simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
      rw [unchanged]
      simp only [bind, Except.bind, pure, Except.pure, found]
      rw [ordinary]
      simp only [Option.filter_none]
      rw [evidence_lambda _ _ _ _ _ _ _ _ _ found form requirements coercions]
      simp [form]
    · change (do
        let actualSource ← SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram prepared.base.plan
          prepared.base.locals named.signature.key none view id
        SourceCoreCompatibleDataExpressions.readExpression checked actualSource id) = .ok (node, reported)
      simpa [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure] using read
  · change SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [] = _
    rw [prepared.ancestry.graph.inputs.callableSelected]

/-- The original interface forgets only the actual binder policy receipt. -/
theorem contextual_certificate {checked : SourceCoreCompatibleCatalog.Checked} (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : view.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered) :
    ∃ (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer),
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) (context prepared named)
        view scope id reasonAt = .ok lowered ∧
      Nonempty (CallableIndexedLambdaCertificates.Certificate policy lowerBody fuel (context prepared named)
        view scope id node parameters result body reported reasonAt lowered) ∧
      policy.sourceCells = some (allocator prepared named) ∧
      policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [] ∧
      policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [] ∧
      policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [] ∧
      policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked := by
  obtain ⟨policy, lowerBody, generated, receipt, allocation, manifest, expression, callables, projector, _binder⟩ :=
    contextual_certificate_with_binder prepared compiled record found form owner requirements coercions ordinary read accepted
  exact ⟨policy, lowerBody, generated, receipt, allocation, manifest, expression, callables, projector⟩

/-- A static ordinary generation site keeps the actual callback receipt. Its
owner and native parent are established by that callback, rather than supplied
as unrelated alignment fields by a consumer. -/
structure Site {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (parameters : List TypedBinder) (result : TypeSystem.Ty) (body : List StatementId)
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (captured : Dynamic.Environment) (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context) where private mk ::
  code : Code prepared (closure named parameters result body sourceContext evidence captured) scope administrative
  compilation : code.compilation = context prepared named
  active : code.active = []

private theorem descriptor_exists (table : SourceCoreStageCodebook.Table)
    {origin : SourceCoreStageCodebook.Origin} {id : Word} (selected : table.idAt? origin = some id) :
    Nonempty (SourceCoreCallableContracts.Descriptor table origin) := by
  cases accepted : SourceCoreCallableContracts.descriptor table origin with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at accepted
    split at accepted
    · rename_i absent
      rw [selected] at absent
      cases absent
    · cases accepted
  | ok descriptor => exact ⟨descriptor⟩

/-- Build every static code field from the actual named callback's accepted
ordinary lambda branch. Canonical metadata and native checking remain explicit,
but no generation-history alignment is assumed. -/
theorem of_contextual_with_binder {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
        site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
          ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [] := by
  obtain ⟨policy, lowerBody, accepted, ⟨receipt⟩, allocationProfile, manifest, expressionProfile, callables, projector, binderPolicy⟩ :=
    contextual_certificate_with_binder prepared compiled record found (form.trans sourceForm) owner requirements coercions ordinary read accepted
  have parameterProjected := receipt.parameterProjected
  have resultProjected := receipt.resultProjected
  rw [projector] at parameterProjected resultProjected
  have parameterProjected := CompatibleExpressionReads.projectType_of_accepted parameterProjected
  have resultProjected := CompatibleExpressionReads.projectType_of_accepted resultProjected
  have projection : checked.catalog.project (FunctionValues.sourceType
      (closure named parameters result body sourceContext evidence captured)) =
      .ok (CallableContract.functionType receipt.parameterCore receipt.resultCore) := by
    change checked.catalog.project (.function (TypeSystem.Ty.productMany (parameters.map (·.scheme.body))) result) = _
    rw [receipt.parameterTypes]
    simp [SourceCoreCompatibleCatalog.Catalog.project, parameterProjected, resultProjected,
      SourceCoreCompatibleCatalog.Catalog.functionType, profile, bind, Except.bind, pure, Except.pure]
  have reportedType : reported = CallableContract.functionType receipt.parameterCore receipt.resultCore := by
    have h := receipt.checked
    rw [callables] at h
    unfold SourceCoreBasic.ensureType at h
    split at h
    · assumption
    · cases h
  have typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType (CallableContract.functionType receipt.parameterCore receipt.resultCore))
      prepared.layouts.definitions := by
    simpa only [congrArg SourceCoreBasic.LoweredExpr.type receipt.emitted, reportedType] using typed
  have hook := receipt.expressionHook
  rw [expressionProfile] at hook
  obtain ⟨origin, _, selected, _, _, _, _, _⟩ := CallableIndexedFormation.expressionHook_receipt prepared.ancestry hook
  rw [(lookupExpression?_sound found).2] at selected
  obtain ⟨descriptor⟩ := descriptor_exists _ selected
  let code : Code prepared (closure named parameters result body sourceContext evidence captured) scope administrative := {
    policy, lowerBody, fuel, compilation := context prepared named, active := [], view, viewOfSource,
    id, sourceNode, sourceFound, sourceForm, node, found, form, reported, reasonAt, lowered, receipt, accepted,
    allocationError := fun error => .sourceAllocation (reprStr error), allocationProfile, manifest, expressionProfile,
    callables, descriptor, projection, typed }
  exact ⟨⟨code, rfl, rfl⟩, rfl, rfl, binderPolicy⟩

/-- The original site factory preserves its complete Code and output fields. -/
theorem of_contextual {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered := by
  obtain ⟨site, siteId, siteLowered, _binder⟩ := of_contextual_with_binder prepared compiled record
    sourceContext evidence captured profile viewOfSource sourceFound sourceForm found form owner requirements coercions
    ordinary read accepted typed
  exact ⟨site, siteId, siteLowered⟩

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {capturedSource : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope}

/-- The named seed and factory-created site agree on full source, owner and
native parent. Source context, evidence and captured locations remain exactly
the arguments to the closure constructor. -/
def Site.historyAt {administrative : Core.Context}
    (site : Site prepared named parameters result body sourceContext evidence capturedSource scope administrative)
    {origin : Word}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized) :
    History site.code where
  native := SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin
  ghost := .named origin
  metadata := state named
  carried := named_complete prepared.ancestry.graph (seed prepared selected record)
  source := rfl
  owner := by rw [site.compilation]; rfl
  active := site.active.symm

/-- The real named entry hook supplies the selected origin; consumers do not
invent a matching graph index or any of the three history alignment fields. -/
theorem Site.history {administrative : Core.Context}
    (site : Site prepared named parameters result body sourceContext evidence capturedSource scope administrative)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized) :
    ∃ origin, prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      ∃ history : History site.code,
        history.native = SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin ∧
        history.ghost = .named origin ∧ history.metadata = state named := by
  obtain ⟨origin, selected, _, _⟩ := compiled.history record
  exact ⟨origin, selected, site.historyAt selected record, rfl, rfl, rfl⟩

/-- A real initial frame read justifies the administrative write. An explicit
prefix frame contract transports that exact token to the generation store;
it is not inferred from native typing or arbitrary preceding code. -/
theorem installed_after_prefix {origin : Word} {before after : Store} {location : Location}
    {saved : Value} {mapping futureMapping : LocationMap}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (read : before.read? location = some saved) (unmapped : location ∉ mapping)
    (preserved : AdministrativePreserved mapping
      (before.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) futureMapping after) :
    location ∉ futureMapping ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) (.named origin) after := by
  have installed := CallableIndexedNamedGeneration.installed selected record read
  have bound := (List.getElem?_eq_some_iff.mp installed.read).1
  obtain ⟨absent, same⟩ := preserved location unmapped bound
  exact ⟨absent, same.trans installed.read, installed.history⟩

/-- Generation and completed reflection at this accepted site, following an
administratively preserving prefix from the real named entry. Runtime capture
authentication is supplied independently and the actual captured environment
is retained, including hidden slots. -/
theorem Site.formation_after_prefix
    {mapping world actual}
    (captured : Captures prepared mapping world scope capturedSource actual)
    (site : Site prepared named parameters result body sourceContext evidence capturedSource scope captured.administrative)
    {origin : Word}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (program : Program) (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout site.code.sourceNode.requirements site.code.sourceNode.coercions [])
    (coercions : site.code.sourceNode.coercions = [])
    {entryStore store : Store} {location : Location} {saved : Value} {entryMap : LocationMap}
    (entryRead : entryStore.read? location = some saved) (unmapped : location ∉ entryMap)
    (preserved : AdministrativePreserved entryMap
      (entryStore.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) mapping store)
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[site.code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location)) :
    Dynamic.ExpressionEvaluates program sourceContext evidence (source named) capturedSource heap site.code.id
      (.closure (closure named parameters result body sourceContext evidence capturedSource)) heap ∧
    Evaluates actual store (site.code.lowered.expression.rename captured.embedding)
      (.inRight .word (value site.code captured.embedding
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) actual)) store ∧
    Represents prepared mapping world (FunctionValues.sourceType (closure named parameters result body sourceContext evidence capturedSource))
      (.closure (closure named parameters result body sourceContext evidence capturedSource))
      (value site.code captured.embedding (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) actual)
      (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) := by
  obtain ⟨_, cell⟩ := installed_after_prefix selected record entryRead unmapped preserved
  exact formation (function := closure named parameters result body sourceContext evidence capturedSource) captured site.code (site.historyAt selected record) program heap ordinary coercions stored reference cell.read

theorem Site.reflects_after_prefix
    {mapping world actual}
    (captured : Captures prepared mapping world scope capturedSource actual)
    (site : Site prepared named parameters result body sourceContext evidence capturedSource scope captured.administrative)
    {origin : Word}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (program : Program) (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout site.code.sourceNode.requirements site.code.sourceNode.coercions [])
    (coercions : site.code.sourceNode.coercions = [])
    {entryStore store after : Store} {location : Location} {saved output : Value} {entryMap : LocationMap}
    (entryRead : entryStore.read? location = some saved) (unmapped : location ∉ entryMap)
    (preserved : AdministrativePreserved entryMap
      (entryStore.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) mapping store)
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[site.code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (completed : Evaluates actual store (site.code.lowered.expression.rename captured.embedding) output after) :
    output = .inRight .word (value site.code captured.embedding
      (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) actual) ∧ after = store ∧
    Dynamic.ExpressionEvaluates program sourceContext evidence (source named) capturedSource heap site.code.id
      (.closure (closure named parameters result body sourceContext evidence capturedSource)) heap ∧
    Represents prepared mapping world (FunctionValues.sourceType (closure named parameters result body sourceContext evidence capturedSource))
      (.closure (closure named parameters result body sourceContext evidence capturedSource))
      (value site.code captured.embedding (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) actual)
      (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) := by
  obtain ⟨_, cell⟩ := installed_after_prefix selected record entryRead unmapped preserved
  exact reflects (function := closure named parameters result body sourceContext evidence capturedSource) captured site.code (site.historyAt selected record) program heap ordinary coercions stored reference cell.read completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
