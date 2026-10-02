import Solcore.SourceSemantics.CoreLowering.ImperativeNativePolicyTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaScalarNativeTyping

/-! General imperative lambda bodies use the actual statement compiler and
its native callback laws. The parameter fold, manifest, snapshot, descriptor
and generation history remain the production receipts. Concrete source and
callback admission, applied views and generalized parameters are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaImperativeNativeTyping
open Core Frontend SourceInference
open CallableIndexedParameterNativeTyping CallableIndexedLambdaCertificates CallableIndexedLambdaGeneration CallableIndexedNamedGeneration

/-- Static laws for the exact body callback and its actual entry scope. There
is no singleton/scalar restriction or whole-body typing/execution field. -/
structure BodyProfile {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered)
    (definitions : DataEnvironment) (administrative : Core.Context) where
  loops : SourceCoreLoops.Policy
  callback : lowerBody (FunctionCode.children policy lowerBody fuel compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy loops
  admitted : ImperativeNativePolicyTyping.Admission
  laws : ImperativeNativePolicyTyping.PolicyLaws definitions administrative admitted loops
  allowed : admitted view receipt.bodyScope

theorem body_native {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered}
    {definitions : DataEnvironment} {administrative : Core.Context}
    (profile : BodyProfile receipt definitions administrative)
    (wellFormed : receipt.resultCore.WellFormed definitions) :
    HasType (SourceCoreLocalCell.coreContext receipt.bodyScope ++ administrative) receipt.body
      (LanguageResult.resultType receipt.resultCore) definitions := by
  have accepted := receipt.bodyCompiled
  rw [profile.callback] at accepted
  exact ImperativeNativePolicyTyping.body_native profile.laws profile.allowed wellFormed accepted

private theorem projected_parameters {checked : SourceCoreCompatibleCatalog.Checked}
    (bindings : List CallableIndexedParameterCertificates.Binding)
    (projected : ∀ binding ∈ bindings, SourceCoreCompatibleDataExpressions.projectType checked
      (.binder binding.1.id) binding.1.scheme.body = .ok binding.2) :
    checked.catalog.project (TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body))) =
      .ok (packed (bindings.map Prod.snd)) := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    have head := CompatibleExpressionReads.projectType_of_accepted (projected binding (by simp))
    cases rest with
    | nil => exact head
    | cons next tail =>
      have rest := ih (fun item member => projected item (List.mem_cons_of_mem _ member))
      change (do pure (Ty.product (← checked.catalog.project binding.1.scheme.body)
        (← checked.catalog.project (TypeSystem.Ty.productMany ((next :: tail).map
          (fun binding : CallableIndexedParameterCertificates.Binding => binding.1.scheme.body)))))) = _
      rw [head, rest]
      rfl

theorem certificate_native {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered)
    (administrative : Core.Context) (profile : BodyProfile receipt prepared.layouts.definitions administrative)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
      prepared.ancestry.layout.frame prepared.base.globals.length
      (prepared.layouts.allocatorAt compilation.owner [] (fun error => .sourceAllocation (reprStr error)))))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates compilation.owner [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry compilation.owner [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.lambda compilation.owner id []))
    (administrativePrefix : compilation.administrativePrefix = 1)
    (parameterProjections : ∀ binding ∈ receipt.loweredParameters, SourceCoreCompatibleDataExpressions.projectType checked
      (.binder binding.1.id) binding.1.scheme.body = .ok binding.2)
    (ordinary : ∀ binding ∈ receipt.loweredParameters,
      view.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type)) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions := by
  have binderTree := FunctionCode.Parameters.of_accepted receipt.parametersCompiled
  have projected := projected_parameters receipt.loweredParameters parameterProjections
  have parameter := CompatibleExpressionReads.projectType_of_accepted (projector ▸ receipt.parameterProjected)
  have bundle : receipt.parameterCore = packed (receipt.loweredParameters.map Prod.snd) := by
    have sameTypes : receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
        parameters.map (·.scheme.body) := by
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) binderTree.binders
    rw [sameTypes, receipt.parameterTypes] at projected
    exact Except.ok.inj (parameter.symm.trans projected)
  have parameterWF := fun binding member => CompatibleExpressionReads.projectType_wellFormed (parameterProjections binding member)
  have resultWF := (CompatibleExpressionReads.projectType_wellFormed (projector ▸ receipt.resultProjected)).extend_definitions
    (CallableIndexedAmbient.ambientDefinitions prepared).basePrefix
  exact CallableIndexedLambdaScalarNativeTyping.certificate_native prepared receipt projector allocation manifest expressionHook
    callables descriptor administrativePrefix bundle parameterWF ordinary scopeWF administrative current (body_native profile resultWF)

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
    (contracts : checked.catalog.callableContracts = true)
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
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    (receipt : Certificate policy lowerBody fuel (context prepared named) view scope id node
      parameters result body reported reasonAt lowered)
    (profile : BodyProfile receipt prepared.layouts.definitions administrative)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (allocator prepared named))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (binderPolicy : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
      (representation prepared) prepared.base.locals named.signature.key [])
    (monomorphic : ∀ binder ∈ parameters, binder.scheme.quantified = [])
    (ordinaryParameters : ∀ binder ∈ parameters, view.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type)) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered := by
  have hook := receipt.expressionHook
  rw [expressionHook] at hook
  obtain ⟨origin, _, selected, _, _, _, _, _⟩ := CallableIndexedFormation.expressionHook_receipt prepared.ancestry hook
  rw [(lookupExpression?_sound found).2] at selected
  obtain ⟨descriptor⟩ := descriptor_exists _ selected
  have projections := CallableIndexedLambdaScalarNativeTyping.parameter_projections receipt.parametersCompiled binderPolicy (by rfl) monomorphic
  have ordinaryBindings : ∀ binding ∈ receipt.loweredParameters,
      view.inputs.any (fun input => decide (input.id = binding.1.id)) = false := by
    intro binding member
    apply ordinaryParameters binding.1
    rw [← (FunctionCode.Parameters.of_accepted receipt.parametersCompiled).binders]
    exact List.mem_map.mpr ⟨binding, member, rfl⟩
  have native := certificate_native prepared receipt administrative profile projector allocation manifest expressionHook
    callables descriptor rfl projections ordinaryBindings scopeWF current
  exact CallableIndexedLambdaGeneration.of_contextual prepared compiled record sourceContext evidence captured contracts
    viewOfSource sourceFound sourceForm found form owner requirements coercions ordinary read accepted native

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaImperativeNativeTyping
