import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaBinderProjections
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredNativePackReceipts

/-! The actual contextual Site supplies its selected binder projection row.
The complete same-Code Source projection also determines its parameter and
result projections. Concrete ordinary and principal associations retain all
capture, history and Source-origin fields at this same Site. Raw Source bundle
equality, genuine arity and call-site stage facts remain separate receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPackReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaGeneration
open CallableIndexedOwnedStoredNativePackReceipts

/-- A complete genuine Source function projection retains both native
endpoints. This finite inversion recovers no Source facts from native values. -/
theorem Code.source_projections {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative)
    (profile : checked.catalog.callableContracts = true) :
    checked.catalog.project (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) =
      .ok code.receipt.parameterCore ∧
    checked.catalog.project function.resultType = .ok code.receipt.resultCore := by
  have projected := code.projection
  change (do pure (checked.catalog.functionType
    (← checked.catalog.project (TypeSystem.Ty.productMany (function.parameters.map (fun binder : TypedBinder => binder.scheme.body))))
    (← checked.catalog.project function.resultType))) = _ at projected
  cases parameterEq : checked.catalog.project
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder : TypedBinder => binder.scheme.body))) with
  | error error =>
    simp only [parameterEq, bind, Except.bind] at projected
    cases projected
  | ok parameter =>
    cases resultEq : checked.catalog.project function.resultType with
    | error error =>
      simp only [parameterEq, resultEq, bind, Except.bind] at projected
      cases projected
    | ok result =>
      simp only [parameterEq, resultEq, bind, Except.bind, pure, Except.pure,
        SourceCoreCompatibleCatalog.Catalog.functionType, profile, ↓reduceIte, Except.ok.injEq] at projected
      obtain ⟨parameterSame, resultSame⟩ := callable_parameters projected
      cases parameterSame
      cases resultSame
      exact ⟨rfl, rfl⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : CallableIndexedNamedGeneration.Named}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- The actual producer's retained binder policy and genuine Source extension
close the packed binder type for this same returned Site. -/
theorem Site.binding_pack
    (site : Site compiled.indexed named parameters result statements sourceContext evidence environment scope administrative)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (binderPolicy : site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
      ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
      compiled.indexed.base.locals named.signature.key [])
    {types : List TypeSystem.Ty} {bodyContext : SourceSemantics.Context}
    (extended : MonoBindersExtend (CallableIndexedNamedGeneration.source named).owner
      sourceContext parameters types bodyContext) :
    site.code.receipt.parameterCore =
      SourceCoreCompatibleCatalog.packTypes (site.code.receipt.loweredParameters.map Prod.snd) :=
  code_binding_pack site.code profile
    (CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings site binderPolicy extended)
    (Code.source_projections site.code profile).2

section Compiler
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope environment actual)
  (site : Site compiled.indexed named parameters result statements sourceContext evidence environment
    scope captured.administrative)
  (history : History site.code)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (binderPolicy : site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
    compiled.indexed.base.locals named.signature.key [])
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {callerScope : SourceCoreBasic.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {rawType : TypeSystem.Ty}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source callerScope
    id callee ids metadata reasonAt lowered)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (represented : ValueRep compiled.compatible.checked registry functions mapping world rawType
    (.closure (closure named parameters result statements sourceContext evidence environment))
    (value site.code captured.embedding history.native actual) receipt.calleeCode.type)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (referenceIndex : site.code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
  (typed : RuntimeValueHasType world (value site.code captured.embedding history.native actual)
    (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore)
    compiled.indexed.layouts.definitions)
  (escaped : faults .controlEscapedFunction site.code.compilation.internalReason)

include profile binderPolicy actualFunctionType represented owner observed referenceIndex typed escaped

/-- The ordinary association is constructed from the exact Site Code and its
complete actual Source origin, so its selected row is the producer's row. -/
theorem compiler_binding_pack_of_ordinary_site
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support site.code registry faults)
    (sourceOrigin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin support history)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial compiled.compatible.checked) support.caller)
    (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source named)
      (support.expressionSyntax (CallableIndexedNamedGeneration.source named)) support.body.context
      (.statements true statements) result) :
    SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (site.code.receipt.loweredParameters.map Prod.snd) := by
  have association : CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
      (closure named parameters result statements sourceContext evidence environment)
      (value site.code captured.embedding history.native actual) site.code.receipt.loweredParameters
      site.code.receipt.parameterCore site.code.receipt.resultCore :=
    CallableIndexedOwnedStoredClosureInvocation.Association.ordinary
      (headers := headers) (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (function := closure named parameters result statements sourceContext evidence environment)
      (scope := scope) (actual := actual)
      owner captured site.code history support sourceOrigin prefixContext observed referenceIndex typed escaped syntaxTree
  exact (compiler_parameter_pack receipt actualFunctionType association represented).trans
    (Site.binding_pack site profile binderPolicy support.body.extended)

/-- The principal association keeps its authentic leading bundle and full
Source origin beside this same actual Site and selected binder row. -/
theorem compiler_binding_pack_of_principal_site
    (support : CallableIndexedOwnedMethodLambdaSupport.Support site.code registry faults)
    (sourceOrigin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
    (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
    (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source named)
      (support.expressionSyntax (CallableIndexedNamedGeneration.source named)) support.body.context
      (.statements true statements) result) :
    SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (site.code.receipt.loweredParameters.map Prod.snd) := by
  have association : CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
      (closure named parameters result statements sourceContext evidence environment)
      (value site.code captured.embedding history.native actual) site.code.receipt.loweredParameters
      site.code.receipt.parameterCore site.code.receipt.resultCore :=
    CallableIndexedOwnedStoredClosureInvocation.Association.principal
      (headers := headers) (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (function := closure named parameters result statements sourceContext evidence environment)
      (scope := scope) (actual := actual)
      owner captured site.code history support sourceOrigin observed leading referenceIndex typed escaped syntaxTree
  exact (compiler_parameter_pack receipt actualFunctionType association represented).trans
    (Site.binding_pack site profile binderPolicy support.body.extended)

end Compiler
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPackReceipts
