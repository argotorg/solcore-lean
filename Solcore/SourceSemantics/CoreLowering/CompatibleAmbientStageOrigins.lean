import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews

/-! Actual callable origins at compatible function leaves supply the retained
stage dispatch rows under the same ambient model. Data and heap relations keep
their original representation; source provenance comes from explicit factory
receipts and never from native callable typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleAmbientStageOrigins
open Core Frontend SourceInference
open GeneralHeap CoreProof ReadOnly
open CompatiblePayload RecursiveNamedPreparedStageContracts

variable {checked : SourceCoreCompatibleCatalog.Checked} {rawRegistry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}

/-- This condition records actual origin receipts only for represented function
leaves. It contains no heap relation or execution premise. -/
def FunctionOrigins (functions : FunctionModel checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (sidecar : SourceCoreStageContracts.Sidecar)
    (site : SourceCoreCallableContracts.Callsite) : Prop :=
  ∀ {mapping world sourceType source carrier type},
    functions.Represents registry mapping world sourceType source carrier type →
    CallableLedger.OriginRep sidecar.plan site.table source carrier

/-- Refinement affects only function leaves. Its value properties and all
world extensions are inherited from the same ambient function model. -/
def with_origins (functions : FunctionModel checked.catalog ambient)
    (sidecar : SourceCoreStageContracts.Sidecar) (site : SourceCoreCallableContracts.Callsite) :
    FunctionModel checked.catalog ambient where
  Represents registry mapping world sourceType source carrier type :=
    functions.Represents registry mapping world sourceType source carrier type ∧
      CallableLedger.OriginRep sidecar.plan site.table source carrier
  projection related := functions.projection related.1
  runtime_hasType related := functions.runtime_hasType related.1
  source_function related := functions.source_function related.1
  extend related registry maps worlds := ⟨functions.extend related.1 registry maps worlds, related.2⟩

theorem supplied_origins : FunctionOrigins (with_origins functions sidecar site) rawRegistry sidecar site :=
  fun related => related.2

/-- Forgetting provenance never strengthens a value relation. -/
theorem forget_origin {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (represented : (with_origins functions sidecar site).Represents rawRegistry mapping world sourceType source carrier type) :
    functions.Represents rawRegistry mapping world sourceType source carrier type := represented.1

/-- The converse requires the static origin supply for this exact function
model. It is not inferred from a related heap or native typing. -/
theorem refinement_iff (origins : FunctionOrigins functions rawRegistry sidecar site)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty} :
    (with_origins functions sidecar site).Represents rawRegistry mapping world sourceType source carrier type ↔
      functions.Represents rawRegistry mapping world sourceType source carrier type :=
  ⟨forget_origin, fun represented => ⟨represented, origins represented⟩⟩

theorem related_origin
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (represented : ValueRep checked rawRegistry functions mapping world sourceType source carrier type)
    (callable : Staging.CallBoundary.UserCallable source) :
    CallableLedger.OriginRep sidecar.plan site.table source carrier := by
  induction represented using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | proxy | constructed | mappingValue => cases callable
  | function related => exact origins related
  | compatible _ _ ih => exact ih callable
  | nil | cons | empty | entry | absent | present => trivial

theorem covers_from_rows {call : ExpressionId} {arguments : List ExpressionId}
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    (rows : CallableLedger.Rows sidecar site call arguments)
    (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      (CallableLedger.frame sidecar) site call arguments sourceType type := by
  intro mapping world source carrier contract represented bound
  exact CallableLedger.dispatch rows (related_origin origins represented (CallableLedger.Binds.userCallable bound)) bound

/-- The real public artifact supplies every original guard row. Only actual
function-leaf provenance remains separate from that compiler receipt. -/
theorem actual_coverage {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiled native)
    {context : SourceCoreFunctions.Context} {node : ExpressionNode}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (issued : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      (CallableLedger.frame sidecar) site node.id arguments sourceType type :=
  covers_from_rows origins (prepared.rows issued caller contains form) sourceType type

/-- Actual source selection and descriptor preparation supply the extra
function-leaf receipt while its original code/capture relation stays explicit. -/
theorem actual_named_leaf {program : CheckedProgram}
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {key : SourceCoreStageCodebook.Key} {function : Dynamic.GlobalFunction}
    (accepted : SourceCoreStageCodebook.prepareWithProjection program sidecar.plan project limits firstId = .ok site.table)
    (descriptor : SourceCoreCallableContracts.Descriptor site.table (.named key))
    (selected : SourceCompilationPlan.exactInstantiationKey sidecar.plan function.instantiation = .ok key)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {raw : Value} {type : Ty}
    (represented : functions.Represents rawRegistry mapping world sourceType (.global function)
      (.pair raw (.word descriptor.id)) type) :
    (with_origins functions sidecar site).Represents rawRegistry mapping world sourceType (.global function)
      (.pair raw (.word descriptor.id)) type :=
  ⟨represented, RecursiveStageProjection.named_origin accepted descriptor selected raw⟩

theorem actual_lambda_origin {program : CheckedProgram}
    {plan : SourceCoreStageCodebook.Plan}
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat} {table : SourceCoreStageCodebook.Table}
    {owner : SourceCoreStageCodebook.Key} {id : ExpressionId} {active : TypeSystem.Substitution}
    {function : Dynamic.Closure} {view : TypedSource} {node : ExpressionNode}
    (accepted : SourceCoreStageCodebook.prepareWithProjection program plan project limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda owner id active))
    (receipt : LambdaSourceAlignment.SourceReceipt program plan owner active function.source)
    (metadata : LambdaMetadataViews.MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (found : view.lookupExpression? id = some node)
    (form : node.form = .lambda function.parameters function.resultType function.body) (raw : Value) :
    CallableLedger.OriginRep plan table (.closure function) (.pair raw (.word descriptor.id)) := by
  obtain ⟨actual⟩ := RecursiveStageProjection.lambda_site_of_descriptor accepted descriptor
  have origin := LambdaMetadataViews.lambda_origin receipt actual.original metadata unique found form
  have represented := CallableLedger.OriginRep.closure (raw := raw)
    actual.member actual.origin actual.retained origin
  simpa only [actual.id_eq] using represented

abbrev actual_builtin_origin := @RecursiveStageProjection.builtin_origin


end Solcore.SourceSemantics.CoreLowering.CompatibleAmbientStageOrigins
