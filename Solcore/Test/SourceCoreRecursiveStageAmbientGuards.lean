import Solcore.SourceSemantics.CoreLowering.RecursiveStageArguments
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientStageOrigins
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts

/-! Actual guard rows under one ambient value model. Function provenance is a
separate static supply obligation at function leaves; ordinary data and the
entire heap continue to use their original compatible representation. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveStageAmbientGuards
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
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
  CompatibleAmbientStageOrigins.FunctionOrigins functions registry sidecar site

/-- Refinement affects only function leaves. Its value properties and all
world extensions are inherited from the same ambient function model. -/
def with_origins (functions : FunctionModel checked.catalog ambient)
    (sidecar : SourceCoreStageContracts.Sidecar) (site : SourceCoreCallableContracts.Callsite) :
    FunctionModel checked.catalog ambient :=
  CompatibleAmbientStageOrigins.with_origins functions sidecar site

theorem supplied_origins : FunctionOrigins (with_origins functions sidecar site) rawRegistry sidecar site :=
  CompatibleAmbientStageOrigins.supplied_origins

/-- Forgetting provenance never strengthens a value relation. -/
theorem forget_origin {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (represented : (with_origins functions sidecar site).Represents rawRegistry mapping world sourceType source carrier type) :
    functions.Represents rawRegistry mapping world sourceType source carrier type :=
  CompatibleAmbientStageOrigins.forget_origin represented

/-- The converse requires the static origin supply for this exact function
model. It is not inferred from a related heap or native typing. -/
theorem refinement_iff (origins : FunctionOrigins functions rawRegistry sidecar site)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty} :
    (with_origins functions sidecar site).Represents rawRegistry mapping world sourceType source carrier type ↔
      functions.Represents rawRegistry mapping world sourceType source carrier type :=
  CompatibleAmbientStageOrigins.refinement_iff origins

theorem related_origin
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (represented : ValueRep checked rawRegistry functions mapping world sourceType source carrier type)
    (callable : Staging.CallBoundary.UserCallable source) :
    CallableLedger.OriginRep sidecar.plan site.table source carrier :=
  CompatibleAmbientStageOrigins.related_origin origins represented callable

theorem covers_from_rows {call : ExpressionId} {arguments : List ExpressionId}
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    (rows : CallableLedger.Rows sidecar site call arguments)
    (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      (CallableLedger.frame sidecar) site call arguments sourceType type :=
  CompatibleAmbientStageOrigins.covers_from_rows origins rows sourceType type

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
  CompatibleAmbientStageOrigins.actual_coverage prepared issued caller contains form origins sourceType type

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
  CompatibleAmbientStageOrigins.actual_named_leaf accepted descriptor selected represented

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
    CallableLedger.OriginRep plan table (.closure function) (.pair raw (.word descriptor.id)) :=
  CompatibleAmbientStageOrigins.actual_lambda_origin accepted descriptor receipt metadata unique found form raw

abbrev actual_builtin_origin := @RecursiveStageProjection.builtin_origin

/-- Actual preparation covers the refined function model without adding an
origin condition to data or requiring a separate function-origin callback. -/
theorem refined_actual_coverage {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiled native)
    {context : SourceCoreFunctions.Context} {node : ExpressionNode}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (issued : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor
      (CompatibleAmbientHeap.payloadModel checked rawRegistry (with_origins functions sidecar site))
      (CallableLedger.frame sidecar) site node.id arguments sourceType type :=
  CompatibleAmbientStageOrigins.actual_coverage prepared issued caller contains form
    CompatibleAmbientStageOrigins.supplied_origins sourceType type

abbrev callee_fault := @RecursiveStageMeaning.preserves_callee_fault_for
abbrev plain_guard_rejection := @CallStageBoundary.preserves_rejection_for

/-- Ordinary data remains representable without any callable origin. -/
theorem data_without_origin (mapping : LocationMap) (world : StoreTyping) :
    (CompatibleAmbientHeap.payloadModel checked rawRegistry functions).Represents mapping world
      (.product .word .unit) (.product (.word Word.zero) .unit) (.pair (.word Word.zero) .unit) (.product .word .unit) ∧
    ¬ CallableLedger.OriginRep sidecar.plan site.table
      (.product (.word Word.zero) .unit) (.pair (.word Word.zero) .unit) := by
  exact ⟨.product (.word _) .unit, by intro impossible; cases impossible⟩

theorem builtin_has_no_user_contract (function : Dynamic.BuiltinFunction)
    (contract : Staging.CallGuard.Contract) :
    ¬ (CallableLedger.frame sidecar).Binds (.builtin function) contract := by
  intro impossible
  cases impossible

section Prefixes
open RecursiveStageMeaning
local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "catalog" => CompatibleEquality.storageCatalog checked.catalog

theorem guard_rejection
    {program : SourceSemantics.Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {certificate : Certificate} {faults : FaultRep} {site : SourceCoreCallableContracts.Callsite}
    {call callee : ExpressionId} {arguments : List ExpressionId} {scope : SourceCoreLocalCell.Scope}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (childMeaning : PreservesFor model program registry frame context certificate faults)
    (sameGuards : frame.guards = CallableLedger.frame sidecar)
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    (rows : CallableLedger.Rows sidecar site call arguments)
    (reasonMeaning : ∀ reason token, CallStageBoundary.ReasonRepresents site reason token →
      faults (.stage frame call reason) token)
    (unknown : Word) (result : Ty) (argumentCode : Expr)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {callable : Dynamic.Value} {reason : Staging.CallGuard.Fault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (child : Staging.Recursive.Expression program registry frame context environment before callee (.value callable) after)
    (rejected : Staging.CallBoundary.GuardRejects frame.guards call arguments callable reason) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown result (lowered.expression.rename ξ) argumentCode)
        (.inLeft result (.word token)) finalStore ∧
      faults (.stage frame call reason) token ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have coverage : CallStageBoundary.CoversFor model frame.guards site call arguments node.type lowered.type := by
    rw [sameGuards]
    exact covers_from_rows origins rows node.type lowered.type
  exact RecursiveStageMeaning.preserves_rejection_for certified found childMeaning coverage reasonMeaning
    unknown result argumentCode environments heaps locals layout child rejected

variable {program : SourceSemantics.Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : RecursiveStageMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}
open RecursiveStageMeaning
open DataExpressionSequence (Tree)

theorem argument_fault
    {site : SourceCoreCallableContracts.Callsite} {call callee : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : PreservesFor model program registry frame context certificate faults)
    (sameGuards : frame.guards = CallableLedger.frame sidecar)
    (origins : FunctionOrigins functions rawRegistry sidecar site)
    (rows : CallableLedger.Rows sidecar site call ids)
    (unknown : Word) (resultType : Ty)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before middle after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {callable : Dynamic.Value} {contract : Staging.CallGuard.Contract}
    {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (child : Staging.Recursive.Expression program registry frame context environment before callee (.value callable) middle)
    (bound : frame.guards.Binds callable contract)
    (accepted : Staging.CallBoundary.GuardAccepts frame.guards call ids callable)
    (arguments : Staging.Recursive.Expressions program registry frame context environment middle ids (.fault failure) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown resultType (lowered.expression.rename ξ)
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)) (.inLeft resultType (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have coverage : CallStageBoundary.CoversFor model frame.guards site call ids node.type lowered.type := by
    rw [sameGuards]
    exact covers_from_rows origins rows node.type lowered.type
  exact RecursiveStageArguments.preserves_call_argument_fault_for certified found tree meaning coverage unknown resultType
    environments heaps locals layout child bound accepted arguments

end Prefixes

end Tests.SourceCoreRecursiveStageAmbientGuards
