import Solcore.SourceSemantics.Staging.RecursiveTraceProperties
import Solcore.SourceSemantics.CoreLowering.CallStageBoundary
import Solcore.SourceSemantics.CoreLowering.ContractedFunctionCalls

/-! Universal semantic interfaces for the recursive staged profile. Static
expression/body certificates remain free of execution assumptions. The semantic
IHs range over related heaps and real lexical renamings, and their fault relation
retains the failing invocation scope. An actual compiler profile must establish
these IHs and the static closure-scope registry; Core typing does not supply them. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageMeaning
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly

abbrev Certificate := GenericExpressionMeaning.Certificate
abbrev FaultRep := Staging.Recursive.Failure → Word → Prop

inductive ResultRepresentsFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : StoreTyping) (sourceType : TypeSystem.Ty) (type : Ty) (faults : FaultRep) :
    Staging.Recursive.Outcome → Value → Prop where
  | value {source value} (represented : model.Represents mapping world sourceType source value type) :
      ResultRepresentsFor model mapping world sourceType type faults (.value source) (.inRight .word value)
  | fault {failure token} (represented : faults failure token) :
      ResultRepresentsFor model mapping world sourceType type faults (.fault failure) (.inLeft type (.word token))

def PreservesFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (registry : Staging.Recursive.Registry) (frame : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, frame.source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Staging.Recursive.Expression program registry frame context environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def ReflectsFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (registry : Staging.Recursive.Registry) (frame : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, frame.source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expression program registry frame context environment before id outcome after ∧
      ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-- A completed staged body keeps both its actual statement exit and the
source rule converting that exit to a callable result. -/
def BodyTrace (program : Program) (registry : Staging.Recursive.Registry) (frame : Staging.Recursive.Scope) (function : Dynamic.Closure)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ finalContext control,
    Staging.Recursive.Statements program registry frame context environment before function.body finalContext control after ∧
      Staging.Recursive.BodyResult function.resultType control outcome

def BodyPreservesFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (registry : Staging.Recursive.Registry) (frame : Staging.Recursive.Scope) (function : Dynamic.Closure)
    (certificate : FunctionCode.BodyCertificate) (faults : FaultRep) : Prop :=
  ∀ {scope type body}, certificate function.source scope function.body type body →
  ∀ {context staticFinal facts}, StatementsHaveType function.source
    {returnType := function.resultType, loopDepth := 0} context function.body staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    BodyTrace program registry frame function context environment before outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (body.rename ξ) value finalStore ∧
      ResultRepresentsFor model finalMap finalWorld function.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def BodyReflectsFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (registry : Staging.Recursive.Registry) (frame : Staging.Recursive.Scope) (function : Dynamic.Closure)
    (certificate : FunctionCode.BodyCertificate) (faults : FaultRep) : Prop :=
  ∀ {scope type body}, certificate function.source scope function.body type body →
  ∀ {context staticFinal facts}, StatementsHaveType function.source
    {returnType := function.resultType, loopDepth := 0} context function.body staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (body.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      BodyTrace program registry frame function context environment before outcome after ∧
      ResultRepresentsFor model finalMap finalWorld function.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

theorem ResultRepresentsFor.extend {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions} {mapping futureMapping : LocationMap}
    {world futureWorld : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty} {faults : FaultRep}
    {outcome : Staging.Recursive.Outcome} {value : Value}
    (represented : ResultRepresentsFor model mapping world sourceType type faults outcome value)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ResultRepresentsFor model futureMapping futureWorld sourceType type faults outcome value := by
  cases represented with
  | value payload => exact .value (model.extend payload maps worlds)
  | fault failure => exact .fault failure

/-- Legacy interfaces use the same relation with the original catalog projection and definitions. -/
abbrev ResultRepresents {catalog : SourceCoreDataCatalog.Catalog} :=
  @ResultRepresentsFor catalog (GenericHeap.strictProjection catalog) catalog.definitions

abbrev Preserves {catalog : SourceCoreDataCatalog.Catalog} :=
  @PreservesFor catalog (GenericHeap.strictProjection catalog) catalog.definitions

abbrev Reflects {catalog : SourceCoreDataCatalog.Catalog} :=
  @ReflectsFor catalog (GenericHeap.strictProjection catalog) catalog.definitions

abbrev BodyPreserves {catalog : SourceCoreDataCatalog.Catalog} :=
  @BodyPreservesFor catalog (GenericHeap.strictProjection catalog) catalog.definitions

abbrev BodyReflects {catalog : SourceCoreDataCatalog.Catalog} :=
  @BodyReflectsFor catalog (GenericHeap.strictProjection catalog) catalog.definitions

abbrev ResultRepresents.value {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {faults : FaultRep} {source : Dynamic.Value} {value : Value}
    (represented : model.Represents mapping world sourceType source value type) :
    ResultRepresents model mapping world sourceType type faults (.value source) (.inRight .word value) :=
  ResultRepresentsFor.value represented

abbrev ResultRepresents.fault {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {faults : FaultRep}
    {failure : Staging.Recursive.Failure} {token : Word} (represented : faults failure token) :
    ResultRepresents model mapping world sourceType type faults (.fault failure) (.inLeft type (.word token)) :=
  ResultRepresentsFor.fault represented

theorem ResultRepresents.extend {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog} {mapping futureMapping : LocationMap}
    {world futureWorld : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty} {faults : FaultRep}
    {outcome : Staging.Recursive.Outcome} {value : Value}
    (represented : ResultRepresents model mapping world sourceType type faults outcome value)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ResultRepresents model futureMapping futureWorld sourceType type faults outcome value :=
  ResultRepresentsFor.extend represented maps worlds

/-- A nested failure in the callee bypasses both outer gates and all
arguments. Its original fault label and the callee's exact heap survive. -/
theorem preserves_callee_fault {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {certificate : Certificate} {faults : FaultRep}
    {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId} {scope : SourceCoreLocalCell.Scope}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (childMeaning : Preserves model program registry frame context certificate faults)
    (unknown : Word) (result : Ty) (argumentCode : Expr)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (child : Staging.Recursive.Expression program registry frame context environment before callee (.fault failure) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown result (lowered.expression.rename ξ) argumentCode)
        (.inLeft result (.word token)) finalStore ∧ faults failure token ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata⟩ :=
    childMeaning certified found environments heaps locals layout child
  cases represented with
  | fault reason =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      CallableContract.call_callee_failure site.gates unknown evaluated,
      reason, finalHeaps, maps, worlds, preserved, metadata⟩

/-- The real Core gate follows a recursively staged callee prefix. The IH can
itself contain nested argument/body guards; no plain child execution is used. -/
theorem preserves_rejection {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {certificate : Certificate} {faults : FaultRep} {site : SourceCoreCallableContracts.Callsite}
    {call callee : ExpressionId} {arguments : List ExpressionId} {scope : SourceCoreLocalCell.Scope}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (childMeaning : Preserves model program registry frame context certificate faults)
    (coverage : CallStageBoundary.Covers model frame.guards site call arguments node.type lowered.type)
    (reasonMeaning : ∀ reason token, CallStageBoundary.ReasonRepresents site reason token →
      faults (.stage frame call reason) token)
    (unknown : Word) (result : Ty) (argumentCode : Expr)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {callable : Dynamic.Value} {reason : Staging.CallGuard.Fault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
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
  obtain ⟨carrier, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata⟩ :=
    childMeaning certified found environments heaps locals layout child
  cases represented with
  | value payload =>
    obtain ⟨contract, bound⟩ : ∃ contract, frame.guards.Binds callable contract := by
      cases rejected with | contract bound _ => exact ⟨_, bound⟩
    obtain ⟨dispatch⟩ := coverage payload bound
    rw [dispatch.shape] at evaluated
    exact ⟨dispatch.reason reason, finalStore, finalMap, finalWorld,
      site.lower_stage_failure unknown dispatch.row _ dispatch.found (dispatch.rejected rejected) evaluated,
      reasonMeaning reason _ (dispatch.reason_represents reason), finalHeaps, maps, worlds, preserved, metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveStageMeaning
