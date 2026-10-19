import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds

/-! Independent Source lifting follows the actual mixed physical state after
an expression or scoped branch. Exact descriptor effects preserve the owning
frame and its allocation readiness at every reached continuation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open SelectedCompilationStageBodyLiftBounds

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}

def Ready (environment : Dynamic.Environment) (canonical actual : Environment)
    (actualContext : Core.Context) (embedding : Renaming) (heap : Dynamic.Heap) : Prop :=
  ∃ mapping world store,
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions ∧
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world heap store ∧
    Dynamic.EnvironmentAgrees heap context.locals environment ∧
    EnvironmentsAgree embedding canonical actual ∧
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions ∧
    Dynamic.SourceRuntimeValid program context (source named) ∧ invocation.evidence.Covers context ∧
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements ∧
    ∃ initial : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩,
      Admission bridge context initial ∧
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
        named.signature.key [] mapping world heap store environment ∧
      ∃ (physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world heap store environment)
        (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys),
        owner.key.frameLocation = physical.location ∧
        ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native

variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {embedding : Renaming}

local notation "ReadyAt" => Ready (named := named) (administrative := administrative)
  (invocation := invocation) (context := context) (scope := scope)
  bridge producer environment canonical actual actualContext embedding

theorem test_value {child : Nat} {before after : Dynamic.Heap} {value : Dynamic.Value}
    {certificate : GenericExpressionMeaning.Certificate} {test : ExpressionId} {node : ExpressionNode} {code : Expr}
    (children : ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificate size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults size)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (found : invocation.source.lookupExpression? test = some node) (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool,code⟩)
    (ready : ReadyAt before)
    (trace : SourceExecutionSize.ExpressionEvaluates program child context invocation.evidence invocation.source
      environment before test value after) :
    (∃ origin call reason reached, Staging.Recursive.Expression program registry invocation context environment before test
      (.fault (.stage origin call reason)) reached) ∨
    (Staging.Recursive.Expression program registry invocation context environment before test (.value value) after ∧
      ReadyAt after ∧ Dynamic.BooleanValue value) := by
  obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
    initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩ := ready
  obtain ⟨staged,reached,lifted,adapted⟩ := children child generated found typed
    environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation (.value trace)
  cases adapted with
  | rejected origin call reason reached => exact .inl ⟨origin,call,reason,reached,lifted⟩
  | completed =>
    obtain ⟨size,measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    obtain ⟨_,finalStore,finalMap,finalWorld,_,represented,finalHeaps,maps,worlds,preserved,metadata,effect,
      last,_,post⟩ := preservation size generated found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation measured
    have boolean : Dynamic.BooleanValue value := by
      cases represented with
      | value payload =>
        obtain ⟨truth,same,_⟩ := booleans (nodeType ▸ payload)
        rw [same]
        trivial
    exact .inr ⟨lifted,⟨finalMap,finalWorld,finalStore,environments.extend maps worlds,finalHeaps,
      locals.mono metadata,agrees,actualTyped.weaken worlds,runtime,covers,sameLedger,
      last,post.at_value.2,authority.transport effect,physical.transport effect preserved,owner,sameLocation,allocationReady⟩,boolean⟩

theorem body_prefix {size : Nat} {before after : Dynamic.Heap}
    {statements : List StatementId} {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (body : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false statements)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements)
    (ready : ReadyAt before)
    (trace : RecursiveNamedCallBounds.StatementsOutcome program size context invocation.evidence invocation.source
      environment before statements finalContext outcome after) :
    BodyLift program registry false invocation context environment before statements finalContext outcome after := by
  obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
    initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩ := ready
  exact body environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation allocationReady trace

theorem body_ready {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context}
    {finalEnvironment : Dynamic.Environment} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (preservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type code size)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements)
    (ready : ReadyAt before)
    (trace : Staging.Recursive.StatementsIn program registry false invocation context environment before statements
      finalContext (.fallthrough finalEnvironment) after) : ReadyAt after := by
  obtain ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
    initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩ := ready
  obtain ⟨size,measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace trace
  obtain ⟨_,finalStore,finalMap,finalWorld,_,_,finalHeaps,maps,worlds,preserved,metadata,effect,
    last,_,post⟩ := preservation size environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation allocationReady measured
  exact ⟨finalMap,finalWorld,finalStore,environments.extend maps worlds,finalHeaps,
    locals.mono metadata,agrees,actualTyped.weaken worlds,runtime,covers,sameLedger,
    last,post,authority.transport effect,physical.transport effect preserved,owner,sameLocation,allocationReady⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowReadiness
