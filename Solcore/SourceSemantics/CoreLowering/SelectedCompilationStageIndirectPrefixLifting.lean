import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectCalleeLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectSourceTrace
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectValuesPrefix

/-! The original ordinary indirect call reaches either its exact staged
outcome or the genuine post-argument application prefix. Every nested rejection
keeps the heap reached before the remaining ordinary effects. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectPrefixLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open Staging.Recursive.Lifting (ExpressionLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functions : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  [positive : CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual headers keys bodyRegistry semanticFaults profile functions]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (certified : certificate scope callee compiler.calleeCode)
  (sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


def ApplicationPrefix (budget : Nat) (plain : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ calleeSize argumentsSize callSize sourceValue calleeHeap argumentsHeap sources callEvidence,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize
      context invocation.evidence callEvidence argumentsHeap sourceValue sources plain after ∧
    callSize < budget ∧
    SelectedCompilationIndirectValuesPrefix.ValuesPrefix
      (functionModel := functions) (registry := registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := port.calleeNode) (sidecar := port.sidecar)
      bridge profile compiler port.prepared initial sourceValue calleeHeap argumentsHeap sources

include positive certified sourceTyped tree unique parentTyped environments heaps locals agrees typed admitted in
theorem lift_prefix (budget : Nat)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ stageSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults stageSize)
    {size : Nat} {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (execution : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      context invocation.evidence invocation.source environment before id plain after)
    (within : size ≤ budget) :
    ExpressionLift (Program.ofChecked compiled.sourceProgram) stages invocation context environment before id plain after ∨
    ApplicationPrefix (functions := functions) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (environment := environment)
      bridge profile compiler port initial budget plain after := by
  have occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  obtain ⟨_parameter, _result, _functionType, argumentTypes, _bundle, _originalType⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.source_rows
      (sourceEq := rfl) (found := port.calleeFound) (sourceParent := port.sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  cases SelectedCompilationStageIndirectSourceTrace.source_inv unique compiler.found compiler.originalForm
    port.sourceParent.coercions compiler.argumentCoercions port.sourceParent.arity execution with
  | calleeFault failed smaller =>
    obtain ⟨outcome, reached, trace, adapted⟩ := children _ (Nat.lt_of_lt_of_le smaller within)
      certified port.calleeFound sourceTyped environments heaps locals agrees typed initial admitted (.fault failed)
    cases adapted with
    | completed => exact .inl ⟨_, _, .calleeFault occurrence trace, .completed⟩
    | rejected origin call reason reached => exact .inl ⟨_, _, .calleeFault occurrence trace, .rejected origin call reason _⟩
  | notCallable evaluated invalid smaller =>
    rcases SelectedCompilationStageIndirectCalleeLifting.callee_value bridge profile compiler port certified sourceTyped
      tree unique parentTyped environments heaps locals agrees typed initial admitted budget children preservation
      evaluated (Nat.lt_of_lt_of_le smaller within) with complete | ⟨carrier, calleeStore, calleeMap, calleeWorld, _calleeTrace, _post, accepted⟩
    · exact .inl complete
    · exact False.elim (invalid accepted.callable)
  | argumentsFault calleeTrace _callable failed calleeSmaller argumentsSmaller =>
    rcases SelectedCompilationStageIndirectCalleeLifting.callee_value bridge profile compiler port certified sourceTyped
      tree unique parentTyped environments heaps locals agrees typed initial admitted budget children preservation
      calleeTrace (Nat.lt_of_lt_of_le calleeSmaller within) with complete | ⟨carrier, calleeStore, calleeMap, calleeWorld, liftedCallee, post, accepted⟩
    · exact .inl complete
    · obtain ⟨_native, _payload, calleeHeaps, maps, worlds, _frame, metadata, reached, _related, post⟩ := post
      obtain ⟨outcome, finalHeap, liftedArguments, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge
        budget tree unique argumentTypes children preservation (environments.extend maps worlds) calleeHeaps
        (locals.mono metadata) agrees (typed.weaken worlds) reached post.at_value.2 failed
        (Nat.le_of_lt (Nat.lt_of_lt_of_le argumentsSmaller within))
      cases adapted with
      | completed => exact .inl ⟨_, _, .argumentsFault occurrence liftedCallee accepted liftedArguments, .completed⟩
      | rejected origin call reason reached =>
        exact .inl ⟨_, _, .argumentsFault occurrence liftedCallee accepted liftedArguments, .rejected origin call reason _⟩
  | apply calleeTrace argumentsTrace called calleeSmaller argumentsSmaller callSmaller =>
    rcases SelectedCompilationStageIndirectCalleeLifting.callee_value bridge profile compiler port certified sourceTyped
      tree unique parentTyped environments heaps locals agrees typed initial admitted budget children preservation
      calleeTrace (Nat.lt_of_lt_of_le calleeSmaller within) with complete | ⟨carrier, calleeStore, calleeMap, calleeWorld, liftedCallee, post, accepted⟩
    · exact .inl complete
    · obtain ⟨_native, _payload, calleeHeaps, maps, worlds, _frame, metadata, reached, _related, post⟩ := post
      obtain ⟨outcome, finalHeap, liftedArguments, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge
        budget tree unique argumentTypes children preservation (environments.extend maps worlds) calleeHeaps
        (locals.mono metadata) agrees (typed.weaken worlds) reached post.at_value.2 argumentsTrace
        (Nat.le_of_lt (Nat.lt_of_lt_of_le argumentsSmaller within))
      cases adapted with
      | rejected origin call reason reached =>
        exact .inl ⟨_, _, .argumentsFault occurrence liftedCallee accepted liftedArguments, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨calleeSize, sizedCallee⟩ := Staging.Recursive.Size.Expression.of_trace liftedCallee
        obtain ⟨argumentsSize, sizedArguments⟩ := Staging.Recursive.Size.Expressions.of_trace liftedArguments
        have valuePrefix := SelectedCompilationIndirectValuesPrefix.preserves_values
          bridge profile compiler port.prepared rfl certified port.calleeFound sourceTyped environments heaps locals agrees typed
          initial admitted port.caller port.view port.originalUnique port.guardFrame port.sourceParent tree unique parentTyped
          (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize]) (fun size _ => preservation size)
          sizedCallee accepted sizedArguments (Nat.le_refl _)
        exact .inr ⟨_, _, _, _, _, _, _, _, sizedCallee, accepted, sizedArguments,
          called, Nat.lt_of_lt_of_le callSmaller within, valuePrefix⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndirectPrefixLifting
