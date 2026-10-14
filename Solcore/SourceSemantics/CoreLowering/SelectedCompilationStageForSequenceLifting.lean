import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSourceInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSequenceLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageWhileLifting
open SelectedCompilationStageForInitialBounds
open CallableIndexedOwnedAdmittedStagedConditionalHeads
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {items postItems : List ForItemForm}
  {expected : TypeSystem.Ty} {type : Ty} {initialCode : Expr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


variable {mode : Bool} {id : StatementId} {statement : StatementNode}
  {rest : List StatementId} {selfReason : Word}

/-- Lift the actual for head and precisely the suffix reached after normal
completion. Earlier returns and genuine failures retain their original scope. -/
theorem lifts {budget : Nat}
    (initialLift : InitializersLifts (administrative := administrative) (receiving := receiving) (frame := frame)
      (globals := globals) (context := context) (scope := scope) (stages := stages) (invocation := invocation)
      bridge functions condition items test postItems statements budget)
    (initialPreservation : ∀ n, CallableIndexedOwnedAdmittedStagedForHeadContracts.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope items test postItems statements expected type initialCode n)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .forLoop items test postItems statements)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope mode rest budget) :
    FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
    finalContext outcome after trace
  have ready : PhysicalReady (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (context := context) (scope := scope)
      bridge functions condition environment canonical actual actualContext ξ contextLocation native before :=
    ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
      initial, conditioned, admitted⟩
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique statementFound
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨headSize, reason, headSmaller, rfl, rfl, failed⟩ |
    ⟨headSize, headSmaller, terminal, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, headSmaller, tailSmaller, executed, tail⟩
  · have loop := SelectedCompilationStageForSourceInversion.fault unique statementFound form failed
    obtain ⟨stagedSize, staged, reached, lifted, adapted⟩ := initialLift
      (Nat.le_trans (Nat.le_of_lt headSmaller) within) ready loop
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound, .completed (.fault reason)⟩
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound,
        .rejected origin call reason _ _⟩
  · obtain ⟨rfl, loop⟩ := SelectedCompilationStageForSourceInversion.control unique statementFound form executed
    obtain ⟨stagedSize, staged, reached, lifted, adapted⟩ := initialLift
      (Nat.le_trans (Nat.le_of_lt headSmaller) within) ready loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched with
      | breaking innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed lifted).1 innerEnvironment rfl).elim
      | continuing innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed lifted).2 innerEnvironment rfl).elim
      | returned value =>
        exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.returned statementFound form lifted).sound, .completed (.returned value)⟩
      | fault reason =>
        exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        cases SelectedCompilationStageForSourceInversion.fallthrough_environment loop
        rcases terminal with terminal | rfl
        · cases terminal
        · exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fallthrough statementFound form lifted .nil).sound,
            .completed (.fallthrough environment)⟩
  · obtain ⟨rfl, loop⟩ := SelectedCompilationStageForSourceInversion.control unique statementFound form executed
    cases SelectedCompilationStageForSourceInversion.fallthrough_environment loop
    obtain ⟨stagedSize, staged, reached, lifted, adapted⟩ := initialLift
      (Nat.le_trans (Nat.le_of_lt headSmaller) within) ready loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched
      obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata,
        last, _, post⟩ := initialPreservation stagedSize (Nat.le_refl _) environments heaps locals agrees actualTyped
          reference read unmapped initial conditioned admitted lifted
      obtain ⟨tailContext, tailOutcome, tailHeap, liftedTail, adaptedTail⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
        (environments.extend maps worlds) finalHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
        reference ((preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 last conditioned post tail
      obtain ⟨tailGrade, tailMeasured⟩ := Staging.Recursive.Size.StatementsIn.of_trace liftedTail
      exact ⟨tailContext, tailOutcome, tailHeap,
        (CallableIndexedOwnedAdmittedStagedForSourceBridge.fallthrough statementFound form lifted tailMeasured).sound,
        adaptedTail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSequenceLifting
