import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLoopOutcomes
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSourceInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSequenceLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageWhileLifting
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
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode : Expr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


variable {mode : Bool} {id : StatementId} {statement : StatementNode}
  {rest : List StatementId} {selfReason : Word}

include transport in
/-- Lift the actual while head and precisely the suffix reached after normal
completion. Earlier returns and genuine failures retain their original scope. -/
theorem lifts {budget : Nat}
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node) (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (body : FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope false statements budget)
    (bodyPreservation : ∀ n, FlowPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope false statements expected type loopCode n)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .whileLoop test statements)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope mode rest budget) :
    FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
    finalContext outcome after trace
  have lift {n : Nat} {plain : Dynamic.ControlOutcome} {reached : Dynamic.Heap}
      (small : n ≤ budget)
      (loop : PlainWhile program n invocation context environment before test statements plain reached) :
      WhileLift program stages invocation context environment before test statements plain reached :=
    while_loop bridge functions condition children preservation found typed generated body bodyPreservation small
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted loop
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique statementFound
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨headSize, reason, headSmaller, rfl, rfl, failed⟩ |
    ⟨headSize, headSmaller, terminal, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, headSmaller, tailSmaller, executed, tail⟩
  · obtain ⟨loopSize, loopSmaller, loop⟩ := SelectedCompilationStageWhileSourceInversion.fault unique statementFound form failed
    obtain ⟨staged, reached, lifted, adapted⟩ := lift
      (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans loopSmaller headSmaller)) within) loop
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted, .completed (.fault reason)⟩
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call reason _ _⟩
  · obtain ⟨loopSize, loopSmaller, rfl, loop⟩ := SelectedCompilationStageWhileSourceInversion.control unique statementFound form executed
    obtain ⟨staged, reached, lifted, adapted⟩ := lift
      (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans loopSmaller headSmaller)) within) loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched with
      | breaking innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed_of_trace lifted).1 innerEnvironment rfl).elim
      | continuing innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed_of_trace lifted).2 innerEnvironment rfl).elim
      | returned value =>
        exact ⟨_, _, _, .whileReturned (lookupStatement?_sound statementFound) form lifted, .completed (.returned value)⟩
      | fault reason =>
        exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        cases SelectedCompilationStageWhileSourceInversion.fallthrough_environment loop
        rcases terminal with terminal | rfl
        · cases terminal
        · exact ⟨_, _, _, .whileFallthrough (lookupStatement?_sound statementFound) form lifted .nil,
            .completed (.fallthrough environment)⟩
  · obtain ⟨loopSize, loopSmaller, rfl, loop⟩ := SelectedCompilationStageWhileSourceInversion.control unique statementFound form executed
    cases SelectedCompilationStageWhileSourceInversion.fallthrough_environment loop
    obtain ⟨staged, reached, lifted, adapted⟩ := lift
      (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans loopSmaller headSmaller)) within) loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.While.of_trace lifted
      obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata,
        last, _, post⟩ := CallableIndexedOwnedAdmittedStagedWhileHeads.preserves bridge functions condition transport
          (fun n _ => preservation n) found nodeType typed generated nativeTyped (bodyPreservation stagedSize)
          (Nat.le_refl _) environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted measured
      obtain ⟨tailContext, tailOutcome, tailHeap, liftedTail, adaptedTail⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
        (environments.extend maps worlds) finalHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
        reference ((preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 last conditioned post tail
      exact ⟨tailContext, tailOutcome, tailHeap,
        .whileFallthrough (lookupStatement?_sound statementFound) form lifted liftedTail, adaptedTail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSequenceLifting
