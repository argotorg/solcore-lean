import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchSequences
import Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuationMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceInversion

/-! Match heads restore the selected lexical scope before the actual suffix.
Returning and failing bypass that suffix; a genuine default-stopping receipt
justifies the compiler's unreachable continuation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchSequences
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

open CallableIndexedOwnedAdmittedStagedConditionalHeads
open CallableIndexedOwnedAdmittedStagedMatchSequences (MatchPreserves)
open SelectedCompilationStageScopedLiftBounds SelectedCompilationStageBodyLiftBounds
open SelectedCompilationStageMatchSourceInversion (PlainMatch)
open SelectedCompilationStageMatchLifting (MatchLift)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

def MatchLifts (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (resolution : MatchResolution) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_conditioned : condition contextLocation native)
    (_admitted : Admission bridge context initial),
    ∀ {outcome : Dynamic.ControlOutcome} {after : Dynamic.Heap},
      PlainMatch program size invocation context environment before
        resolution outcome after →
    MatchLift program stages invocation context environment before resolution outcome after
private theorem fallthrough_environment {program registry size invocation context before after resolution outer inner}
    (trace : Staging.Recursive.Size.Match program registry size invocation context outer before
      resolution (.fallthrough inner) after) : inner = outer := by
  generalize outcomeEq : (Staging.Recursive.BodyOutcome.fallthrough inner) = outcome at trace
  cases trace with
  | scrutineeFault => cases outcomeEq
  | patternFault => cases outcomeEq
  | @arm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | @default _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | noBranch => exact Staging.Recursive.BodyOutcome.fallthrough.inj outcomeEq

private theorem breaking_environment {program registry size invocation context before after resolution outer inner}
    (trace : Staging.Recursive.Size.Match program registry size invocation context outer before
      resolution (.breaking inner) after) : inner = outer := by
  generalize outcomeEq : (Staging.Recursive.BodyOutcome.breaking inner) = outcome at trace
  cases trace with
  | scrutineeFault => cases outcomeEq
  | patternFault => cases outcomeEq
  | @arm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | @default _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | noBranch => cases outcomeEq

private theorem continuing_environment {program registry size invocation context before after resolution outer inner}
    (trace : Staging.Recursive.Size.Match program registry size invocation context outer before
      resolution (.continuing inner) after) : inner = outer := by
  generalize outcomeEq : (Staging.Recursive.BodyOutcome.continuing inner) = outcome at trace
  cases trace with
  | scrutineeFault => cases outcomeEq
  | patternFault => cases outcomeEq
  | @arm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | @default _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outcome _ _ _ _ _ =>
      cases outcome <;> simp_all [Staging.Recursive.BodyOutcome.restore]
  | noBranch => cases outcomeEq

private theorem stopped_not_fallthrough {program registry size invocation context before after resolution environment inner id statement}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .matchWith resolution)
    (stopped : ReachableMatchContinuations.DefaultStopped invocation.source id resolution)
    (trace : Staging.Recursive.Size.Match program registry size invocation context environment before
      resolution (.fallthrough inner) after) : False := by
  have executed := trace.sound.plain id statement (lookupStatement?_sound found) form
  cases stopped.terminates unique executed


include bridge functions condition in
/-- The lifted match restores outer bindings before its actual suffix. -/
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest : List StatementId} {statement : StatementNode}
    {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .matchWith resolution)
    (inner : MatchLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope resolution budget)
    (preservation : ∀ n, MatchPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope resolution expected type code n)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode rest budget ∨
      ReachableMatchContinuations.DefaultStopped invocation.source id resolution) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  have notTail : ∀ expression, statement.form ≠ .expression expression false := by
    intro expression same
    rw [form] at same
    cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found notTail trace with
    ⟨headSize, reason, strict, contextEq, outcomeEq, failed⟩ |
    ⟨headSize, strict, stopped, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, executed, tail⟩
  · subst finalContext
    subst outcome
    have plain := SelectedCompilationStageMatchSourceInversion.fault unique found form failed
    obtain ⟨staged, reached, lifted, adapted⟩ := inner (Nat.le_trans (Nat.le_of_lt strict) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted plain
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨context, _, _, .matchFault (lookupStatement?_sound found) form lifted, .completed (.fault reason)⟩
    | rejected origin call reason reachedContext reached =>
      exact ⟨context, _, _, .matchFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
  · obtain ⟨contextEq, plain⟩ := SelectedCompilationStageMatchSourceInversion.control unique found form executed
    subst finalContext
    obtain ⟨staged, reached, lifted, adapted⟩ := inner (Nat.le_trans (Nat.le_of_lt strict) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted plain
    cases adapted with
    | rejected origin call reason reachedContext reached =>
      exact ⟨context, _, _, .matchFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
    | completed matched =>
      cases matched with
      | returned value =>
        exact ⟨context, _, _, .matchReturned (lookupStatement?_sound found) form lifted, .completed (.returned value)⟩
      | breaking innerEnvironment =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Match.of_trace lifted
        have same := breaking_environment measured
        subst innerEnvironment
        exact ⟨context, _, _, .matchBreaking (lookupStatement?_sound found) form lifted, .completed (.breaking environment)⟩
      | continuing innerEnvironment =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Match.of_trace lifted
        have same := continuing_environment measured
        subst innerEnvironment
        exact ⟨context, _, _, .matchContinuing (lookupStatement?_sound found) form lifted, .completed (.continuing environment)⟩
      | fault reason =>
        exact ⟨context, _, _, .matchFault (lookupStatement?_sound found) form lifted, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Match.of_trace lifted
        have same := fallthrough_environment measured
        subst innerEnvironment
        rcases stopped with impossible | rfl
        · cases impossible
        · exact ⟨context, _, _, .matchFallthrough (lookupStatement?_sound found) form lifted .nil,
            .completed (.fallthrough environment)⟩
  · obtain ⟨contextEq, plain⟩ := SelectedCompilationStageMatchSourceInversion.control unique found form executed
    subst middleContext
    obtain ⟨staged, reached, lifted, adapted⟩ := inner (Nat.le_trans (Nat.le_of_lt strict) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted plain
    cases adapted with
    | rejected origin call reason reachedContext reached =>
      exact ⟨context, _, _, .matchFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
    | completed matched =>
      cases matched
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Match.of_trace lifted
      have same := fallthrough_environment measured
      subst nextEnvironment
      rcases remaining with remaining | stopped
      · obtain ⟨_, middleStore, middleMap, middleWorld, _, _, middleHeaps, maps, worlds, preserved, metadata,
          reached, _, post⟩ := preservation stagedSize (Nat.le_refl _) environments heaps locals agrees actualTyped
          reference read unmapped initial conditioned admitted measured
        obtain ⟨lastContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
          (Nat.le_trans (Nat.le_of_lt tailStrict) within) (environments.extend maps worlds)
          middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference
          ((preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned post tail
        exact ⟨lastContext, result, finalHeap,
          .matchFallthrough (lookupStatement?_sound found) form lifted restTrace, restAdapted⟩
      · exact False.elim (stopped_not_fallthrough unique found form stopped measured)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMatchSequences
