import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchHeads
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
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchSequences
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

open CallableIndexedOwnedAdmittedStagedConditionalHeads

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

/-- A selected scoped arm's numeric reflection port, closed by the surrounding
compiler-tree induction. Its postcondition is at the original outer context. -/
def MatchReflects (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (resolution : MatchResolution) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
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
    EvaluationSize size actual store (code.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Match program stages sourceSize invocation context environment before
        resolution outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached

/-- The corresponding Source-to-native port retains successful branch typing,
fallthrough admission, and the same final heap for every admitted caller. -/
def MatchPreserves (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (resolution : MatchResolution) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
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
    ∀ {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap},
      Staging.Recursive.Size.Match program stages size invocation context environment before
        resolution outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached


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

variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {innerCode : Expr}

variable {mode : Bool} {id : StatementId} {statement : StatementNode}
  {rest : List StatementId} {body : Expr}

include bridge functions condition in
theorem reflects {budget : Nat}
    (innerCorrect : MatchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope resolution expected type innerCode budget)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .matchWith resolution)
    (remaining : FlowReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope mode rest expected type body budget ∨
      (NodeOccurrencesUnique invocation.source ∧ ReachableMatchContinuations.DefaultStopped invocation.source id resolution))
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store ((LocalLoop.sequence type innerCode body).rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages mode sourceSize invocation context environment before
        (id :: rest) finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, headRelated, headPost⟩ :=
    innerCorrect (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted headEval
  cases represented with
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .matchReturned (lookupStatement?_sound statementFound) form headTrace,
        .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
        middleState, headRelated, headPost⟩
  | breaking innerEnvironment =>
      have environmentEq := breaking_environment headTrace
      subst innerEnvironment
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .matchBreaking (lookupStatement?_sound statementFound) form headTrace,
        .breaking environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
        middleState, headRelated, headPost⟩
  | continuing innerEnvironment =>
      have environmentEq := continuing_environment headTrace
      subst innerEnvironment
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .matchContinuing (lookupStatement?_sound statementFound) form headTrace,
        .continuing environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
        middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .matchFault (lookupStatement?_sound statementFound) form headTrace,
        .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
        middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      have environmentEq := fallthrough_environment headTrace
      subst innerEnvironment
      rcases remaining with remaining | ⟨unique, stopped⟩
      · obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
        obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented,
            finalHeaps, maps, worlds, framePreserved, metadata, reached, tailRelated, post⟩ :=
          remaining (Nat.le_trans (Nat.le_of_lt smaller) within)
            (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken firstWorlds)))) reference
            ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            middleState conditioned headPost
            (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
        exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
          .matchFallthrough (lookupStatement?_sound statementFound) form headTrace tailTrace,
          represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
          firstFrame.trans framePreserved, firstMetadata.trans metadata, reached,
          callerProtocol.trans headRelated tailRelated, post⟩
      · exact False.elim (stopped_not_fallthrough unique statementFound form stopped headTrace)

include bridge functions condition in
theorem preserves {budget : Nat}
    (innerCorrect : MatchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope resolution expected type innerCode budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .matchWith resolution)
    (remaining : FlowPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope mode rest expected type body budget ∨
      (ReachableMatchContinuations.DefaultStopped invocation.source id resolution))
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.StatementsIn program stages mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.sequence type innerCode body).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have finish {headSize : Nat}
      {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Staging.Recursive.Size.Match program stages headSize invocation context
        environment before resolution headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type innerCode body).rename ξ) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults headOutcome value ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          callerProtocol.Relates initial reached ∧ Post bridge context expected headOutcome reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, reached, related, post⟩ :=
      innerCorrect bounded environments heaps locals agrees actualTyped
        reference read unmapped initial conditioned admitted headTrace
    cases represented with
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | breaking innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .breaking innerEnvironment, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | continuing innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .continuing innerEnvironment, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedMatchSourceInversion.match_and_tail unique statementFound form trace with
    ⟨innerSize, sourceValue, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, failure, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, tailSize, middle, sameSize, innerTrace, tailTrace⟩
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · rcases remaining with remaining | stopped
    · have headWithin : innerSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
          maps, worlds, preservation, metadata, middleState, headRelated, headPost⟩ :=
        innerCorrect headWithin environments heaps locals agrees actualTyped
          reference read unmapped initial conditioned admitted innerTrace
      cases represented with
      | fallthrough innerEnvironment _ =>
          have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
            rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
          obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
              lastMaps, lastWorlds, lastFrame, lastMetadata, reached, tailRelated, post⟩ :=
            remaining tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
                (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
              (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState conditioned headPost tailTrace
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
            maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
            metadata.trans lastMetadata, reached, callerProtocol.trans headRelated tailRelated, post⟩
          rw [LoopRenaming.sequence]
          simp only [GenericExpressionMeaning.rename_prefix] at tailEval
          exact LocalLoop.sequence_fallthrough _ headEval tailEval
    · exact False.elim (stopped_not_fallthrough unique statementFound form stopped innerTrace)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchSequences
