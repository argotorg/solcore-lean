import Solcore.SourceSemantics.CoreLowering.DataExpressionSequence
import Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts

/-! Typed actual-environment composition for the real argument packing helper.
Static trees, source traces and payload results are shared with the unrestricted
sequence theory. Each inserted payload receives its type from the represented
result, and the existing environment is transported along the actual world
extension before the next child executes. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedDataExpressionSequence
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open GenericExpressionMeaning (Certificate FaultRep agree_prefix rename_prefix)
open DataPatternValues DataExpressionSequence

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}

/-- Successful evaluation keeps left-to-right effects and every represented
payload, including captured references inside earlier argument values. -/
theorem preserves_values (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (execution : Dynamic.ExpressionsEvaluate program context evidence source environment before ids sources after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual actualContext before store ξ sources after with
  | nil =>
    cases execution
    exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | single found generated =>
    cases execution with
    | cons head tail =>
      cases tail
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout actualTyped (.value head)
      cases represented with
      | value payload =>
        exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
          finalHeaps, maps, worlds, frame, metadata⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head rest =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning generated found environments heaps locals layout actualTyped (.value head)
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
          maps, worlds, frame, metadata⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix layout coreValue)
            (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) rest
        have nonempty : values ≠ [] := by
          intro absent
          have lengths := restRep.length.2
          simp [absent] at lengths
        refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
          .cons (model.extend payload maps worlds) restRep, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [rename_prefix] at second
        have combined := LocalSequence.pair_success lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
        simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

variable {expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost}
  {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}

/-- A source fault evaluates only its successful prefix. The generated helper
propagates the exact token without evaluating later arguments. -/
theorem preserves_fault_with_post (tree : Tree source certificate scope ids sourceTypes codes)
    (joins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (meaning : ExpressionFailurePostContracts.TypedPreserves model program context evidence source certificate faults expressionPost)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (execution : Dynamic.ExpressionsFault program context evidence source environment before ids reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      listPost program context evidence source environment before ids reason after token finalMap finalWorld finalStore := by
  induction tree generalizing mapping world actual actualContext before store ξ after with
  | nil => cases execution
  | single found generated =>
    cases execution with
    | head failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, retained⟩ := meaning generated found environments heaps locals layout actualTyped (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched,
          finalHeaps, maps, worlds, frame, metadata, joins.head failed (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩
    | tail _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | head failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, retained⟩ := meaning generated found environments heaps locals layout actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata, joins.head failed (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type evaluated
    | tail head failed =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        meaning generated found environments heaps locals layout actualTyped (.value head)
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
          maps, worlds, frame, metadata, retained⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix layout coreValue)
            (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) failed
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, joins.tail head failed retained⟩
        rw [rename_prefix] at second
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second

theorem preserves_fault (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (execution : Dynamic.ExpressionsFault program context evidence source environment before ids reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := preserves_fault_with_post tree
    (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
    (ExpressionFailurePostContracts.TypedPreserves.of_trivial meaning) environments heaps locals layout actualTyped execution
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

/-- Every completed evaluation of the actual generated bundle constructs a
finite source trace. Typed inserted temporary slots are admitted through
the child theorem's explicit renaming; no exact closure weakening is used. -/
theorem reflects_with_post (tree : Tree source certificate scope ids sourceTypes codes)
    (joins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (meaning : ExpressionFailurePostContracts.TypedReflects model program context evidence source certificate faults expressionPost)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ExpressionFailurePostContracts.ListOutcomePost listPost program context evidence source environment before ids
        (SourceCoreCalls.packArguments codes).type outcome after value finalMap finalWorld finalStore := by
  induction tree generalizing mapping world actual actualContext before store ξ value finalStore with
  | nil =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (show Evaluates actual store
      ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
    exact ⟨.ok [], before, mapping, world, .values .nil, .values (values := []) .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _, trivial⟩
  | single found generated =>
    obtain ⟨outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
      maps, worlds, frame, metadata, retained⟩ := meaning generated found environments heaps locals layout actualTyped evaluated
    cases represented with
    | value payload =>
      cases execution with
      | value trace => exact ⟨.ok [_], after, finalMap, finalWorld,
          .values (.cons trace .nil), .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata, trivial⟩
    | fault matched =>
      cases execution with
      | fault trace => exact ⟨.error _, after, finalMap, finalWorld,
          .fault (.head trace), .fault matched, finalHeaps, maps, worlds, frame, metadata, ⟨_, rfl, joins.head trace (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    change Evaluates actual store ((LocalSequence.pair lowered.type
      (SourceCoreCalls.packArguments (nextCode :: codes)).type lowered.expression
      (SourceCoreCalls.packArguments (nextCode :: codes)).expression).rename ξ) value finalStore at evaluated
    rw [pair_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft first _ =>
      obtain ⟨outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
        maps, worlds, frame, metadata, retained⟩ := meaning generated found environments heaps locals layout actualTyped first
      cases represented with
      | fault matched =>
        cases execution with
        | fault trace =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.pair_left_failure lowered.type
            (SourceCoreCalls.packArguments (nextCode :: codes)).type first)
          exact ⟨.error _, after, finalMap, finalWorld, .fault (.head trace), .fault matched,
            finalHeaps, maps, worlds, frame, metadata, ⟨_, rfl, joins.head trace (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
    | caseRight first continuation =>
      obtain ⟨outcome, middle, middleMap, middleWorld, execution, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        meaning generated found environments heaps locals layout actualTyped first
      cases represented with
      | @value sourceValue coreValue payload =>
        rename_i middleStore coreValue
        have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical
            (coreValue :: actual) := agree_prefix layout coreValue
        cases execution with
        | value firstSource =>
          cases continuation with
          | caseLeft second _ =>
            have shifted := second
            rw [← rename_prefix] at shifted
            obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
              maps, worlds, frame, metadata, retained⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) nextLayout
                (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) shifted
            cases result with
            | fault matched =>
              cases sourceTrace with
              | fault tailSource =>
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                  (LocalSequence.pair_right_failure lowered.type
                    (SourceCoreCalls.packArguments (nextCode :: codes)).type first second)
                exact ⟨.error _, after, finalMap, finalWorld, .fault (.tail firstSource tailSource), .fault matched,
                  finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans metadata,
                  ⟨_, rfl, joins.tail firstSource tailSource (ExpressionFailurePostContracts.ListOutcomePost.fault retained)⟩⟩
          | caseRight second _ =>
            have shifted := second
            rw [← rename_prefix] at shifted
            obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
              maps, worlds, frame, metadata, retained⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) nextLayout
                (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) shifted
            cases result with
            | @values sources values restRep =>
              cases sourceTrace with
              | values tailSource =>
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                  (LocalSequence.pair_success lowered.type
                    (SourceCoreCalls.packArguments (nextCode :: codes)).type first second)
                have nonempty : values ≠ [] := by
                  intro absent
                  have lengths := restRep.length.2
                  simp [absent] at lengths
                refine ⟨.ok (sourceValue :: sources), after, finalMap, finalWorld,
                  .values (.cons firstSource tailSource), ?_, finalHeaps,
                  firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans metadata, trivial⟩
                simpa [packValues, nonempty] using
                  Result.values (codes := lowered :: nextCode :: codes)
                    (.cons (model.extend payload maps worlds) restRep)

theorem reflects (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Reflects model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := reflects_with_post tree
    (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
    (ExpressionFailurePostContracts.TypedReflects.of_trivial meaning) environments heaps locals layout actualTyped evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves_with_post (tree : Tree source certificate scope ids sourceTypes codes)
    (joins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (meaning : ExpressionFailurePostContracts.TypedPreserves model program context evidence source certificate faults expressionPost)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (execution : Trace program context evidence source environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ExpressionFailurePostContracts.ListOutcomePost listPost program context evidence source environment before ids
        (SourceCoreCalls.packArguments codes).type outcome after value finalMap finalWorld finalStore := by
  cases execution with
  | values execution =>
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := preserves_values tree (ExpressionFailurePostContracts.TypedPreserves.forget meaning) environments heaps locals layout actualTyped execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented,
      finalHeaps, maps, worlds, frame, metadata, trivial⟩
  | fault execution =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, retained⟩ := preserves_fault_with_post tree joins meaning environments heaps locals layout actualTyped execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault represented,
      finalHeaps, maps, worlds, frame, metadata, ⟨token, rfl, retained⟩⟩

theorem preserves (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (execution : Trace program context evidence source environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases execution with
  | values execution =>
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := preserves_values tree meaning environments heaps locals layout actualTyped execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented,
      finalHeaps, maps, worlds, frame, metadata⟩
  | fault execution =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := preserves_fault tree meaning environments heaps locals layout actualTyped execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault represented,
      finalHeaps, maps, worlds, frame, metadata⟩

/-- Finiteness comes from the independent source trace. Fuel exhaustion remains
a resumable machine state, rather than a successful or faulting source outcome. -/
theorem preserves_sufficient_fuel (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (execution : Trace program context evidence source environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := preserves tree meaning environments heaps locals layout actualTyped execution
  obtain ⟨required, runs⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required, runs, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem reflects_done (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Reflects model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value} {fuel : Nat}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (completed : runStateful fuel
      (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects tree meaning environments heaps locals layout actualTyped (runStateful_evaluation_sound completed)

end Solcore.SourceSemantics.CoreLowering.TypedDataExpressionSequence
