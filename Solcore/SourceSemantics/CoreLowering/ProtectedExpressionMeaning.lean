import Solcore.SourceSemantics.CoreLowering.SourceExecutionSize
import Solcore.SourceSemantics.CoreLowering.CoreEvaluationSize
import Solcore.SourceSemantics.CoreLowering.TypedGenericExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedCompositions

/-! Recursive expression meanings with a protected administrative entry.
The entry concerns the canonical environment and real store. Temporary actual
slots are tracked by the existing renaming, while successful child effects
transport the entry along real heap/world extensions and protected writes.
An entry contains no source execution or body meaning.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open GenericExpressionMeaning (Certificate FaultRep ResultRepresents)

abbrev Entry := SourceCoreLocalCell.Scope → LocationMap → StoreTyping →
  Dynamic.Heap → Store → Environment → Prop

/-- The exact administrative observations survive the effects already
certified by expression meaning. Actual temporary binders leave this canonical
environment unchanged. -/
structure Transport (entry : Entry) : Prop where
  extend : ∀ {scope mapping world before store canonical futureMap futureWorld after futureStore},
    entry scope mapping world before store canonical →
    LocationMap.Extends mapping futureMap → WorldExtends world futureWorld →
    AdministrativePreserved mapping store futureMap futureStore →
    Dynamic.HeapMetadataExtend before after →
    entry scope futureMap futureWorld after futureStore canonical

def Preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) (entry : Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def Reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) (entry : Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

theorem preserves_of_typed
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (entry : Entry)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults) :
    Preserves model program context evidence source certificate faults entry := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed _ trace
  exact meaning certified found environments heaps locals agrees typed trace

theorem reflects_of_typed
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (entry : Entry)
    (meaning : TypedGenericExpressionMeaning.Reflects model program context evidence source certificate faults) :
    Reflects model program context evidence source certificate faults entry := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed _ evaluated
  exact meaning certified found environments heaps locals agrees typed evaluated

end Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning

-- Protected ordered argument composition.
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedDataExpressionSequence
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open GenericExpressionMeaning (Certificate FaultRep agree_prefix rename_prefix)
open DataPatternValues DataExpressionSequence


/-- An outcome wrapper around the existing measured source judgment. -/
inductive ExpressionTraceAt (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : ExpressionId) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {value after} (trace : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before id value after) :
      ExpressionTraceAt program size context evidence source environment before id (.value value) after
  | fault {reason after} (trace : SourceExecutionSize.ExpressionFaults program size context evidence source environment before id reason after) :
      ExpressionTraceAt program size context evidence source environment before id (.fault reason) after

theorem ExpressionTraceAt.sound {program size context evidence source environment before id outcome after}
    (trace : ExpressionTraceAt program size context evidence source environment before id outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | value trace => exact .value trace.sound
  | fault trace => exact .fault trace.sound

theorem ExpressionTraceAt.has_size {program context evidence source environment before id outcome after}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ∃ size, ExpressionTraceAt program size context evidence source environment before id outcome after := by
  cases trace with
  | value trace => obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionEvaluates.has_size trace; exact ⟨size, .value sized⟩
  | fault trace => obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionFaults.has_size trace; exact ⟨size, .fault sized⟩

inductive TraceAt (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (ids : List ExpressionId) : Outcome → Dynamic.Heap → Prop where
  | values {values after} (trace : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before ids values after) :
      TraceAt program size context evidence source environment before ids (.ok values) after
  | fault {reason after} (trace : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) :
      TraceAt program size context evidence source environment before ids (.error reason) after

theorem TraceAt.sound {program size context evidence source environment before ids outcome after}
    (trace : TraceAt program size context evidence source environment before ids outcome after) :
    Trace program context evidence source environment before ids outcome after := by
  cases trace with
  | values trace => exact .values trace.sound
  | fault trace => exact .fault trace.sound

theorem TraceAt.has_size {program context evidence source environment before ids outcome after}
    (trace : Trace program context evidence source environment before ids outcome after) :
    ∃ size, TraceAt program size context evidence source environment before ids outcome after := by
  cases trace with
  | values trace => obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionsEvaluate.has_size trace; exact ⟨size, .values sized⟩
  | fault trace => obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionsFault.has_size trace; exact ⟨size, .fault sized⟩

def ExpressionPreservesAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) (entry : ProtectedExpressionMeaning.Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    ExpressionTraceAt program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def ExpressionReflectsAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) (entry : ProtectedExpressionMeaning.Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      ExpressionTraceAt program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport


omit transport in
private theorem preserves_at_of_unbounded
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    (size : Nat) : ExpressionPreservesAt size model program context evidence source certificate faults entry := by
  intro scope id lowered generated node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed installed trace
  exact meaning generated found environments heaps locals agrees typed installed trace.sound

omit transport in
private theorem reflects_at_of_unbounded
    (meaning : ProtectedExpressionMeaning.Reflects model program context evidence source certificate faults entry)
    (size : Nat) : ExpressionReflectsAt size model program context evidence source certificate faults entry := by
  intro scope id lowered generated node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed installed evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, rest⟩ := meaning generated found environments heaps locals agrees typed installed evaluated.sound
  obtain ⟨sourceSize, sized⟩ := ExpressionTraceAt.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, rest⟩

theorem preserves_values_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → ExpressionPreservesAt size model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before ids sources after) (bounded : size ≤ budget) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing size mapping world actual actualContext before store ξ sources after with
  | nil =>
    cases execution
    exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | single found generated =>
    cases execution with
    | cons head tail =>
      cases tail
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) generated found environments heaps locals layout actualTyped installedEntry (.value head)
      cases represented with
      | value payload =>
        exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
          finalHeaps, maps, worlds, frame, metadata⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head rest =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) generated found environments heaps locals layout actualTyped installedEntry (.value head)
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
          maps, worlds, frame, metadata⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix layout coreValue)
            (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
            (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) rest
            (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded)
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

theorem preserves_fault_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → ExpressionPreservesAt size model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing size mapping world actual actualContext before store ξ after with
  | nil => cases execution
  | single found generated =>
    cases execution with
    | head failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) generated found environments heaps locals layout actualTyped installedEntry (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched,
          finalHeaps, maps, worlds, frame, metadata⟩
    | tail _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | head failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) generated found environments heaps locals layout actualTyped installedEntry (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata⟩
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type evaluated
    | tail head failed =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning _ (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) bounded) generated found environments heaps locals layout actualTyped installedEntry (.value head)
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
          maps, worlds, frame, metadata⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix layout coreValue)
            (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
            (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) failed
            (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) bounded)
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [rename_prefix] at second
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second

theorem reflects_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → ExpressionReflectsAt size model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) (bounded : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      TraceAt program sourceSize context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing size mapping world actual actualContext before store ξ value finalStore with
  | nil =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (show Evaluates actual store
      ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
    exact ⟨_, .ok [], before, mapping, world, .values .nil, .values (values := []) .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | single found generated =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := meaning _ (by omega) generated found environments heaps locals layout actualTyped installedEntry evaluated
    cases represented with
    | value payload =>
      cases execution with
      | value trace => exact ⟨_, .ok [_], after, finalMap, finalWorld,
          .values (.cons trace .nil), .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata⟩
    | fault matched =>
      cases execution with
      | fault trace => exact ⟨_, .error _, after, finalMap, finalWorld,
          .fault (.head trace), .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    change EvaluationSize size actual store ((LocalSequence.pair lowered.type
      (SourceCoreCalls.packArguments (nextCode :: codes)).type lowered.expression
      (SourceCoreCalls.packArguments (nextCode :: codes)).expression).rename ξ) value finalStore at evaluated
    rw [pair_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft first _ =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning _ (by omega) generated found environments heaps locals layout actualTyped installedEntry first
      cases represented with
      | fault matched =>
        cases execution with
        | fault trace =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound (LocalSequence.pair_left_failure lowered.type
            (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound)
          exact ⟨_, .error _, after, finalMap, finalWorld, .fault (.head trace), .fault matched,
            finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight first continuation =>
      obtain ⟨sourceSize, outcome, middle, middleMap, middleWorld, execution, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning _ (by omega) generated found environments heaps locals layout actualTyped installedEntry first
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
            obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
              maps, worlds, frame, metadata⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) nextLayout
                (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) shifted (by omega)
            cases result with
            | fault matched =>
              cases sourceTrace with
              | fault tailSource =>
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                  (LocalSequence.pair_right_failure lowered.type
                    (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                exact ⟨_, .error _, after, finalMap, finalWorld, .fault (.tail firstSource tailSource), .fault matched,
                  finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans metadata⟩
          | caseRight second _ =>
            have shifted := second
            rw [← rename_prefix] at shifted
            obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
              maps, worlds, frame, metadata⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) nextLayout
                (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) shifted (by omega)
            cases result with
            | @values sources values restRep =>
              cases sourceTrace with
              | values tailSource =>
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                  (LocalSequence.pair_success lowered.type
                    (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                have nonempty : values ≠ [] := by
                  intro absent
                  have lengths := restRep.length.2
                  simp [absent] at lengths
                refine ⟨_, .ok (sourceValue :: sources), after, finalMap, finalWorld,
                  .values (.cons firstSource tailSource), ?_, finalHeaps,
                  firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans metadata⟩
                simpa [packValues, nonempty] using
                  Result.values (codes := lowered :: nextCode :: codes)
                    (.cons (model.extend payload maps worlds) restRep)

theorem preserves_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → ExpressionPreservesAt size model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    {size : Nat}
    (execution : TraceAt program size context evidence source environment before ids outcome after) (bounded : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases execution with
  | values execution =>
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩  := preserves_values_bounded transport budget tree meaning environments heaps locals layout actualTyped installedEntry execution bounded
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented,
      finalHeaps, maps, worlds, frame, metadata⟩
  | fault execution =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩  := preserves_fault_bounded transport budget tree meaning environments heaps locals layout actualTyped installedEntry execution bounded
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault represented,
      finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves_values (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    (execution : Dynamic.ExpressionsEvaluate program context evidence source environment before ids sources after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionsEvaluate.has_size execution
  exact preserves_values_bounded transport size tree (fun child _ => preserves_at_of_unbounded meaning child)
    environments heaps locals layout actualTyped installedEntry sized (Nat.le_refl size)


theorem preserves_fault (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    (execution : Dynamic.ExpressionsFault program context evidence source environment before ids reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionsFault.has_size execution
  exact preserves_fault_bounded transport size tree (fun child _ => preserves_at_of_unbounded meaning child)
    environments heaps locals layout actualTyped installedEntry sized (Nat.le_refl size)


theorem reflects (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ProtectedExpressionMeaning.Reflects model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    reflects_bounded transport (size + 1) tree (fun child _ => reflects_at_of_unbounded meaning child)
      environments heaps locals layout actualTyped installedEntry sized (by omega)
  exact ⟨outcome, after, finalMap, finalWorld, trace.sound, rest⟩


theorem preserves (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installedEntry : entry scope mapping world before store canonical)
    (execution : Trace program context evidence source environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := TraceAt.has_size execution
  exact preserves_bounded transport size tree (fun child _ => preserves_at_of_unbounded meaning child)
    environments heaps locals layout actualTyped installedEntry sized (Nat.le_refl size)

end Solcore.SourceSemantics.CoreLowering.ProtectedDataExpressionSequence

-- Protected primitive/control composition.
namespace Solcore.SourceSemantics.CoreLowering.ProtectedExpressionCompositions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals
open CompatibleExpressionTypedCompositions (Head)
private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId) (first second : SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate := fun current id code =>
  current = scope ∧ ((id = left ∧ code = first) ∨ (id = right ∧ code = second))

private theorem two_tree {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {left right : ExpressionId}
    {leftNode rightNode : ExpressionNode} {first second : SourceCoreBasic.LoweredExpr}
    (leftFound : source.lookupExpression? left = some leftNode)
    (rightFound : source.lookupExpression? right = some rightNode) :
    DataExpressionSequence.Tree source (Two scope left right first second) scope
      [left, right] [leftNode.type, rightNode.type] [first, second] :=
  .cons leftFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ (.single rightFound ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

private theorem pair_result {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {leftType rightType : TypeSystem.Ty}
    {first second : SourceCoreBasic.LoweredExpr} {faults : FunctionCalls.FaultRep}
    {sequence : DataExpressionSequence.Outcome} {value : Value}
    (result : DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world [leftType, rightType] [first, second] faults sequence value) :
    ∃ outcome, CompatibleExpressionProducts.PacksOutcome sequence outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping world (.product leftType rightType) (.product first.type second.type) faults outcome value := by
  cases result with
  | values represented =>
    change DataExpressionSequence.Values _ _ _ [leftType, rightType] [first.type, second.type] _ _ at represented
    cases represented with
    | cons left tail =>
      cases tail with
      | cons right tail =>
        cases tail
        exact ⟨_, .values (.cons (.singleton _)), .value (.product left right)⟩
  | fault matched => exact ⟨_, .fault _, .fault matched⟩


variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport

theorem Head.preserves
    (unique : NodeOccurrencesUnique source)
    (meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults entry) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ih innerFound environments heaps locals agrees actualTyped installedEntry (CompatibleExpressionProducts.group_inv metadata form unique trace)
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have leftIH := @meaning _ _ _ firstTree
    have rightIH := @meaning _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have children : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (Two scope left right first second) faults entry := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    obtain ⟨sequence, sourceTrace, packed⟩ := CompatibleExpressionProducts.pair_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ProtectedDataExpressionSequence.preserves transport (two_tree (first := first) (second := second) leftFound rightFound) children environments heaps locals agrees actualTyped installedEntry sourceTrace
    obtain ⟨actualOutcome, actualPack, payload⟩ := pair_result represented
    have sameOutcome := actualPack.functional packed
    subst actualOutcome
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := unary_inv metadata form unique trace
    cases sourceStep with
    | value childTrace applied =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih childFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, actualApplied, coreApplied, resultRep⟩ := profile.preserves payload
        have same := actualApplied.functional applied
        subst sourceResult
        refine ⟨.inRight .word result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
        · rw [unary_rename]; exact LocalPrimitiveResults.unary_success evaluated coreApplied
        · exact .value (outputType ▸ resultRep)
    | fault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih childFound environments heaps locals agrees actualTyped installedEntry (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [unary_rename]; exact LocalPrimitiveResults.unary_failure evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | invalid childTrace failed =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := ih childFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨_, _, applied, _, _⟩ := profile.preserves payload
        exact False.elim (unary_fault_excluded applied failed)
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have leftIH := @meaning _ _ _ leftTree
    have rightIH := @meaning _ _ _ rightTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := binary_inv metadata form unique trace
    cases sourceStep with
    | leftFault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact mode.left_failure operator evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | leftInvalid childTrace invalid =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := leftIH leftFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        exact False.elim (profile.left_valid payload invalid)
    | short childTrace circuit =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit evaluated
        exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
          .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata⟩
    | rightFault firstTrace continues secondTrace =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.fault secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact profile.right_failure payload continues first second,
            .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
    | value firstTrace continues secondTrace applied =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          obtain ⟨sourceResult, result, actualApplied, resultRep, combined⟩ := profile.right_success leftPayload rightPayload continues first second
          have same := actualApplied.functional applied
          subst sourceResult
          exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
            .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
    | invalid firstTrace continues secondTrace failed =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, _, _, _, second, represented, _, maps, worlds, _⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          obtain ⟨_, _, applied, _, _⟩ := profile.right_success leftPayload rightPayload continues first second
          exact False.elim (binary_fault_excluded applied failed)

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have conditionIH := @meaning _ _ _ conditionTree
    have thenIH := @meaning _ _ _ thenTree
    have elseIH := @meaning _ _ _ elseTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := conditional_inv metadata form unique trace
    cases sourceStep with
    | fault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped installedEntry (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [choose_rename]; exact LocalControl.choose_failure type evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | @branch flag middle outcome after conditionTrace branchTrace =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped installedEntry (.value conditionTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualFlag, sourceEq, coreEq⟩ := bool_fields payload
        cases sourceEq
        subst coreEq
        cases flag with
        | false =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
            elseIH elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
          · rw [choose_rename]; exact LocalControl.choose_false type first branch
          · simpa only [elseType] using represented
        | true =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
            thenIH thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
          · rw [choose_rename]; exact LocalControl.choose_true type first branch
          · simpa only [thenType] using represented
    | invalid childTrace invalid runtimeType =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := conditionIH conditionFound environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨flag, rfl, _⟩ := bool_fields payload
        exact False.elim (invalid trivial)


theorem Head.reflects
    (meaning : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source certificate faults entry) :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context evidence source (Head checked source certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | @group node inner innerNode lowered metadata form innerFound sourceType child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ih innerFound environments heaps locals agrees actualTyped installedEntry evaluated
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.group_intro metadata form trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using represented
  | @pair node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree =>
    have leftIH := @meaning _ _ _ firstTree
    have rightIH := @meaning _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have children : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
        program context evidence source (Two scope left right first second) faults entry := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    obtain ⟨sequence, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ProtectedDataExpressionSequence.reflects transport (two_tree (first := first) (second := second) leftFound rightFound) children environments heaps locals agrees actualTyped installedEntry evaluated
    obtain ⟨outcome, packed, payload⟩ := pair_result represented
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.pair_intro metadata form sourceTrace packed, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
    simpa only [sourceType] using payload

  | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
    have ih := @meaning _ _ _ child
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [unary_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih childFound environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_failure (operator := core) childEvaluation) complete
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.fault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih childFound environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
        obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_success childEvaluation coreApplied) complete
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.value childTrace applied),
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata⟩
  | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
    have leftIH := @meaning _ _ _ leftTree
    have rightIH := @meaning _ _ _ rightTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [Mode.binary_rename] at evaluated
    have complete := evaluated
    rw [Mode.binary_eq] at evaluated
    cases evaluated with
    | caseLeft leftEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry leftEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (mode.left_failure operator leftEvaluation)
          exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.leftFault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight leftEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        leftIH leftFound environments heaps locals agrees actualTyped installedEntry leftEvaluation
      cases represented with
      | @value sourceValue coreValue payload =>
        rw [leftType] at payload
        cases trace with
        | value firstTrace =>
          rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
          · obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit leftEvaluation
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            exact ⟨_, middle, middleMap, middleWorld, binary_intro metadata form (.short firstTrace circuit),
              .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩
          · obtain ⟨rightValue, rightStore, rightEvaluation⟩ := profile.right_evaluated payload continues branch
            have shifted := rightEvaluation
            rw [← GenericExpressionMeaning.rename_prefix] at shifted
            obtain ⟨rightOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
              rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) shifted
            cases represented with
            | fault matched =>
              cases trace with
              | fault failed =>
                have combined := profile.right_failure payload continues leftEvaluation rightEvaluation
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.rightFault firstTrace continues failed),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
            | value rightPayload =>
              rw [rightType] at rightPayload
              have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
              obtain ⟨sourceResult, result, applied, resultRep, combined⟩ :=
                profile.right_success leftPayload rightPayload continues leftEvaluation rightEvaluation
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              cases trace with
              | value secondTrace =>
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.value firstTrace continues secondTrace applied),
                  .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata⟩

  | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
    have conditionIH := @meaning _ _ _ conditionTree
    have thenIH := @meaning _ _ _ thenTree
    have elseIH := @meaning _ _ _ elseTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [choose_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalControl.choose_failure type childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, conditional_intro metadata form (.fault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        conditionIH conditionFound environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | value payload =>
        obtain ⟨flag, sourceEq, coreEq⟩ := bool_fields payload
        subst sourceEq
        subst coreEq
        cases trace with
        | value conditionTrace =>
          have selected := choose_branch_evaluated branch
          cases flag with
          | false =>
            change Evaluates _ _ ((elseCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
              elseIH elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace branchTrace),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
            simpa only [elseType] using represented
          | true =>
            change Evaluates _ _ ((thenCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
              thenIH thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace branchTrace),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata⟩
            simpa only [thenType] using represented


end Solcore.SourceSemantics.CoreLowering.ProtectedExpressionCompositions
