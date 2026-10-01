import Solcore.SourceSemantics.CoreLowering.RecursiveStageMeaning
import Solcore.SourceSemantics.CoreLowering.DataExpressionSequence

/-! Recursive stage correspondence for the actual argument packing helper.
The static Tree is reused from actual list compilation receipts. Universal
staged child theorems are instantiated at each real inserted-prefix layout;
compound argument executions are constructed, never assumed at those layouts.
Faults preserve the originating invocation scope and call through the bundle. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageArguments
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly DataPatternValues
open DataExpressionSequence (Tree Values pair_rename)
open RecursiveStageMeaning

inductive Result {catalog : SourceCoreDataCatalog.Catalog} (model : GenericHeap.PayloadModel catalog)
    (mapping : LocationMap) (world : StoreTyping) (types : List TypeSystem.Ty)
    (codes : List SourceCoreBasic.LoweredExpr) (faults : FaultRep) : Staging.Recursive.ValuesOutcome → Value → Prop where
  | values {sources values}
      (represented : Values model mapping world types (codes.map (·.type)) sources values) :
      Result model mapping world types codes faults (.values sources) (.inRight .word (packValues values))
  | fault {reason token} (represented : faults reason token) :
      Result model mapping world types codes faults (.fault reason)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token))

variable {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
  {program : Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : Certificate} {faults : FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}

/-- Successful evaluation keeps left-to-right effects and every represented
payload, including captured references inside earlier argument values. -/
theorem preserves_values (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.Recursive.Expressions program registry frame context environment before ids (.values sources) after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual before store ξ sources after with
  | nil =>
    cases execution
    exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | single found generated =>
    cases execution with
    | cons head tail =>
      cases tail
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout head
      cases represented with
      | value payload =>
        exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
          finalHeaps, maps, worlds, frame, metadata⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head rest =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning generated found environments heaps locals layout head
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
          maps, worlds, frame, metadata⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix layout coreValue) rest
        have nonempty : values ≠ [] := by
          intro absent
          have lengths := restRep.length.2
          simp [absent] at lengths
        refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
          .cons (model.extend payload maps worlds) restRep, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [GenericExpressionMeaning.rename_prefix] at second
        have combined := LocalSequence.pair_success lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
        simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

/-- A source fault evaluates only its successful prefix. The generated helper
propagates the exact token without evaluating later arguments. -/
theorem preserves_fault (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.Recursive.Expressions program registry frame context environment before ids (.fault reason) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual before store ξ after with
  | nil => cases execution
  | single found generated =>
    cases execution with
    | headFault failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout failed
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched,
          finalHeaps, maps, worlds, frame, metadata⟩
    | tailFault _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | headFault failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout failed
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata⟩
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type evaluated
    | tailFault head failed =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning generated found environments heaps locals layout head
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
          maps, worlds, frame, metadata⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix layout coreValue) failed
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [GenericExpressionMeaning.rename_prefix] at second
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second


/-- Completed Core bundles reconstruct the recursive staged argument trace.
The earlier successful argument payload is kept under the exact inserted slot;
a later stage failure is propagated with its original scope and call. -/
theorem reflects (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Reflects model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expressions program registry frame context environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual before store ξ value finalStore with
  | nil =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (show Evaluates actual store
      ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
    exact ⟨.values [], before, mapping, world, .nil, .values (values := []) .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | single found generated =>
    obtain ⟨outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout evaluated
    cases represented with
    | value payload =>
      exact ⟨.values [_], after, finalMap, finalWorld,
        .cons execution .nil, .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata⟩
    | fault matched =>
      exact ⟨.fault _, after, finalMap, finalWorld,
        .headFault execution, .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    change Evaluates actual store ((LocalSequence.pair lowered.type
      (SourceCoreCalls.packArguments (nextCode :: codes)).type lowered.expression
      (SourceCoreCalls.packArguments (nextCode :: codes)).expression).rename ξ) value finalStore at evaluated
    rw [pair_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft first _ =>
      obtain ⟨outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout first
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.pair_left_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first)
        exact ⟨.fault _, after, finalMap, finalWorld, .headFault execution, .fault matched,
          finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight first continuation =>
      obtain ⟨outcome, middle, middleMap, middleWorld, execution, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning generated found environments heaps locals layout first
      cases represented with
      | @value sourceValue coreValue payload =>
        rename_i middleStore coreValue
        have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical
            (coreValue :: actual) := GenericExpressionMeaning.agree_prefix layout coreValue
        cases continuation with
        | caseLeft second _ =>
          have shifted := second
          rw [← GenericExpressionMeaning.rename_prefix] at shifted
          obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
            maps, worlds, frame, metadata⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
              (locals.mono firstMetadata) nextLayout shifted
          cases result with
          | fault matched =>
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
              (LocalSequence.pair_right_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second)
            exact ⟨.fault _, after, finalMap, finalWorld, .tailFault execution sourceTrace, .fault matched,
              finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans metadata⟩
        | caseRight second _ =>
          have shifted := second
          rw [← GenericExpressionMeaning.rename_prefix] at shifted
          obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
            maps, worlds, frame, metadata⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
              (locals.mono firstMetadata) nextLayout shifted
          cases result with
          | @values sources values restRep =>
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
              (LocalSequence.pair_success lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second)
            have nonempty : values ≠ [] := by
              intro absent
              have lengths := restRep.length.2
              simp [absent] at lengths
            refine ⟨.values (sourceValue :: sources), after, finalMap, finalWorld,
              .cons execution sourceTrace, ?_, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans metadata⟩
            simpa [packValues, nonempty] using
              Result.values (codes := lowered :: nextCode :: codes)
                (.cons (model.extend payload maps worlds) restRep)

/-- Finite source arguments, including failures, produce the actual Core
bundle. Child correspondence is universal over all related states. -/
theorem preserves (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.ValuesOutcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.Recursive.Expressions program registry frame context environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases outcome with
  | values sources =>
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := preserves_values tree meaning environments heaps locals layout execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented,
      finalHeaps, maps, worlds, frame, metadata⟩
  | fault reason =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := preserves_fault tree meaning environments heaps locals layout execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault represented,
      finalHeaps, maps, worlds, frame, metadata⟩

/-- Only an existing finite source trace supplies a sufficient fuel bound. -/
theorem preserves_sufficient_fuel (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.ValuesOutcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.Recursive.Expressions program registry frame context environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := preserves tree meaning environments heaps locals layout execution
  obtain ⟨required, runs⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required, runs, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem reflects_done (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Reflects model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value} {fuel : Nat}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (completed : runStateful fuel
      (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expressions program registry frame context environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects tree meaning environments heaps locals layout (runStateful_evaluation_sound completed)

/-- An accepted user-callable gate evaluates recursive staged arguments at
its two real hidden slots. An argument failure returns before application and
keeps its own origin, rather than relabelling it as a fault at the caller. -/
theorem preserves_call_argument_fault
    {site : SourceCoreCallableContracts.Callsite} {call callee : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program registry frame context certificate faults)
    (coverage : CallStageBoundary.Covers model frame.guards site call ids node.type lowered.type)
    (unknown : Word) (resultType : Ty)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before middle after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {callable : Dynamic.Value} {contract : Staging.CallGuard.Contract}
    {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
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
  obtain ⟨carrier, middleStore, middleMap, middleWorld, calleeRun, represented, middleHeaps,
    firstMaps, firstWorlds, firstFrame, firstMetadata⟩ := meaning certified found environments heaps locals layout child
  cases represented with
  | value payload =>
    obtain ⟨dispatch⟩ := coverage payload bound
    rw [dispatch.shape] at calleeRun
    have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) canonical
        (.unit :: .pair dispatch.function (.word dispatch.contract) :: actual) := GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix layout (.pair dispatch.function (.word dispatch.contract))) .unit
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentRun, matched, finalHeaps,
      maps, worlds, preserved, metadata⟩ := preserves_fault tree meaning
        (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata) nextLayout arguments
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentRun
    have gate : CallableContract.decision site.gates .beforeArguments unknown dispatch.contract = none := by
      rw [site.decision_known .beforeArguments unknown dispatch.contract dispatch.row dispatch.found]
      exact SourceCoreCallableContracts.reason_accepted _ _ _ (dispatch.accepted accepted)
    exact ⟨token, finalStore, finalMap, finalWorld,
      CallableContract.call_argument_failure site.gates unknown calleeRun gate argumentRun,
      matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
      firstFrame.trans preserved, firstMetadata.trans metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveStageArguments
