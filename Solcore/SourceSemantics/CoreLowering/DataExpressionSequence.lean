import Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning

/-! Correspondence for the production argument/key packing helper. Each child
has a static compilation receipt and a universal semantic theorem. The list
theorems construct the intervening heaps and the actual inserted payload slots;
they do not assume child evaluations at those generated layouts. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataExpressionSequence
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open GenericExpressionMeaning DataPatternValues

inductive Tree (source : TypedSource) (certificate : Certificate) (scope : SourceCoreLocalCell.Scope) :
    List ExpressionId → List TypeSystem.Ty → List SourceCoreBasic.LoweredExpr → Prop where
  | nil : Tree source certificate scope [] [] []
  | single {id node lowered}
      (found : source.lookupExpression? id = some node) (generated : certificate scope id lowered) :
      Tree source certificate scope [id] [node.type] [lowered]
  | cons {id node lowered next ids types nextCode codes}
      (found : source.lookupExpression? id = some node) (generated : certificate scope id lowered)
      (tail : Tree source certificate scope (next :: ids) types (nextCode :: codes)) :
      Tree source certificate scope (id :: next :: ids) (node.type :: types) (lowered :: nextCode :: codes)

/-- A vector of individual static receipts determines the production packing
tree. There is no evaluation or semantic condition in this extraction. -/
theorem Tree.of_children {source : TypedSource} {certificate : Certificate} {scope : SourceCoreLocalCell.Scope}
    {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
    (children : ListRel (fun id code => ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code) ids codes) :
    ∃ types, Tree source certificate scope ids types codes := by
  induction children with
  | nil => exact ⟨[], .nil⟩
  | @cons id code ids codes head tail ih =>
    obtain ⟨node, found, generated⟩ := head
    cases tail with
    | nil => exact ⟨[node.type], .single found generated⟩
    | cons _ _ =>
      obtain ⟨types, rest⟩ := ih
      exact ⟨node.type :: types, .cons found generated rest⟩

/-- Successful effectful list traversal exposes the exact individual compiler
results; callers may retain their metadata/type-validation wrapper in `compile`. -/
theorem Tree.of_mapM {α error : Type} {source : TypedSource} {certificate : Certificate}
    {scope : SourceCoreLocalCell.Scope} (identify : α → ExpressionId)
    (compile : α → Except error SourceCoreBasic.LoweredExpr)
    {inputs : List α} {codes : List SourceCoreBasic.LoweredExpr}
    (accepted : inputs.mapM compile = .ok codes)
    (extract : ∀ input code, compile input = .ok code → ∃ node,
      source.lookupExpression? (identify input) = some node ∧ certificate scope (identify input) code) :
    ∃ types, Tree source certificate scope (inputs.map identify) types codes := by
  apply Tree.of_children
  induction inputs generalizing codes with
  | nil => simp at accepted; subst codes; exact .nil
  | cons input rest ih =>
    cases head : compile input with
    | error reason => simp [List.mapM_cons, head, bind, Except.bind] at accepted
    | ok code =>
      cases tail : rest.mapM compile with
      | error reason => simp [List.mapM_cons, head, tail, bind, Except.bind] at accepted
      | ok restCodes =>
        simp only [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at accepted
        subst codes
        exact .cons (extract input code head) (ih tail)

inductive Values {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} (model : GenericHeap.PayloadModel catalog projects)
    (mapping : LocationMap) (world : StoreTyping) :
    List TypeSystem.Ty → List Ty → List Dynamic.Value → List Value → Prop where
  | nil : Values model mapping world [] [] [] []
  | cons {sourceType type source value sourceTypes types sources values}
      (head : model.Represents mapping world sourceType source value type)
      (tail : Values model mapping world sourceTypes types sources values) :
      Values model mapping world (sourceType :: sourceTypes) (type :: types) (source :: sources) (value :: values)

theorem Values.extend {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {model : GenericHeap.PayloadModel catalog projects}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {sourceTypes : List TypeSystem.Ty} {types : List Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : Values model mapping world sourceTypes types sources values)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Values model futureMapping futureWorld sourceTypes types sources values := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons (model.extend head maps worlds) ih

theorem Values.length {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {model : GenericHeap.PayloadModel catalog projects}
    {mapping : LocationMap} {world : StoreTyping}
    {sourceTypes : List TypeSystem.Ty} {types : List Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : Values model mapping world sourceTypes types sources values) :
    types.length = sources.length ∧ types.length = values.length := by
  induction represented with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩

theorem pair_rename (leftType rightType : Ty) (left right : Expr) (ξ : Renaming) :
    (LocalSequence.pair leftType rightType left right).rename ξ =
      LocalSequence.pair leftType rightType (left.rename ξ) (right.rename ξ) := by
  simp [LocalSequence.pair, LanguageResult.bind, LanguageResult.success, Expr.rename, Renaming.lift]

abbrev Outcome := Except Dynamic.SemanticFault (List Dynamic.Value)

inductive Trace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (ids : List ExpressionId) : Outcome → Dynamic.Heap → Prop where
  | values {sources after}
      (evaluated : Dynamic.ExpressionsEvaluate program context evidence source environment before ids sources after) :
      Trace program context evidence source environment before ids (.ok sources) after
  | fault {reason after}
      (failed : Dynamic.ExpressionsFault program context evidence source environment before ids reason after) :
      Trace program context evidence source environment before ids (.error reason) after

inductive Result {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} (model : GenericHeap.PayloadModel catalog projects)
    (mapping : LocationMap) (world : StoreTyping) (types : List TypeSystem.Ty)
    (codes : List SourceCoreBasic.LoweredExpr) (faults : FaultRep) : Outcome → Value → Prop where
  | values {sources values}
      (represented : Values model mapping world types (codes.map (·.type)) sources values) :
      Result model mapping world types codes faults (.ok sources) (.inRight .word (packValues values))
  | fault {reason token} (represented : faults reason token) :
      Result model mapping world types codes faults (.error reason)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token))

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {model : GenericHeap.PayloadModel catalog projects}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}

/-- Successful evaluation keeps left-to-right effects and every represented
payload, including captured references inside earlier argument values. -/
theorem Tree.preserves_values (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Dynamic.ExpressionsEvaluate program context evidence source environment before ids sources after) :
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
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout (.value head)
      cases represented with
      | value payload =>
        exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
          finalHeaps, maps, worlds, frame, metadata⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head rest =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning generated found environments heaps locals layout (.value head)
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
          maps, worlds, frame, metadata⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix layout coreValue) rest
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

/-- A source fault evaluates only its successful prefix. The generated helper
propagates the exact token without evaluating later arguments. -/
theorem Tree.preserves_fault (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Dynamic.ExpressionsFault program context evidence source environment before ids reason after) :
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
    | head failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched,
          finalHeaps, maps, worlds, frame, metadata⟩
    | tail _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | head failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata⟩
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type evaluated
    | tail head failed =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning generated found environments heaps locals layout (.value head)
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
          maps, worlds, frame, metadata⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix layout coreValue) failed
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [rename_prefix] at second
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second

/-- Every completed evaluation of the actual generated bundle constructs a
finite source trace. Arbitrary inserted temporary slots are admitted through
the child theorem's explicit renaming; no exact closure weakening is used. -/
theorem Tree.reflects (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : Reflects model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual before store ξ value finalStore with
  | nil =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (show Evaluates actual store
      ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
    exact ⟨.ok [], before, mapping, world, .values .nil, .values (values := []) .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | single found generated =>
    obtain ⟨outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout evaluated
    cases represented with
    | value payload =>
      cases execution with
      | value trace => exact ⟨.ok [_], after, finalMap, finalWorld,
          .values (.cons trace .nil), .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata⟩
    | fault matched =>
      cases execution with
      | fault trace => exact ⟨.error _, after, finalMap, finalWorld,
          .fault (.head trace), .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
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
        cases execution with
        | fault trace =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.pair_left_failure lowered.type
            (SourceCoreCalls.packArguments (nextCode :: codes)).type first)
          exact ⟨.error _, after, finalMap, finalWorld, .fault (.head trace), .fault matched,
            finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight first continuation =>
      obtain ⟨outcome, middle, middleMap, middleWorld, execution, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning generated found environments heaps locals layout first
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
              maps, worlds, frame, metadata⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) nextLayout shifted
            cases result with
            | fault matched =>
              cases sourceTrace with
              | fault tailSource =>
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                  (LocalSequence.pair_right_failure lowered.type
                    (SourceCoreCalls.packArguments (nextCode :: codes)).type first second)
                exact ⟨.error _, after, finalMap, finalWorld, .fault (.tail firstSource tailSource), .fault matched,
                  finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans metadata⟩
          | caseRight second _ =>
            have shifted := second
            rw [← rename_prefix] at shifted
            obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
              maps, worlds, frame, metadata⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) nextLayout shifted
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
                  firstFrame.trans frame, firstMetadata.trans metadata⟩
                simpa [packValues, nonempty] using
                  Result.values (codes := lowered :: nextCode :: codes)
                    (.cons (model.extend payload maps worlds) restRep)

theorem Tree.preserves (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
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
      maps, worlds, frame, metadata⟩ := tree.preserves_values meaning environments heaps locals layout execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented,
      finalHeaps, maps, worlds, frame, metadata⟩
  | fault execution =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := tree.preserves_fault meaning environments heaps locals layout execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault represented,
      finalHeaps, maps, worlds, frame, metadata⟩

/-- Finiteness comes from the independent source trace. Fuel exhaustion remains
a resumable machine state, rather than a successful or faulting source outcome. -/
theorem Tree.preserves_sufficient_fuel (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Trace program context evidence source environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := tree.preserves meaning environments heaps locals layout execution
  obtain ⟨required, runs⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required, runs, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem Tree.reflects_done (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : Reflects model program context evidence source certificate faults)
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
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  tree.reflects meaning environments heaps locals layout (runStateful_evaluation_sound completed)

end Solcore.SourceSemantics.CoreLowering.DataExpressionSequence
