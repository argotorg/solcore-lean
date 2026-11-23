import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationArrayCells

/-!
# Cell-aware invocations: memory arrays' references

The heads of `CanStore.load(lidx(a, i))`, the memref made on the spot: the array's and the index's meanings,
then `0x32` from the array's length on, else the element at the index, read as `a[i]` reads it. A memref
has no value relation of its own, so the head takes the array and the index as its children. Main
declarations: `CellAwareInvocationArrayBounds.load_preserves` and `load_reflects`.
-/

section
/-! `CanStore.load(lidx(a, i))`: the memref's bounds check against the array's length, then the read. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationArrayBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds CellAwareArraySourceInversion CompatibleArrayEvaluation
open CellAwareArrayCells
open GenericExpressionMeaning (agree_prefix rename_prefix)
universe u

/-- `CanStore.load(r)` has the element type of its memref. -/
theorem load_source_types {source : TypedSource} {context : SourceSemantics.Context} {id reference : ExpressionId}
    {node : ExpressionNode} (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .memrefLoad reference) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ExpressionHasType source context reference (TypeSystem.Ty.memref node.type) := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    cases raw with
    | memrefLoad referenceTyped => exact typeEq ▸ referenceTyped

/-- `lidx(a, i)` of a memref of `T` takes an array of `T`s and an index of `word` or one of the twelve
types. -/
theorem reference_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id base subscript : ExpressionId} {node : ExpressionNode} {element : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .elementRef base subscript) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id (TypeSystem.Ty.memref element)) :
    ExpressionHasType source context base (TypeSystem.Ty.array element) ∧
      ∃ subscriptType, ExpressionHasType source context subscript subscriptType ∧ ArrayIndexType subscriptType := by
  generalize typeEq : TypeSystem.Ty.memref element = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | elementRef baseTyped subscriptTyped kind =>
      have sameType := typeEq.trans resultEq
      simp only [TypeSystem.Ty.memref, TypeSystem.Ty.application.injEq, true_and] at sameType
      subst sameType
      exact ⟨baseTyped, _, subscriptTyped, kind⟩

theorem memrefLoad_split (layout : OrderedMapping.Layout) (comparison reference : Expr) :
    ∃ tail, SourceCoreDataExpressions.memrefLoad layout comparison reference =
      LanguageResult.bind layout.valueType reference tail := ⟨_, rfl⟩

theorem elementRef_split (layout : OrderedMapping.Layout) (base subscript : Expr) :
    ∃ tail, SourceCoreDataExpressions.elementRef layout base subscript =
      LanguageResult.bind (.product (.cell (.product .word (.product layout.valueType layout.type))) .word) base
        (LanguageResult.bind (.product (.cell (.product .word (.product layout.valueType layout.type))) .word)
          (subscript.weakenAt 0) tail) := ⟨_, rfl⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)
  {scope : SourceCoreLocalCell.Scope} {id base : ExpressionId} {node baseNode : ExpressionNode}
  {first lowered : SourceCoreBasic.LoweredExpr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include bridge functions faults unique selectedBodies runtime covers in
/-- `CanStore.load(lidx(a, i))`'s head: the array's and the index's meanings, then `0x32` from the array's
length on, else the element at the index, read as `a[i]` reads it. -/
theorem load_preserves [RecursiveStageMeaning.FaultTokens faults] {children : GenericExpressionMeaning.Certificate}
    {reference subscript : ExpressionId} {referenceNode subscriptNode : ExpressionNode} {fuel : Nat}
    {layout : OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {second : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node layout.valueType)
    (form : node.form = .memrefLoad reference)
    (referenceMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source reference
      referenceNode (.product first.type .word))
    (referenceForm : referenceNode.form = .elementRef base subscript)
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (subscriptFound : invocation.source.lookupExpression? subscript = some subscriptNode)
    (firstChild : children scope base first) (secondChild : children scope subscript second)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0, layout))
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel compiled.compatible.checked
      (.constructor (.builtin .word)) = .ok comparison)
    (code : lowered = ⟨layout.valueType, SourceCoreDataExpressions.memrefLoad layout comparison.expression
      (SourceCoreDataExpressions.elementRef layout first.expression second.expression)⟩)
    (size : Nat)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation (Point scope id lowered)
      faults size := by
  intro current child code' point root found sourceTyped mapping world administrative environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees actualTyped initial admitted authority
    physical owner ownerFrame trace
  obtain ⟨sameScope, sameId, sameCode⟩ := point
  subst current; subst child; subst code'; subst code
  cases Option.some.inj (found.symm.trans metadata.found)
  have referenceTypedAt := load_source_types unique found form metadata.coercions sourceTyped
  obtain ⟨baseTypedAt, subscriptType, subscriptTypedAt, kind⟩ :=
    reference_source_types unique referenceMetadata.found referenceForm referenceMetadata.coercions referenceTypedAt
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have subscriptTypeEq := CellAwareArraySourceInversion.typed_type unique subscriptFound subscriptTypedAt
  have baseTyped : ExpressionHasType invocation.source context base baseNode.type := baseTypeEq ▸ baseTypedAt
  have subscriptTyped : ExpressionHasType invocation.source context subscript subscriptNode.type :=
    subscriptTypeEq ▸ subscriptTypedAt
  have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
      SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array node.type) := by rw [← baseTypeEq]
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ subscriptFound subscriptTyped
  have keyType := CellAwareArrayReads.viewShape_keyType shaped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreDataExpressions.memrefLoad layout comparison.expression
        (SourceCoreDataExpressions.elementRef layout first.expression second.expression)).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type layout.valueType faults outcome
        value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [memrefLoad_rename, elementRef_rename, closed_rename comparison.typed]
    cases CellAwareArraySourceInversion.children unique found form rfl trace with
    | fault failed smaller =>
      obtain ⟨referenceSize, referenceSmaller, referenceTrace⟩ := single_fault failed
      cases CellAwareArraySourceInversion.children unique referenceMetadata.found referenceForm rfl referenceTrace with
      | fault failed referenceChildren =>
        rcases pair_fault failed with ⟨firstSize, firstSmaller, firstTrace⟩ |
          ⟨firstSize, secondSize, baseSource, middle, firstSmaller, secondSmaller, firstTrace, secondTrace⟩
        · obtain ⟨_, finalStore, finalMap, finalWorld, firstEval, represented, finalHeaps, maps, worlds, frame,
            heapMetadata, effect, reached, related, _⟩ :=
            firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
              owner ownerFrame firstTrace
          cases represented with
          | fault matched =>
            exact ⟨_, finalStore, finalMap, finalWorld, memrefLoad_failure (elementRef_base_failure firstEval),
              .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
        · obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
            firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
              owner ownerFrame firstTrace
          cases represented with
          | @value _ coreValue payload =>
            obtain ⟨_, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame,
              heapMetadata, effect, reached, related, _⟩ :=
              secondIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) (agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
                (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame
                secondTrace
            cases represented with
            | fault matched =>
              rw [rename_prefix] at secondEval
              exact ⟨_, finalStore, finalMap, finalWorld,
                memrefLoad_failure (elementRef_index_failure firstEval secondEval), .fault matched, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
                callerProtocol.trans firstRelated related⟩
      | result evaluated result referenceChildren =>
        obtain ⟨firstSize, secondSize, baseSource, subscriptSource, middle, firstSmaller, secondSmaller, rfl,
          firstTrace, secondTrace⟩ := pair_values evaluated
        obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
          firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
            owner ownerFrame firstTrace
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨_, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, maps, worlds, frame,
            heapMetadata, effect, reached, related, _⟩ :=
            secondIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
              (locals.mono firstMetadata) (agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
              (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
          cases represented with
          | @value _ coreIndex indexPayload =>
            rw [rename_prefix] at secondEval
            rw [← subscriptTypeEq] at indexPayload
            obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
            have basePayload := payload.extend (.refl _) maps worlds
            cases result with
            | elementRefIndexType notWord _ => exact (notWord trivial).elim
            | elementRefOutOfBounds outside =>
              obtain ⟨element', location, rfl⟩ := array_source basePayload baseRuntime
              obtain ⟨target, payloadType, identity, rfl, _, _, _, _⟩ := arrayRef_fields basePayload rfl
              cases outside with
              | @array _ _ cell elements _ read stored beyond =>
                obtain ⟨measured, small⟩ :=
                  CellAwareArrayReads.length_preserve keyHeaps (.array read stored) basePayload shaped
                cases measured with
                | array coreRead =>
                  have outsideCore : ¬ word < Word.ofNatModulo elements.length := by
                    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                    omega
                  exact ⟨_, keyStore, keyMap, keyWorld,
                    memrefLoad_failure (elementRef_outOfBounds firstEval secondEval coreRead outsideCore),
                    .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps, firstMaps.trans maps,
                    firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
                    firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
    | result evaluated result smaller =>
      obtain ⟨referenceSize, memref, referenceSmaller, rfl, referenceTrace⟩ := single_values evaluated
      cases result with
      | memrefLoad reads =>
        cases CellAwareArraySourceInversion.children unique referenceMetadata.found referenceForm rfl referenceTrace with
        | result evaluated result referenceChildren =>
          obtain ⟨firstSize, secondSize, baseSource, subscriptSource, middle, firstSmaller, secondSmaller, rfl,
            firstTrace, secondTrace⟩ := pair_values evaluated
          obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
            firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
              owner ownerFrame firstTrace
          cases represented with
          | @value _ coreValue payload =>
            obtain ⟨_, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, maps, worlds, frame,
              heapMetadata, effect, reached, related, _⟩ :=
              secondIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) (agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
                (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame
                secondTrace
            cases represented with
            | @value _ coreIndex indexPayload =>
              rw [rename_prefix] at secondEval
              rw [← subscriptTypeEq] at indexPayload
              obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
              have basePayload := payload.extend (.refl _) maps worlds
              cases result with
              | @elementRef _ _ _ _ _ _ count counted within =>
                obtain ⟨target, payloadType, identity, rfl, typeEq, _, _, _⟩ := arrayRef_fields basePayload rfl
                obtain ⟨measured, small⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
                cases measured with
                | array coreRead =>
                  have below : word < Word.ofNatModulo count := by
                    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                    exact within
                  have referenceEval := elementRef_evaluates (layout := layout) firstEval secondEval coreRead below
                  have pairTyped : RuntimeValueHasType keyWorld
                      (.pair (.cellRef (.product .word (.product payloadType (.namedData identity))) target)
                        (.word word)) (.product first.type .word)
                      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
                    .pair basePayload.runtime_hasType .word
                  have readTyped := RuntimeEnvironmentHasTypes.cons pairTyped
                    (actualTyped.weaken (firstWorlds.trans worlds))
                  obtain ⟨result, final, futureWorld, suffix, coreReads, elementRep, finalHeaps, suffixWorlds,
                    suffixFrame, suffixAppend⟩ :=
                    CellAwareArrayReads.reads_preserve prepared keyHeaps readTyped reads basePayload baseRuntime
                      (.array _) shaped word.isLt
                  rw [CellAwareArrayReads.ofNatModulo_self] at coreReads
                  subst suffixAppend
                  let suffixPool : State headers keys
                      ⟨scope, keyMap, futureWorld, after, keyStore ++ suffix, canonical⟩ :=
                    (bridge.pool reached).extend (.refl _) suffixWorlds suffixFrame (.refl _)
                  obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
                    (.refl _) suffixWorlds suffixFrame (.refl _) (Relates.of_records_eq rfl)
                  exact ⟨_, _, keyMap, futureWorld,
                    memrefLoad_evaluates prepared keyType referenceEval coreReads,
                    .value (elementRep.extend (.refl _) (.refl _) suffixWorlds), finalHeaps, firstMaps.trans maps,
                    (firstWorlds.trans worlds).trans suffixWorlds,
                    (firstFrame.trans frame).trans suffixFrame, firstMetadata.trans heapMetadata,
                    (firstEffect.trans effect).trans (CellAwareScopeAuthority.Effect.append
                      (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) _ suffix
                      (.refl _) (.refl keyMap) suffixWorlds),
                    returned, callerProtocol.trans (callerProtocol.trans firstRelated related) returnedRelated⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `CanStore.load(lidx(a, i))`'s head, reflected: the array's and the index's Core runs give their Source
runs, and the load's Core run is the one the Source read, or its position from the array's length on, gives. -/
theorem load_reflects [RecursiveStageMeaning.FaultTokens faults] {children : GenericExpressionMeaning.Certificate}
    {reference subscript : ExpressionId} {referenceNode subscriptNode : ExpressionNode} {fuel : Nat}
    {layout : OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {second : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node layout.valueType)
    (form : node.form = .memrefLoad reference)
    (referenceMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source reference
      referenceNode (.product first.type .word))
    (referenceForm : referenceNode.form = .elementRef base subscript)
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (subscriptFound : invocation.source.lookupExpression? subscript = some subscriptNode)
    (firstChild : children scope base first) (secondChild : children scope subscript second)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0, layout))
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel compiled.compatible.checked
      (.constructor (.builtin .word)) = .ok comparison)
    (code : lowered = ⟨layout.valueType, SourceCoreDataExpressions.memrefLoad layout comparison.expression
      (SourceCoreDataExpressions.elementRef layout first.expression second.expression)⟩)
    (size : Nat)
    (childMeaning : ReflectsBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation (Point scope id lowered)
      faults size := by
  intro current child code' point root found sourceTyped mapping world administrative environment canonical actual
    actualContext before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted
    authority physical owner ownerFrame evaluated
  obtain ⟨sameScope, sameId, sameCode⟩ := point
  subst current; subst child; subst code'; subst code
  cases Option.some.inj (found.symm.trans metadata.found)
  have referenceTypedAt := load_source_types unique found form metadata.coercions sourceTyped
  obtain ⟨baseTypedAt, subscriptType, subscriptTypedAt, kind⟩ :=
    reference_source_types unique referenceMetadata.found referenceForm referenceMetadata.coercions referenceTypedAt
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have subscriptTypeEq := CellAwareArraySourceInversion.typed_type unique subscriptFound subscriptTypedAt
  have baseTyped : ExpressionHasType invocation.source context base baseNode.type := baseTypeEq ▸ baseTypedAt
  have subscriptTyped : ExpressionHasType invocation.source context subscript subscriptNode.type :=
    subscriptTypeEq ▸ subscriptTypedAt
  have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
      SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array node.type) := by rw [← baseTypeEq]
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ subscriptFound subscriptTyped
  have occurrence : Staging.Recursive.Occurrence invocation id (.memrefLoad reference) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have referenceOccurrence : Staging.Recursive.Occurrence invocation reference (.elementRef base subscript) :=
    ⟨_, lookupExpression?_sound referenceMetadata.found, referenceForm, referenceMetadata.requirements,
      referenceMetadata.coercions⟩
  have keyType := CellAwareArrayReads.viewShape_keyType shaped
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type layout.valueType faults outcome
        value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    change EvaluationSize size actual store ((SourceCoreDataExpressions.memrefLoad layout comparison.expression
      (SourceCoreDataExpressions.elementRef layout first.expression second.expression)).rename ξ) value finalStore
      at evaluated
    rw [memrefLoad_rename, elementRef_rename, closed_rename comparison.typed] at evaluated
    have complete := evaluated.sound
    obtain ⟨tail, split⟩ := memrefLoad_split layout comparison.expression
      (SourceCoreDataExpressions.elementRef layout (first.expression.rename ξ) (second.expression.rename ξ))
    rw [split] at evaluated
    obtain ⟨referenceSize, referenceResult, referenceStore, referenceSmaller, referenceEvaluation⟩ :
        ∃ referenceSize referenceResult referenceStore, referenceSize < size ∧
          EvaluationSize referenceSize actual store (SourceCoreDataExpressions.elementRef layout
            (first.expression.rename ξ) (second.expression.rename ξ)) referenceResult referenceStore := by
      cases evaluated with
      | caseLeft head _ => exact ⟨_, _, _, by omega, head⟩
      | caseRight head _ => exact ⟨_, _, _, by omega, head⟩
    obtain ⟨referenceTail, referenceSplit⟩ :=
      elementRef_split layout (first.expression.rename ξ) (second.expression.rename ξ)
    rw [referenceSplit] at referenceEvaluation
    cases referenceEvaluation with
    | caseLeft firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
        frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
          (memrefLoad_failure (elementRef_base_failure firstEvaluation.sound))
        exact ⟨_, _, after, finalMap, finalWorld,
          .arrayFault occurrence rfl (.headFault (.arrayFault referenceOccurrence rfl (.headFault firstTrace))),
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | caseRight firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps, firstMaps,
        firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | @value baseSource coreValue payload =>
        cases branch with
        | caseLeft secondEvaluation rest =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps, maps,
            worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
            secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState
              firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner
              ownerFrame shifted
          cases represented with
          | fault matched =>
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
              (memrefLoad_failure (elementRef_index_failure firstEvaluation.sound secondEvaluation.sound))
            exact ⟨_, _, after, finalMap, finalWorld,
              .arrayFault occurrence rfl (.headFault (.arrayFault referenceOccurrence rfl
                (.tailFault firstTrace (.headFault secondTrace)))), .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
              firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
        | caseRight secondEvaluation rest =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, after, keyMap, keyWorld, secondTrace, represented, keyHeaps, maps, worlds,
            frame, heapMetadata, effect, reached, related, _post⟩ :=
            secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState
              firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner
              ownerFrame shifted
          cases represented with
          | @value subscriptSource coreIndex indexPayload =>
            rw [← subscriptTypeEq] at indexPayload
            obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
            have basePayload := payload.extend (.refl _) maps worlds
            have baseSourceTyped := Dynamic.ValueHasType.mono heapMetadata firstPost.at_value.1
            rw [← baseTypeEq] at baseSourceTyped
            obtain ⟨element', location, rfl⟩ := array_source basePayload baseRuntime
            obtain ⟨target, payloadType, identity, rfl, _, _, _, _⟩ := arrayRef_fields basePayload rfl
            obtain ⟨count, counted⟩ :=
              CellAwareArrayReads.length_cases keyHeaps rfl basePayload baseRuntime baseSourceTyped
            cases counted with
            | @array _ _ cell elements read stored =>
              obtain ⟨measured, small⟩ :=
                CellAwareArrayReads.length_preserve keyHeaps (.array read stored) basePayload shaped
              cases measured with
              | array coreRead =>
                by_cases within : word.val < elements.length
                · obtain ⟨element, elementAt⟩ : ∃ element, elements[word.val]? = some element :=
                    ⟨_, List.getElem?_eq_getElem within⟩
                  have reads : Dynamic.ViewReads after (.arrayRef element' location) word.val element :=
                    .array read stored elementAt
                  have below : word < Word.ofNatModulo elements.length := by
                    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                    exact within
                  have referenceEval := elementRef_evaluates (layout := layout) firstEvaluation.sound
                    secondEvaluation.sound coreRead below
                  have pairTyped : RuntimeValueHasType keyWorld
                      (.pair (.cellRef (.product .word (.product payloadType (.namedData identity))) target)
                        (.word word)) (.product first.type .word)
                      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
                    .pair basePayload.runtime_hasType .word
                  have readTyped := RuntimeEnvironmentHasTypes.cons pairTyped
                    (actualTyped.weaken (firstWorlds.trans worlds))
                  obtain ⟨result, final, futureWorld, suffix, coreReads, elementRep, finalHeaps, suffixWorlds,
                    suffixFrame, suffixAppend⟩ :=
                    CellAwareArrayReads.reads_preserve prepared keyHeaps readTyped reads basePayload baseRuntime
                      (.array _) shaped word.isLt
                  rw [CellAwareArrayReads.ofNatModulo_self] at coreReads
                  subst suffixAppend
                  obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                    (memrefLoad_evaluates prepared keyType referenceEval coreReads)
                  let suffixPool : State headers keys ⟨scope, keyMap, futureWorld, after, _, canonical⟩ :=
                    (bridge.pool reached).extend (.refl _) suffixWorlds suffixFrame (.refl _)
                  obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
                    (.refl _) suffixWorlds suffixFrame (.refl _) (Relates.of_records_eq rfl)
                  exact ⟨_, _, after, keyMap, futureWorld,
                    .arrayResult occurrence rfl
                      (.cons (.arrayResult referenceOccurrence rfl (.cons firstTrace (.cons secondTrace .nil))
                        (.elementRef (.array read stored) within)) .nil) (.memrefLoad reads),
                    .value (elementRep.extend (.refl _) (.refl _) suffixWorlds), finalHeaps, firstMaps.trans maps,
                    (firstWorlds.trans worlds).trans suffixWorlds,
                    (firstFrame.trans frame).trans suffixFrame, firstMetadata.trans heapMetadata,
                    (firstEffect.trans effect).trans (CellAwareScopeAuthority.Effect.append
                      (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) _ suffix
                      (.refl _) (.refl keyMap) suffixWorlds),
                    returned, callerProtocol.trans (callerProtocol.trans firstRelated related) returnedRelated⟩
                · have outside : Dynamic.ViewOutOfBounds after (.arrayRef element' location) word.val :=
                    .array read stored (by omega)
                  have outsideCore : ¬ word < Word.ofNatModulo elements.length := by
                    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                    exact within
                  obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                    (memrefLoad_failure (elementRef_outOfBounds firstEvaluation.sound secondEvaluation.sound coreRead
                      outsideCore))
                  exact ⟨_, _, after, keyMap, keyWorld,
                    .arrayFault occurrence rfl (.headFault (.arrayResult referenceOccurrence rfl
                      (.cons firstTrace (.cons secondTrace .nil)) (.elementRefOutOfBounds outside))),
                    .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps, firstMaps.trans maps,
                    firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
                    firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationArrayBounds
end
