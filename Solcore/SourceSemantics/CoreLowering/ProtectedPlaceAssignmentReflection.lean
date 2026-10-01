import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceReflection


/-! Typed child meanings for the actual CompatiblePlaceKeyReflection phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentKeyReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceKeyReflection CompatibleRenamedPlace

/-- Completed emitted code supplies the key runs to the protected reflection
theorem. No source projection trace or child runtime execution is an input. -/
theorem reflects {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before : Dynamic.Heap} {store finalStore : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType operator bitNot invalid) result finalStore) :
    Result checked registry functions program context evidence source faults prepared (renamedCodes codes ξ) sourceTypes place environment
      coreEnvironment before store mapping world (ξ index) rhs next outputType operator bitNot invalid result finalStore := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  have reflectKeys := fun {keyValue : Value} {keyStore : Store}
      (evaluated : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments (renamedCodes codes ξ)).expression) keyValue keyStore) =>
    ProtectedPlaceKeys.reflects transport children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) actualTyped) installed
      (by simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  cases completed with
  | letE referenceEvaluated tail =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic referenceEvaluated (Evaluates.var (agrees selected))
    cases tail with
    | caseLeft keysEvaluated failed =>
      obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ := reflectKeys keysEvaluated
      cases represented with
      | fault tokenRep =>
        cases sourceTrace with
        | fault sourceTrace =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.projectionExpression lookup initialRead sourceTrace) rfl tokenRep finalHeaps maps worlds frame metadata
    | caseRight keysEvaluated tail =>
      obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ := reflectKeys keysEvaluated
      cases represented with
      | @values sources values related =>
        cases sourceTrace with
        | @values _ resolved _ shaped sourceTrace =>
          obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
          obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
          have locationEq := lookup.functional staticLookupRuntime
          subst staticLocation
          have cellEq := initialRead.functional staticRead
          subst staticCell
          obtain ⟨cell, read, type, _⟩ := metadata _ _ initialRead
          exact .keys lookup sourceTrace
            ⟨target, sources, values, _, finalMap, finalWorld, cell, read,
              type.trans (staticCellType.trans bodyEq), reference.extend maps worlds, agrees selected, shaped,
              keysEvaluated, by simpa only [renamedCodes_types] using related, finalHeaps, maps, worlds, frame, metadata⟩ tail

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentKeyReflection


/-! Typed child meanings for the actual CompatiblePlacePrefixReflection phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentPrefixReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlacePrefixReflection CompatibleRenamedPlace

/-- The diagnostic premises are static interpretations of emitted tokens.
They do not supply any source or native execution. All target source traces
are reconstructed from a completed emitted assignment and protected child theorem. -/
theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming} {rhsType : Core.Ty}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext rhsType)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType operator bitNot invalid) result finalStore) :
    Result compilation.checked registry functions program context evidence source faults prepared (renamedCodes codes ξ) sourceTypes place leaf environment
      coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore := by
  have closed := virtual_closed layout ordinary
  have getterTyped := getter_typed layout closed (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨scheme, staticLookup, _, _, _⟩ := rootTyped.scheme
  obtain ⟨location, initialCell, lookup, initialRead, _, _⟩ := locals.lookup staticLookup
  have keyPhase := ProtectedPlaceAssignmentKeyReflection.reflects layout.children transport meaning environments heaps locals agrees actualTyped installed slot rootTyped lookup initialRead completed
  cases keyPhase with
  | fault sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata =>
    exact .fault sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata
  | @keys sourceLocation resolved after keyLookup sourceTrace keys continuation =>
    have locationEq := lookup.functional keyLookup
    subst sourceLocation
    have keyRelated : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) keys.keyMap keys.keyWorld sourceTypes (codes.map (·.type)) keys.sources keys.values := by
      simpa only [renamedCodes_types] using keys.related
    have arguments := layout.views.arguments keys.shaped keyRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
    have currentPath : PreparedPath compilation.checked source site keys.cell.type place.projections 0 prepared.steps prepared.keys leaf := keys.type ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld source site keys.values currentPath resolved := by
      simpa only [keys.type] using arguments
    have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
        (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          actualContext) ambient.definitions :=
      .cons (CompatiblePlaceResolution.values_typed keyRelated)
        (.cons (.cellRef keys.reference.typed) (actualTyped.weaken keys.worlds))
    have reflectGetter := fun {value : Value} {afterStore : Store}
        (evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment) keys.keyStore
          (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0))) value afterStore) =>
      CompatiblePlaceGetterReflection.reflects currentArguments layout.leafProjected
        (fun k v same => layout.virtual k v (keys.type.symm.trans same))
        (fun nonmapping => ordinary (fun k v same => nonmapping k v (keys.type.trans same)))
        registryExtension layout.nonempty functionTypes faithful observations (layout.keyTypes ▸ keyRelated.length.2)
        keys.heaps keys.reference keys.read typedEnvironment getterTyped (.var rfl) (.var rfl) evaluated
    unfold CompatiblePlaceKeyReflection.remainder at continuation
    simp only [packed_renamed_type] at continuation
    cases continuation with
    | caseLeft getterEvaluated failed =>
      obtain ⟨futureWorld, _, resultRep, finalHeaps, extension, frame, _⟩ := reflectGetter getterEvaluated
      cases resultRep with
      | missing initial fault receipt =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            exact .fault (.projectionRead lookup initialRead sourceTrace keys.read initial fault) rfl
              (missingTokens receipt) finalHeaps keys.maps (keys.worlds.trans extension) (keys.frame.trans frame) keys.metadata
      | uninitialized empty notMapping nonempty =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            exact .fault (.uninitialized lookup initialRead sourceTrace keys.read empty notMapping nonempty) rfl
              (invalidTokens _) finalHeaps keys.maps (keys.worlds.trans extension) (keys.frame.trans frame) keys.metadata
    | caseRight getterEvaluated remaining =>
      obtain ⟨futureWorld, _, resultRep, finalHeaps, extension, frame, _⟩ := reflectGetter getterEvaluated
      cases resultRep with
      | @read sourceRoot selected snapshot initial read represented =>
        exact .resolved (.intro lookup initialRead sourceTrace keys.read initial read)
          { target := keys.target
            sources := keys.sources
            values := keys.values
            selected := selected
            snapshot := snapshot
            keyStore := keys.keyStore
            store := _
            mapping := keys.keyMap
            world := futureWorld
            selectedEq := rfl
            currentCell := keys.cell
            currentRead := keys.read
            currentType := keys.type
            reference := keys.reference.extend (.refl _) extension
            shaped := keys.shaped
            keysEvaluated := keys.evaluated
            snapshotEvaluated := by simpa only [packed_renamed_type] using getterEvaluated
            keysRelated := keys.related.extend (.refl _) extension
            snapshotRelated := represented
            heaps := finalHeaps
            maps := keys.maps
            worlds := keys.worlds.trans extension
            frame := keys.frame.trans frame
            metadata := keys.metadata } (by simpa only [CompatiblePlacePrefixReflection.remainder, packed_renamed_type, snapshotEnvironment] using remaining)

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentPrefixReflection

namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentReflection
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceRhsReflection

/-- Source and Core RHS types are connected by the retained raw runtime view,
not by inverting the many-to-one native type projection. -/
private theorem rhs_reflects {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults entry)
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (coreType : lowered.type = prepared.route.leafType)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {next : Expr} {outputType : Ty} {operator : Syntax.ValueAssignOp} {invalid : Word} {result : Value}
    (resolution : CompatiblePlacePrefixReflection.Result checked registry functions program context evidence source faults prepared (renamedCodes codes ξ) sourceTypes
      place leaf environment coreEnvironment before store mapping world (lowered.expression.rename ξ) next outputType
      (binaryOperator (prepared.route.leafType = .integer) operator) false invalid result finalStore) :
    Result checked registry functions program context evidence source faults prepared (renamedCodes codes ξ) sourceTypes place leaf environment
      coreEnvironment before store mapping world id node (renamed lowered ξ) next outputType operator invalid result finalStore := by
  cases resolution with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
    exact .fault (.target sourceFault) resultEq tokenRep heaps maps worlds frame metadata
  | resolved sourceTrace resolution remaining =>
    cases remaining with
    | caseLeft rhsEvaluated failed =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, rhsResult⟩ :=
        ProtectedPlaceRhs.reflects resolution transport meaning generated found environments agrees actualTyped locals installed rhsEvaluated
      cases represented : rhsResult.represented with
      | fault tokenRep =>
        cases rhsResult.trace with
        | fault sourceRhs =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.rhs sourceTrace sourceRhs) rfl tokenRep rhsResult.heaps
                (resolution.maps.trans rhsResult.maps) (resolution.worlds.trans rhsResult.worlds)
                (resolution.frame.trans rhsResult.frame) (resolution.metadata.trans rhsResult.metadata)
    | caseRight rhsEvaluated remaining =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, rhsResult⟩ :=
        ProtectedPlaceRhs.reflects resolution transport meaning generated found environments agrees actualTyped locals installed rhsEvaluated
      cases represented : rhsResult.represented with
      | value payload =>
        exact .ready sourceTrace resolution
          { right := _
            value := _
            heap := rhsHeap
            store := _
            mapping := rhsMap
            world := rhsWorld
            meaning := rhsResult
            related := .compatible rhsView (by simpa only [payloadModel, renamed, coreType] using payload) } remaining

theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (preservation : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) result finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after ∧
      result = .inLeft outputType (.word token) ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧
      RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
        (ProtectedPlaceAssignmentSuccess.writtenContext prepared (SourceCoreCalls.packArguments codes).type
          actualContext) ambient.definitions ∧
      Evaluates (slots ++ coreEnvironment) written (shift 7 (next.rename ξ)) result finalStore) := by
  have nativeCompleted := completed
  rw [execute_rename layout.path (virtual_closed layout ordinary)] at nativeCompleted
  simp only [renamed_packed, Expr.rename] at nativeCompleted
  have resolution := ProtectedPlaceAssignmentPrefixReflection.reflects layout ordinary registryExtension transport meaning functionTypes faithful observations
    missingTokens invalidTokens environments heaps locals agrees actualTyped installed slot rootTyped nativeCompleted
  have rhsResult := rhs_reflects transport meaning rhsGenerated found rhsView rhsCoreType environments agrees actualTyped installed locals resolution
  have observed : CompatiblePlaceTailReflection.Result compilation.checked registry functions program context evidence source faults place operator rhs
      environment coreEnvironment before store mapping world (next.rename ξ) outputType result finalStore := by
    cases rhsResult with
    | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
      exact .fault sourceFault resultEq tokenRep heaps maps worlds frame metadata
    | ready sourceTrace resolution right continuation =>
      simp only [packed_renamed_type] at continuation
      exact CompatibleRenamedPlaceTail.reflects_ready layout ordinary registryExtension functionTypes faithful observations missingTokens
        operatorProfile environments agrees actualTyped sourceTrace resolution right continuation
  cases observed with
  | fault trace resultEq matched finalHeaps maps worlds frame metadata =>
    exact .inl ⟨_, _, _, _, _, trace, resultEq, matched, finalHeaps, maps, worlds, frame, metadata⟩
  | committed trace _ _ _ _ _ _ _ =>
    obtain ⟨nativeRoot, written, finalMap, finalWorld, rootRep, finalHeaps, maps, worlds, frame, metadata,
      slots, length, typed, agreement⟩ :=
      ProtectedPlaceAssignmentSuccess.preserves_prefix layout ordinary registryExtension transport preservation faithful observations
        rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped installed slot rootTyped trace invalid
    exact .inr ⟨_, _, written, finalMap, finalWorld, slots, trace, finalHeaps, maps, worlds, frame, metadata,
      length, typed, (agreement next outputType).unwrap completed⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentReflection
