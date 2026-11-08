import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceReflection
import Solcore.Frontend.SourceCore.Compatible
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MatchPrefixes

/-!
# Compatible places: write-back and faults

Write-back, target and setter faults, getter and prefix reflection, and continuations.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceFailures
/-! Whole emitted assignments short-circuit on key and RHS faults, retaining
all preceding source effects. The executions of children are obtained from the
universal expression IH; neither phase accepts a child evaluation as its
static compiler contract. Structural missing-default guards are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceFailures
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

theorem keys {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (meaning : Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {index : Nat} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before place.projections reason after)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨target, coreLookup, _⟩ := environments.lookup_visible lookup slot
  have layout : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
    DataPlaceKeyOrder.preserves_fault children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees layout [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) trace
  refine ⟨token, finalStore, finalMap, finalWorld, .target (.projectionExpression lookup read trace), ?_,
    tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
  apply execute_key_failure prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) false invalid token
    (.cellRef (OptionalCell.cellType prepared.route.rootType) target) (.var coreLookup)
  simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

/-- This composition consumes a semantic resolution result, produced by
CompatiblePlaceResolution.preserves, and the independent RHS fault. It derives
the actual RHS run and suppresses modifier, setter, write and continuation. -/
theorem rhs {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {sourceTarget : Dynamic.ResolvedPlace} {coreEnvironment : Environment} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap after : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf sourceTarget
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    (meaning : Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {administrativeContext : Core.Context} {environment : Dynamic.Environment}
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (coreType : lowered.type = prepared.route.leafType)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (resolved : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {index : Nat} (reference : coreEnvironment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context evidence source environment targetHeap id reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after ∧
      Evaluates coreEnvironment initialStore
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends initialMap finalMap ∧ WorldExtends initialWorld finalWorld ∧
      AdministrativePreserved initialMap initialStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, store, mapping, world, result⟩ :=
    CompatiblePlaceRhs.preserves resolution meaning generated found environments locals (.fault failed)
  cases represented : result.represented with
  | @fault _ token tokenRep =>
    refine ⟨token, store, mapping, world, .rhs resolved failed, ?_, tokenRep, result.heaps,
      resolution.maps.trans result.maps, resolution.worlds.trans result.worlds,
      resolution.frame.trans result.frame, resolution.metadata.trans result.metadata⟩
    apply SourceCoreCompatibleDataPlaces.execute_rhs_failure prepared (.var index) (SourceCoreCalls.packArguments codes)
      lowered.expression next outputType (binaryOperator (prepared.route.leafType = .integer) operator) false invalid token
      (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target) (packValues resolution.values)
      (.inRight .unit resolution.snapshot) (.var reference) resolution.keysEvaluated resolution.snapshotEvaluated
    simpa only [coreType, snapshotEnvironment, keysEnvironment, referenceEnvironment] using result.evaluated

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceFailures
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceWriteback
/-! The compatible setter reads the latest optional root, rebuilds its actual
raw carrier, and writes the mapped source cell once. Administrative helper
allocations extend the existing world and preserve the common source heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceWriteback
open Core Frontend SourceInference GeneralHeap DataPatternValues DataEquality
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces CompatibleMapping.MixedPaths

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {prepared : Prepared} {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}
  {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot : Dynamic.Value}

/-- The argument contains a real load. Only the local reference, already
evaluated keys, and replacement use pure selection receipts. -/
theorem setter_at
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    {keys : List Value} {replacementSource updated : Dynamic.Value} {replacement : Value}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (tree : UpdateTree checked registry functions mapping world prepared keys replacementSource replacement
      cell.type sourceRoot rootValue prepared.route.rootType prepared.steps projections updated count)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (observations : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (keyType : Ty) (referenceExpression keyExpression replacementExpression : Expr)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ native after administrative,
      ValueRep checked registry functions mapping world cell.type updated native prepared.route.rootType ∧
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inRight .word native) after ∧ after = store ++ administrative ∧ administrative.length = count := by
  let input := Value.pair optional (.pair (packValues keys) replacement)
  obtain ⟨native, after, administrative, _, related, evaluated, appended, counted⟩ := tree.preserves faithful observations keyLength
    (rootValue :: input :: environment) store prepared.route.rootType
    (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
    (.var rfl) (.first (.second (.var rfl))) (.second (.second (.var rfl)))
  refine ⟨native, after, administrative, related, ?_, appended, counted⟩
  apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) root.nativeRead)
    (.pair (keysSelected.evaluates store) (replacementSelected.evaluates store)))
  cases steps : prepared.steps with
  | nil => exact (nonempty steps).elim
  | cons head tail =>
    simp only [steps] at evaluated ⊢
    exact .caseRight (root.input.normalize _ store (.first (.var 0)) (.first (.var rfl))) evaluated

/-- A successful independent reconstruction and source write derive the
actual setter evaluation and native mapped write. No helper run is assumed. -/
theorem preserves
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {leaf : TypeSystem.Ty}
    {sourceProjections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site cell.type sourceProjections position prepared.steps keySites leaf}
    {keys : List Value} {projections : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path projections)
    {replacementSource updated : Dynamic.Value} {replacement : Value}
    (replacementRep : ValueRep checked registry functions mapping world leaf replacementSource replacement prepared.route.leafType)
    (changed : Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some sourceRoot) projections updated)
    {after : Dynamic.Heap} (written : Dynamic.Heap.Writes heap location (some updated) after)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (observations : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    {environment : Environment} {context : Core.Context} {keyType : Ty}
    {referenceExpression keyExpression replacementExpression : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (setterTyped : HasType context
      (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ native helperStore finalStore futureWorld,
      ValueRep checked registry functions mapping futureWorld cell.type updated native prepared.route.rootType ∧
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inRight .word native) helperStore ∧
      helperStore.read? target = some optional ∧
      helperStore.write? target (.inRight .unit native) = some finalStore ∧
      HeapRepresents checked registry functions mapping futureWorld after finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      Dynamic.HeapMetadataExtend heap after := by
  have tree := arguments.updateTree root.payload replacementRep changed prepared
  obtain ⟨native, helperStore, administrative, related, evaluated, appended, _⟩ :=
    setter_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression replacementExpression
      referenceSelected keysSelected replacementSelected
  obtain ⟨futureWorld, extension, storeTyped, _, frame⟩ :=
    evaluation_frame (mapping := mapping) heaps.runtime_hasTypes environmentTyped setterTyped evaluated appended
  have helperHeaps := CompatibleHeap.HeapRepresents.after_snapshot heaps extension storeTyped appended
  have related := related.extend (.refl _) (.refl _) extension
  obtain ⟨finalStore, nativeWrite, finalHeaps, writeFrame⟩ :=
    helperHeaps.write_initialized (root.reference.extend (.refl _) extension) root.sourceRead related written
  have nativeRead : helperStore.read? target = some optional := by
    rw [appended]
    simpa [Store.read?, List.getElem?_append_left (heaps.target_lt root.reference.mapped)] using root.nativeRead
  exact ⟨native, helperStore, finalStore, futureWorld, related, evaluated, nativeRead, nativeWrite,
    finalHeaps, extension, frame.trans writeFrame, Dynamic.HeapMetadataExtend.of_write written⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceWriteback
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceAssignmentSuccess
/-! Whole successful compatible assignment, including effectful keys and RHS,
old snapshot, latest-root reconstruction and mapped write. The static layout
contains no child/helper execution. Bare-root assignment and the whole
statement compiler's receipt extraction are separate boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceAssignmentSuccess
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

structure Layout (compilation : SourceCoreCompatibleDataPlaces.Context) (source : TypedSource)
    (certificate : Certificate) (scope : Scope) (site : SourceCoreElaboration.ErrorSite)
    (place : PlaceResolution) (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr)
    (sourceTypes : List TypeSystem.Ty) (leaf : TypeSystem.Ty) (administrativeContext : Core.Context)
    (rhsType : Core.Ty := prepared.route.leafType)
    (definitions : DataEnvironment := compilation.checked.catalog.definitions) : Prop where
  path : PreparedPath compilation.checked source site prepared.route.rootSourceType place.projections
    0 prepared.steps prepared.keys leaf
  views : KeyViews path sourceTypes
  children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes
  keyTypes : prepared.keyTypes = codes.map (·.type)
  leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType
  virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
    CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value
  nonempty : prepared.steps ≠ []
  getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
    (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
    (LanguageResult.resultType prepared.optionalLeaf) definitions
  setterTyped : HasType
    (prepared.route.leafType :: rhsType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
      OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
    (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
    (LanguageResult.resultType prepared.route.rootType) definitions

private theorem resolved_nonempty {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {sources : List Dynamic.Value} {resolved : List Dynamic.EvaluatedProjection}
    (shaped : DataPlaceKeyOrder.Values projections sources resolved) (nonempty : steps ≠ []) : resolved ≠ [] := by
  have lengths : steps.length = resolved.length := by
    clear nonempty
    induction path generalizing sources resolved with
    | nil => cases shaped; rfl
    | member _ _ _ _ ih => cases shaped with | member tail => exact congrArg Nat.succ (ih tail)
    | index _ _ _ ih => cases shaped with | index tail => exact congrArg Nat.succ (ih tail)
  intro empty
  rw [empty, List.length_nil] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero lengths)

private theorem none_update {modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate modify none projections updated) : projections = [] := by
  cases changed
  rfl

/-- An independent successful transaction constructs every native phase.
Raw metadata and duplicate entries are retained by the full payload relation;
the native store additionally contains tracked administrative helper cells. -/
theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression (LanguageResult.success .unit) .unit
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inRight .word .unit) finalStore ∧
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases trace with
  | @intro _ _ _ _ _ _ targetHeap rhsHeap _ _ sourceTarget _ right _ resolve evaluate written =>
    obtain ⟨resolution, coreLookup⟩ := CompatiblePlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
      environments heaps locals slot rootTyped resolve
    obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
      CompatiblePlaceRhs.preserves resolution meaning rhsGenerated found environments locals (.value evaluate)
    cases represented : rhsResult.represented with
    | @value _ rightValue rightRep =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCoreType] using rightRep)
      have snapshotRep := rhsResult.saved_snapshot
      have keyRep := resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
      have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
      have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
      obtain ⟨latest⟩ := rhsResult.latest
      cases written with
      | @intro _ _ cell initial _ sourceRead _ initialValue update sourceWrite =>
        have cellEq := sourceRead.functional latest.read
        have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
        obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
        rw [resolution.selectedEq] at applies
        obtain ⟨replacementValue, replacementRep, modifiedEvaluated, _⟩ :=
          CompatiblePlaceModifier.preserves observations operatorProfile snapshotRep rightRep applies
            (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
            (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
        have present : ∃ sourceRoot, initial = some sourceRoot := by
          cases initial with
          | some value => exact ⟨value, rfl⟩
          | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_update changed)).elim
        obtain ⟨sourceRoot, rfl⟩ := present
        have rootExists : ∃ optional rootValue,
            RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
              cell optional sourceRoot rootValue := by
          cases initialValue with
          | initialized =>
            obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root rhsResult.heaps reference sourceRead
            exact ⟨_, value, root⟩
          | emptyMapping key value =>
            obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root rhsResult.heaps reference sourceRead
              (layout.virtual key value cellType.symm) registryExtension
            exact ⟨_, native, root⟩
        obtain ⟨optional, rootValue, root⟩ := rootExists
        have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
        have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
            (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
            (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
              OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
            ambient.definitions :=
          .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
            (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
              ((environments.extend (resolution.maps.trans rhsResult.maps) (resolution.worlds.trans rhsResult.worlds)).runtime_hasTypes)))))
        have currentPath : PreparedPath compilation.checked source site cell.type place.projections
            0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
        have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
            currentPath sourceTarget.projections := by simpa only [cellType] using arguments
        obtain ⟨updatedValue, helperStore, finalStore, finalWorld, updatedRep, setterEvaluated,
          helperRead, coreWritten, finalHeaps, extension, frame, metadata⟩ :=
          CompatiblePlaceWriteback.preserves root rhsResult.heaps currentArguments replacementRep changed sourceWrite layout.nonempty
            faithful observations keyLength typedEnvironment layout.setterTyped (.var rfl) (.var rfl) (.var rfl)
        refine ⟨updatedValue, finalStore, rhsMap, finalWorld, ?_,
          by simpa only [cellType] using updatedRep, finalHeaps, resolution.maps.trans rhsResult.maps,
          (resolution.worlds.trans rhsResult.worlds).trans extension, (resolution.frame.trans rhsResult.frame).trans frame,
          (resolution.metadata.trans rhsResult.metadata).trans metadata⟩
        exact .letE (.var coreLookup)
          (LanguageResult.bind_success _ resolution.keysEvaluated
            (LanguageResult.bind_success _ resolution.snapshotEvaluated
              (LanguageResult.bind_success _ rhsResult.evaluated
                (LanguageResult.bind_success _ modifiedEvaluated
                  (LanguageResult.bind_success _ setterEvaluated
                    (.letE (.storeCell (.var rfl) helperRead (.inRight (.var rfl)) coreWritten)
                      (by simpa only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success, writtenEnvironment, modifiedEnvironment, rhsEnvironment,
                        snapshotEnvironment, keysEnvironment, referenceEnvironment] using
                        (Evaluates.inRight (environment := writtenEnvironment prepared.route.rootType resolution.target
                          (packValues resolution.values) (.inRight .unit resolution.snapshot) rightValue replacementValue updatedValue coreEnvironment)
                          (initialStore := finalStore) (leftType := .word) Evaluates.unit))))))))

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceAssignmentSuccess
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTargetFaults
/-! Target-resolution faults before the RHS. The actual key runs are derived
from the universal expression theorem. The getter uses the live root after
those effects, preserving exact raw missing-default tokens and administrative
allocations. An absent ordinary root fails without allocating a helper. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTargetFaults
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {administrativeContext : Core.Context}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
  {before after : Dynamic.Heap} {store : Store} {index : Nat}
  {location : Dynamic.Location} {initialCell currentCell : Dynamic.Cell}
  {resolved : List Dynamic.EvaluatedProjection}

/-- Independent structural failure determines the actual whole emitted
assignment's failure before its RHS, modifier, setter or continuation starts. -/
theorem projection
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (fault : Dynamic.ProjectionsFaults initial resolved reason)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨keys⟩ := CompatiblePlaceTargetKeys.preserves layout.children meaning environments heaps locals slot rootTyped lookup initialRead trace
  have cellEq := currentRead.functional keys.read
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have present : ∃ sourceRoot, initial = some sourceRoot := by
    cases initial with
    | some value => exact ⟨value, rfl⟩
    | none => cases fault
  obtain ⟨sourceRoot, rfl⟩ := present
  have rootExists : ∃ optional rootValue,
      RootRead compilation.checked registry functions keys.keyMap keys.keyWorld prepared after keys.keyStore location keys.target
        currentCell optional sourceRoot rootValue := by
    cases initialValue with
    | initialized =>
      obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root keys.heaps keys.reference currentRead
      exact ⟨_, value, root⟩
    | emptyMapping key value =>
      obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root keys.heaps keys.reference currentRead
        (layout.virtual key value cellType.symm) registryExtension
      exact ⟨_, native, root⟩
  obtain ⟨optional, rootValue, root⟩ := rootExists
  have arguments := layout.views.arguments keys.shaped keys.related (fun _ _ found => by simpa only [Nat.zero_add] using found)
  have currentPath : PreparedPath compilation.checked source site currentCell.type place.projections
      0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
  have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld source site keys.values
      currentPath resolved := by simpa only [cellType] using arguments
  obtain ⟨token, count, receipt, tree⟩ := currentArguments.faultTree root.payload fault prepared
  have keyLength : prepared.keyTypes.length = keys.values.length := layout.keyTypes ▸ keys.related.length.2
  obtain ⟨finalStore, administrative, _, _, evaluated, appended, _⟩ :=
    faultTree_at root tree layout.nonempty faithful observations keyLength
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
  have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) ambient.definitions :=
    .cons (CompatiblePlaceResolution.values_typed keys.related)
      (.cons (.cellRef keys.reference.typed) ((environments.extend keys.maps keys.worlds).runtime_hasTypes))
  obtain ⟨finalWorld, extension, typedStore, _, frame⟩ :=
    evaluation_frame (mapping := keys.keyMap) keys.heaps.runtime_hasTypes typedEnvironment layout.getterTyped evaluated appended
  refine ⟨token, count, sourceRoot, finalStore, keys.keyMap, finalWorld,
    .target (.projectionRead lookup initialRead trace currentRead initialValue fault), initialValue, receipt, ?_,
    CompatibleHeap.HeapRepresents.after_snapshot keys.heaps extension typedStore appended,
    keys.maps, keys.worlds.trans extension, keys.frame.trans frame, keys.metadata⟩
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

/-- Actual describe supplies `ordinary`. It is a static route fact, not a
claim that native type equality recovers the source declaration. -/
theorem uninitialized
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨keys⟩ := CompatiblePlaceTargetKeys.preserves layout.children meaning environments heaps locals slot rootTyped lookup initialRead trace
  have cellEq := currentRead.functional keys.read
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have noVirtual : prepared.route.rootMapping = none := ordinary (fun key value same => notMapping ⟨key, value, cellType.trans same⟩)
  obtain ⟨optional, native, represented⟩ := CompatibleHeap.HeapRepresents.read_at keys.heaps keys.reference currentRead
  have absent : optional = .inLeft prepared.route.rootType .unit := by
    cases represented with
    | uninitialized => rfl
    | initialized => cases empty
  rw [absent] at native
  have evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      keys.keyStore (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) keys.keyStore := by
    apply Evaluates.apply .lambda (.pair (.loadCell (.var rfl) native) (.var rfl))
    cases steps : prepared.steps with
    | nil => exact (layout.nonempty steps).elim
    | cons head tail =>
      simp only [normalizeRoot, noVirtual, LanguageResult.failure]
      exact .caseLeft (.first (.var rfl)) (.inLeft .word)
  refine ⟨keys.keyStore, keys.keyMap, keys.keyWorld,
    .target (.uninitialized lookup initialRead trace currentRead empty notMapping hasProjection), ?_,
    keys.heaps, keys.maps, keys.worlds, keys.frame, keys.metadata⟩
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTargetFaults
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSetterFault
/-! A structural source fault in the latest root derives a failed actual setter
load. The raw key guard and missing-default metadata come from the independent
fault trace. Administrative comparisons may allocate; no source cell is written.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSetterFault
open Core Frontend SourceInference GeneralHeap DataPatternValues DataEquality
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces CompatibleMapping.MixedPaths

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {prepared : Prepared} {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}
  {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot : Dynamic.Value}

/-- Actual load plus the generated structural recursion. Replacement is only
an already evaluated value; a fault never executes an insertion or root write. -/
theorem setter_at
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    {keys : List Value} {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
    (tree : FaultTree checked registry functions mapping world prepared keys sourceRoot rootValue prepared.route.rootType
      prepared.steps projections reason token count)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (observations : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (keyType : Ty) (referenceExpression keyExpression replacementExpression : Expr) (replacement : Value)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ after administrative,
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inLeft prepared.route.rootType (.word token)) after ∧
      after = store ++ administrative ∧ administrative.length = count := by
  let input := Value.pair optional (.pair (packValues keys) replacement)
  obtain ⟨after, administrative, _, _, evaluated, appended, counted⟩ := tree.preserves faithful observations keyLength
    (rootValue :: input :: environment) store (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
    (.var rfl) (.first (.second (.var rfl)))
  refine ⟨after, administrative, ?_, appended, counted⟩
  apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) root.nativeRead)
    (.pair (keysSelected.evaluates store) (replacementSelected.evaluates store)))
  cases steps : prepared.steps with
  | nil => exact (nonempty steps).elim
  | cons head tail =>
    simp only [steps] at evaluated ⊢
    exact .caseRight (root.input.normalize _ store (.first (.var 0)) (.first (.var rfl))) evaluated

/-- The source fault automatically supplies the exact token and fault tree.
Finite Core preservation and the real administrative suffix transport the
common heap; the latest source and native root remain unchanged. -/
theorem preserves
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {leaf : TypeSystem.Ty}
    {sourceProjections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site cell.type sourceProjections position prepared.steps keySites leaf}
    {keys : List Value} {projections : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path projections)
    {reason : Dynamic.SemanticFault} (fault : Dynamic.ProjectionsFaults (some sourceRoot) projections reason)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (observations : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {replacement : Value}
    {referenceExpression keyExpression replacementExpression : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (setterTyped : HasType context
      (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ token count after administrative futureWorld,
      FaultToken checked registry sourceRoot prepared.steps projections reason token count ∧
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inLeft prepared.route.rootType (.word token)) after ∧
      HeapRepresents checked registry functions mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧
      RootRead checked registry functions mapping futureWorld prepared heap after location target cell optional sourceRoot rootValue ∧
      after = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree root.payload fault prepared
  obtain ⟨after, administrative, evaluated, appended, counted⟩ :=
    setter_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression replacementExpression replacement
      referenceSelected keysSelected replacementSelected
  obtain ⟨futureWorld, extension, typedStore, _, frame⟩ := evaluation_frame heaps.runtime_hasTypes environmentTyped setterTyped evaluated appended
  exact ⟨token, count, after, administrative, futureWorld, receipt, evaluated,
    CompatibleHeap.HeapRepresents.after_snapshot heaps extension typedStore appended, extension, frame,
    by rw [appended]; exact root.after_append extension, appended, counted⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSetterFault
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceStructuralFault
/-! Structural missing-default failure after the RHS. The source specification
traverses the latest root before applying the modifier. For authenticated equal
or scalar numeric operands, the generated earlier modifier is total; therefore
the same structural fault wins and neither source nor native final write runs.
Exact raw key guards come from the source fault, not native projection equality.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceStructuralFault
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

/-- All key/RHS native evaluations come from their universal IH. The fault
receipt retains the raw mapping header and ordered selection where traversal
stopped; no decoder or source evaluator supplies the semantic result. -/
theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    (evaluate : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (rootType : cell.type = sourceTarget.rootType)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (fault : Dynamic.ProjectionsFaults initial sourceTarget.projections reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap ∧
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps sourceTarget.projections reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap := by
  have sourceFault := Dynamic.SourcePlaceAssignmentFaults.structuralUpdate (operator := operator) resolve evaluate sourceRead rootType initialValue fault
  obtain ⟨resolution, coreLookup⟩ := CompatiblePlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
    layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
    environments heaps locals slot rootTyped resolve
  obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
    CompatiblePlaceRhs.preserves resolution meaning rhsGenerated found environments locals (.value evaluate)
  cases represented : rhsResult.represented with
  | @value _ rightValue rightRep =>
    have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
      .compatible rhsView (by simpa only [payloadModel, rhsCoreType] using rightRep)
    have snapshotRep := rhsResult.saved_snapshot
    have keyRep := resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
    have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
    have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
    obtain ⟨latest⟩ := rhsResult.latest
    have cellEq := sourceRead.functional latest.read
    have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
    obtain ⟨replacement, replacementValue, replacementRep, _, modifiedEvaluated, valid⟩ :=
      CompatiblePlaceModifier.initialized_success observations operatorProfile snapshotRep rightRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => cases fault
    obtain ⟨sourceRoot, rfl⟩ := present
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
          cell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root rhsResult.heaps reference sourceRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root rhsResult.heaps reference sourceRead
          (layout.virtual key value cellType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
        (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          ((environments.extend (resolution.maps.trans rhsResult.maps) (resolution.worlds.trans rhsResult.worlds)).runtime_hasTypes)))))
    have currentPath : PreparedPath compilation.checked source site cell.type place.projections
        0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
        currentPath sourceTarget.projections := by simpa only [cellType] using arguments
    obtain ⟨token, count, finalStore, administrative, finalWorld, receipt, setterEvaluated,
      finalHeaps, extension, frame, _, _, _⟩ :=
      CompatiblePlaceSetterFault.preserves root rhsResult.heaps currentArguments fault layout.nonempty
        faithful observations keyLength typedEnvironment layout.setterTyped (.var rfl) (.var rfl) (.var rfl)
    refine ⟨token, count, sourceRoot, finalStore, rhsMap, finalWorld, sourceFault, initialValue, receipt, ?_, finalHeaps,
      resolution.maps.trans rhsResult.maps, (resolution.worlds.trans rhsResult.worlds).trans extension,
      (resolution.frame.trans rhsResult.frame).trans frame, resolution.metadata.trans rhsResult.metadata⟩
    exact .letE (.var coreLookup)
      (LanguageResult.bind_success _ resolution.keysEvaluated
        (LanguageResult.bind_success _ resolution.snapshotEvaluated
          (LanguageResult.bind_success _ rhsResult.evaluated
            (LanguageResult.bind_success _ modifiedEvaluated
              (LanguageResult.bind_failure _ setterEvaluated)))))

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceStructuralFault
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceGetterReflection
/-! Every actual completed live compatible getter has an independent source
read, exact raw missing-default fault, or absent-root fault. The source outcome
is constructed from static path/authentication receipts and the common heap;
no source projection trace or helper execution is supplied by the caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceGetterReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open CompatibleMapping CompatibleMapping.MixedPaths SourceCoreCompatibleDataPlaces

inductive ResultRep (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (prepared : Prepared) (cell : Dynamic.Cell) (resolved : List Dynamic.EvaluatedProjection)
    (leaf : TypeSystem.Ty) : Value → Prop where
  | read {sourceRoot selected : Dynamic.Value} {native : Value}
      (initial : Dynamic.RootInitialValue cell (some sourceRoot))
      (selection : Dynamic.ProjectionsRead (some sourceRoot) resolved (some selected))
      (represented : ValueRep checked registry functions mapping world leaf selected native prepared.route.leafType) :
      ResultRep checked registry functions mapping world prepared cell resolved leaf (.inRight .word (.inRight .unit native))
  | missing {sourceRoot : Dynamic.Value} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
      (initial : Dynamic.RootInitialValue cell (some sourceRoot))
      (fault : Dynamic.ProjectionsFaults (some sourceRoot) resolved reason)
      (receipt : FaultToken checked registry sourceRoot prepared.steps resolved reason token count) :
      ResultRep checked registry functions mapping world prepared cell resolved leaf (.inLeft prepared.optionalLeaf (.word token))
  | uninitialized
      (empty : cell.value = none)
      (ordinary : ¬ ∃ key value, cell.type = .mapping key value)
      (nonempty : resolved ≠ []) :
      ResultRep checked registry functions mapping world prepared cell resolved leaf (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection))

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {prepared : Prepared}
  {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell}
  {projections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
  {path : PreparedPath compilation.checked source site cell.type projections position prepared.steps keySites leaf}
  {keys : List Value} {resolved : List Dynamic.EvaluatedProjection}
  {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression : Expr}
  {identities : Dynamic.Value → Word → Prop}

private theorem present_evaluates
    {optional rootValue : Value} {sourceRoot : Dynamic.Value}
    (root : RootRead compilation.checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys)) :
    ∃ result after futureWorld administrative,
      Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression)) result after ∧
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved leaf result ∧
      HeapRepresents compilation.checked registry functions mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  rcases CompatiblePlaceReadTotality.read_or_fault arguments functionTypes root.payload leafProjected with
      ⟨selected, _, read, _⟩ | ⟨reason, fault⟩
  · have tree := arguments.readTree root.payload leafProjected read prepared
    obtain ⟨native, after, administrative, initial, _, represented, evaluated, appended, _⟩ :=
      readTree_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression referenceSelected keysSelected
    obtain ⟨futureWorld, extension, typedStore, _, frame⟩ :=
      evaluation_frame (mapping := mapping) heaps.runtime_hasTypes environmentTyped helperTyped evaluated appended
    exact ⟨_, after, futureWorld, administrative, evaluated,
      .read initial read (represented.extend (.refl _) (.refl _) extension),
      CompatibleHeap.HeapRepresents.after_snapshot heaps extension typedStore appended, extension, frame, appended⟩
  · obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree root.payload fault prepared
    obtain ⟨after, administrative, initial, _, evaluated, appended, _⟩ :=
      faultTree_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression referenceSelected keysSelected
    obtain ⟨futureWorld, extension, typedStore, _, frame⟩ :=
      evaluation_frame (mapping := mapping) heaps.runtime_hasTypes environmentTyped helperTyped evaluated appended
    exact ⟨_, after, futureWorld, administrative, evaluated, .missing initial fault receipt,
      CompatibleHeap.HeapRepresents.after_snapshot heaps extension typedStore appended, extension, frame, appended⟩

private theorem resolved_nonempty
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (nonempty : prepared.steps ≠ []) : resolved ≠ [] := by
  have general : ∀ {root leaf projections position steps sites}
      {path : PreparedPath compilation.checked source site root projections position steps sites leaf} {resolved},
      Arguments compilation.checked registry functions mapping world source site keys path resolved → steps.length = resolved.length := by
    intro root leaf projections position steps sites path resolved arguments
    induction arguments with
    | nil => rfl
    | member _ ih | index _ _ _ ih => exact congrArg Nat.succ ih
  have length := general arguments
  intro empty
  rw [empty, List.length_nil] at length
  exact nonempty (List.eq_nil_of_length_eq_zero length)

/-- Construct finite execution of the real live getter, including its source
classification and any administrative suffix, from authenticated live inputs. -/
theorem evaluates
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, cell.type = .mapping key value → VirtualRoot.Generated compilation prepared.route key value)
    (ordinary : (∀ key value, cell.type ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys)) :
    ∃ result after futureWorld administrative,
      Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression)) result after ∧
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved leaf result ∧
      HeapRepresents compilation.checked registry functions mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  obtain ⟨optional, native, represented⟩ := CompatibleHeap.HeapRepresents.read_at heaps reference read
  cases represented with
  | initialized related =>
    exact present_evaluates (.initialized read reference native related) arguments leafProjected nonempty functionTypes
      faithful observations keyLength heaps environmentTyped helperTyped referenceSelected keysSelected
  | @uninitialized sourceType payload projected =>
    by_cases mappingRoot : ∃ key value, sourceType = .mapping key value
    · obtain ⟨key, value, rfl⟩ := mappingRoot
      obtain ⟨rootValue, root⟩ := RootRead.virtual (virtual key value rfl) registryExtension projected read reference native
      exact present_evaluates root arguments leafProjected nonempty functionTypes faithful observations keyLength
        heaps environmentTyped helperTyped referenceSelected keysSelected
    · have noVirtual := ordinary (fun key value same => mappingRoot ⟨key, value, same⟩)
      have evaluated : Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
          (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) store := by
        apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) native) (keysSelected.evaluates store))
        cases steps : prepared.steps with
        | nil => exact (nonempty steps).elim
        | cons head tail =>
          simp only [normalizeRoot, noVirtual, LanguageResult.failure]
          exact .caseLeft (.first (.var rfl)) (.inLeft .word)
      exact ⟨_, store, world, [], evaluated, .uninitialized rfl mappingRoot (resolved_nonempty arguments nonempty),
        heaps, .refl _, .refl _ _, by simp⟩

/-- Actual completed native execution determines an independent source
outcome without a prior source trace or a helper-execution certificate. -/
theorem reflects
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, cell.type = .mapping key value → VirtualRoot.Generated compilation prepared.route key value)
    (ordinary : (∀ key value, cell.type ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys))
    {result : Value} {after : Store}
    (completed : Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression)) result after) :
    ∃ futureWorld administrative,
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved leaf result ∧
      HeapRepresents compilation.checked registry functions mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  obtain ⟨actual, actualStore, futureWorld, administrative, evaluated, resultRep, heaps, worlds, frame, appended⟩ :=
    evaluates arguments leafProjected virtual ordinary registryExtension nonempty functionTypes faithful observations keyLength
      heaps reference read environmentTyped helperTyped referenceSelected keysSelected
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
  exact ⟨futureWorld, administrative, resultRep, heaps, worlds, frame, appended⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceGetterReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlacePrefixReflection
/-! Reflection of the actual reference, key and snapshot prefix. Universal
child reflection supplies source key traces; authenticated getter reflection
then supplies the independent target result. The real RHS continuation is an
output witness under its three hidden slots, never a static premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlacePrefixReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution

def remainder (prepared : Prepared) (keyType : Ty) (rhs next : Expr) (outputType : Ty)
    (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word) : Expr :=
  LanguageResult.bind outputType (shift 3 rhs)
    (LanguageResult.bind outputType
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalid)
      (LanguageResult.bind outputType
        (.apply (setter prepared keyType) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
        (.letE (.storeCell (.var 5) (.inRight .unit (.var 0))) (shift 7 next))))

inductive Result (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (leaf : TypeSystem.Ty) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs next : Expr) (outputType : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word)
    (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : Dynamic.SourcePlaceFaults program context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore
  | resolved {target : Dynamic.ResolvedPlace} {after : Dynamic.Heap}
      (sourceTrace : Dynamic.SourcePlaceResolves program context evidence source environment before place target after)
      (execution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
        coreEnvironment store mapping world before after)
      (continuation : Evaluates (snapshotEnvironment prepared.route.rootType execution.target (packValues execution.values)
        (.inRight .unit execution.snapshot) coreEnvironment) execution.store
        (remainder prepared (SourceCoreCalls.packArguments codes).type rhs next outputType operator bitNot invalid) result finalStore) :
      Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
        coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore

/-- The diagnostic premises are static interpretations of emitted tokens.
They do not supply any source or native execution. All target source traces
are reconstructed from a completed emitted assignment and universal child IH. -/
theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context} {rhsType : Core.Ty}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext rhsType)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType operator bitNot invalid) result finalStore) :
    Result compilation.checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
      coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore := by
  obtain ⟨scheme, staticLookup, _, _, _⟩ := rootTyped.scheme
  obtain ⟨location, initialCell, lookup, initialRead, _, _⟩ := locals.lookup staticLookup
  have keyPhase := CompatiblePlaceKeyReflection.reflects layout.children meaning environments heaps locals slot rootTyped lookup initialRead completed
  cases keyPhase with
  | fault sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata =>
    exact .fault sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata
  | @keys sourceLocation resolved after keyLookup sourceTrace keys continuation =>
    have locationEq := lookup.functional keyLookup
    subst sourceLocation
    have arguments := layout.views.arguments keys.shaped keys.related (fun _ _ found => by simpa only [Nat.zero_add] using found)
    have currentPath : PreparedPath compilation.checked source site keys.cell.type place.projections 0 prepared.steps prepared.keys leaf := keys.type ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld source site keys.values currentPath resolved := by
      simpa only [keys.type] using arguments
    have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
        (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) ambient.definitions :=
      .cons (CompatiblePlaceResolution.values_typed keys.related)
        (.cons (.cellRef keys.reference.typed) ((environments.extend keys.maps keys.worlds).runtime_hasTypes))
    have reflectGetter := fun {value : Value} {afterStore : Store}
        (evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment) keys.keyStore
          (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0))) value afterStore) =>
      CompatiblePlaceGetterReflection.reflects currentArguments layout.leafProjected
        (fun k v same => layout.virtual k v (keys.type.symm.trans same))
        (fun nonmapping => ordinary (fun k v same => nonmapping k v (keys.type.trans same)))
        registryExtension layout.nonempty functionTypes faithful observations (layout.keyTypes ▸ keys.related.length.2)
        keys.heaps keys.reference keys.read typedEnvironment layout.getterTyped (.var rfl) (.var rfl) evaluated
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
            snapshotEvaluated := getterEvaluated
            keysRelated := keys.related.extend (.refl _) extension
            snapshotRelated := represented
            heaps := finalHeaps
            maps := keys.maps
            worlds := keys.worlds.trans extension
            frame := keys.frame.trans frame
            metadata := keys.metadata } remaining

end Solcore.SourceSemantics.CoreLowering.CompatiblePlacePrefixReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceHelperTyping
/-! Getter typing comes from the real enclosing Core checker. Finite-well-
formed catalog definitions alone do not authenticate nominal row completeness.
No runtime evaluation premise is used in this extraction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceHelperTyping
open Core Frontend SourceCoreCompatibleDataPlaces

theorem getter_of_execute {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType resultType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    (typed : HasType context (execute prepared reference keys rhs next outputType operator bitNot invalid)
      resultType definitions) :
    HasType (keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) definitions := by
  unfold execute LanguageResult.bind at typed
  cases typed with
  | letE reference body =>
    cases body with
    | caseE keys failure success =>
      cases success with
      | caseE snapshot failure success =>
        cases snapshot with
        | apply function argument =>
          cases function with
          | lambda parameterTyped resultTyped body =>
            cases argument with
            | pair referenceArgument keyArgument =>
              cases referenceArgument with
              | loadCell referenceTyped =>
                cases referenceTyped with
                | var referenceAt =>
                  cases keyArgument with
                  | var keyAt =>
                    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at referenceAt keyAt
                    subst_vars
                    exact .apply (.lambda parameterTyped resultTyped body) (.pair (.loadCell (.var rfl)) (.var rfl))

/-- Direct consumer of an actual successful whole-expression inference. -/
theorem getter_of_infer {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType resultType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    (accepted : infer? context (execute prepared reference keys rhs next outputType operator bitNot invalid)
      definitions = some resultType) :
    HasType (keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) definitions :=
  getter_of_execute (infer_sound accepted)

/-- The retained child typing fixes the otherwise unused RHS slot. This is a
static compiler obligation and does not assume any child evaluation. -/
theorem setter_of_execute_rhs {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType resultType rhsType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    (typed : HasType context (execute prepared reference keys rhs next outputType operator bitNot invalid)
      resultType definitions)
    (rhsTyped : HasType (prepared.optionalLeaf :: keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (shift 3 rhs) (LanguageResult.resultType rhsType) definitions) :
    HasType (prepared.route.leafType :: rhsType :: prepared.optionalLeaf :: keys.type ::
        OptionalCell.referenceType prepared.route.rootType :: context)
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) definitions := by
  unfold execute LanguageResult.bind at typed
  cases typed with
  | letE reference body =>
    cases body with
    | caseE keys failure success =>
      cases success with
      | caseE snapshot failure success =>
        cases snapshot with
        | apply function argument =>
          cases function with
          | lambda parameterTyped resultTyped body =>
            cases argument with
            | pair referenceArgument keyArgument =>
              cases referenceArgument with
              | loadCell referenceTyped =>
                cases referenceTyped with
                | var referenceAt =>
                  cases keyArgument with
                  | var keyAt =>
                    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at referenceAt keyAt
                    subst_vars
                    cases success with
                    | caseE right failure success =>
                      have same := typing_deterministic right rhsTyped
                      cases same
                      cases success with
                      | caseE modified failure success =>
                        cases success with
                        | caseE written failure success =>
                          cases written with
                          | apply function argument =>
                            cases function with
                            | lambda parameterTyped resultTyped body =>
                              cases argument with
                              | pair referenceArgument rest =>
                                cases rest with
                                | pair keys replacement =>
                                  cases replacement with
                                  | var replacementAt =>
                                    simp only [List.getElem?_cons_zero, Option.some.injEq] at replacementAt
                                    subst_vars
                                    exact .apply (.lambda parameterTyped resultTyped body) (.pair referenceArgument (.pair keys (.var rfl)))

theorem setter_of_execute {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType resultType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    (typed : HasType context (execute prepared reference keys rhs next outputType operator bitNot invalid)
      resultType definitions)
    (rhsTyped : HasType (prepared.optionalLeaf :: keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (shift 3 rhs) (LanguageResult.resultType prepared.route.leafType) definitions) :
    HasType (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: keys.type ::
        OptionalCell.referenceType prepared.route.rootType :: context)
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) definitions :=
  setter_of_execute_rhs typed rhsTyped

/-- Ordinary child typing yields the exact three administrative slots used by
execute. This is syntactic weakening only; store values are never compared. -/
theorem rhs_shift_typed_rhs {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {rhsType : Ty} {keys : SourceCoreBasic.LoweredExpr} {rhs : Expr}
    (typed : HasType context rhs (LanguageResult.resultType rhsType) definitions) :
    HasType (prepared.optionalLeaf :: keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (shift 3 rhs) (LanguageResult.resultType rhsType) definitions := by
  simpa only [shift, List.range, List.range.loop, List.foldl, Core.Context.insertAt] using
    (((typed.weakenAt (inserted := OptionalCell.referenceType prepared.route.rootType) 0).weakenAt (inserted := keys.type) 0).weakenAt
      (inserted := prepared.optionalLeaf) 0)
theorem rhs_shift_typed {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {keys : SourceCoreBasic.LoweredExpr} {rhs : Expr}
    (typed : HasType context rhs (LanguageResult.resultType prepared.route.leafType) definitions) :
    HasType (prepared.optionalLeaf :: keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (shift 3 rhs) (LanguageResult.resultType prepared.route.leafType) definitions :=
  rhs_shift_typed_rhs typed

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceHelperTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceConcretePreparation
/-! Real catalog preparation and actual place description supply the concrete
route gate used by the missing-default inventory. The authentic root binder
is selected by the original declared-binder lookup. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceConcretePreparation
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatibleCatalogRegistrationPrefix

/-- Successful description in an actually closed catalog proves the exact
concrete gate for its Source assignment and declared root binder. -/
theorem describe_concrete {context : SourceCoreCompatibleDataPlaces.Context} (closed : ClosedSources context.checked.catalog)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {route : Route}
    (described : describe context context.checked.signatures source site assignment = .ok route) :
    (SourceCoreDataCatalog.closed assignment.target.type &&
      ((SourceCoreDataPlaces.declaredBinders source).filter (fun binder =>
        decide (binder.id = assignment.target.root))).any (fun binder => SourceCoreDataCatalog.closed binder.scheme.body)) = true := by
  obtain ⟨binder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
  have binding : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder := description.binding
  have filtered := CompatibleMatchArmScopes.rootBinder_filter binding
  have targetClosed := CompatibleCatalogClosedSources.project_closed closed description.leafProjected
  have rootClosed := CompatibleCatalogClosedSources.project_closed closed description.rootProjected
  rw [targetClosed, filtered]
  simp only [List.any_cons, List.any_nil, rootClosed, Bool.true_or, Bool.true_and]

/-- The actual catalog factory discharges Source closure before the real
place description discharges the concrete inventory gate. -/
theorem describe_concrete_of_prepare {context : SourceCoreCompatibleDataPlaces.Context}
    {signatures : ProgramSignatures} {fuel : Nat} {types : List TypeSystem.Ty}
    {metadata : List SourceCoreRawMetadata.Metadata} {limits : SourceCoreRawMetadata.Limits} {profile : Bool}
    (prepared : SourceCoreCompatibleCatalog.prepare signatures fuel types metadata limits profile = .ok context.checked)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {route : Route}
    (described : describe context context.checked.signatures source site assignment = .ok route) :
    (SourceCoreDataCatalog.closed assignment.target.type &&
      ((SourceCoreDataPlaces.declaredBinders source).filter (fun binder =>
        decide (binder.id = assignment.target.root))).any (fun binder => SourceCoreDataCatalog.closed binder.scheme.body)) = true :=
  describe_concrete (CompatibleCatalogClosedSources.prepare_closed prepared) described

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceConcretePreparation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceContinuation
/-! A completed assignment prefix can be followed by a universally certified
expression under execute's seven real administrative values. Closure captures
use that actual extended environment; no exact-value weakening is assumed.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceContinuation
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues CompatiblePayload CompatibleEquality CompatibleHeap
open GenericExpressionMeaning SourceCoreCompatibleDataPlaces

/-- Successful terminal Unit exposes the actual seven values and admits an
arbitrary continuation at the resulting store. All prefix evaluations are
reused exactly once, including the latest-root load and final write. -/
theorem plug {prepared : Prepared} {reference rhs : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    {environment : Environment} {before after : Store}
    (completed : Evaluates environment before
      (execute prepared reference keys rhs (LanguageResult.success .unit) .unit operator bitNot invalid)
      (.inRight .word .unit) after) :
    ∃ slots : Environment, slots.length = 7 ∧
      ∀ {next : Expr} {outputType : Ty} {value : Value} {finalStore : Store},
        Evaluates (slots ++ environment) after (shift 7 next) value finalStore →
        Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalid) value finalStore := by
  cases completed with
  | letE referenceEvaluated tail =>
    rename_i referenceStore referenceValue
    cases tail with
    | caseLeft _ impossible => cases impossible
    | caseRight keysEvaluated tail =>
      rename_i keyStore keyType keyValue
      cases tail with
      | caseLeft _ impossible => cases impossible
      | caseRight snapshotEvaluated tail =>
        rename_i snapshotStore snapshotType snapshotValue
        cases tail with
        | caseLeft _ impossible => cases impossible
        | caseRight rhsEvaluated tail =>
          rename_i rhsStore rhsType rightValue
          cases tail with
          | caseLeft _ impossible => cases impossible
          | caseRight modifiedEvaluated tail =>
            rename_i modifiedStore modifiedType modifiedValue
            cases tail with
            | caseLeft _ impossible => cases impossible
            | caseRight setterEvaluated tail =>
              rename_i setterStore setterType updatedValue
              cases tail with
              | letE writeEvaluated terminal =>
                rename_i writtenStore writtenValue
                simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] at terminal
                cases terminal with
                | inRight unitEvaluated =>
                  cases unitEvaluated
                  refine ⟨[writtenValue, updatedValue, modifiedValue, rightValue, snapshotValue, keyValue, referenceValue], rfl, ?_⟩
                  intro next outputType value finalStore continuation
                  exact .letE referenceEvaluated (.caseRight keysEvaluated (.caseRight snapshotEvaluated
                    (.caseRight rhsEvaluated (.caseRight modifiedEvaluated (.caseRight setterEvaluated
                      (.letE writeEvaluated continuation))))))

/-- A universal expression IH supplies the continuation evaluation at the
actual temporary slots. `completed` is an already proved assignment result,
not a child-runtime assumption or a field of a static compilation receipt. -/
theorem preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (meaning : Preserves model program context evidence source certificate faults)
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    {prepared : Prepared} {reference rhs : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    {coreEnvironment : Environment} {initialStore store : Store}
    (completed : Evaluates coreEnvironment initialStore
      (execute prepared reference keys rhs (LanguageResult.success .unit) .unit operator bitNot invalid)
      (.inRight .word .unit) store)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (definitions := definitions) catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates coreEnvironment initialStore
        (execute prepared reference keys rhs lowered.expression lowered.type operator bitNot invalid) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨slots, length, finish⟩ := plug completed
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
    intro i v selected; exact selected
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, rest⟩ :=
    meaning generated found environments heaps locals (DataPlaceChildExpressions.prefix_agrees sameEnvironment slots) trace
  exact ⟨value, finalStore, finalMap, finalWorld,
    finish (by simpa only [DataPlaceChildExpressions.rename_prefix, length, Expr.rename_id, SourceCoreDataPlaces.shift, shift] using evaluated), rest⟩

/-- Whole assignment followed by a child outcome under the actual seven
hidden slots. The completed prefix is constructed from independent source
semantics here; it is not a caller-supplied execution assumption. -/
theorem preserves_from_source {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after)
    (invalidOperand : Word)
    {nextId : ExpressionId} {next : SourceCoreBasic.LoweredExpr} {nextNode : ExpressionNode}
    (nextGenerated : certificate scope nextId next) (nextFound : source.lookupExpression? nextId = some nextNode)
    {outcome : Dynamic.ExpressionOutcome} {finalHeap : Dynamic.Heap}
    (nextTrace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment after nextId outcome finalHeap) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next.expression next.type
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand) value finalStore ∧
      ResultRepresents (payloadModel compilation.checked registry functions) finalMap finalWorld nextNode.type next.type faults outcome value ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before finalHeap := by
  obtain ⟨_, prefixStore, prefixMap, prefixWorld, completed, _, prefixHeaps,
    prefixMaps, prefixWorlds, prefixFrame, prefixMetadata⟩ :=
    CompatiblePlaceAssignmentSuccess.preserves layout registryExtension meaning faithful observations rhsGenerated found rhsView rhsCoreType
      operatorProfile environments heaps locals slot rootTyped trace invalidOperand
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    preserves meaning nextGenerated nextFound completed (environments.extend prefixMaps prefixWorlds)
      prefixHeaps (locals.mono prefixMetadata) nextTrace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    prefixMaps.trans maps, prefixWorlds.trans worlds, prefixFrame.trans frame, prefixMetadata.trans metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceContinuation
end
