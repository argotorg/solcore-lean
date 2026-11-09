import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceWriteback
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection

/-!
# Compatible places: bit-not updates

Modifiers, commits, tails, meaning and faults of bit-not updates on places.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotModifier
/-! Bit-not consumes the saved leaf. The generated Unit RHS is administrative
and has no corresponding source expression. This module supplies
the Word case; Integer snapshot agreement is provided by IntegerBitNotSnapshot. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotModifier
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}


theorem word_success

    {sourceType : TypeSystem.Ty} {type : Ty} {source : Dynamic.Value} {value : Value}
    (profile : SourceCoreRawMetadata.runtimeType sourceType = .word)
    (represented : ValueRep checked registry functions mapping world sourceType source value type)
    {environment : Environment} {snapshot rhs : Expr}
    (selected : DataEquality.Selects environment snapshot (.inRight .unit value))
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (store : Store) (invalid : Word) :
    ∃ result native, ValueRep checked registry functions mapping world sourceType result native type ∧
      Dynamic.BitNotSnapshot (some source) result ∧
      Evaluates environment store (modified type operator true snapshot rhs invalid) (.inRight .word native) store ∧
      ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot source := by
  obtain ⟨word, rfl, rfl, rfl⟩ := CompatibleRawScalarFields.word_fields represented profile
  obtain ⟨applies, evaluated, valid⟩ := DataPlaceModifier.word_bitNot_success word selected operator store invalid
  exact ⟨_, _, .compatible (actual := .word) profile (.word word.bitNot), applies, evaluated, valid⟩

theorem functional {current : Option Dynamic.Value} {left right : Dynamic.Value}
    (first : Dynamic.BitNotSnapshot current left) (second : Dynamic.BitNotSnapshot current right) : left = right := by
  cases first <;> cases second <;> rfl

/-- A successful independent target supplies all structural facts needed for
a snapshot-only write. No post-RHS source heap exists in this operation. -/
theorem write_exists {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before selected : Dynamic.Heap} {place : PlaceResolution} {target : Dynamic.ResolvedPlace}
    (resolved : Dynamic.SourcePlaceResolves program context evidence source environment before place target selected)
    {replacement : Dynamic.Value} (applies : Dynamic.BitNotSnapshot target.selected replacement) :
    ∃ updated after, Dynamic.ResolvedPlaceWrites (fun _ value => Dynamic.BitNotSnapshot target.selected value)
      selected target updated after := by
  cases resolved with
  | intro lookup initialRead keys currentRead initial read =>
    obtain ⟨updated, changed⟩ := DataPlaceUpdateTotality.read_update read replacement
    exact ⟨updated, _, .intro currentRead rfl initial
      (DataPlaceCommitReflection.update_of_replacement changed (fun _ => applies))
      (DataPlaceCommitReflection.source_writes currentRead updated)⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotModifier
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceNumericBitNotModifier
/-! Closed Word/Integer snapshot modifier semantics for the retained IR
profile. This extends no source checker or static admission rule. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceNumericBitNotModifier
open Core Frontend GeneralHeap CompatiblePayload CompatibleEquality SourceCoreCompatibleDataPlaces

theorem success {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}

    {sourceType : TypeSystem.Ty} {type : Ty} {source : Dynamic.Value} {value : Value}
    (profile : SourceCoreRawMetadata.runtimeType sourceType = .word ∨ SourceCoreRawMetadata.runtimeType sourceType = .integer)
    (represented : ValueRep checked registry functions mapping world sourceType source value type)
    {environment : Environment} {snapshot rhs : Expr}
    (selected : DataEquality.Selects environment snapshot (.inRight .unit value))
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (store : Store) (invalid : Word) :
    ∃ result native, ValueRep checked registry functions mapping world sourceType result native type ∧
      Dynamic.BitNotSnapshot (some source) result ∧
      Evaluates environment store (modified type operator true snapshot rhs invalid) (.inRight .word native) store ∧
      ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot source := by
  rcases profile with word | integer
  · exact CompatiblePlaceBitNotModifier.word_success word represented selected operator store invalid
  · exact IntegerBitNotSnapshot.compatible_success integer represented selected operator store invalid

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceNumericBitNotModifier
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCommit
/-! Generate the real bit-not tail from independent target resolution and a
snapshot write. RHS is Unit, while the replacement keeps the leaf type. No
child or helper evaluation is a premise of this commit construction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCommit
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr)
    (environment : Environment) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (target : Location) (keys : List Value) (snapshot : Value) (before after : Dynamic.Heap)
    (updated : Dynamic.Value) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) where
  replacement : Value
  value : Value
  helperStore : Store
  finalStore : Store
  finalWorld : StoreTyping
  related : ValueRep checked registry functions mapping finalWorld prepared.route.rootSourceType updated value prepared.route.rootType
  heaps : HeapRepresents checked registry functions mapping finalWorld after finalStore
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping store mapping finalStore
  metadata : Dynamic.HeapMetadataExtend before after
  modified : Evaluates (rhsEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) .unit environment) store
    (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType operator true (.var 1) (.var 0) invalid)
    (.inRight .word replacement) store
  setter : Evaluates (modifiedEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) .unit replacement environment) store
    (.apply (SourceCoreCompatibleDataPlaces.setter prepared (SourceCoreCalls.packArguments codes).type)
      (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) (.inRight .word value) helperStore
  read : ∃ optional, helperStore.read? target = some optional
  written : helperStore.write? target (.inRight .unit value) = some finalStore

private theorem none_update {modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate modify none projections updated) : projections = [] := by
  cases changed
  rfl

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

/-- Consume an independent snapshot write and derive its actual native
modifier, latest-root reconstruction and single mapped store update. -/
theorem of_write_numeric {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before selectedHeap after : Dynamic.Heap} {store : Store} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (resolution : CompatiblePlaceResolution.Execution compilation.checked registry functions prepared codes sourceTypes place leaf target
      coreEnvironment store mapping world before selectedHeap)
    (written : Dynamic.ResolvedPlaceWrites (fun _ value => Dynamic.BitNotSnapshot target.selected value) selectedHeap target updated after)
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) :
    Nonempty (Execution compilation.checked registry functions prepared codes coreEnvironment resolution.store resolution.mapping resolution.world
      resolution.target resolution.values resolution.snapshot selectedHeap after updated operator invalid) := by
  have snapshotRep := resolution.snapshotRelated
  have keyRep := resolution.keysRelated
  have reference := resolution.reference
  have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
  cases written with
  | @intro _ _ cell initial _ sourceRead _ initialValue update sourceWrite =>
    have cellEq := sourceRead.functional resolution.currentRead
    have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ resolution.currentType
    obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
    rw [resolution.selectedEq] at applies
    obtain ⟨replacement', replacementValue, replacementRep, applies', modifiedEvaluated, _⟩ :=
      CompatiblePlaceNumericBitNotModifier.success profile snapshotRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit coreEnvironment)
        (.var (index := 1) rfl) operator resolution.store invalid
    have same := CompatiblePlaceBitNotModifier.functional applies' applies
    subst replacement'
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_update changed)).elim
    obtain ⟨sourceRoot, rfl⟩ := present
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions resolution.mapping resolution.world prepared selectedHeap resolution.store target.location resolution.target
          cell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root resolution.heaps reference sourceRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root resolution.heaps reference sourceRead
          (layout.virtual key value cellType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have typedEnvironment : RuntimeEnvironmentHasTypes resolution.world
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit replacementValue coreEnvironment)
        (prepared.route.leafType :: .unit :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons .unit (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          ((environments.extend resolution.maps resolution.worlds).runtime_hasTypes)))))
    have currentPath : PreparedPath compilation.checked source site cell.type place.projections
        0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions resolution.mapping resolution.world source site resolution.values
        currentPath target.projections := by simpa only [cellType] using arguments
    obtain ⟨updatedValue, helperStore, finalStore, finalWorld, updatedRep, setterEvaluated,
      helperRead, coreWritten, finalHeaps, extension, frame, metadata⟩ :=
      CompatiblePlaceWriteback.preserves root resolution.heaps currentArguments replacementRep changed sourceWrite layout.nonempty
        faithful observations (layout.keyTypes ▸ keyRep.length.2) typedEnvironment layout.setterTyped (.var rfl) (.var rfl) (.var rfl)
    exact ⟨⟨replacementValue, updatedValue, helperStore, finalStore, finalWorld,
      by simpa only [cellType] using updatedRep, finalHeaps, extension, frame, metadata,
      modifiedEvaluated, setterEvaluated, ⟨_, helperRead⟩, coreWritten⟩⟩

/-- Word-only compatibility API. -/
theorem of_write {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before selectedHeap after : Dynamic.Heap} {store : Store} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (resolution : CompatiblePlaceResolution.Execution compilation.checked registry functions prepared codes sourceTypes place leaf target
      coreEnvironment store mapping world before selectedHeap)
    (written : Dynamic.ResolvedPlaceWrites (fun _ value => Dynamic.BitNotSnapshot target.selected value) selectedHeap target updated after)
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) :
    Nonempty (Execution compilation.checked registry functions prepared codes coreEnvironment resolution.store resolution.mapping resolution.world
      resolution.target resolution.values resolution.snapshot selectedHeap after updated operator invalid) :=
  of_write_numeric layout registryExtension faithful observations (.inl profile) environments resolution written operator invalid

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCommit
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotTail
/-! Exact Unit-RHS sequencing for the absent source RHS branch. These laws
compose or invert a commit constructed from independent source semantics. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCommit
open Core Frontend SourceInference GeneralHeap DataPatternValues CompatiblePayload CompatibleHeap
open SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr}
  {environment : Environment} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {target : Location} {keys : List Value} {snapshot : Value} {before after : Dynamic.Heap}
  {updated : Dynamic.Value} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {invalid : Word}

private theorem unit_rhs (environment : Environment) (store : Store) :
    Evaluates environment store (shift 3 (LanguageResult.success .unit)) (.inRight .word .unit) store := by
  simpa only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] using
    (Evaluates.inRight (leftType := .word) (environment := environment) (initialStore := store) Evaluates.unit)

theorem Execution.plug (execution : Execution checked registry functions prepared codes environment store mapping world
    target keys snapshot before after updated operator invalid) (passes : SourceCoreDataPlaces.Passes operator .unit)
    {next : Expr} {outputType : Ty} {result : Value} {finalStore : Store}
    (continuation : Evaluates (writtenEnvironment prepared.route.rootType target (packValues keys)
      (.inRight .unit snapshot) .unit execution.replacement execution.value environment)
      execution.finalStore (shift 7 next) result finalStore) :
    Evaluates (snapshotEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) environment)
      store (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type
        (LanguageResult.success .unit) next outputType operator true invalid) result finalStore := by
  obtain ⟨optional, read⟩ := execution.read
  exact LanguageResult.bind_success _ (unit_rhs _ _) (LanguageResult.bind_success _ execution.modified
    (LanguageResult.bind_success _ execution.setter
      (SourceCoreDataPlaces.guard_passes passes
        (.letE (.storeCell (.var rfl) read (.inRight (.var rfl)) execution.written) continuation))))

/-- A completed absent-RHS tail must reach the exact generated mapped commit.
The remaining seven-slot continuation is recovered as an output witness. -/
theorem Execution.reflects (execution : Execution checked registry functions prepared codes environment store mapping world
    target keys snapshot before after updated operator invalid)
    {next : Expr} {outputType : Ty} {result : Value} {finalStore : Store}
    (completed : Evaluates (snapshotEnvironment prepared.route.rootType target (packValues keys) (.inRight .unit snapshot) environment)
      store (CompatiblePlacePrefixReflection.remainder prepared (SourceCoreCalls.packArguments codes).type
        (LanguageResult.success .unit) next outputType operator true invalid) result finalStore) :
    Evaluates (writtenEnvironment prepared.route.rootType target (packValues keys)
      (.inRight .unit snapshot) .unit execution.replacement execution.value environment)
      execution.finalStore (shift 7 next) result finalStore := by
  cases completed with
  | caseLeft rhsEvaluated failed =>
    have impossible := (evaluation_deterministic rhsEvaluated (unit_rhs _ _)).1
    cases impossible
  | caseRight rhsEvaluated remaining =>
    obtain ⟨same, stores⟩ := evaluation_deterministic rhsEvaluated (unit_rhs _ _)
    cases same
    subst_vars
    cases remaining with
    | caseLeft modifiedEvaluated failed =>
      have impossible := (evaluation_deterministic modifiedEvaluated execution.modified).1
      cases impossible
    | caseRight modifiedEvaluated remaining =>
      obtain ⟨same, stores⟩ := evaluation_deterministic modifiedEvaluated execution.modified
      cases same
      subst_vars
      cases remaining with
      | caseLeft setterEvaluated failed =>
        have impossible := (evaluation_deterministic setterEvaluated execution.setter).1
        cases impossible
      | caseRight setterEvaluated remaining =>
        obtain ⟨same, stores⟩ := evaluation_deterministic setterEvaluated execution.setter
        cases same
        subst_vars
        -- The right-hand side is Unit, so no modifier check can fail.
        rcases SourceCoreDataPlaces.guard_inv remaining with ⟨_, remaining⟩ | ⟨_, _, impossible, _, _⟩
        · cases remaining with
          | letE written continuation =>
            obtain ⟨optional, read⟩ := execution.read
            have actual : Evaluates
                (execution.value :: modifiedEnvironment prepared.route.rootType target (packValues keys)
                  (.inRight .unit snapshot) .unit execution.replacement environment) execution.helperStore
                (.storeCell (.var 5) (.inRight .unit (.var 0))) .unit execution.finalStore :=
              .storeCell (.var rfl) read (.inRight (.var rfl)) execution.written
            obtain ⟨same, stores⟩ := evaluation_deterministic written actual
            subst_vars
            exact continuation
        · cases impossible

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCommit
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotMeaning
/-! Successful source bit-not assignments and every completed emitted numeric
bit-not assignment agree. Index expressions use a universal induction premise;
there is no RHS source expression or assumed child/helper execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotMeaning
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

inductive Result (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (place : PlaceResolution) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (next : Expr) (outputType : Ty) (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked registry functions program context evidence source faults place environment coreEnvironment
        before store mapping world next outputType result finalStore
  | committed {updated : Dynamic.Value} {after : Dynamic.Heap} {written : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
        environment before place updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (length : slots.length = 7)
      (continuation : Evaluates (slots ++ coreEnvironment) written (shift 7 next) result finalStore) :
      Result checked registry functions program context evidence source faults place environment coreEnvironment
        before store mapping world next outputType result finalStore

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}

/-- Every independent successful numeric snapshot update has a finite actual
native execution, including real setter allocations and the mapped write. -/
theorem preserves_numeric
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updated : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before place updated after)
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word)
    (passes : SourceCoreDataPlaces.Passes operator .unit) :
    ∃ finalStore finalMap finalWorld,
      Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments codes)
        (LanguageResult.success .unit) (LanguageResult.success .unit) .unit operator true invalid)
        (.inRight .word .unit) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases trace with
  | intro resolve write =>
    obtain ⟨resolution, reference⟩ := CompatiblePlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
      environments heaps locals slot rootTyped resolve
    obtain ⟨commit⟩ := CompatiblePlaceBitNotCommit.of_write_numeric layout registryExtension faithful observations profile environments resolution write operator invalid
    refine ⟨commit.finalStore, resolution.mapping, commit.finalWorld, ?_, commit.heaps, resolution.maps,
      resolution.worlds.trans commit.worlds, resolution.frame.trans commit.frame, resolution.metadata.trans commit.metadata⟩
    exact .letE (.var reference) (LanguageResult.bind_success _ resolution.keysEvaluated
      (LanguageResult.bind_success _ resolution.snapshotEvaluated (commit.plug passes
        (by simpa only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] using
          (Evaluates.inRight (leftType := .word) (initialStore := commit.finalStore)
            (environment := writtenEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) .unit commit.replacement commit.value coreEnvironment) Evaluates.unit)))))

/-- Reflection has no prior source trace: the actual key/getter prefix gives
resolution, then the saved numeric leaf constructs the independent snapshot write.
The generated Unit RHS leaves both heaps untouched. -/
theorem reflects_numeric
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments codes)
      (LanguageResult.success .unit) next outputType operator true invalid) result finalStore) :
    Result compilation.checked registry functions program context evidence source faults place environment coreEnvironment
      before store mapping world next outputType result finalStore := by
  have targetPhase := CompatiblePlacePrefixReflection.reflects layout ordinary registryExtension meaning functionTypes faithful observations
    missingTokens invalidTokens environments heaps locals slot rootTyped completed
  cases targetPhase with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
    exact .fault (.target sourceFault) resultEq tokenRep heaps maps worlds frame metadata
  | resolved sourceTrace resolution remainder =>
    obtain ⟨replacement, native, represented, applies, _, _⟩ :=
      CompatiblePlaceNumericBitNotModifier.success profile resolution.snapshotRelated
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) .unit coreEnvironment) (rhs := .var 0) (.var (index := 1) rfl)
        operator resolution.store invalid
    have applies := resolution.selectedEq.symm ▸ applies
    obtain ⟨updated, after, written⟩ := CompatiblePlaceBitNotModifier.write_exists sourceTrace applies
    obtain ⟨commit⟩ := CompatiblePlaceBitNotCommit.of_write_numeric layout registryExtension faithful observations profile environments resolution written operator invalid
    exact .committed (.intro sourceTrace written) commit.heaps resolution.maps (resolution.worlds.trans commit.worlds)
      (resolution.frame.trans commit.frame) (resolution.metadata.trans commit.metadata)
      (slots := [.unit, commit.value, commit.replacement, .unit, .inRight .unit resolution.snapshot,
        packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) rfl
      (commit.reflects remainder)

/-- Word-only compatibility API. -/
theorem preserves
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updated : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before place updated after)
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word)
    (passes : SourceCoreDataPlaces.Passes operator .unit) :
    ∃ finalStore finalMap finalWorld,
      Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments codes)
        (LanguageResult.success .unit) (LanguageResult.success .unit) .unit operator true invalid)
        (.inRight .word .unit) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves_numeric layout registryExtension meaning faithful observations (.inl profile) environments heaps locals slot rootTyped trace
    operator invalid passes

/-- Word-only compatibility API. -/
theorem reflects
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments codes)
      (LanguageResult.success .unit) next outputType operator true invalid) result finalStore) :
    Result compilation.checked registry functions program context evidence source faults place environment coreEnvironment
      before store mapping world next outputType result finalStore :=
  reflects_numeric layout ordinary registryExtension meaning functionTypes faithful observations missingTokens invalidTokens (.inl profile) environments heaps locals slot rootTyped completed

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCertificates
/-! The actual absent-RHS branch retains a literal Unit administrative slot.
Only index children receive source expression certificates. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCertificates
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces DataPatternValues
open DataPlaceCertificates CompatibleMixedRoute CompatiblePlaceCompilerCertificates

theorem of_describe_prepare {compilation : SourceCoreCompatibleDataPlaces.Context} {definitions : DataEnvironment}
    {source : TypedSource} {context : SourceSemantics.Context} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {route : Route} {prepared : Prepared}
    {fuel : Nat} {invalid : Word} {missing : TypeSystem.Ty → Word}
    {expression : ExpressionLowerer} {scope : Scope} {reasonAt : ExpressionId → Word}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    {administrativeContext : Core.Context} {reference rhs next : Expr} {outputType resultType : Ty}
    {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalidOperand : Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compilation.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (nonempty : assignment.target.projections ≠ [])
    (described : describe compilation compilation.checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation fuel route invalid missing = .ok prepared)
    (generated : ListRel (KeyGenerated expression fuel source scope reasonAt) prepared.keys codes)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext)
      (execute prepared reference (SourceCoreCalls.packArguments codes) rhs next outputType operator bitNot invalidOperand)
      resultType definitions)
    (rhsTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) rhs
      (LanguageResult.resultType .unit) definitions) :
    ∃ binder leaf sourceTypes,
      rootBinder source assignment.target.root = .ok binder ∧
      prepared.route.rootSourceType = binder.scheme.body ∧
      SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType assignment.target.type ∧
      CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) compilation source certificate scope site assignment.target prepared codes sourceTypes leaf administrativeContext .unit ∧
      ((∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none) := by
  obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
  obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
  obtain ⟨sourceTypes, tree, keyTypes⟩ := tree_of_keys path generated extract
  obtain ⟨views, leafView⟩ := CompatiblePlaceKeyTyping.of_typing unique signatures path rfl (sourceTyped binder description.binding) tree
  have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
  have actualPath : PreparedPath compilation.checked source site prepared.route.rootSourceType assignment.target.projections
      0 prepared.steps prepared.keys leaf := rootEq ▸ path
  refine ⟨binder, leaf, sourceTypes, description.binding, rootEq, leafView, ?_, ?_⟩
  · refine ⟨actualPath, by simpa only [rootEq] using views, tree, keyTypes, ?_, ?_, ?_,
      CompatiblePlaceHelperTyping.getter_of_execute typed,
      CompatiblePlaceHelperTyping.setter_of_execute_rhs typed (CompatiblePlaceHelperTyping.rhs_shift_typed_rhs rhsTyped)⟩
    · rw [← compilation.checked.catalog.project_runtimeType leaf, description.selectedType,
        compilation.checked.catalog.project_runtimeType, routeEq]
      exact description.leafProjected
    · intro k v declared
      rw [routeEq]
      exact description.virtual k v (rootEq.symm.trans declared)
    · intro empty
      have length := PreparedPath.steps_length path
      rw [empty, List.length_nil] at length
      exact nonempty (List.eq_nil_of_length_eq_zero length.symm)
  · intro notMapping
    rw [routeEq]
    exact description.ordinary (fun k v same => notMapping k v (rootEq.trans same))

/-- Actual `rhs := none` compilation fixes the Unit RHS, with no source
expression invented for that administrative value. -/
theorem of_lower {compilation : SourceCoreCompatibleDataPlaces.Context} {definitions : DataEnvironment}
    {source : TypedSource} {context : SourceSemantics.Context} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {fuel : Nat} {expression : ExpressionLowerer} {scope : Scope}
    {reasonAt : ExpressionId → Word} {operator : Syntax.ValueAssignOp}
    {next lowered : Expr} {outputType resultType : Ty} {invalid invalidOperand : Word}
    {missing : TypeSystem.Ty → Word} {certificate : GenericExpressionMeaning.Certificate} {administrativeContext : Core.Context}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compilation.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (nonempty : assignment.target.projections ≠ [])
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none outputType
      next reasonAt invalid invalidOperand missing = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) lowered resultType definitions) :
    ∃ binder leaf prepared codes sourceTypes index,
      (∃ route, describe compilation compilation.checked.signatures source site assignment = .ok route ∧
        prepare compilation fuel route invalid missing = .ok prepared) ∧
      rootBinder source assignment.target.root = .ok binder ∧
      prepared.route.rootSourceType = binder.scheme.body ∧
      SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType assignment.target.type ∧
      SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType) ∧
      CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) compilation source certificate scope site assignment.target prepared codes sourceTypes leaf administrativeContext .unit ∧
      ((∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none) ∧
      (prepared.route.leafType = .word ∨ prepared.route.leafType = .integer) ∧
      lowered = execute prepared (.var index) (SourceCoreCalls.packArguments codes) (LanguageResult.success .unit) next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) true invalidOperand := by
  have receipt := CompatiblePlaceCompilerCertificates.generated_of_lower accepted
  cases receipt with
  | intro route prepared index codes value described lookup preparedBy generated operatorValid rhsGenerated =>
    cases rhsGenerated with
    | absent =>
      have routeEq := (CompatibleMixedPreparation.of_prepare preparedBy).1
      obtain ⟨binder, leaf, sourceTypes, binding, rootEq, leafView, layout, ordinary⟩ :=
        of_describe_prepare unique signatures sourceTyped nonempty described preparedBy generated extract typed
          (LanguageResult.success_hasType .unit)
      have profile : prepared.route.leafType = .word ∨ prepared.route.leafType = .integer := by
        simpa only [Option.isNone_none, Bool.true_eq_false, and_false, false_or, routeEq] using
          operatorValid.imp_right (Or.imp_right And.left)
      exact ⟨binder, leaf, prepared, codes, sourceTypes, index, ⟨route, described, preparedBy⟩, binding, rootEq,
        leafView, by simpa only [routeEq] using lookup, layout, ordinary, profile, by simp [routeEq]⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotFaults
/-! Target-resolution faults for absent-RHS bit-not. The actual key runs are derived
from the universal expression theorem. The getter uses the live root after
those effects, preserving exact raw missing-default tokens and administrative
allocations. An absent ordinary root fails without allocating a helper. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotFaults
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
    (operator : Syntax.ValueAssignOp) (rhs next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) true invalid)
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
    (binaryOperator (prepared.route.leafType = .integer) operator) true invalid token
    (.cellRef (OptionalCell.cellType prepared.route.rootType) target) (.var coreLookup)
  simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

/-- Independent structural failure determines the actual whole emitted
assignment's failure before its RHS, modifier, setter or continuation starts. -/
theorem projection
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
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
    (operator : Syntax.ValueAssignOp) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) true invalidOperand)
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
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
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
    (operator : Syntax.ValueAssignOp) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) true invalidOperand)
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

/-- Every independent fault in the supported numeric profile occurs before the
administrative RHS. Typed live locals exclude dangling/unbound roots; an
accepted successful projected read supplies an initialized numeric snapshot. -/
theorem preserves_numeric
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments codes)
        (LanguageResult.success .unit) next outputType (binaryOperator (prepared.route.leafType = .integer) operator) true invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨scheme, staticLookup, _, _, _⟩ := rootTyped.scheme
  obtain ⟨location, initialCell, lookup, initialRead, _, _⟩ := locals.lookup staticLookup
  cases trace with
  | target fault =>
    cases fault with
    | unbound missing => exact (missing.excludes_lookup lookup).elim
    | dangling found missing =>
      have same := found.functional lookup
      subst_vars
      exact (missing.excludes_read initialRead).elim
    | projectionExpression found read failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, _, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
        keys layout.children meaning environments heaps locals slot found read failed operator (LanguageResult.success .unit) next outputType invalidOperand
      exact ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
    | danglingAfterProjections found read evaluated missing =>
      obtain ⟨keys⟩ := CompatiblePlaceTargetKeys.preserves layout.children meaning environments heaps locals slot rootTyped found read evaluated
      exact (missing.excludes_read keys.read).elim
    | projectionRead found read evaluated currentRead initial fault =>
      obtain ⟨token, count, root, finalStore, finalMap, finalWorld, _, _, tokenRep, executed, finalHeaps, maps, worlds, frame, metadata⟩ :=
        projection layout meaning environments heaps locals slot rootTyped found read evaluated currentRead registryExtension faithful observations
          initial fault operator (LanguageResult.success .unit) next outputType invalidOperand
      exact ⟨token, finalStore, finalMap, finalWorld, executed, missingTokens tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
    | uninitialized found read evaluated currentRead empty nonmapping nonempty =>
      obtain ⟨finalStore, finalMap, finalWorld, _, executed, finalHeaps, maps, worlds, frame, metadata⟩ :=
        uninitialized layout meaning environments heaps locals slot rootTyped found read evaluated currentRead ordinary empty nonmapping nonempty
          operator (LanguageResult.success .unit) next outputType invalidOperand
      exact ⟨_, finalStore, finalMap, finalWorld, executed, invalidTokens _, finalHeaps, maps, worlds, frame, metadata⟩
  | uninitialized resolve empty =>
    obtain ⟨resolution, _⟩ := CompatiblePlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
      environments heaps locals slot rootTyped resolve
    rw [resolution.selectedEq] at empty
    cases empty
  | operand resolve selected invalid =>
    obtain ⟨resolution, _⟩ := CompatiblePlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
      environments heaps locals slot rootTyped resolve
    have same := Option.some.inj (selected.symm.trans resolution.selectedEq)
    obtain ⟨replacement, native, represented, applies, evaluated, valid⟩ :=
      CompatiblePlaceNumericBitNotModifier.success profile resolution.snapshotRelated
        (environment := [.inRight .unit resolution.snapshot]) (rhs := .unit) (.var (index := 0) rfl) none resolution.store invalidOperand
    exact (valid (same ▸ invalid)).elim

/-- Word-only compatibility API. -/
theorem preserves
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext .unit)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    (profile : SourceCoreRawMetadata.runtimeType leaf = .word)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments codes)
        (LanguageResult.success .unit) next outputType (binaryOperator (prepared.route.leafType = .integer) operator) true invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves_numeric layout ordinary registryExtension meaning faithful observations missingTokens invalidTokens (.inl profile)
    environments heaps locals slot rootTyped trace operator next outputType invalidOperand

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotFaults
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotLowerReflection
/-! The production compatible place lowerer is connected to whole numeric bit-not
reflection. The absent RHS is Unit; only universal index-child certificates/meaning and independent checked source
facts remain; no manually supplied path or helper-typing layout is needed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotLowerReflection
open Core Frontend SourceInference GeneralHeap GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces

theorem reflects_numeric {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {assignment : AssignmentResolution}
    {administrativeContext : Core.Context} {expression : ExpressionLowerer} {fuel : Nat}
    {operator : Syntax.ValueAssignOp} {next lowered : Expr} {outputType resultType : Ty}
    {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compilation.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (nonempty : assignment.target.projections ≠ [])
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none outputType
      next reasonAt invalid invalidOperand missing = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) lowered resultType ambient.definitions)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {prepared root resolved reason token count},
      (∃ route, describe compilation compilation.checked.signatures source site assignment = .ok route ∧
        prepare compilation fuel route invalid missing = .ok prepared) →
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) invalid)
    (operatorProfile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {result : Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (completed : Evaluates coreEnvironment store lowered result finalStore) :
    CompatiblePlaceBitNotMeaning.Result compilation.checked registry functions program context evidence source faults assignment.target
      environment coreEnvironment before store mapping world next outputType result finalStore := by
  obtain ⟨binder, leaf, prepared, codes, sourceTypes, index, actualPreparation, binding, rootEq, leafView, slot, layout, ordinary,
      _, lowering⟩ :=
    CompatiblePlaceBitNotCertificates.of_lower unique signatures sourceTyped nonempty extract accepted typed
  have profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer := by
    simpa only [leafView] using operatorProfile
  have invalidEq : prepared.invalidProjection = invalid := by
    obtain ⟨route, _, preparedBy⟩ := actualPreparation
    exact (CompatibleMixedPreparation.of_prepare preparedBy).2.1
  exact CompatiblePlaceBitNotMeaning.reflects_numeric layout ordinary registryExtension meaning functionTypes faithful observations
    (fun receipt => missingTokens actualPreparation receipt) (by simpa only [invalidEq] using invalidTokens)
    profile environments heaps locals slot (rootEq ▸ rootTyped binder binding) (lowering ▸ completed)

/-- Word-only compatibility API. -/
theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {assignment : AssignmentResolution}
    {administrativeContext : Core.Context} {expression : ExpressionLowerer} {fuel : Nat}
    {operator : Syntax.ValueAssignOp} {next lowered : Expr} {outputType resultType : Ty}
    {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compilation.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (nonempty : assignment.target.projections ≠ [])
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none outputType
      next reasonAt invalid invalidOperand missing = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) lowered resultType ambient.definitions)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {prepared root resolved reason token count},
      (∃ route, describe compilation compilation.checked.signatures source site assignment = .ok route ∧
        prepare compilation fuel route invalid missing = .ok prepared) →
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) invalid)
    (operatorProfile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {result : Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (completed : Evaluates coreEnvironment store lowered result finalStore) :
    CompatiblePlaceBitNotMeaning.Result compilation.checked registry functions program context evidence source faults assignment.target
      environment coreEnvironment before store mapping world next outputType result finalStore :=
  reflects_numeric unique signatures sourceTyped rootTyped nonempty extract accepted typed registryExtension meaning
    functionTypes faithful observations missingTokens invalidTokens (.inl operatorProfile) environments heaps locals completed

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotLowerReflection
end
