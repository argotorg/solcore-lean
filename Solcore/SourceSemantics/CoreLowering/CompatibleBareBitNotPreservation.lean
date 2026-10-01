import Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning

/-! Preservation for every independent bare-root snapshot trace and fault.
No source key/RHS exists, and the native store is unchanged on failure. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel compilation.checked.catalog}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {administrativeContext : Core.Context}
  {place : PlaceResolution} {prepared : Prepared} {mapping : LocationMap} {world : StoreTyping}
  {environment : Dynamic.Environment} {coreEnvironment : Environment} {before after : Dynamic.Heap}
  {store : Store} {index : Nat}

theorem preserves (layout : Layout prepared) (bare : place.projections = [])
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before place updated after)
    (operator : Option BinaryOp) (invalid : Word) :
    ∃ finalStore,
      Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
        (LanguageResult.success .unit) (LanguageResult.success .unit) .unit operator true invalid)
        (.inRight .word .unit) finalStore ∧
      HeapRepresents compilation.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases trace with
  | intro resolve written =>
    cases resolve with
    | @intro _ _ _ _ _ _ _ location initialCell currentCell resolved initial selected lookup initialRead keys currentRead root selection =>
      rw [bare] at keys
      cases keys
      cases selection
      cases written with
      | intro writeRead typeEq writeInitial changed sourceWrite =>
        cases changed with
        | leaf applies =>
          obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
          obtain ⟨staticLocation, staticCell, staticLookup, staticRead, staticType, _⟩ := locals.lookup schemeLookup
          have sameLocation := lookup.functional staticLookup
          subst staticLocation
          have sameCell := currentRead.functional staticRead
          subst staticCell
          have cellType := staticType.trans bodyEq
          obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
          obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference currentRead
          cases root with
          | emptyMapping key value =>
            have impossible := cellType ▸ profile
            rcases impossible with impossible | impossible <;> cases impossible
          | uninitialized => cases applies
          | initialized =>
            cases represented with
            | @initialized rawType payload sourceValue nativeValue related =>
              simp only at cellType
              subst_vars
              obtain ⟨replacement, changedValue, replacementRep, actualApplies, modifier, _⟩ :=
                CompatiblePlaceNumericBitNotModifier.success observations profile related
                  (environment := rhsEnvironment prepared.route.rootType target .unit (.inRight .unit nativeValue) .unit coreEnvironment)
                  (rhs := .var 0) (.var (index := 1) rfl) operator store invalid
              have same := CompatiblePlaceBitNotModifier.functional actualApplies applies
              subst replacement
              obtain ⟨finalStore, coreWritten, finalHeaps, frame⟩ := heaps.write_initialized reference currentRead replacementRep sourceWrite
              let commit : CompatiblePlaceBitNotCommit.Execution compilation.checked registry functions prepared [] coreEnvironment
                  store mapping world target [] nativeValue before after updated operator invalid := {
                replacement := changedValue, value := changedValue, helperStore := store, finalStore := finalStore,
                finalWorld := world, related := replacementRep, heaps := finalHeaps, worlds := .refl _, frame := frame,
                metadata := .of_write sourceWrite,
                modified := by simpa only [← layout.sameType, packValues] using modifier,
                setter := CompatibleBareBitNotNative.setter_evaluates layout (.inRight .unit nativeValue) changedValue nativeRead,
                read := ⟨_, nativeRead⟩, written := coreWritten }
              refine ⟨finalStore, ?_, finalHeaps, frame, .of_write sourceWrite⟩
              apply CompatibleBareBitNotNative.prefix_plug layout nativeLookup nativeRead
              apply commit.plug
              simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success]
              simpa only [commit, packValues] using (Evaluates.inRight (leftType := .word)
                (environment := writtenEnvironment prepared.route.rootType target .unit (.inRight .unit nativeValue)
                  .unit changedValue changedValue coreEnvironment) (initialStore := finalStore) Evaluates.unit)

end Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
