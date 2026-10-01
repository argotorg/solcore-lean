import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNotMeaning
import Solcore.SourceSemantics.CoreLowering.ReadOnlyRenaming

/-! Independent bare unary source updates and completed actual renamed Core
code agree. Successful reflection returns all seven typed slots, with a Unit
RHS; preservation uses the exact source write and supports any continuation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
open Core Frontend SourceInference GeneralHeap CoreProof DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

inductive Result (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (faults : FaultRep) (prepared : Prepared) (place : PlaceResolution)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (store : Store) (mapping : LocationMap)
    (world : StoreTyping) (actual : Environment) (actualContext : Core.Context) (ξ : Renaming)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word}
      (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason before)
      (result : value = .inLeft output (.word token)) (represented : faults reason token)
      (storeEq : finalStore = store) :
      Result checked registry functions program context evidence source faults prepared place environment before store
        mapping world actual actualContext ξ next output value finalStore
  | success {updated : Dynamic.Value} {replacement : Value} {after : Dynamic.Heap}
      {written : Store} {slots : Environment}
      (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
        environment before place updated after)
      (represented : ValueRep checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType)
      (heaps : HeapRepresents checked registry functions mapping world after written)
      (frame : AdministrativePreserved mapping store mapping written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions)
      (continuation : Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) :
      Result checked registry functions program context evidence source faults prepared place environment before store
        mapping world actual actualContext ξ next output value finalStore

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {prepared : Prepared} {place : PlaceResolution} {scope : Scope}
  {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {index : Nat} {ξ : Renaming}
  {identities : Dynamic.Value → Word → Prop}

private theorem writes_functional {heap left right : Dynamic.Heap} {location : Dynamic.Location} {value : Option Dynamic.Value}
    (first : Dynamic.Heap.Writes heap location value left) (second : Dynamic.Heap.Writes heap location value right) : left = right := by
  have cells : ∀ {before first second : List Dynamic.Cell} {index : Nat} {value : Dynamic.Cell},
      Dynamic.Heap.CellsWrite before index value first → Dynamic.Heap.CellsWrite before index value second → first = second := by
    intro before first second index value left
    induction left generalizing second with
    | head => intro right; cases right; rfl
    | tail _ ih => intro right; cases right with | tail rest => exact congrArg (List.cons _) (ih rest)
  cases first with
  | intro firstRead firstWrite =>
    cases second with
    | intro secondRead secondWrite =>
      have same := firstRead.functional secondRead
      cases same
      exact congrArg Dynamic.Heap.mk (cells firstWrite secondWrite)

theorem preserves_prefix (layout : Layout prepared) (bare : place.projections = [])
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before place updated after) (operator : Option BinaryOp) (invalid : Word) :
    ∃ replacement finalStore slots,
      ValueRep compilation.checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
          next output operator true invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
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
          cases root with
          | emptyMapping key value =>
            have impossible := cellType ▸ profile
            rcases impossible with impossible | impossible <;> cases impossible
          | uninitialized => cases applies
          | initialized =>
            obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference currentRead
            cases represented with
            | @initialized rawType payload sourceValue nativeValue related =>
              simp only at cellType
              subst_vars
              obtain ⟨replacement, native, generatedAfter, finalStore, slots, generated, generatedWrite,
                related, finalHeaps, frame, metadata, count, typed, agreement⟩ :=
                initialized_prefix layout observations profile heaps reference currentRead nativeRead related
                  (agrees nativeLookup) actualTyped operator invalid
              have same := CompatiblePlaceBitNotModifier.functional generated applies
              subst replacement
              have same := writes_functional generatedWrite sourceWrite
              subst generatedAfter
              exact ⟨native, finalStore, slots, related, finalHeaps, frame, metadata, count, typed, agreement⟩

/-- The sole runtime premise is completion of the real renamed code. It
produces an independent source fault/write and the actual typed continuation. -/
theorem reflects (layout : Layout prepared) (bare : place.projections = [])
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {faults : FaultRep} {next : Expr} {output : Ty} {operator : Option BinaryOp} {invalid : Word}
    {result : Value} {finalStore : Store}
    (token : faults (.invalidUnaryOperand .bitNot) invalid)
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
        next output operator true invalid).rename ξ) result finalStore) :
    Result compilation.checked registry functions program context evidence source faults prepared place environment before store
      mapping world actual actualContext ξ next output result finalStore := by
  obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨sourceLocation, cell, sourceLookup, sourceRead, cellType, _⟩ := locals.lookup schemeLookup
  have cellType := cellType.trans bodyEq
  obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible sourceLookup slot
  obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference sourceRead
  cases represented with
  | uninitialized projected =>
    have initial : Dynamic.RootInitialValue _ none := .uninitialized (by
      rintro ⟨key, value, same⟩
      have impossible : prepared.route.rootSourceType = .mapping key value := cellType.symm.trans same
      rw [impossible] at profile
      rcases profile with impossible | impossible <;> cases impossible)
    have trace := CompatibleBareBitNotMeaning.resolves (program := program) (context := context)
      (evidence := evidence) (source := source) bare sourceLookup sourceRead initial
    obtain ⟨resultEq, storeEq⟩ := absent_reflects layout (agrees nativeLookup) nativeRead completed
    exact .fault (.uninitialized trace rfl) resultEq token storeEq
  | @initialized type _payload sourceValue value related =>
    simp only at cellType
    subst type
    have trace := CompatibleBareBitNotMeaning.resolves (program := program) (context := context)
      (evidence := evidence) (source := source) bare sourceLookup sourceRead Dynamic.RootInitialValue.initialized
    obtain ⟨updated, replacement, after, written, slots, applies, sourceWrite, represented, finalHeaps,
      frame, metadata, count, typed, agreement⟩ := initialized_prefix layout observations profile heaps
        reference sourceRead nativeRead related (agrees nativeLookup) actualTyped operator invalid
    exact .success (.intro trace (.intro sourceRead rfl .initialized (.leaf applies) sourceWrite))
      represented finalHeaps frame metadata count typed ((agreement next output).unwrap completed)

private theorem excludes_target_fault {heap after : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    {reason : Dynamic.SemanticFault}
    (bare : place.projections = []) (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (read : Dynamic.Heap.Reads heap location cell)
    (fault : Dynamic.SourcePlaceFaults program context evidence source environment heap place reason after) : False := by
  cases fault with
  | unbound missing => exact missing.excludes_lookup lookup
  | dangling found missing => exact missing.excludes_read (found.functional lookup ▸ read)
  | projectionExpression found initialRead fault => rw [bare] at fault; cases fault
  | danglingAfterProjections found initialRead keys missing =>
    rw [bare] at keys
    cases keys
    exact missing.excludes_read initialRead
  | projectionRead found initialRead keys currentRead root fault =>
    rw [bare] at keys
    cases keys
    cases fault
  | uninitialized found initialRead keys currentRead empty notMapping nonempty =>
    rw [bare] at keys
    cases keys
    exact nonempty rfl

/-- Every independent fault of a live numeric bare root is the absent unary
operand. Generated helpers and the continuation do not alter either heap. -/
theorem preserves_fault (layout : Layout prepared) (bare : place.projections = [])
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after)
    (next : Expr) (output : Ty) (operator : Option BinaryOp) (invalid : Word) :
    reason = .invalidUnaryOperand .bitNot ∧ after = before ∧
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
          next output operator true invalid).rename ξ) (.inLeft output (.word invalid)) store := by
  obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨staticLocation, staticCell, staticLookup, staticRead, staticType, _⟩ := locals.lookup schemeLookup
  cases trace with
  | target fault => exact (excludes_target_fault bare staticLookup staticRead fault).elim
  | uninitialized resolve empty =>
    cases resolve with
    | intro lookup initialRead keys currentRead root selection =>
      rw [bare] at keys
      cases keys
      cases selection
      cases empty
      cases root with
      | uninitialized notMapping =>
        obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
        obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference currentRead
        cases represented with
        | uninitialized projected => exact ⟨rfl, rfl,
            absent_evaluates layout (agrees nativeLookup) nativeRead next output operator invalid⟩
  | operand resolve selected invalidOperand =>
    cases resolve with
    | intro lookup initialRead keys currentRead root selection =>
      rw [bare] at keys
      cases keys
      cases selection
      cases selected
      have sameLocation := lookup.functional staticLookup
      subst staticLocation
      have sameCell := currentRead.functional staticRead
      subst staticCell
      have cellType := staticType.trans bodyEq
      cases root with
      | emptyMapping key value =>
        have impossible := cellType ▸ profile
        rcases impossible with impossible | impossible <;> cases impossible
      | initialized =>
        obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
        obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference currentRead
        cases represented with
        | initialized related =>
          have profile := cellType ▸ profile
          obtain ⟨_, _, _, _, _, valid⟩ := CompatiblePlaceNumericBitNotModifier.success observations profile related
            (environment := [_]) (rhs := .unit) (.var (index := 0) rfl) operator store invalid
          exact (valid invalidOperand).elim

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
