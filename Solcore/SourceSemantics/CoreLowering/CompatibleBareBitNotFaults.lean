import Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotPreservation

/-! Bare numeric faults are exactly absent unary operands. They bypass the
setter, mapped write and continuation, preserving both source and native heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

private theorem excludes_target_fault {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {heap after : Dynamic.Heap} {place : PlaceResolution} {location : Dynamic.Location} {cell : Dynamic.Cell}
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

theorem preserves_fault {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel compilation.checked.catalog}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {administrativeContext : Core.Context}
    {place : PlaceResolution} {prepared : Prepared} {mapping : LocationMap} {world : StoreTyping}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before after : Dynamic.Heap}
    {store : Store} {index : Nat} {reason : Dynamic.SemanticFault}
    (layout : Layout prepared) (bare : place.projections = [])
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after)
    (next : Expr) (outputType : Ty) (operator : Option BinaryOp) (invalid : Word) :
    reason = .invalidUnaryOperand .bitNot ∧ after = before ∧
      Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
        (LanguageResult.success .unit) next outputType operator true invalid) (.inLeft outputType (.word invalid)) store := by
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
            CompatibleBareBitNotNative.absent_evaluates layout nativeLookup nativeRead next outputType operator invalid⟩
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

end Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
