import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingVirtualRoot
import Solcore.SourceSemantics.CoreLowering.GenericExpressionMeaning

/-! Actual compatible local reads over the complete native definition table.
The pure encoder receipt constructs a lazy mapping value; reading an ordinary
cell either returns its authenticated payload or produces the specified fault.
No child runtime premise or assumption of whole-source determinism is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleMapping.VirtualRoot

private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible

/-- Actual successful encoding supplies the original source metadata relation
under any ambient function model; this data encoder creates no function leaf. -/
theorem Literal.represents {fuel : Nat} {context : ValuesContext} {node : ExpressionNode}
    {sourceType : TypeSystem.Ty} {carrier : SourceCoreCompatibleValues.Value} {code : Expr}
    (literal : Literal fuel context node sourceType carrier code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    {sourceValue : Dynamic.Value} (meaning : CompatibleEncoding.Means carrier sourceValue)
    (mapping : LocationMap) (world : StoreTyping) :
    ∃ value type, Quoted value code ∧
      ValueRep context.checked registry functions mapping world sourceType sourceValue value type := by
  cases literal with
  | encoded encoded accepted unchanged quoted =>
    have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions context.checked.catalog)
      accepted meaning mapping world
    have represented := represented.extend (return_registry encoded unchanged) (.refl _) (.refl _)
    have extended := ValueRep.map_functions (future := functions)
      (fun impossible => False.elim impossible) represented
    exact ⟨_, _, quoted_of_quote quoted, extended.extend extension (.refl _) (.refl _)⟩

/-- The source scope fixes the raw declaration type separately from its native
projection. Occurrence views may erase staging wrappers, but keep their own
original source type in the result relation. -/
structure StaticBinding {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    (sourceContext : SourceSemantics.Context) : Prop where
  declared : Resolved.LocalScope.Lookup sourceContext.locals certificate.binder certificate.declared.scheme
  occurrence : SourceCoreRawMetadata.runtimeType certificate.node.type =
    SourceCoreRawMetadata.runtimeType certificate.declared.scheme.body

private theorem monomorphic_instance {context : SourceSemantics.Context}
    {scheme : TypeSystem.Scheme} {type : TypeSystem.Ty}
    (monomorphic : scheme.quantified = [])
    (instantiates : SchemeInstantiatesAt context scheme type) : scheme.body = type := by
  cases instantiates with
  | intro _ substitution exactDomain _ result =>
    have emptyDomain : substitution.domain = [] := by
      have permutation := exactDomain.domain_permutation
      rw [monomorphic] at permutation
      exact List.perm_nil.mp permutation
    have empty : substitution = [] := by
      cases substitution with
      | nil => rfl
      | cons head tail => simp [TypeSystem.Substitution.domain] at emptyDomain
    subst substitution
    simpa [SchemeInstantiates.empty_apply] using result

/-- The independent source typing judgment supplies the declaration/occurrence
agreement. Equal native projections are not used to recover source metadata. -/
theorem StaticBinding.of_expression_type {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declared : Resolved.LocalScope.Lookup sourceContext.locals certificate.binder certificate.declared.scheme)
    (typed : ExpressionHasType source sourceContext id certificate.node.type) :
    StaticBinding certificate sourceContext := by
  refine ⟨declared, ?_⟩
  generalize nodeType : certificate.node.type = occurrenceType at typed
  cases typed with
  | @intro _ _ node rawType plan contains formTyped rawEq _ _ requirements =>
    have found := lookupExpression?_complete unique contains
    have same := Option.some.inj (found.symm.trans certificate.metadata.found)
    subst node
    have path := requirements.outputPath
    rw [certificate.metadata.coercions] at path
    cases path
    rw [certificate.form] at formTyped
    cases formTyped with
    | reference valid =>
      generalize binderEq : certificate.binder = binderId at valid
      cases valid with
      | «local» lookup _ instantiation =>
        rw [binderEq] at declared
        have schemeEq := lookup.value_unique declared
        have instantiates := instantiation.toSchemeInstantiatesAt
        rw [schemeEq] at instantiates
        exact congrArg SourceCoreRawMetadata.runtimeType
          (monomorphic_instance certificate.monomorphic instantiates).symm

private theorem cells_write_exists {cells : List Dynamic.Cell} {index : Nat} {cell : Dynamic.Cell}
    (found : Dynamic.Heap.CellAt cells index cell) (value : Dynamic.Value) : ∃ updated,
      Dynamic.Heap.CellsWrite cells index {cell with value := some value} updated := by
  induction found with
  | head => exact ⟨_, .head⟩
  | tail _ ih => obtain ⟨updated, written⟩ := ih; exact ⟨_, .tail written⟩

private theorem writes_exists {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads heap location cell) (value : Dynamic.Value) :
    ∃ after, Dynamic.Heap.Writes heap location (some value) after := by
  cases read with
  | intro selected =>
    obtain ⟨updated, written⟩ := cells_write_exists selected value
    exact ⟨⟨updated⟩, .intro (.intro selected) written⟩

private theorem ordinary_rename (type : Ty) (index : Nat) (reason : Word) (ξ : Renaming) :
    (OptionalCell.read type (.var index) reason).rename ξ = OptionalCell.read type (.var (ξ index)) reason := rfl

private theorem Quoted.rename {value : Value} {code : Expr} (quoted : Quoted value code) (ξ : Renaming) :
    code.rename ξ = code := by
  induction quoted generalizing ξ <;> simp_all [Expr.rename]

private theorem mapping_rename {value : Value} {literal : Expr} (quoted : Quoted value literal)
    (index : Nat) (ξ : Renaming) :
    (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal).rename ξ =
      SourceCoreCompatibleDataExpressions.readMapping (.var (ξ index)) literal := by
  have pureLiteral := quoted.weaken 0
  simp only [SourceCoreCompatibleDataExpressions.readMapping, pureLiteral]
  simp only [Expr.rename, Quoted.rename quoted, Renaming.lift, LanguageResult.success]

/-- An actual accepted read and its static source binding construct both finite
executions and the resulting heap/frame correspondence. Mapping initialization
updates the existing mapped cell; it allocates no administrative cell. -/
theorem Certificate.evaluates {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep} (uninitialized : ∀ location, faults (.uninitializedLocation location) reason) :
    ∃ outcome after value finalStore,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  rcases certificate with ⟨node, type, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
  rcases binding with ⟨declaredScope, occurrence⟩
  dsimp only at *
  obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup declaredScope
  obtain ⟨target, selected, optional, nativeLookup, reference, selectedRead, nativeRead, represented⟩ :=
    GenericHeap.lookup_visible environments heaps lookup slot
  have sameCell := read.functional selectedRead
  subst selected
  have representedAt : ∀ {sourceValue native},
      ValueRep context.checked registry functions mapping world cell.type sourceValue native type →
      ValueRep context.checked registry functions mapping world node.type sourceValue native type := by
    intro sourceValue native related
    exact .compatible (cellType ▸ occurrence) related
  have contains := lookupExpression?_sound metadata.found
  have sourceSuccess : ∀ {value after},
      Dynamic.ExpressionFormEvaluates program sourceContext evidence source environment heap
        node.form [] [] value after →
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id (.value value) after := by
    intro value after form
    exact .value (.intro contains (by rw [metadata.requirements, metadata.coercions]; exact form)
      (by rw [metadata.coercions]; exact .nil))
  have sourceFault : ∀ {fault after},
      Dynamic.ExpressionFormFaults program sourceContext evidence source environment heap
        node.form [] [] fault after →
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id (.fault fault) after := by
    intro fault after form
    exact .fault (.form contains (by rw [metadata.requirements, metadata.coercions]; exact form))
  cases represented with
  | @initialized sourceType _ sourceValue native payload =>
    have sourceEvaluated := sourceSuccess (form ▸
      (Dynamic.ExpressionFormEvaluates.local (coercions := []) rfl lookup read rfl rfl))
    refine ⟨_, heap, .inRight .word native, store, sourceEvaluated, ?_,
      .value (representedAt payload), heaps, (fun _ _ _ => ⟨by assumption, rfl⟩), .refl _⟩
    cases emitted with
    | ordinary _ =>
      rw [ordinary_rename]
      exact OptionalCell.read_success reason (.var (agrees nativeLookup)) nativeRead
    | mapping declared generated =>
      obtain ⟨_, _, quoted, _⟩ := generated.represents functions extension (.mapping .empty) mapping world
      rw [mapping_rename quoted]
      exact SourceCoreCompatibleDataExpressions.readMapping_present (.var (agrees nativeLookup)) nativeRead
  | @uninitialized sourceType _ projected =>
    change sourceType = declared.scheme.body at cellType
    cases emitted with
    | ordinary notMapping =>
      refine ⟨.fault (.uninitializedLocation location), heap, .inLeft type (.word reason), store,
        sourceFault (form ▸ (.localUninitialized (owned := []) rfl lookup read rfl rfl ?_)), ?_,
        .fault (uninitialized location), heaps, (fun _ _ _ => ⟨by assumption, rfl⟩), .refl _⟩
      · simpa only [cellType] using notMapping
      · rw [ordinary_rename]
        exact OptionalCell.read_failure reason (.var (agrees nativeLookup)) nativeRead
    | @mapping key value literal declared generated =>
      obtain ⟨native, encodedType, quoted, payload⟩ := generated.represents functions extension (.mapping .empty) mapping world
      have same : encodedType = type := Except.ok.inj (payload.projection.symm.trans (cellType ▸ projected))
      subst encodedType
      obtain ⟨after, written⟩ := writes_exists read (.mapping key value [])
      have cellPayload : ValueRep context.checked registry functions mapping world sourceType (.mapping key value []) native type :=
        cellType.symm ▸ payload
      obtain ⟨finalStore, nativeWritten, finalHeaps, frame⟩ := heaps.write_initialized reference read cellPayload written
      have finalEq := (Store.write?_eq_some_iff.mp nativeWritten).2
      refine ⟨.value (.mapping key value []), after, .inRight .word native, finalStore,
        sourceSuccess (form ▸ (.localEmptyMapping rfl lookup read rfl (cellType.trans declared) rfl written)), ?_,
        .value (representedAt cellPayload), finalHeaps, frame, .of_write written⟩
      rw [mapping_rename quoted, finalEq]
      apply SourceCoreCompatibleDataExpressions.readMapping_initializes (.var (agrees nativeLookup)) nativeRead
      · rw [quoted.weaken 0]
        rw [quoted.weaken 0]
        exact quoted.evaluates _ _
      · exact nativeRead

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
