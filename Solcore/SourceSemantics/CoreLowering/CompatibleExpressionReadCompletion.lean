import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLeaves
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadFaultPolicies

/-! Direct completion of the actual compatible local-read code. The mapping
branch writes the certified empty payload to the same ordinary source cell;
virtual-root getters and generalized cells remain separate interfaces. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCompletion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleMapping.VirtualRoot

/-- Pure quoted values are recovered by inspecting their original execution.
No second execution or determinism argument is used. -/
theorem quoted_completed {native result : Value} {code : Expr}
    (quoted : Quoted native code) {environment : Environment} {before after : Store}
    (evaluated : Evaluates environment before code result after) : result = native ∧ after = before := by
  induction quoted generalizing environment before result after with
  | unit => cases evaluated; exact ⟨rfl, rfl⟩
  | bool => cases evaluated; exact ⟨rfl, rfl⟩
  | word => cases evaluated; exact ⟨rfl, rfl⟩
  | integer => cases evaluated; exact ⟨rfl, rfl⟩
  | pair _ _ left right =>
    cases evaluated with
    | pair first second =>
      obtain ⟨rfl, rfl⟩ := left first
      obtain ⟨rfl, rfl⟩ := right second
      exact ⟨rfl, rfl⟩
  | inLeft _ _ ih =>
    cases evaluated with
    | inLeft child => obtain ⟨rfl, rfl⟩ := ih child; exact ⟨rfl, rfl⟩
  | inRight _ _ ih =>
    cases evaluated with
    | inRight child => obtain ⟨rfl, rfl⟩ := ih child; exact ⟨rfl, rfl⟩
  | constructed _ _ ih =>
    cases evaluated with
    | construct child => obtain ⟨rfl, rfl⟩ := ih child; exact ⟨rfl, rfl⟩

theorem var_completed {environment : Environment} {before after : Store}
    {index : Nat} {expected result : Value}
    (lookup : environment[index]? = some expected)
    (evaluated : Evaluates environment before (.var index) result after) : result = expected ∧ after = before := by
  cases evaluated with
  | var actual => exact ⟨(Option.some.inj (lookup.symm.trans actual)).symm, rfl⟩

theorem load_completed {environment : Environment} {before after : Store}
    {index target : Nat} {type : Ty} {result : Value}
    (lookup : environment[index]? = some (.cellRef type target))
    (evaluated : Evaluates environment before (.loadCell (.var index)) result after) :
    before.read? target = some result ∧ after = before := by
  cases evaluated with
  | loadCell reference read =>
    obtain ⟨same, rfl⟩ := var_completed lookup reference
    cases same
    exact ⟨read, rfl⟩

/-- The original lazy-read code either keeps its present payload or writes the
quoted empty value to that same cell. The original write determines the final
store, including all unrelated and administrative cells. -/
theorem read_completed {environment : Environment} {before after : Store}
    {index target : Nat} {type : Ty} {optional empty result : Value} {literal : Expr}
    (lookup : environment[index]? = some (.cellRef type target))
    (read : before.read? target = some optional) (quoted : Quoted empty literal)
    (evaluated : Evaluates environment before
      (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal) result after) :
    (∃ annotation payload, optional = .inRight annotation payload ∧ result = .inRight .word payload ∧ after = before) ∨
    (∃ annotation payload, optional = .inLeft annotation payload ∧ result = .inRight .word empty ∧
      before.write? target (.inRight .unit empty) = some after) := by
  unfold SourceCoreCompatibleDataExpressions.readMapping at evaluated
  simp only [quoted.weaken 0] at evaluated
  cases evaluated with
  | letE reference branch =>
    obtain ⟨rfl, rfl⟩ := var_completed lookup reference
    cases branch with
    | caseRight loaded branch =>
      obtain ⟨actualRead, rfl⟩ := load_completed (by rfl) loaded
      cases branch with
      | inRight payload =>
        obtain ⟨rfl, rfl⟩ := var_completed (by rfl) payload
        exact .inl ⟨_, _, Option.some.inj (read.symm.trans actualRead), rfl, rfl⟩
    | caseLeft loaded branch =>
      obtain ⟨actualRead, rfl⟩ := load_completed (by rfl) loaded
      cases branch with
      | letE literalEvaluation writeAndResult =>
        obtain ⟨rfl, rfl⟩ := quoted_completed quoted literalEvaluation
        cases writeAndResult with
        | letE written completed =>
          cases written with
          | storeCell reference _ stored write =>
            obtain ⟨same, rfl⟩ := var_completed (by rfl) reference
            cases same
            cases stored with
            | inRight payload =>
              obtain ⟨rfl, rfl⟩ := var_completed (by rfl) payload
              cases completed with
              | inRight payload =>
                obtain ⟨rfl, rfl⟩ := var_completed (by rfl) payload
                exact .inr ⟨_, _, Option.some.inj (read.symm.trans actualRead), rfl, write⟩

theorem quoted_rename {native : Value} {literal : Expr} (quoted : Quoted native literal) (ξ : Renaming) :
    literal.rename ξ = literal := by
  induction quoted generalizing ξ <;> simp_all [Expr.rename]

theorem mapping_rename {native : Value} {literal : Expr} (quoted : Quoted native literal)
    (index : Nat) (ξ : Renaming) :
    (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal).rename ξ =
      SourceCoreCompatibleDataExpressions.readMapping (.var (ξ index)) literal := by
  simp only [SourceCoreCompatibleDataExpressions.readMapping, quoted.weaken 0]
  simp only [Expr.rename, quoted_rename quoted, Renaming.lift, LanguageResult.success]

theorem cells_write_exists {cells : List Dynamic.Cell} {index : Nat} {cell : Dynamic.Cell}
    (found : Dynamic.Heap.CellAt cells index cell) (value : Dynamic.Value) : ∃ updated,
      Dynamic.Heap.CellsWrite cells index {cell with value := some value} updated := by
  induction found with
  | head => exact ⟨_, .head⟩
  | tail _ ih => obtain ⟨updated, written⟩ := ih; exact ⟨_, .tail written⟩

theorem writes_exists {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads heap location cell) (value : Dynamic.Value) :
    ∃ after, Dynamic.Heap.Writes heap location (some value) after := by
  cases read with
  | intro selected =>
    obtain ⟨updated, written⟩ := cells_write_exists selected value
    exact ⟨⟨updated⟩, .intro (.intro selected) written⟩

theorem ordinary_completed {environment : Environment} {store finalStore : Store}
    {index target : Nat} {type : Ty} {reason : Word} {value optional : Value}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType type) target))
    (read : store.read? target = some optional)
    (evaluated : Evaluates environment store (OptionalCell.read type (.var index) reason) value finalStore) :
    (∃ annotation payload, optional = .inRight annotation payload ∧ value = .inRight .word payload ∧ finalStore = store) ∨
    (∃ annotation payload, optional = .inLeft annotation payload ∧ value = .inLeft type (.word reason) ∧ finalStore = store) := by
  cases evaluated with
  | caseLeft loaded branch =>
    cases loaded with
    | loadCell reference actualRead =>
      cases reference with
      | var actualLookup =>
        have same := Option.some.inj (lookup.symm.trans actualLookup)
        cases same
        have same := Option.some.inj (read.symm.trans actualRead)
        cases branch with
        | inLeft token =>
          cases token
          exact .inr ⟨_, _, same, rfl, rfl⟩
  | caseRight loaded branch =>
    cases loaded with
    | loadCell reference actualRead =>
      cases reference with
      | var actualLookup =>
        have same := Option.some.inj (lookup.symm.trans actualLookup)
        cases same
        have same := Option.some.inj (read.symm.trans actualRead)
        cases branch with
        | inRight payload =>
          cases payload with
          | var samePayload =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at samePayload
            cases samePayload
            exact .inl ⟨_, _, same, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCompletion

namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionReadCompletion

/-- Mapping completion constructs only the actual raw source rule and its full
heap relation; callers choose their ordinary or staged outer constructor. -/
theorem Certificate.mapping_completed {fuel : Nat} {context : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel context source scope id reason code)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (program : Program) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (binding : StaticBinding certificate sourceContext)
    (declaredMapping : ∃ key value, certificate.declared.scheme.body = .mapping key value)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog context.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap sourceContext.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {faults : FunctionCalls.FaultRep}
    {result : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) result finalStore) :
    ∃ sourceValue after,
      Dynamic.ExpressionFormEvaluates program sourceContext evidence source environment heap
        certificate.node.form [] [] sourceValue after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults (.value sourceValue) result ∧
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
  cases emitted with
  | ordinary notMapping => exact False.elim (notMapping declaredMapping)
  | @mapping key value literal declaredType generated =>
    obtain ⟨empty, encodedType, quoted, emptyRep⟩ := generated.represents functions extension (.mapping .empty) mapping world
    rw [mapping_rename quoted] at evaluation
    have completed := read_completed (agrees nativeLookup) nativeRead quoted evaluation
    cases represented with
    | initialized payload =>
      dsimp only at cellType
      rcases completed with ⟨_, _, sameOptional, sameValue, sameStore⟩ | ⟨_, _, impossible, _⟩
      · cases sameOptional
        subst result finalStore
        exact ⟨_, heap, form ▸ .local rfl lookup read rfl rfl,
          .value (.compatible (by simpa only [← cellType] using occurrence) payload), heaps, .refl _ _, .refl _⟩
      · cases impossible
    | @uninitialized sourceType _ projected =>
      change sourceType = declared.scheme.body at cellType
      have same : encodedType = type := Except.ok.inj (emptyRep.projection.symm.trans (cellType ▸ projected))
      subst encodedType
      rcases completed with ⟨_, _, impossible, _⟩ | ⟨_, _, sameOptional, sameValue, originalWritten⟩
      · cases impossible
      · cases sameOptional
        subst result
        obtain ⟨after, written⟩ := writes_exists read (.mapping _ _ [])
        have cellPayload : ValueRep context.checked registry functions mapping world sourceType (.mapping _ _ []) empty type :=
          cellType.symm ▸ emptyRep
        obtain ⟨updated, nativeWritten, finalHeaps, frame⟩ := heaps.write_initialized reference read cellPayload written
        have sameStore := Option.some.inj (nativeWritten.symm.trans originalWritten)
        cases sameStore
        exact ⟨_, after, form ▸ .localEmptyMapping rfl lookup read rfl (cellType.trans declaredType) rfl written,
          .value (.compatible (cellType ▸ occurrence) cellPayload), finalHeaps, frame, .of_write written⟩

/-- Every completed accepted local read determines its independent source outcome. -/
theorem Certificate.completed_with_diagnostics {fuel : Nat} {context : ValuesContext} {source : TypedSource}
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
    {faults : FunctionCalls.FaultRep} (uninitialized : UninitializedPolicy certificate sourceContext environment heap faults)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  by_cases declaredMapping : ∃ key value, certificate.declared.scheme.body = .mapping key value
  · obtain ⟨sourceValue, after, raw, represented, finalHeaps, frame, metadata⟩ :=
      certificate.mapping_completed functions extension program sourceContext evidence binding declaredMapping
        environments heaps locals agrees evaluation
    refine ⟨.value sourceValue, after, .value (.intro (middle := after) (raw := sourceValue) (lookupExpression?_sound certificate.metadata.found) ?_ ?_),
      represented, finalHeaps, frame, metadata⟩
    · simpa only [certificate.metadata.requirements, certificate.metadata.coercions] using raw
    · rw [certificate.metadata.coercions]; exact .nil
  · rcases certificate with ⟨node, type, binder, name, declared, index, metadata, form, binderOwner, slot, declaration, emitted⟩
    rcases binding with ⟨declaredScope, occurrence⟩
    dsimp only at *
    cases emitted with
    | mapping declaredType generated => exact False.elim (declaredMapping ⟨_, _, declaredType⟩)
    | ordinary _ =>
      obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup declaredScope
      obtain ⟨target, selected, optional, nativeLookup, reference, selectedRead, nativeRead, represented⟩ :=
        GenericHeap.lookup_visible environments heaps lookup slot
      have sameCell := read.functional selectedRead
      subst selected
      have ordinary := represented.ordinary
      have result := ordinary_completed (agrees nativeLookup) nativeRead evaluation
      have contains := lookupExpression?_sound metadata.found
      cases represented with
      | @initialized sourceType _ sourceValue nativeValue payload =>
        dsimp only at cellType
        rcases result with ⟨_, native, sameOptional, sameValue, sameStore⟩ | ⟨_, _, impossible, _⟩
        · cases sameOptional
          subst value finalStore
          refine ⟨.value _, heap, .value (.intro (middle := heap) (raw := sourceValue) contains ?_ ?_),
            .value (.compatible (by simpa only [← cellType] using occurrence) payload), heaps, .refl _ _, .refl _⟩
          · rw [form, metadata.requirements, metadata.coercions]
            exact .local rfl lookup read ordinary rfl
          · rw [metadata.coercions]; exact .nil
        · cases impossible
      | uninitialized projected =>
        dsimp only at cellType
        rcases result with ⟨_, _, impossible, _⟩ | ⟨_, _, _, sameValue, sameStore⟩
        · cases impossible
        · subst value finalStore
          refine ⟨.fault (.uninitializedLocation location), heap, .fault (.form contains ?_),
            .fault (uninitialized location _ ⟨contains, form, declaredScope, occurrence, lookup, read,
              cellType, ordinary, rfl, by simpa only [cellType] using declaredMapping⟩), heaps, .refl _ _, .refl _⟩
          rw [form, metadata.requirements, metadata.coercions]
          exact .localUninitialized (owned := []) rfl lookup read ordinary rfl (by simpa only [cellType] using declaredMapping)

/-- The original uniform inclusion supplies the policy at its actual witness. -/
theorem Certificate.completed {fuel : Nat} {context : ValuesContext} {source : TypedSource}
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
    {faults : FunctionCalls.FaultRep} (uninitialized : ∀ location, faults (.uninitializedLocation location) reason)
    {value : Value} {finalStore : Store} (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after,
      Dynamic.ExpressionEvaluatesOutcome program sourceContext evidence source environment heap id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel context.checked registry functions)
        mapping world certificate.node.type certificate.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents context.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  exact certificate.completed_with_diagnostics functions extension program sourceContext evidence binding
    environments heaps locals agrees (fun location _ _ => uninitialized location) evaluation

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
