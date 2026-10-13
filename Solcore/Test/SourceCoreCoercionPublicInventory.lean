import Solcore.Test.SourceCoreCoercionPublicFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootCoverage
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure OrdinaryInventory (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled
  makeInput : Input fixture.recipe.compiled
  makeSame : makeInput.row = observed.makeRow.row
  makePacket : Issued makeInput
  makeRetained : Inventory.HasRow makePacket catalog.rows
  makeHeader : ActualHeader fixture observed.makeRow.row
  makeAligned : makeHeader.header = makePacket.header
  makeSlot : makeHeader.header.slot = observed.makeRow.index
  makeSignature : makeHeader.header.named.signature = observed.makeRow.global
  useInput : Input fixture.recipe.compiled
  useSame : useInput.row = observed.useRow.row
  usePacket : Issued useInput
  useRetained : Inventory.HasRow usePacket catalog.rows
  useHeader : ActualHeader fixture observed.useRow.row
  useAligned : useHeader.header = usePacket.header
  useSlot : useHeader.header.slot = observed.useRow.index
  useSignature : useHeader.header.named.signature = observed.useRow.global
  keepInput : Input fixture.recipe.compiled
  keepSame : keepInput.row = observed.keepRow.row
  keepPacket : Issued keepInput
  keepRetained : Inventory.HasRow keepPacket catalog.rows
  keepHeader : ActualHeader fixture observed.keepRow.row
  keepAligned : keepHeader.header = keepPacket.header
  keepSlot : keepHeader.header.slot = observed.keepRow.index
  keepSignature : keepHeader.header.named.signature = observed.keepRow.global

def OrdinaryInventory.rows {fixture observed} (given : OrdinaryInventory fixture observed) :
    Inventory [given.makeInput, given.useInput, given.keepInput] :=
  .cons given.makePacket (.cons given.usePacket (.cons given.keepPacket .nil))

theorem ordinary_inventory (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (OrdinaryInventory fixture observed) := by
  obtain ⟨catalog⟩ := CallableIndexedOwnedPreparedOrdinaryCatalog.of_compiled fixture.recipe.compiled fixture.source_wellFormed
  obtain ⟨makeInput, makeSame, makePacket, makeRetained, makeHeader, makeAligned, makeSlot, makeSignature⟩ := observed.makeRow.issue_at catalog
  obtain ⟨useInput, useSame, usePacket, useRetained, useHeader, useAligned, useSlot, useSignature⟩ := observed.useRow.issue_at catalog
  obtain ⟨keepInput, keepSame, keepPacket, keepRetained, keepHeader, keepAligned, keepSlot, keepSignature⟩ := observed.keepRow.issue_at catalog
  exact ⟨{catalog, makeInput, makeSame, makePacket, makeRetained, makeHeader, makeAligned, makeSlot, makeSignature, useInput, useSame, usePacket, useRetained, useHeader, useAligned, useSlot, useSignature, keepInput, keepSame, keepPacket, keepRetained, keepHeader, keepAligned, keepSlot, keepSignature}⟩

theorem OrdinaryInventory.make_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.makeHeader.header ∈ headers given.rows := by
  rw [given.makeAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.use_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.useHeader.header ∈ headers given.rows := by
  rw [given.useAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.keep_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.keepHeader.header ∈ headers given.rows := by
  rw [given.keepAligned]
  simp [OrdinaryInventory.rows, headers]

/-- Actual instantiation metadata selects one exact ordinary row even while
other physical slots contain implementation methods. -/
theorem ObservedRow.direct_slot {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {reasonAt : ExpressionId → Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body fuel
      compilation values source scope id callee ids instantiation reasonAt lowered)
    (plan : compilation.plan = fixture.recipe.compiled.indexed.base.plan)
    (globals : compilation.globals = fixture.recipe.compiled.indexed.base.globals)
    (metadata : instantiation = CallableNamedCanonicalOrder.retainedInstantiation observed.row) :
    receipt.signature = observed.global ∧ receipt.index = observed.index := by
  have target := receipt.target
  simp only [plan, metadata, observed.target] at target
  have key := Except.ok.inj target
  have found := receipt.global
  rw [globals] at found
  have member : (receipt.signature, receipt.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = observed.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr found, ?_⟩
    simp only [observed.globalKey, key, decide_true]
  rw [observed.slot] at member
  exact Prod.mk.inj (List.mem_singleton.mp member)

theorem ObservedRow.global_slot {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) {index : Nat} {global : SourceCoreCalls.Signature}
    (found : fixture.recipe.compiled.indexed.base.globals[index]? = some global)
    (key : global.key = observed.row.key) : global = observed.global ∧ index = observed.index := by
  have member : (global, index) ∈ fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
      (fun item => decide (item.1.key = observed.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr found, ?_⟩
    simp only [observed.globalKey, key, decide_true]
  rw [observed.slot] at member
  exact Prod.mk.inj (List.mem_singleton.mp member)

/-- Both public entries have genuine ordinary Source headers. The separate
physical cache also retains the actual coercion method. -/
theorem OrdinaryInventory.public_coverage {fixture observed}
    (given : OrdinaryInventory fixture observed) :
    RecursiveNamedPublicRootCoverage.Coverage
      (compiled := fixture.recipe.compiled)
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (headers given.rows) := by
  intro entry member named slot found
  have entryKey : entry.key ∈ [observed.makeRow.row.key, observed.useRow.row.key] := by
    rw [← observed.entryKeys]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have namedKey : named.signature.key = entry.key := of_decide_eq_true (List.find?_some (p := fun item : SourceCoreGeneralFunctions.Function × Nat => decide (item.1.signature.key = entry.key)) found)
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled
    (List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at entryKey
  rcases entryKey with same | same
  · have slots := observed.makeRow.global_slot selected (namedKey.trans same)
    exact ⟨given.makeHeader.header, given.make_member, given.makeSlot.trans slots.2.symm⟩
  · have slots := observed.useRow.global_slot selected (namedKey.trans same)
    exact ⟨given.useHeader.header, given.use_member, given.useSlot.trans slots.2.symm⟩

end Tests.SourceCoreCoercionPublic
