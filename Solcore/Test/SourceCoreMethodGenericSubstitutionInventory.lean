import Solcore.Test.SourceCoreMethodGenericSubstitutionFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootCoverage
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodGenericSubstitution
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure OrdinaryInventory (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  wordInput : Input fixture.recipe.compiled
  wordSame : wordInput.row = observed.wordRow.row
  wordPacket : Issued wordInput
  wordHeader : ActualHeader fixture observed.wordRow.row
  wordAligned : wordHeader.header = wordPacket.header
  wordSlot : wordHeader.header.slot = observed.wordRow.index
  wordSignature : wordHeader.header.named.signature = observed.wordRow.global
  boolInput : Input fixture.recipe.compiled
  boolSame : boolInput.row = observed.boolRow.row
  boolPacket : Issued boolInput
  boolHeader : ActualHeader fixture observed.boolRow.row
  boolAligned : boolHeader.header = boolPacket.header
  boolSlot : boolHeader.header.slot = observed.boolRow.index
  boolSignature : boolHeader.header.named.signature = observed.boolRow.global
  makeWordInput : Input fixture.recipe.compiled
  makeWordSame : makeWordInput.row = observed.makeWordRow.row
  makeWordPacket : Issued makeWordInput
  makeWordHeader : ActualHeader fixture observed.makeWordRow.row
  makeWordAligned : makeWordHeader.header = makeWordPacket.header
  makeWordSlot : makeWordHeader.header.slot = observed.makeWordRow.index
  makeWordSignature : makeWordHeader.header.named.signature = observed.makeWordRow.global
  makeBoolInput : Input fixture.recipe.compiled
  makeBoolSame : makeBoolInput.row = observed.makeBoolRow.row
  makeBoolPacket : Issued makeBoolInput
  makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row
  makeBoolAligned : makeBoolHeader.header = makeBoolPacket.header
  makeBoolSlot : makeBoolHeader.header.slot = observed.makeBoolRow.index
  makeBoolSignature : makeBoolHeader.header.named.signature = observed.makeBoolRow.global
  relayWordInput : Input fixture.recipe.compiled
  relayWordSame : relayWordInput.row = observed.relayWordRow.row
  relayWordPacket : Issued relayWordInput
  relayWordHeader : ActualHeader fixture observed.relayWordRow.row
  relayWordAligned : relayWordHeader.header = relayWordPacket.header
  relayWordSlot : relayWordHeader.header.slot = observed.relayWordRow.index
  relayWordSignature : relayWordHeader.header.named.signature = observed.relayWordRow.global
  relayBoolInput : Input fixture.recipe.compiled
  relayBoolSame : relayBoolInput.row = observed.relayBoolRow.row
  relayBoolPacket : Issued relayBoolInput
  relayBoolHeader : ActualHeader fixture observed.relayBoolRow.row
  relayBoolAligned : relayBoolHeader.header = relayBoolPacket.header
  relayBoolSlot : relayBoolHeader.header.slot = observed.relayBoolRow.index
  relayBoolSignature : relayBoolHeader.header.named.signature = observed.relayBoolRow.global
  useWordInput : Input fixture.recipe.compiled
  useWordSame : useWordInput.row = observed.useWordRow.row
  useWordPacket : Issued useWordInput
  useWordHeader : ActualHeader fixture observed.useWordRow.row
  useWordAligned : useWordHeader.header = useWordPacket.header
  useWordSlot : useWordHeader.header.slot = observed.useWordRow.index
  useWordSignature : useWordHeader.header.named.signature = observed.useWordRow.global
  useBoolInput : Input fixture.recipe.compiled
  useBoolSame : useBoolInput.row = observed.useBoolRow.row
  useBoolPacket : Issued useBoolInput
  useBoolHeader : ActualHeader fixture observed.useBoolRow.row
  useBoolAligned : useBoolHeader.header = useBoolPacket.header
  useBoolSlot : useBoolHeader.header.slot = observed.useBoolRow.index
  useBoolSignature : useBoolHeader.header.named.signature = observed.useBoolRow.global
  identityWordInput : Input fixture.recipe.compiled
  identityWordSame : identityWordInput.row = observed.identityWordRow.row
  identityWordPacket : Issued identityWordInput
  identityWordHeader : ActualHeader fixture observed.identityWordRow.row
  identityWordAligned : identityWordHeader.header = identityWordPacket.header
  identityWordSlot : identityWordHeader.header.slot = observed.identityWordRow.index
  identityWordSignature : identityWordHeader.header.named.signature = observed.identityWordRow.global
  identityBoolInput : Input fixture.recipe.compiled
  identityBoolSame : identityBoolInput.row = observed.identityBoolRow.row
  identityBoolPacket : Issued identityBoolInput
  identityBoolHeader : ActualHeader fixture observed.identityBoolRow.row
  identityBoolAligned : identityBoolHeader.header = identityBoolPacket.header
  identityBoolSlot : identityBoolHeader.header.slot = observed.identityBoolRow.index
  identityBoolSignature : identityBoolHeader.header.named.signature = observed.identityBoolRow.global

def OrdinaryInventory.rows {fixture observed} (given : OrdinaryInventory fixture observed) :
    Inventory [given.wordInput, given.boolInput, given.makeWordInput, given.makeBoolInput, given.relayWordInput, given.relayBoolInput, given.useWordInput, given.useBoolInput, given.identityWordInput, given.identityBoolInput] :=
  .cons given.wordPacket (.cons given.boolPacket (.cons given.makeWordPacket (.cons given.makeBoolPacket (.cons given.relayWordPacket (.cons given.relayBoolPacket (.cons given.useWordPacket (.cons given.useBoolPacket (.cons given.identityWordPacket (.cons given.identityBoolPacket (.nil))))))))))

theorem ordinary_inventory (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (OrdinaryInventory fixture observed) := by
  obtain ⟨wordInput, wordSame, wordPacket, wordHeader, wordAligned, wordSlot, wordSignature⟩ := observed.wordRow.issue
  obtain ⟨boolInput, boolSame, boolPacket, boolHeader, boolAligned, boolSlot, boolSignature⟩ := observed.boolRow.issue
  obtain ⟨makeWordInput, makeWordSame, makeWordPacket, makeWordHeader, makeWordAligned, makeWordSlot, makeWordSignature⟩ := observed.makeWordRow.issue
  obtain ⟨makeBoolInput, makeBoolSame, makeBoolPacket, makeBoolHeader, makeBoolAligned, makeBoolSlot, makeBoolSignature⟩ := observed.makeBoolRow.issue
  obtain ⟨relayWordInput, relayWordSame, relayWordPacket, relayWordHeader, relayWordAligned, relayWordSlot, relayWordSignature⟩ := observed.relayWordRow.issue
  obtain ⟨relayBoolInput, relayBoolSame, relayBoolPacket, relayBoolHeader, relayBoolAligned, relayBoolSlot, relayBoolSignature⟩ := observed.relayBoolRow.issue
  obtain ⟨useWordInput, useWordSame, useWordPacket, useWordHeader, useWordAligned, useWordSlot, useWordSignature⟩ := observed.useWordRow.issue
  obtain ⟨useBoolInput, useBoolSame, useBoolPacket, useBoolHeader, useBoolAligned, useBoolSlot, useBoolSignature⟩ := observed.useBoolRow.issue
  obtain ⟨identityWordInput, identityWordSame, identityWordPacket, identityWordHeader, identityWordAligned, identityWordSlot, identityWordSignature⟩ := observed.identityWordRow.issue
  obtain ⟨identityBoolInput, identityBoolSame, identityBoolPacket, identityBoolHeader, identityBoolAligned, identityBoolSlot, identityBoolSignature⟩ := observed.identityBoolRow.issue
  exact ⟨{wordInput, wordSame, wordPacket, wordHeader, wordAligned, wordSlot, wordSignature, boolInput, boolSame, boolPacket, boolHeader, boolAligned, boolSlot, boolSignature, makeWordInput, makeWordSame, makeWordPacket, makeWordHeader, makeWordAligned, makeWordSlot, makeWordSignature, makeBoolInput, makeBoolSame, makeBoolPacket, makeBoolHeader, makeBoolAligned, makeBoolSlot, makeBoolSignature, relayWordInput, relayWordSame, relayWordPacket, relayWordHeader, relayWordAligned, relayWordSlot, relayWordSignature, relayBoolInput, relayBoolSame, relayBoolPacket, relayBoolHeader, relayBoolAligned, relayBoolSlot, relayBoolSignature, useWordInput, useWordSame, useWordPacket, useWordHeader, useWordAligned, useWordSlot, useWordSignature, useBoolInput, useBoolSame, useBoolPacket, useBoolHeader, useBoolAligned, useBoolSlot, useBoolSignature, identityWordInput, identityWordSame, identityWordPacket, identityWordHeader, identityWordAligned, identityWordSlot, identityWordSignature, identityBoolInput, identityBoolSame, identityBoolPacket, identityBoolHeader, identityBoolAligned, identityBoolSlot, identityBoolSignature}⟩

theorem OrdinaryInventory.word_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.wordHeader.header ∈ headers given.rows := by
  rw [given.wordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.bool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.boolHeader.header ∈ headers given.rows := by
  rw [given.boolAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.makeWord_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.makeWordHeader.header ∈ headers given.rows := by
  rw [given.makeWordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.makeBool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.makeBoolHeader.header ∈ headers given.rows := by
  rw [given.makeBoolAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.relayWord_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.relayWordHeader.header ∈ headers given.rows := by
  rw [given.relayWordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.relayBool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.relayBoolHeader.header ∈ headers given.rows := by
  rw [given.relayBoolAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.useWord_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.useWordHeader.header ∈ headers given.rows := by
  rw [given.useWordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.useBool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.useBoolHeader.header ∈ headers given.rows := by
  rw [given.useBoolAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.identityWord_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.identityWordHeader.header ∈ headers given.rows := by
  rw [given.identityWordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.identityBool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.identityBoolHeader.header ∈ headers given.rows := by
  rw [given.identityBoolAligned]
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

/-- The four actual public entries are covered by their ordinary Source
headers; the complete physical cache separately retains both method slots. -/
theorem OrdinaryInventory.public_coverage {fixture observed}
    (given : OrdinaryInventory fixture observed) :
    RecursiveNamedPublicRootCoverage.Coverage
      (compiled := fixture.recipe.compiled)
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (headers given.rows) := by
  intro entry member named slot found
  have entryKey : entry.key ∈ [observed.wordRow.row.key, observed.boolRow.row.key,
      observed.useWordRow.row.key, observed.useBoolRow.row.key] := by
    rw [← observed.entryKeys]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have namedKey : named.signature.key = entry.key := of_decide_eq_true (List.find?_some (p := fun item : SourceCoreGeneralFunctions.Function × Nat => decide (item.1.signature.key = entry.key)) found)
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled
    (List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at entryKey
  rcases entryKey with same | same | same | same
  · have slots := observed.wordRow.global_slot selected (namedKey.trans same)
    exact ⟨given.wordHeader.header, given.word_member, given.wordSlot.trans slots.2.symm⟩
  · have slots := observed.boolRow.global_slot selected (namedKey.trans same)
    exact ⟨given.boolHeader.header, given.bool_member, given.boolSlot.trans slots.2.symm⟩
  · have slots := observed.useWordRow.global_slot selected (namedKey.trans same)
    exact ⟨given.useWordHeader.header, given.useWord_member, given.useWordSlot.trans slots.2.symm⟩
  · have slots := observed.useBoolRow.global_slot selected (namedKey.trans same)
    exact ⟨given.useBoolHeader.header, given.useBool_member, given.useBoolSlot.trans slots.2.symm⟩

end Tests.SourceCoreMethodGenericSubstitution
