import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues

/-!
# Prepared callables: the ordinary catalog

The finite ordinary catalog, its receipts, admission and syntax table, and contextual formation.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCachedInputs
/-! Actual final cached ordinary rows supply their retained target and unique
physical slot. Source range and ordinary staging admission remain independent;
no Header, execution, or body correspondence is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCachedInputs
open Core Frontend SourceInference TypeSystem
open RecursiveNamedPublicSpecializationMeaning (Origin Prepared)
open CallablePreparedFinalCatalogOrigins (CatalogOrigin)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input)

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) :
    ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

private theorem prepared_key {program : CheckedProgram}
    {representation : SourceCoreGeneralFunctions.Representation}
    {row : SourceSpecialization.SpecializedFunction}
    {named : SourceCoreGeneralFunctions.Function}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation
      program representation row = .ok named) : named.signature.key = row.key := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (row.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged] at accepted
    cases shape : row.function.type <;>
      simp only [shape, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
        bind, Except.bind] at accepted <;> try contradiction
    rename_i parameter result
    by_cases mismatch : result ≠ row.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      cases accepted
      rfl

private theorem specialization_key {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok row) :
    row.key = ⟨row.declaration, row.parameterSubstitution.map Prod.snd⟩ := by
  unfold SourceSpecialization.specializeFunction at accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction
      (SourceSpecialization.applyCheckedFunction canonical generic) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
      simp only [analysis, pure, Except.pure, bind, Except.bind,
        Except.ok.injEq] at accepted
      subst row
      rfl

/-- The original second-pass hook authenticates this complete cached record. -/
theorem cached_record (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      named.signature.key = .ok named.specialized := by
  obtain ⟨_, _, _, ⟨compilation⟩⟩ :=
    CallableIndexedNamedGeneration.compiled_at compiled.indexed selected
  exact CallableIndexedActualNamedSourceReceipts.cached_record compiled selected compilation.hook

private theorem cached_position (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    compiled.indexed.base.plan.specializations.reverse[index]? = some named.specialized ∧
      named.signature.key = named.specialized.key := by
  obtain ⟨row, found, prepared⟩ :=
    RecursiveNamedPreparedParameterProjections.cached_preparation compiled selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs prepared).1
  refine ⟨?_, (prepared_key prepared).trans (congrArg (·.key) same.symm)⟩
  rw [CallableIndexedPreparedInventories.indexed_base compiled.indexedPrepared]
  simpa only [same] using found

private theorem filter_key {α β : Type} [DecidableEq β]
    (key : α → β) {items : List α} (unique : (items.map key).Nodup)
    {item : α} (member : item ∈ items) :
    items.filter (fun candidate => decide (key candidate = key item)) = [item] := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | member
      · subst item
        have empty : tail.filter (fun candidate => decide (key candidate = key head)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro candidate found
          simp only [decide_eq_true_eq]
          intro same
          exact absent (List.mem_map.mpr ⟨candidate, found, same⟩)
        simp [empty]
      · have different : key head ≠ key item := by
          intro same
          exact absent (List.mem_map.mpr ⟨item, member, same.symm⟩)
        simpa [different] using ih tailUnique member

private theorem substitution_self {substitution : ParameterSubstitution}
    (unique : (substitution.map Prod.fst).Nodup) :
    SourceCompilationPlan.parameterSubstitutionsEquivalent substitution substitution = true := by
  have each : ∀ entry ∈ substitution,
      SourceCompilationPlan.exactParameterBinding? substitution entry.1 = some entry.2 := by
    intro entry member
    have one := filter_key Prod.fst unique member
    have same : (fun candidate : TypeParameterId × TypeSystem.Ty => candidate.1 == entry.1) =
        (fun candidate => decide (candidate.1 = entry.1)) := by
      funext candidate
      exact Bool.eq_iff_iff.mpr (by simp)
    simp only [SourceCompilationPlan.exactParameterBinding?, same, one]
  simp only [SourceCompilationPlan.parameterSubstitutionsEquivalent, beq_self_eq_true,
    Bool.true_and, Bool.and_self]
  exact List.all_eq_true.mpr (fun entry member => by rw [each entry member]; simp)

private theorem function_impl_ne {program : CheckedProgram}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    {implementation : ProgramImplementationSignature}
    (implMember : implementation ∈ program.signatures.implementations) :
    signature.id ≠ implementation.id := by
  have unique := wellFormed.signatures.declaration_ids
  simp only [signatureDeclarationIds] at unique
  have separated := (List.nodup_append.mp (List.nodup_append.mp unique).1).2.2
  apply separated signature.id
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨signature, member, rfl⟩)))
    implementation.id (List.mem_map.mpr ⟨implementation, implMember, rfl⟩)

/-- A final row naming a real function signature is an ordinary request even
when it was discovered below an implementation-method root. -/
theorem ordinary_origin (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.indexed.base.plan.specializations)
    {signature : ProgramFunctionSignature}
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (declaration : row.declaration = signature.id) : Origin compiled.sourceProgram row := by
  have tagged := CallablePreparedFinalCatalogOrigins.of_default_preparation
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) row member
  cases tagged with
  | ordinary origin => exact origin
  | method selected =>
      have identities := RecursiveNamedSpecializationBodyFacts.identities selected.specialized
      have owner := identities.2.2.trans identities.1.symm
      exact False.elim (function_impl_ne wellFormed signatureMember selected.implementationMember
        (declaration.symm.trans owner))

private theorem origin_signature {program : CheckedProgram}
    {row : SourceSpecialization.SpecializedFunction} (origin : Origin program row) :
    ∃ signature ∈ program.signatures.functions,
      row.declaration = signature.id ∧
      row.parameterSubstitution.map Prod.fst = signature.scheme.parameters ∧
      row.key = ⟨row.declaration, row.parameterSubstitution.map Prod.snd⟩ ∧
      row.function.declaration = row.declaration ∧
      row.function.typedBody.owner = row.declaration := by
  obtain ⟨request, signature, generic, member, _, _, accepted⟩ := origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have fields := CallableCoercionBodyProvenance.specialization_fields accepted
  refine ⟨signature, member, identities.2.2.trans identities.1.symm,
    SourceSpecialization.specializeFunction_parameterDomain accepted, specialization_key accepted, ?_, ?_⟩
  · rw [fields.1, SourceSpecialization.applyCheckedFunction_declaration, identities.2.2]
  · rw [fields.1, SourceSpecialization.applyCheckedFunction_bodyOwner, identities.2.1, identities.2.2]

private theorem exact_filter {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    plan.specializations.filter (fun candidate => decide (candidate.key = key)) = [row] := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try cases accepted
  assumption

private theorem filter_position_unique {α : Type} {predicate : α → Bool}
    {items : List α} {only left right : α} {first second : Nat}
    (single : items.filter predicate = [only])
    (leftAt : items[first]? = some left) (leftAccepted : predicate left = true)
    (rightAt : items[second]? = some right) (rightAccepted : predicate right = true) :
    first = second := by
  induction items generalizing first second with
  | nil => simp at leftAt
  | cons head tail ih =>
      have absent (headAccepted : predicate head = true) : tail.filter predicate = [] := by
        have tails := congrArg List.tail single
        simpa only [List.filter_cons, headAccepted, ↓reduceIte, List.tail_cons] using tails
      have noTail (headAccepted : predicate head = true) {item : α} {index : Nat}
          (found : tail[index]? = some item) (accepted : predicate item = true) : False := by
        have member := List.mem_filter.mpr ⟨List.mem_of_getElem? found, accepted⟩
        rw [absent headAccepted] at member
        exact List.not_mem_nil member
      cases first with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at leftAt
          subst left
          cases second with
          | zero => rfl
          | succ second => exact False.elim (noTail leftAccepted rightAt rightAccepted)
      | succ first =>
          cases second with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at rightAt
              subst right
              exact False.elim (noTail rightAccepted leftAt leftAccepted)
          | succ second =>
              by_cases headAccepted : predicate head = true
              · exact False.elim (noTail headAccepted leftAt leftAccepted)
              · apply congrArg Nat.succ
                apply ih (by simpa [List.filter_cons, headAccepted] using single)
                  leftAt rightAt

/-- Actual successful preparation preserves the key attached to the full row. -/
theorem cached_key (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    named.signature.key = named.specialized.key := (cached_position compiled selected).2

/-- The physical slot is recovered from the actual two-pass cache and its
unique full specialization lookup, without an independently observed filter. -/
theorem cached_slot (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named) :
    CallableNamedMetadata.Slot compiled.indexed.base.globals index named.signature := by
  have globalAt := CallableIndexedPreparedInventories.cached_global_at compiled selected
  have mainMember := List.mk_mem_zipIdx_iff_getElem?.mpr globalAt
  have unique : (compiled.indexed.base.globals.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  unfold CallableNamedMetadata.Slot
  rw [← filter_key Prod.snd unique mainMember]
  apply List.filter_congr
  intro item member
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro sameKey
    have itemAt := List.mem_zipIdx_iff_getElem?.mp member
    rw [CallableIndexedPreparedInventories.cached_globals, List.getElem?_map] at itemAt
    cases found : compiled.indexed.base.functions[item.2]? with
    | none => simp only [found, Option.map_none] at itemAt; cases itemAt
    | some other =>
        simp only [found, Option.map_some, Option.some.injEq] at itemAt
        have one : compiled.indexed.base.plan.specializations.reverse.filter
            (fun row => decide (row.key = named.signature.key)) = [named.specialized] := by
          rw [List.filter_reverse, exact_filter (cached_record compiled selected)]
          rfl
        exact filter_position_unique one (cached_position compiled found).1
          (by simpa only [decide_eq_true_eq, ← cached_key compiled found, itemAt] using sameKey)
          (cached_position compiled selected).1
          (by simp only [decide_eq_true_eq, cached_key compiled selected])
  · intro sameIndex
    have itemAt := List.mem_zipIdx_iff_getElem?.mp member
    rw [sameIndex, globalAt] at itemAt
    have sameSignature := Option.some.inj itemAt
    exact congrArg (·.key) sameSignature.symm

/-- The retained reverse-order metadata selects precisely the authentic final
ordinary specialization, including all unused replacement rows. -/
theorem retained_target (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (origin : Origin compiled.sourceProgram named.specialized) :
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation named.specialized) = .ok named.signature.key := by
  obtain ⟨signature, signatureMember, declaration, domain, key, functionOwner, sourceOwner⟩ :=
    origin_signature origin
  have domainUnique : (named.specialized.parameterSubstitution.map Prod.fst).Nodup :=
    domain ▸ (wellFormed.signatures.function_parameters signature signatureMember).1
  have selfMatch : SourceCompilationPlan.specializationMatchesInstantiation named.specialized
      (CallableNamedMetadata.instantiation named.specialized) = true := by
    simp [SourceCompilationPlan.specializationMatchesInstantiation,
      SourceCompilationPlan.specializationOwnershipCoherent, CallableNamedMetadata.instantiation,
      key, functionOwner, sourceOwner, decide_true,
      substitution_self domainUnique, Bool.and_self]
  have sameFilter : compiled.indexed.base.plan.specializations.filter
      (fun candidate => SourceCompilationPlan.specializationMatchesInstantiation candidate
        (CallableNamedMetadata.instantiation named.specialized)) = [named.specialized] := by
    rw [← exact_filter (cached_record compiled selected)]
    apply List.filter_congr
    intro candidate member
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro matched
      have matchedFields := CallableNamedMetadata.matches_of_checked matched
      have candidateOrigin := ordinary_origin compiled wellFormed member signatureMember
        (matchedFields.declaration.trans declaration)
      obtain ⟨other, otherMember, otherDeclaration, otherDomain, otherKey, _, _⟩ :=
        origin_signature candidateOrigin
      have sameSignature : other = signature := by
        have unique := wellFormed.signatures.function_ids
        have sameId := otherDeclaration.symm.trans (matchedFields.declaration.trans declaration)
        have retained : other ∈ compiled.sourceProgram.signatures.functions.filter
            (fun candidate => decide (candidate.id = signature.id)) :=
          List.mem_filter.mpr ⟨otherMember, by simpa using sameId⟩
        rw [filter_key (·.id) unique signatureMember] at retained
        exact List.mem_singleton.mp retained
      subst other
      have sameSubstitution := CallableNamedMetadata.substitution_eq_of_domain
        matchedFields.substitution (otherDomain.trans domain.symm)
      simp only [decide_eq_true_eq]
      rw [otherKey, matchedFields.declaration, sameSubstitution]
      change (⟨named.specialized.declaration, named.specialized.parameterSubstitution.map Prod.snd⟩ :
        SourceCompilationPlan.Key) = named.signature.key
      rw [← key, cached_key compiled selected]
    · intro accepted
      have sameKey : candidate.key = named.signature.key := of_decide_eq_true accepted
      have retained : candidate ∈ compiled.indexed.base.plan.specializations.filter
          (fun row => decide (row.key = named.signature.key)) :=
        List.mem_filter.mpr ⟨member, by simpa using sameKey⟩
      rw [exact_filter (cached_record compiled selected)] at retained
      have same : candidate = named.specialized := List.mem_singleton.mp retained
      simpa only [same] using selfMatch
  change SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
    (CallableNamedReversal.instantiation (CallableNamedMetadata.instantiation named.specialized)) = _
  rw [CallableNamedReversal.target_reverse]
  simp only [SourceCompilationPlan.exactInstantiationKey, sameFilter, cached_key compiled selected]

/-- Preserve the selected final index and named row when preparing its original
ordinary Source receipt. The accepted final plan supplies the complete dictionary. -/
theorem of_cached_origin_at (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    (origin : Origin compiled.sourceProgram row) :
    ∃ prepared : Prepared compiled row, prepared.index = index ∧ prepared.named = named := by
  obtain ⟨diagnostics, code, cached, ⟨compilation⟩⟩ :=
    CallableIndexedNamedGeneration.compiled_at compiled.indexed selected
  have preparation := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled
  obtain ⟨_growth, covered⟩ := CallableCoercionPreparation.of_accepted preparation
  obtain ⟨available, resolved, _sites⟩ := covered row
    (RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected same)
  exact ⟨⟨index, named, diagnostics, code, compilation, available,
    selected, same, cached, origin, resolved⟩, rfl, rfl⟩

/-- Every eligible actual cached row supplies an inventory Input with that
exact row, index and named function. Range and staging admission are the only
additional static checks; target, slot and dictionary are derived here. -/
theorem of_cached (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (origin : Origin compiled.sourceProgram named.specialized)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) named.specialized.parameterSubstitution)
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ named.specialized.function.typedBody.inputs →
      binder.comptime = false) :
    ∃ input : Input compiled, input.row = named.specialized ∧
      input.prepared.index = index ∧ input.prepared.named = named := by
  obtain ⟨prepared, indexEq, namedEq⟩ := of_cached_origin_at compiled selected rfl origin
  let input : Input compiled := {
    row := named.specialized
    prepared := prepared
    range := range
    ordinaryReturn := ordinaryReturn
    ordinaryParameters := ordinaryParameters
    target := by rw [namedEq]; exact retained_target compiled wellFormed selected origin
    slot := by rw [indexEq, namedEq]; exact cached_slot compiled selected }
  exact ⟨input, rfl, indexEq, namedEq⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCachedInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
/-! A finite ordinary catalog retains every admitted actual cache position.
Admission uses original Source origin, complete replacement ranges and stage
markers. Physical cache positions are preserved when other rows are omitted. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)

structure Eligible (compiled : SourceCoreUnifiedCompilation.Compiled)
    (row : SourceSpecialization.SpecializedFunction) : Prop where
  origin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram row
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution
  ordinaryReturn : row.function.returnComptime = false
  ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false

structure Catalog (compiled : SourceCoreUnifiedCompilation.Compiled) where
  inputs : List (Input compiled)
  rows : Inventory inputs
  distinct : (inputs.map (fun input => input.prepared.index)).Nodup
  admitted : ∀ input ∈ inputs, Eligible compiled input.row
  covered : ∀ index named, compiled.indexed.base.functions[index]? = some named →
    Eligible compiled named.specialized →
    ∃ input ∈ inputs, input.prepared.index = index ∧ input.prepared.named = named

theorem Catalog.packet_at {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled) {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (eligible : Eligible compiled named.specialized) :
    ∃ input : Input compiled, ∃ packet : Issued input,
      Inventory.HasRow packet catalog.rows ∧ input.row = named.specialized ∧
      input.prepared.index = index ∧ input.prepared.named = named := by
  obtain ⟨input, member, slot, same⟩ := catalog.covered index named selected eligible
  obtain ⟨packet, retained⟩ := catalog.rows.row_at input member
  exact ⟨input, packet, retained, input.prepared.same.symm.trans (congrArg (·.specialized) same), slot, same⟩

theorem Catalog.header_at {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled) {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (eligible : Eligible compiled named.specialized) :
    ∃ header ∈ headers catalog.rows, header.slot = index ∧ header.named = named := by
  obtain ⟨input, packet, retained, _row, slot, same⟩ := catalog.packet_at selected eligible
  exact ⟨packet.header, Inventory.header_member retained,
    packet.aligned.slot.trans slot, packet.aligned.named.trans same⟩

/-- This finite assembly lemma consumes static input receipts. The compiler
entry point constructs those receipts from actual cached preparation. -/
theorem collect (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (receipt : ∀ index named, compiled.indexed.base.functions[index]? = some named →
      Eligible compiled named.specialized →
      ∃ input : Input compiled, input.row = named.specialized ∧
        input.prepared.index = index ∧ input.prepared.named = named) :
    Nonempty (Catalog compiled) := by
  classical
  let functions := compiled.indexed.base.functions
  let positions : List (Fin functions.length) := (List.finRange functions.length).filter
    (fun position => decide (Eligible compiled functions[position.val].specialized))
  have admittedPosition : ∀ position ∈ positions, Eligible compiled functions[position.val].specialized := by
    intro position member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  have available : ∀ position : {position // position ∈ positions},
      ∃ input : Input compiled, input.row = functions[position.val.val].specialized ∧
        input.prepared.index = position.val.val ∧ input.prepared.named = functions[position.val.val] := by
    intro position
    exact receipt position.val.val functions[position.val.val]
      (List.getElem?_eq_getElem position.val.isLt) (admittedPosition position.val position.property)
  let choose := fun position => Classical.choose (available position)
  have chosen := fun position => Classical.choose_spec (available position)
  let inputs := positions.attach.map choose
  have indices : inputs.map (fun input => input.prepared.index) = positions.map Fin.val := by
    calc
      _ = positions.attach.map (fun position => position.val.val) := by
        simp only [inputs, List.map_map]
        exact List.map_congr_left (fun position _ => (chosen position).2.1)
      _ = positions.map Fin.val := List.attach_map_val
  obtain ⟨rows⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.inventory wellFormed inputs
  refine ⟨{ inputs := inputs, rows := rows, distinct := ?_, admitted := ?_, covered := ?_ }⟩
  · rw [indices]
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp (fun different equal => different (Fin.ext equal))
      (List.Pairwise.filter _ (List.nodup_finRange functions.length))
  · intro input member
    obtain ⟨position, _member, rfl⟩ := List.mem_map.mp member
    rw [(chosen position).1]
    exact admittedPosition position.val position.property
  · intro index named selected eligible
    obtain ⟨bound, namedEq⟩ := List.getElem?_eq_some_iff.mp selected
    have namedAt : functions[index] = named := namedEq
    let position : Fin functions.length := ⟨index, bound⟩
    have present : position ∈ positions := by
      apply List.mem_filter.mpr
      exact ⟨List.mem_finRange position, by simpa only [position, namedAt, decide_eq_true_eq] using eligible⟩
    let attached : {position // position ∈ positions} := ⟨position, present⟩
    refine ⟨choose attached, List.mem_map.mpr ⟨attached, List.mem_attach _ _, rfl⟩,
      (chosen attached).2.1, ?_⟩
    exact (chosen attached).2.2.trans namedEq

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogAdmission
/-! Independent declaration admission supplies the complete range of an
actual matched ordinary specialization. The same result applies to a public
program entry without assuming representation of its heap or arguments. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open Frontend SourceInference

theorem Eligible.of_admissible {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {context : Context}
    {instantiation : DeclarationInstantiation}
    (origin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram row)
    (matched : CallableNamedMetadata.Matches row instantiation)
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false) :
    Eligible compiled row := by
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution := by
    obtain ⟨_request, _signature, _generic, _signatureMember, _genericMember, _resolved, accepted⟩ := origin
    simpa only [signatures] using
      CallableIndexedOwnedReachedNamedConcreteRangeReceipts.range_of_admissible_match matched admissible accepted
  exact ⟨origin, range, ordinaryReturn, ordinaryParameters⟩

theorem Eligible.of_entry {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {entry : Dynamic.ProgramEntry}
    {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (origin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram row)
    (matched : CallableNamedMetadata.Matches row entry.instantiation)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false) :
    Eligible compiled row := by
  cases valid.instantiates with
  | intro _ _ _ _ admitted _ _ _ =>
    exact Eligible.of_admissible origin matched admitted.toAdmissible rfl ordinaryReturn ordinaryParameters

theorem Catalog.header_at_admissible {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled) {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {context : Context} {instantiation : DeclarationInstantiation}
    (origin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram named.specialized)
    (matched : CallableNamedMetadata.Matches named.specialized instantiation)
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ named.specialized.function.typedBody.inputs → binder.comptime = false) :
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers catalog.rows,
      header.slot = index ∧ header.named = named :=
  catalog.header_at selected
    (Eligible.of_admissible origin matched admissible signatures ordinaryReturn ordinaryParameters)

theorem Catalog.header_at_entry {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled) {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (origin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram named.specialized)
    (matched : CallableNamedMetadata.Matches named.specialized entry.instantiation)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ named.specialized.function.typedBody.inputs → binder.comptime = false) :
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers catalog.rows,
      header.slot = index ∧ header.named = named :=
  catalog.header_at selected (Eligible.of_entry origin matched valid ordinaryReturn ordinaryParameters)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog
/-! Actual cached preparation supplies a finite ordinary catalog. Original
declaration or program-entry admission identifies each reached member; other
cache rows impose no admission obligation on that call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog
open Frontend SourceInference
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts

theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (Catalog compiled) := by
  apply collect compiled wellFormed
  intro index named selected eligible
  exact CallableIndexedOwnedPreparedOrdinaryCachedInputs.of_cached compiled wellFormed selected
    eligible.origin eligible.range eligible.ordinaryReturn eligible.ordinaryParameters

theorem eligible_of_admissible {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {context : Context} {instantiation : DeclarationInstantiation}
    (matched : CallableNamedMetadata.Matches named.specialized instantiation)
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ordinaryReturn : instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ instantiation.parameterComptime, flag = false) :
    Eligible compiled named.specialized := by
  obtain ⟨signature, member, declaration⟩ := admissible.signature_id
  have origin := CallableIndexedOwnedPreparedOrdinaryCachedInputs.ordinary_origin compiled wellFormed
    (RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected rfl)
    (by simpa only [signatures] using member) (matched.declaration.trans declaration.symm)
  apply Eligible.of_admissible origin matched admissible signatures
    (matched.returnComptime.trans ordinaryReturn)
  intro binder member
  apply ordinaryParameters binder.comptime
  rw [← matched.parameterComptime]
  exact List.mem_map.mpr ⟨binder, member, rfl⟩

theorem eligible_of_entry {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {entry : Dynamic.ProgramEntry} {heap : Dynamic.Heap} {body : Dynamic.BodyInstance}
    (matched : CallableNamedMetadata.Matches named.specialized entry.instantiation)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked compiled.sourceProgram) entry heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    Eligible compiled named.specialized := by
  cases valid.instantiates with
  | intro _ _ _ _ admitted _ _ _ =>
    exact eligible_of_admissible wellFormed selected matched admitted.toAdmissible rfl
      ordinaryReturn ordinaryParameters

/-- A reached direct target obtains its Header from the actual final cache and
the original Source declaration admission. Other cached rows need no admission. -/
theorem covers_direct {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {context : Context} {instantiation : DeclarationInstantiation}
    {index : Nat} {signature : SourceCoreGeneralFunctions.Signature}
    (admissible : SourceSemantics.DeclarationInstantiation.Admissible context instantiation)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ordinaryReturn : instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ instantiation.parameterComptime, flag = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation =
      .ok signature.key)
    (global : compiled.indexed.base.globals[index]? = some signature) :
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers catalog.rows,
      header.slot = index ∧ header.named.signature = signature := by
  rw [CallableIndexedPreparedInventories.cached_globals, List.getElem?_map] at global
  cases selected : compiled.indexed.base.functions[index]? with
  | none => simp [selected] at global
  | some named =>
    have same : named.signature = signature := by simpa [selected] using global
    have matched := CallableNamedMetadata.matches_of_exact
      (show SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation =
        .ok named.signature.key by simpa only [same] using target)
      (CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled selected)
    obtain ⟨header, member, slot, namedAt⟩ := catalog.header_at selected
      (eligible_of_admissible wellFormed selected matched admissible signatures
        ordinaryReturn ordinaryParameters)
    exact ⟨header, member, slot, by rw [namedAt]; exact same⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySyntaxTable
/-! An executable direct-site table scans the actual cached data. Successful
checks retain original ordinary provenance, complete replacement formation and
stage flags. A separate theorem transfers its rows into a proof-issued catalog;
the scanner never evaluates a catalog chosen by classical existence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySyntaxTable
open Frontend SourceInference TypeSystem
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input)

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by
        intro item member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail item member⟩

private theorem types_scoped {context : Context} {types : List Ty}
    (each : ∀ type ∈ types, TypeWellScoped context [] type) : TypesWellScoped context [] types := by
  induction types with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (each head List.mem_cons_self)
        (ih (fun type member => each type (List.mem_cons_of_mem _ member)))

/-- Fuel bounds the type traversal. Nominal replacements retain actual catalog
membership and full arity, rather than merely a closed runtime representation. -/
def type? (signatures : ProgramSignatures) :
    (fuel : Nat) → (type : Ty) → Option (PLift (TypeWellScoped (Context.ofSignatures signatures) [] type))
  | 0, _ => none
  | fuel + 1, type =>
      match type with
      | .constructor (.builtin builtin) => some ⟨.builtin builtin⟩
      | .function parameter result => do
          let ⟨first⟩ ← type? signatures fuel parameter
          let ⟨second⟩ ← type? signatures fuel result
          pure ⟨.function first second⟩
      | .product left right => do
          let ⟨first⟩ ← type? signatures fuel left
          let ⟨second⟩ ← type? signatures fuel right
          pure ⟨.product first second⟩
      | .mapping key value => do
          let ⟨first⟩ ← type? signatures fuel key
          let ⟨second⟩ ← type? signatures fuel value
          pure ⟨.mapping first second⟩
      | .proxy inner => do
          let ⟨formed⟩ ← type? signatures fuel inner
          pure ⟨.proxy formed⟩
      | .comptime inner => do
          let ⟨formed⟩ ← type? signatures fuel inner
          pure ⟨.comptime formed⟩
      | type => do
          let (id, arguments) ← SourceCoreDataCatalog.nominalParts type
          if same : type = Ty.nominal id arguments then
            let ⟨formed⟩ ← allProof?
              (fun argument => TypeWellScoped (Context.ofSignatures signatures) [] argument)
              (type? signatures fuel) arguments
            match found : signatures.dataTypes.find? (fun signature => decide (signature.id = id)) with
            | some signature =>
                if arity : arguments.length = signature.parameters.length then
                  have key : signature.id = id := by
                    simpa only [decide_eq_true_eq] using (List.find?_some found)
                  pure ⟨by
                    rw [same, ← key]
                    exact .nominal signature arguments (List.mem_of_find?_eq_some found) arity
                      (types_scoped formed)⟩
                else none
            | none =>
                match found : signatures.contracts.find? (fun signature => decide (signature.id = id)) with
                | some signature =>
                    if arity : arguments.length = signature.parameters.length then
                      have key : signature.id = id := by
                        simpa only [decide_eq_true_eq] using (List.find?_some found)
                      pure ⟨by
                        rw [same, ← key]
                        exact .contractNominal signature arguments (List.mem_of_find?_eq_some found) arity
                          (types_scoped formed)⟩
                    else none
                | none => none
          else none

def range? (signatures : ProgramSignatures) (fuel : Nat)
    (substitution : TypeSystem.ParameterSubstitution) :
    Option (PLift (SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures signatures) substitution)) := do
  let ⟨formed⟩ ← allProof? (fun item : TypeParameterId × Ty =>
    TypeWellScoped (Context.ofSignatures signatures) [] item.2)
    (fun item => type? signatures fuel item.2) substitution
  pure ⟨by
    intro parameter replacement member
    exact ⟨TypeParameterBindersWellFormed.ofSignatures signatures, formed _ member⟩⟩

/-- Only an actual ordinary declaration can pass; implementation-method rows
cannot acquire ordinary provenance through a matching native type. -/
def eligible? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (fuel : Nat) {index : Nat} (named : SourceCoreGeneralFunctions.Function)
    (selected : compiled.indexed.base.functions[index]? = some named) :
    Option (PLift (Eligible compiled named.specialized)) := do
  match found : compiled.sourceProgram.signatures.functions.find?
      (fun signature => decide (named.specialized.declaration = signature.id)) with
  | none => none
  | some signature =>
      let ⟨range⟩ ← range? compiled.sourceProgram.signatures fuel named.specialized.parameterSubstitution
      if ordinaryReturn : named.specialized.function.returnComptime = false then
        if ordinaryParameters : named.specialized.function.typedBody.inputs.all
            (fun binder => !binder.comptime) = true then
          pure ⟨{
            origin := CallableIndexedOwnedPreparedOrdinaryCachedInputs.ordinary_origin compiled wellFormed
              (RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected rfl)
              (List.mem_of_find?_eq_some found)
              (by simpa only [decide_eq_true_eq] using (List.find?_some found))
            range := range
            ordinaryReturn := ordinaryReturn
            ordinaryParameters := by
              intro binder member
              have checked := List.all_eq_true.mp ordinaryParameters binder member
              cases same : binder.comptime <;> simp_all }⟩
        else none
      else none

structure Table (compiled : SourceCoreUnifiedCompilation.Compiled) where
  rows : List SourceSpecialization.SpecializedFunction
  admitted : ∀ row ∈ rows, ∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function),
    compiled.indexed.base.functions[index]? = some named ∧
    named.specialized = row ∧ Eligible compiled row

/-- The executable result contains data from the actual cache in physical
order. Rows outside the checked fragment are omitted; no completeness is claimed. -/
def collect (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (fuel : Nat) : Table compiled :=
  let rec go (remaining : List (Fin compiled.indexed.base.functions.length)) : Table compiled :=
    match remaining with
    | [] => ⟨[], by intro row member; cases member⟩
    | index :: rest =>
        let named := compiled.indexed.base.functions[index.val]
        have selected : compiled.indexed.base.functions[index.val]? = some named :=
          List.getElem?_eq_getElem index.isLt
        let tail := go rest
        match eligible? compiled wellFormed fuel named selected with
        | none => tail
        | some ⟨accepted⟩ =>
            { rows := named.specialized :: tail.rows
              admitted := by
                intro row member
                rcases List.mem_cons.mp member with same | member
                · subst row; exact ⟨index.val, named, selected, rfl, accepted⟩
                · exact tail.admitted row member }
  go (List.finRange compiled.indexed.base.functions.length)

/-- Pure proof transfer connects data-only scanning to any authentic ordinary
catalog. No catalog Input needs to be inspected by an executable checker. -/
theorem Table.aligned {compiled : SourceCoreUnifiedCompilation.Compiled}
    (table : Table compiled) (catalog : Catalog compiled) :
    ∀ row ∈ table.rows, ∃ input : Input compiled, input ∈ catalog.inputs ∧ input.row = row := by
  intro row member
  obtain ⟨index, named, selected, same, eligible⟩ := table.admitted row member
  obtain ⟨input, retained, _slot, actual⟩ := catalog.covered index named selected (same.symm ▸ eligible)
  exact ⟨input, retained, (input.prepared.same.symm.trans (congrArg (·.specialized) actual)).trans same⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySyntaxTable
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFormationReceipts
/-! Actual ordinary and selected-method formation directly construct the stronger
prepared closure leaf. Each factory runs once at its authentic input packet.
Incoming prepared cells remain at that unchanged heap and store; the actual
Source trace establishes admission there. The receiving registry is explicit
and independent of body preparation. No legacy ResultAt projection, old-leaf
upgrade or semantic body callback is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualCellOrigins (StaticMember CellOrigins PostWithOrigins)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

namespace Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (callerGlobals : support.caller.globals = compiled.indexed.base.globals.length)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

local notation "plain" => CallableIndexedOwnedPreparedOrdinaryBodyProjection.plain support actualSites sites
local notation "history" => CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
  captured code plain owner initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

include callerGlobals callerReceipt actualSites sites packet prepared profile prefixContext observed in
/-- The ordinary factory's actual trace and runtime typing justify the one new
leaf. Preparation comes directly from the retained support at that same Code. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual))
        formed.finalStore ∧
      StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedGeneralLambdaValues.ordinary_lambda_of_formation initial owner captured code history plain
      (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.source_origin captured code plain owner initial packet)
      prefixContext observed (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reference_index captured code plain)
      rfl profile heaps (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.prepared_snapshots prepared) ordinary coercions
  have typed : RuntimeValueHasType formed.finalWorld (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions :=
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
      (registry := bodyRegistry) represented
  exact ⟨formed, sourceTrace, nativeTrace,
    StaticMember.ordinary (.ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) actualSites sites ⟨rfl⟩
      (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.prepared_recapture prepared formed.captured)
      prefixContext (observed.of_slots formed.slots)
      (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reference_index captured code plain) typed callerGlobals callerReceipt),
    determined⟩

variable
  (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include callerGlobals callerReceipt actualSites sites cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile prefixContext observed in
/-- Strong cells and the newly prepared value accompany the original formation
at its unchanged actual packet. Only the real trace establishes Source admission. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual))
        formed.finalStore ∧
      StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, canonical⟩,
        (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
        PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
          function.context profile code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code owner profile support callerGlobals callerReceipt actualSites sites prepared initial packet prefixContext observed
    cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedPreparedContextualCellOrigins.payload_static_member (registry := registry) profile member
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller) (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner support.caller)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member,
    ⟨reached, related, CallableIndexedOwnedPreparedContextualCellOrigins.post_at_same_state
      (bodyRegistry := bodyRegistry) (registry := registry)
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      profile reached post formed.heaps represented⟩,
    determined⟩

end Ordinary

namespace Principal
variable
  (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

local notation "plain" => support.plain actualSites sites
local notation "history" => CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
  captured code plain owner initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

include actualSites sites packet prepared profile in
/-- The existing prepared method producer runs once with actual selected
dictionary authority; its retained Receipt enters the stronger leaf directly. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual))
        formed.finalStore ∧
      StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, preparedMember, determined⟩ :=
    CallableIndexedOwnedPreparedPrincipalFormationReceipts.formation_member
      captured code support actualSites sites prepared owner initial packet profile heaps ordinary coercions
  obtain ⟨receipt⟩ := preparedMember
  exact ⟨formed, sourceTrace, nativeTrace, StaticMember.principal receipt, determined⟩

variable
  (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include actualSites sites cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile in
/-- The actual formed carrier and unchanged principal packet receive strong
prepared cells/result without projecting to a one-registry legacy contract. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual))
        formed.finalStore ∧
      StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩,
        (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
        PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
          function.context profile code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code owner profile support actualSites sites prepared initial packet
    cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedPreparedContextualCellOrigins.payload_static_member (registry := registry) profile member
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named) (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member,
    ⟨reached, related, CallableIndexedOwnedPreparedContextualCellOrigins.post_at_same_state
      (bodyRegistry := bodyRegistry) (registry := registry)
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      profile reached post formed.heaps represented⟩,
    determined⟩

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFormationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFormationBounds
/-! Genuine graded ordinary and selected-method formation leaves retain the
prepared member, strong cells and strong result inside their actual reached
packet. Source preservation inverts the original lambda head. Native reflection
compares one actual factory result and assigns its own finite Source grade.
Receiving registry is explicit on every local ResultAt use. No legacy output
port, equal-registry premise or second factory call is introduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFormationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualCellOrigins (StaticMember CellOrigins PostWithOrigins)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

namespace Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (callerGlobals : support.caller.globals = compiled.indexed.base.globals.length)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

local notation "plain" => CallableIndexedOwnedPreparedOrdinaryBodyProjection.plain support actualSites sites
local notation "history" => CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
  captured code plain owner initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

/-- The complete leaf output retains all real effects and the stronger facet
inside the original existential at the same reached packet. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
      PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        function.context profile code.sourceNode.type code.lowered.type outcome result reached ∧
      ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
            (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code history heap store
          owner.key.frameLocation,
        StaticMember headers keys bodyRegistry faults finalMap finalWorld formed.closure
          (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
          code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

/-- The proved strong post is attached without selecting another state or
running formation again. Source admission belongs to that post's actual trace. -/
private theorem result_at_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code history heap store
      owner.key.frameLocation)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore)
    (member : StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore)
    {reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
      ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, canonical⟩}
    (related : (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached)
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      function.context profile code.sourceNode.type code.lowered.type
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) :
    ResultAt (registry := registry) captured code owner profile support actualSites sites initial packet
      (.value (.closure formed.closure)) formed.finalHeap (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore :=
  ⟨nativeTrace, formed.finalMap, formed.finalWorld, post.result, post.cells, formed.maps, formed.worlds, formed.frame,
    formed.copy.metadata_extends, reached, related, post, formed, member⟩

variable
  (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include callerGlobals callerReceipt prefixContext observed prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- The actual Source value/fault head selects the authentic lambda. Exactly
one prepared formation establishes native completion and the stronger post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore,
      ResultAt (registry := registry) captured code owner profile support actualSites sites initial packet
        outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
      obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions evaluated
      obtain ⟨formed, _sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, _determined⟩ :=
        CallableIndexedOwnedPreparedContextualFormationReceipts.Ordinary.formation_post
          (registry := registry) (captured := captured) (code := code) (owner := owner) (profile := profile)
          (support := support) (callerGlobals := callerGlobals) (callerReceipt := callerReceipt) (actualSites := actualSites) (sites := sites) (prepared := prepared)
          (initial := initial) (packet := packet) (prefixContext := prefixContext) (observed := observed)
          (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
          (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
      obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
      exact ⟨_, formed.finalStore, result_at_formation (registry := registry)
        captured code owner profile support actualSites sites initial packet formed nativeTrace member related post⟩
  | fault failed =>
      exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions failed)

include callerGlobals callerReceipt prefixContext observed prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Native completion is compared with one genuine formation. Its own Source
grade is obtained from that factory trace; preservation is not invoked again. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) captured code owner profile support actualSites sites initial packet
        outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, determined⟩ :=
    CallableIndexedOwnedPreparedContextualFormationReceipts.Ordinary.formation_post
      (registry := registry) (captured := captured) (code := code) (owner := owner) (profile := profile)
      (support := support) (callerGlobals := callerGlobals) (callerReceipt := callerReceipt) (actualSites := actualSites) (sites := sites) (prepared := prepared)
      (initial := initial) (packet := packet) (prefixContext := prefixContext) (observed := observed)
      (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
      (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, sized,
    result_at_formation (registry := registry)
      captured code owner profile support actualSites sites initial packet formed nativeTrace member related post⟩

end Ordinary

namespace Principal
variable
  (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

local notation "plain" => support.plain actualSites sites
local notation "history" => CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
  captured code plain owner initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

/-- The selected-method leaf retains its own principal packet and dictionary.
The outer payload registry is independent of the retained body registry. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
        ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩,
      (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
      PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        function.context profile code.sourceNode.type code.lowered.type outcome result reached ∧
      ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
            (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code history heap store
          owner.key.frameLocation,
        StaticMember headers keys bodyRegistry faults finalMap finalWorld formed.closure
          (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
          code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

private theorem result_at_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code history heap store
      owner.key.frameLocation)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore)
    (member : StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore)
    {reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
      ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩}
    (related : (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached)
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      function.context profile code.sourceNode.type code.lowered.type
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) :
    ResultAt (registry := registry) captured code owner profile support actualSites sites initial packet
      (.value (.closure formed.closure)) formed.finalHeap (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore :=
  ⟨nativeTrace, formed.finalMap, formed.finalWorld, post.result, post.cells, formed.maps, formed.worlds, formed.frame,
    formed.copy.metadata_extends, reached, related, post, formed, member⟩

variable
  (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Source inversion keeps the actual selected principal, then invokes one
prepared method formation at its original dictionary-bearing packet. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore,
      ResultAt (registry := registry) captured code owner profile support actualSites sites initial packet
        outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
      obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions evaluated
      obtain ⟨formed, _sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, _determined⟩ :=
        CallableIndexedOwnedPreparedContextualFormationReceipts.Principal.formation_post
          (registry := registry) (captured := captured) (code := code) (owner := owner) (profile := profile)
          (support := support) (actualSites := actualSites) (sites := sites) (prepared := prepared)
          (initial := initial) (packet := packet)
          (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
          (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
      obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
      exact ⟨_, formed.finalStore, result_at_formation (registry := registry)
        captured code owner profile support actualSites sites initial packet formed nativeTrace member related post⟩
  | fault failed =>
      exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions failed)

include prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- The native grade is independent of the Source grade obtained from one
actual method factory trace. The same strong post and reached pool are retained. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) captured code owner profile support actualSites sites initial packet
        outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, determined⟩ :=
    CallableIndexedOwnedPreparedContextualFormationReceipts.Principal.formation_post
      (registry := registry) (captured := captured) (code := code) (owner := owner) (profile := profile)
      (support := support) (actualSites := actualSites) (sites := sites) (prepared := prepared)
      (initial := initial) (packet := packet)
      (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
      (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, sized,
    result_at_formation (registry := registry)
      captured code owner profile support actualSites sites initial packet formed nativeTrace member related post⟩

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFormationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualLambdaPolicySupport
/-! Prepared compiler packets retain the complete policy at their one actual Site.
The input named Compilation remains concrete. Prepared provenance retains
the same policy and body view. An existing qualification Facet carries
the policy proof through qualified payloads and heaps. Raw body preparation,
catalog Sites, current packet authority and original policy metadata remain
independent static inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualLambdaPolicySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (JointBody)
open CallableIndexedOwnedContextualLambdaSourceDiagnostics (IssuedSource)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The body equation and original input Compilation belong to this literal Site. -/
structure ProducedWithPolicy {named : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (parameters : List TypedBinder) (result : TypeSystem.Ty) (statements : List StatementId)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  site : Site compiled.indexed named parameters result statements context evidence [] scope administrative
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy named site.code
  recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation site.code
  policyRecipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named site.code
  issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained named site.code

/-- Forward the policy proof without selecting another Site or Compilation. -/
def ProducedWithPolicy.forget {named : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : ProducedWithPolicy compilation parameters result statements context evidence
      scope administrative id lowered) :
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Produced (compiled := compiled)
      named parameters result statements context evidence scope administrative id lowered where
  diagnostics := diagnostics
  namedCode := namedCode
  compilation := compilation
  site := produced.site
  identifier := produced.identifier
  emitted := produced.emitted
  binderPolicy := produced.binderPolicy
  recipe := produced.recipe
  compilerPolicy := produced.policyRecipe
  issuedRecipe := produced.issuedRecipe

/-- Eliminate one accepted outer bind and keep all proofs at its same chosen Site. -/
theorem ProducedWithPolicy.of_contextual
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions) :
    Nonempty (ProducedWithPolicy compilation parameters result body sourceContext evidence
      scope administrative id lowered) := by
  obtain ⟨site, identifier, emitted, binderPolicy, recipe, issuedRecipe, _view, _reason⟩ :=
    CallableIndexedLambdaGeneration.of_contextual_with_issued_recipe_exact
      compiled.indexed compilation issued record sourceContext evidence [] profile viewOfSource
      sourceFound sourceForm found form owner requirements coercions ordinary read accepted typed
  exact ⟨⟨site, identifier, emitted, binderPolicy, recipe, issuedRecipe.policy_recipe, issuedRecipe⟩⟩

/-- The existing qualification relation inspects the exact original Support. -/
def policyFacet (compiled : SourceCoreUnifiedCompilation.Compiled) :
    CallableIndexedOwnedPreparedContextualQualification.Facet compiled where
  ordinary := fun code support =>
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained support.caller.named code
  principal := fun code support =>
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained support.principal.named code

/-- Recapture changes the environment while retaining every compiler-policy field. -/
theorem retained_recapture {named : Named} {function : Dynamic.Closure}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (environment : Dynamic.Environment) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named
      (RecursiveNamedLambdaFormationHeads.recaptureCode
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) code environment) := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, body, policy, sameCompilation⟩ := retained
  exact ⟨diagnostics, namedCode, compilation, rootFuel, body, policy, sameCompilation⟩

/-- A companion proof belongs to the existing complete prepared ordinary Formation. -/
structure OrdinaryWithPolicy
    (caller : Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    extends CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation
      caller context evidence scope id lowered where
  policyRecipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained caller.named produced.site.code

/-- The complete genuine JointBody is indexed by the one supplied Compilation. -/
def ordinary_of_produced
    (caller : Header compiled (Program.ofChecked compiled.sourceProgram))
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : ProducedWithPolicy compilation parameters result statements context evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      id lowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named))
    (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (body : JointBody compilation produced.site.code (Program.ofChecked compiled.sourceProgram)
      expressionSyntax certificates diagnosticPolicy
      issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault)
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code)
    (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope context)
    (sourceType : produced.site.code.sourceNode.type = FunctionValues.sourceType
      (closure caller.named parameters result statements context evidence []))
    (ordinary : Dynamic.OrdinaryRequirementLayout produced.site.code.sourceNode.requirements
      produced.site.code.sourceNode.coercions [])
    (coercions : produced.site.code.sourceNode.coercions = []) :
    OrdinaryWithPolicy caller context evidence scope id lowered where
  toFormation := {
    parameters := parameters, result := result, statements := statements
    produced := produced.forget, expressionSyntax := expressionSyntax, certificates := certificates
    issued := issued, diagnosticPolicy := diagnosticPolicy, body := body
    bodyView := bodyView, bodyReasons := bodyReasons, declarations := declarations, sourceType := sourceType, ordinary := ordinary, coercions := coercions }
  policyRecipe := produced.policyRecipe

/-- Preparation and policy qualification refer to the same ordinary Code and Support. -/
theorem OrdinaryWithPolicy.prepared_at
    {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : OrdinaryWithPolicy caller context evidence scope id lowered)
    (environment : Dynamic.Environment) :
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt
      (head.toFormation.code environment) (head.toFormation.support environment) ∧
    (policyFacet compiled).ordinary (head.toFormation.code environment) (head.toFormation.support environment) :=
  ⟨head.toFormation.prepared environment, retained_recapture head.policyRecipe environment⟩

/-- A method seed fixes its actual cached Compilation and dictionary before recapture. -/
structure PrincipalWithPolicy {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  produced : ProducedWithPolicy principal.cached.compilation parameters result statements
    context principal.dictionary scope (CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal) id lowered
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  issued : IssuedSource compiled produced.site.code.compilation.owner (source principal.named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  body : JointBody principal.cached.compilation produced.site.code (Program.ofChecked compiled.sourceProgram)
    expressionSyntax certificates diagnosticPolicy
    issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault
  bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code
  sourceType : produced.site.code.sourceNode.type = FunctionValues.sourceType
    (closure principal.named parameters result statements context principal.dictionary [])
  ordinary : Dynamic.OrdinaryRequirementLayout produced.site.code.sourceNode.requirements
    produced.site.code.sourceNode.coercions []
  coercions : produced.site.code.sourceNode.coercions = []

def PrincipalWithPolicy.function {method : ExecutableImplMethods.CheckedMethod}
    {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : PrincipalWithPolicy principal context scope id lowered) (environment : Dynamic.Environment) :
    Dynamic.Closure :=
  closure principal.named head.parameters head.result head.statements context principal.dictionary environment

def PrincipalWithPolicy.code {method : ExecutableImplMethods.CheckedMethod}
    {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : PrincipalWithPolicy principal context scope id lowered) (environment : Dynamic.Environment) :
    Code compiled.indexed (head.function environment) scope
      (CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal) :=
  RecursiveNamedLambdaFormationHeads.recaptureCode
    (values := .initial compiled.compatible.checked) head.produced.site.code environment

def PrincipalWithPolicy.support {method : ExecutableImplMethods.CheckedMethod}
    {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : PrincipalWithPolicy principal context scope id lowered) (environment : Dynamic.Environment) :
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support (head.code environment) :=
  (CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site principal head.produced.site
    head.expressionSyntax head.certificates head.issued head.diagnosticPolicy head.body).recapture environment

/-- Both witnesses preserve the original selected method and same cached body. -/
theorem PrincipalWithPolicy.prepared_at {method : ExecutableImplMethods.CheckedMethod}
    {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : PrincipalWithPolicy principal context scope id lowered) (environment : Dynamic.Environment) :
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt
      (head.code environment) (head.support environment) ∧
    (policyFacet compiled).principal (head.code environment) (head.support environment) := by
  refine ⟨?_, retained_recapture head.produced.policyRecipe environment⟩
  exact .recaptured principal head.produced.site head.expressionSyntax head.certificates
    head.issued head.diagnosticPolicy head.body head.produced.binderPolicy head.produced.policyRecipe head.produced.issuedRecipe head.bodyView environment

/-- Normalize only the genuine administrative equality; all capture data is copied. -/
def capture_at {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
    (captured : Captures compiled.indexed mapping world scope function.captured actual)
    (administrative : Core.Context) (same : captured.administrative = administrative) :
    Captures compiled.indexed mapping world scope function.captured actual where
  administrative := administrative
  canonical := captured.canonical
  actualContext := captured.actualContext
  embedding := captured.embedding
  represented := by rw [← same]; exact captured.represented
  agrees := captured.agrees
  respects := by rw [← same]; exact captured.respects
  typed := captured.typed

namespace Ordinary
variable {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : OrdinaryWithPolicy caller context evidence scope id lowered) (environment : Dynamic.Environment)
  (callerGlobals : caller.globals = compiled.indexed.base.globals.length)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller context evidence)
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual canonical : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope (head.toFormation.function environment).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree
    (head.toFormation.support environment).body).CatalogSites .reachable bodyRegistry faults)
  (sites : (head.toFormation.support environment).body.tree.CatalogSites .reachable bodyRegistry faults)
  (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

local notation "code" => head.toFormation.code environment
local notation "support" => head.toFormation.support environment
local notation "capturedAt" => capture_at captured _ prefixContext
local notation "plain" => CallableIndexedOwnedPreparedOrdinaryBodyProjection.plain support actualSites sites
local notation "history" => CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
  capturedAt code plain owner initial packet
local notation "carrier" => value code (CallableIndexedLambdaValues.Captures.embedding capturedAt) (History.native history) actual

include callerGlobals callerReceipt head environment captured prefixContext actualSites sites packet profile observed in
/-- The existing formation endpoint receives the derived same-Code policy qualification
at every recaptured environment; the formation copies the captured cells. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store) :
    ∃ formed : Formed model capturedAt code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        (head.toFormation.function environment).context (head.toFormation.function environment).evidence
        (head.toFormation.function environment).source (head.toFormation.function environment).captured
        heap (code).id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store ((code).lowered.expression.rename (capturedAt).embedding) (.inRight .word (value code formed.embedding (History.native history) formed.closureActual))
        formed.finalStore ∧
      CallableIndexedOwnedPreparedContextualQualification.StaticMember (policyFacet compiled)
        headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure (value code formed.embedding (History.native history) formed.closureActual)
        (code).receipt.loweredParameters (code).receipt.parameterCore (code).receipt.resultCore ∧
      (∀ result finalStore, Evaluates actual store ((code).lowered.expression.rename (capturedAt).embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  exact CallableIndexedOwnedPreparedQualifiedFormationReceipts.Ordinary.formation_member
    capturedAt code owner (policyFacet compiled) profile support callerGlobals callerReceipt
    (fun copies => (head.prepared_at copies).2) actualSites sites (head.prepared_at environment).1 initial packet rfl
    observed heaps head.toFormation.ordinary head.toFormation.coercions

end Ordinary

namespace Principal
variable {method : ExecutableImplMethods.CheckedMethod}
  {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : PrincipalWithPolicy principal context scope id lowered) (environment : Dynamic.Environment)
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope (head.function environment).captured actual)
  (prefixContext : captured.administrative = CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree
    (head.support environment).body).CatalogSites .reachable bodyRegistry faults)
  (sites : (head.support environment).body.tree.CatalogSites .reachable bodyRegistry faults)
  (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "code" => head.code environment
local notation "support" => head.support environment
local notation "capturedAt" => capture_at captured _ prefixContext
local notation "plain" => CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.plain support actualSites sites
local notation "history" => CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
  capturedAt code plain owner initial packet
local notation "carrier" => value code (CallableIndexedLambdaValues.Captures.embedding capturedAt) (History.native history) actual

include head environment captured prefixContext actualSites sites packet profile in
/-- The principal endpoint retains its original method, dictionary and cached Compilation. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store) :
    ∃ formed : Formed model capturedAt code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
        (head.function environment).context (head.function environment).evidence
        (head.function environment).source (head.function environment).captured
        heap (code).id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store ((code).lowered.expression.rename (capturedAt).embedding) (.inRight .word (value code formed.embedding (History.native history) formed.closureActual))
        formed.finalStore ∧
      CallableIndexedOwnedPreparedContextualQualification.StaticMember (policyFacet compiled)
        headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure (value code formed.embedding (History.native history) formed.closureActual)
        (code).receipt.loweredParameters (code).receipt.parameterCore (code).receipt.resultCore ∧
      (∀ result finalStore, Evaluates actual store ((code).lowered.expression.rename (capturedAt).embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  exact CallableIndexedOwnedPreparedQualifiedFormationReceipts.Principal.formation_member
    capturedAt code owner (policyFacet compiled) profile support (fun copies => (head.prepared_at copies).2)
    actualSites sites (head.prepared_at environment).1 initial packet heaps head.ordinary head.coercions

end Principal
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualLambdaPolicySupport
end
