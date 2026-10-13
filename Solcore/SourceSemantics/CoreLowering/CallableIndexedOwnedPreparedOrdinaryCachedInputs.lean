import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedFinalPlanOrigins
import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalCatalogOrigins

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
