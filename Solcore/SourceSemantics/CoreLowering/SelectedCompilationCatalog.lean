import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaders
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalog

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
open Core Frontend SourceInference TypeSystem
open RecursiveNamedPublicSpecializationMeaning (Origin Prepared)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Eligible Catalog)
open CallableIndexedOwnedPreparedOrdinaryCachedInputs
  (cached_record cached_key cached_slot of_cached_origin_at)

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
    (catalog : SignatureCatalogWellFormed program.signatures)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    {implementation : ProgramImplementationSignature}
    (implMember : implementation ∈ program.signatures.implementations) :
    signature.id ≠ implementation.id := by
  have unique := catalog.declaration_ids
  simp only [signatureDeclarationIds] at unique
  have separated := (List.nodup_append.mp (List.nodup_append.mp unique).1).2.2
  apply separated signature.id
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨signature, member, rfl⟩)))
    implementation.id (List.mem_map.mpr ⟨implementation, implMember, rfl⟩)

/-- A final row naming a real function signature is an ordinary request even
when it was discovered below an implementation-method root. -/
theorem ordinary_origin (compiled : SourceCoreUnifiedCompilation.Compiled)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
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
      exact False.elim (function_impl_ne catalog signatureMember selected.implementationMember
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


theorem retained_target (compiled : SourceCoreUnifiedCompilation.Compiled)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (origin : Origin compiled.sourceProgram named.specialized) :
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation named.specialized) = .ok named.signature.key := by
  obtain ⟨signature, signatureMember, declaration, domain, key, functionOwner, sourceOwner⟩ :=
    origin_signature origin
  have domainUnique : (named.specialized.parameterSubstitution.map Prod.fst).Nodup :=
    domain ▸ (catalog.function_parameters signature signatureMember).1
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
      have candidateOrigin := ordinary_origin compiled catalog member signatureMember
        (matchedFields.declaration.trans declaration)
      obtain ⟨other, otherMember, otherDeclaration, otherDomain, otherKey, _, _⟩ :=
        origin_signature candidateOrigin
      have sameSignature : other = signature := by
        have unique := catalog.function_ids
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


theorem of_cached (compiled : SourceCoreUnifiedCompilation.Compiled)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
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
    target := by rw [namedEq]; exact retained_target compiled catalog selected origin
    slot := by rw [indexEq, namedEq]; exact cached_slot compiled selected }
  exact ⟨input, rfl, indexEq, namedEq⟩

theorem exists_issued {compiled : SourceCoreUnifiedCompilation.Compiled}
    (input : Input compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled) :
    Nonempty (Issued input) := by
  obtain ⟨selected, header, aligned, function, reason⟩ :=
    SelectedCompilationHeaders.retained_at_prepared input.prepared
      bodies input.range input.ordinaryReturn input.ordinaryParameters input.target
  have named : header.named = input.prepared.named := aligned.named
  have slot : header.slot = input.prepared.index := aligned.slot
  have specialized : header.named.specialized = input.row :=
    (congrArg (·.specialized) named).trans input.prepared.same
  have metadata : header.instantiation =
      CallableNamedReversal.instantiation (CallableNamedMetadata.instantiation header.named.specialized) := by
    rw [aligned.metadata, specialized]
    rfl
  have target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation header.named.specialized) = .ok header.named.signature.key := by
    rw [← CallableNamedReversal.target_reverse, ← metadata]
    exact header.target
  have resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment
      compiled.indexed.base.sourceProgram header.named.signature.key header.named.specialized.assumptions =
      .ok input.prepared.available := by
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1, named,
      RecursiveNamedPreparedCallEvidence.Prepared.signature_key input.prepared, input.prepared.same]
    exact input.prepared.resolved
  have row : CallableIndexedNamedValues.Row compiled.indexed header.slot header.named.signature
      header.named.specialized input.prepared.available :=
    ⟨by simpa only [slot, named] using input.slot,
      CallableIndexedActualNamedSourceReceipts.header_record compiled header, target, resolved⟩
  have dictionary : header.function.evidence =
      (CallableNamedMetadata.global header.named.specialized input.prepared.available).evidence := by
    rw [function]
    rfl
  exact ⟨⟨selected, header, aligned, function, reason,
    CallableIndexedOwnedFunctionValues.NamedSourceAt.of_retained_header row metadata dictionary⟩⟩

theorem inventory {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (inputs : List (Input compiled)) : Nonempty (Inventory inputs) := by
  induction inputs with
  | nil => exact ⟨.nil⟩
  | cons input inputs tail =>
      obtain ⟨packet⟩ := exists_issued input bodies
      obtain ⟨rest⟩ := tail
      exact ⟨.cons packet rest⟩

theorem collect (compiled : SourceCoreUnifiedCompilation.Compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
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
  obtain ⟨rows⟩ := inventory bodies inputs
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


/-- The complete actual cache issues the existing automatic catalog using
only selected original body typing and unchanged global signature identities. -/
theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled) : Nonempty (Catalog compiled) := by
  apply collect compiled bodies
  intro index named selected eligible
  exact of_cached compiled bodies.signatures selected eligible.origin eligible.range
    eligible.ordinaryReturn eligible.ordinaryParameters

/-- Every member of the unchanged inventory has the complete static instance
certificate at its own exact source body, parameter row and context. -/
theorem certificates {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    (header : CallableIndexedOwnedPreparedFiniteNamedInventories.Header compiled)
    (member : header ∈ headers rows) :
    ∃ facts, Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      header.instantiation header.sourceBody header.types header.context facts := by
  obtain ⟨input, packet, retained, same⟩ := rows.mem_headers header member
  subst header
  exact SelectedCompilationHeaders.certificate_at
    (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
    bodies input.range packet.aligned

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
