import Solcore.SourceSemantics.CoreLowering.NamedCallCertificates
import Solcore.SourceSemantics.Dynamic.Value

/-! Exact named metadata from the checks used by the compiler. Parameter
substitution matching is intentionally insensitive to list order. Equality
with the retained canonical record therefore additionally needs its domain
order; this module does not infer that receipt from native types or a key.
Authenticated evidence preserves the entire selected tree, not only its goal. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
open Frontend SourceInference TypeSystem
abbrev Plan := SourceCompilationPlan.Plan
abbrev Key := SourceCompilationPlan.Key
abbrev Specialized := SourceSpecialization.SpecializedFunction

private instance : LawfulBEq ProgramTraitId where
  eq_of_beq := by
    intro a b same
    cases a <;> cases b <;> simp_all [BEq.beq, instBEqProgramTraitId.beq]
  rfl := by
    intro a; cases a with
    | builtin id => cases id; rfl
    | declaration id => simp [BEq.beq, instBEqProgramTraitId.beq]

private instance : LawfulBEq BuiltinImplId where
  eq_of_beq := by intro a b same; cases a <;> cases b <;> simp_all [BEq.beq, instBEqBuiltinImplId.beq, BuiltinImplId.ctorIdx]
  rfl := by intro a; cases a <;> rfl

private instance : LawfulBEq ProgramImplId where
  eq_of_beq := by
    intro a b same
    cases a with
    | builtin first =>
      cases b with
      | builtin second => exact congrArg ProgramImplId.builtin (eq_of_beq (show (first == second) = true from same))
      | declaration second => cases same
    | declaration first =>
      cases b with
      | builtin second => cases same
      | declaration second => exact congrArg ProgramImplId.declaration (eq_of_beq (show (first == second) = true from same))
  rfl := by
    intro a; cases a with
    | builtin id => cases id <;> rfl
    | declaration id => simp [BEq.beq, instBEqProgramImplId.beq]

private instance : LawfulBEq ProgramPredicate where
  eq_of_beq := by
    intro a b same
    cases a with
    | mk trait subject arguments =>
      cases b with
      | mk otherTrait otherSubject otherArguments =>
        change ((trait == otherTrait) && ((subject == otherSubject) && (arguments == otherArguments))) = true at same
        simp only [Bool.and_eq_true, beq_iff_eq] at same
        rcases same with ⟨rfl, rfl, rfl⟩
        rfl
  rfl := by
    intro a
    change ((a.trait == a.trait) && ((a.subject == a.subject) && (a.arguments == a.arguments))) = true
    simp

/-- Full, ordered retained metadata of one actual specialization. -/
def instantiation (specialized : Specialized) : DeclarationInstantiation where
  declaration := specialized.declaration
  parameterSubstitution := specialized.parameterSubstitution
  type := specialized.function.type
  predicates := specialized.assumptions
  parameterComptime := specialized.function.typedBody.inputs.map (·.comptime)
  returnComptime := specialized.function.returnComptime

structure Matches (specialized : Specialized) (source : DeclarationInstantiation) : Prop where
  ownership : specialized.key.declaration = specialized.declaration ∧
    specialized.function.declaration = specialized.declaration ∧
    specialized.function.typedBody.owner = specialized.declaration
  arguments : specialized.key.arguments = specialized.parameterSubstitution.map Prod.snd
  declaration : specialized.declaration = source.declaration
  substitution : SourceCompilationPlan.parameterSubstitutionsEquivalent specialized.parameterSubstitution source.parameterSubstitution = true
  type : specialized.function.type = source.type
  predicates : specialized.assumptions = source.predicates
  parameterComptime : specialized.function.typedBody.inputs.map (·.comptime) = source.parameterComptime
  returnComptime : specialized.function.returnComptime = source.returnComptime

theorem matches_of_checked {specialized : Specialized} {source : DeclarationInstantiation}
    (accepted : SourceCompilationPlan.specializationMatchesInstantiation specialized source = true) :
    Matches specialized source := by
  simp only [SourceCompilationPlan.specializationMatchesInstantiation, Bool.and_eq_true,
    beq_iff_eq, SourceCompilationPlan.specializationOwnershipCoherent, decide_eq_true_eq] at accepted
  rcases accepted with ⟨⟨⟨⟨⟨⟨⟨ownership, arguments⟩, declaration⟩, substitution⟩, type⟩, predicates⟩, parameters⟩, result⟩
  exact ⟨ownership, arguments, declaration, substitution, type, predicates, parameters, result⟩

theorem specialization_of_exact {plan : Plan} {key : Key} {specialized : Specialized}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok specialized) :
    specialized ∈ plan.specializations ∧ specialized.key = key := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · rename_i selected filtered
    cases accepted
    have member : specialized ∈ [specialized] := .head _
    rw [← filtered] at member
    exact ⟨(List.mem_filter.mp member).1, of_decide_eq_true (List.mem_filter.mp member).2⟩
  · cases accepted

/-- Accepted selection identifies the complete matching plan record, even
when duplicate plan records would otherwise make a key alone ambiguous. -/
theorem matches_of_exact {plan : Plan} {key : Key} {source : DeclarationInstantiation} {specialized : Specialized}
    (selected : SourceCompilationPlan.exactInstantiationKey plan source = .ok key)
    (canonical : SourceCompilationPlan.exactSpecialization plan key = .ok specialized) :
    Matches specialized source := by
  unfold SourceCompilationPlan.exactInstantiationKey at selected
  split at selected
  · cases selected
  · rename_i candidate filtered
    cases selected
    have member : candidate ∈ [candidate] := .head _
    rw [← filtered] at member
    have facts := List.mem_filter.mp member
    have candidateMember : candidate ∈ plan.specializations.filter (fun row => decide (row.key = candidate.key)) :=
      List.mem_filter.mpr ⟨facts.1, by simp⟩
    unfold SourceCompilationPlan.exactSpecialization at canonical
    split at canonical
    · cases canonical
    · rename_i row canonicalFiltered
      cases canonical
      rw [canonicalFiltered] at candidateMember
      have same := List.mem_singleton.mp candidateMember
      subst candidate
      exact matches_of_checked facts.2
    · cases canonical
  · cases selected

private theorem exactBinding_at {substitution : ParameterSubstitution} {parameter : TypeParameterId} {type : Ty}
    (accepted : SourceCompilationPlan.exactParameterBinding? substitution parameter = some type)
    {entry : TypeParameterId × Ty} (member : entry ∈ substitution) (key : entry.1 = parameter) : entry.2 = type := by
  unfold SourceCompilationPlan.exactParameterBinding? at accepted
  split at accepted
  · rename_i selected filtered
    have item : entry ∈ substitution.filter (fun item => item.1 == parameter) := List.mem_filter.mpr ⟨member, by simp [key]⟩
    rw [filtered] at item
    have same := List.mem_singleton.mp item
    subst entry
    exact Option.some.inj accepted
  · cases accepted

/-- Ordered domains remove precisely the permutation freedom of the actual
matcher. No injectivity of native type erasure is used. -/
theorem substitution_eq_of_domain {left right : ParameterSubstitution}
    (equivalent : SourceCompilationPlan.parameterSubstitutionsEquivalent left right = true)
    (domain : left.map Prod.fst = right.map Prod.fst) : left = right := by
  have each : ∀ entry ∈ left, SourceCompilationPlan.exactParameterBinding? right entry.1 = some entry.2 := by
    simp only [SourceCompilationPlan.parameterSubstitutionsEquivalent, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at equivalent
    exact equivalent.1.2
  apply List.ext_getElem?
  intro index
  cases l : left[index]? with
  | none =>
    have d := congrArg (fun entries => entries[index]?) domain
    simp only [List.getElem?_map, l, Option.map_none] at d
    cases r : right[index]? <;> simp_all
  | some entry =>
    have d := congrArg (fun entries => entries[index]?) domain
    simp only [List.getElem?_map, l, Option.map_some] at d
    cases r : right[index]? with
    | none => simp [r] at d
    | some other =>
      simp only [r, Option.map_some, Option.some.injEq] at d
      have value := exactBinding_at (each entry (List.mem_of_getElem? l)) (List.mem_of_getElem? r) d.symm
      have same : entry = other := Prod.ext d value.symm
      exact congrArg some same

theorem Matches.canonical {specialized : Specialized} {source : DeclarationInstantiation}
    (matched : Matches specialized source)
    (domain : specialized.parameterSubstitution.map Prod.fst = source.parameterSubstitution.map Prod.fst) :
    source = instantiation specialized := by
  have substitution := substitution_eq_of_domain matched.substitution domain
  cases source
  simp only [DeclarationInstantiation.mk.injEq, instantiation]
  exact ⟨matched.declaration.symm, substitution.symm, matched.type.symm, matched.predicates.symm,
    matched.parameterComptime.symm, matched.returnComptime.symm⟩

/-- Validation pins every node of every dictionary to the actual resolver
selection. Its uniqueness is stronger than matching predicate goals. -/
theorem selected_evidence_unique {signatures : ProgramSignatures} {key : Key} {index : Nat}
    {predicates : List ProgramPredicate} {left right : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (first : SourceCompilationPlan.validateRuntimeEvidenceSelection signatures key index predicates left = .ok ())
    (second : SourceCompilationPlan.validateRuntimeEvidenceSelection signatures key index predicates right = .ok ()) : left = right := by
  induction predicates generalizing index left right with
  | nil => cases left <;> cases right <;> simp_all [SourceCompilationPlan.validateRuntimeEvidenceSelection]
  | cons predicate predicates ih =>
    cases left with
    | nil => simp [SourceCompilationPlan.validateRuntimeEvidenceSelection] at first
    | cons l ls =>
      cases right with
      | nil => simp [SourceCompilationPlan.validateRuntimeEvidenceSelection] at second
      | cons r rs =>
        simp only [SourceCompilationPlan.validateRuntimeEvidenceSelection] at first second
        split at first
        · cases first
        · cases first
        · rename_i chosen resolved
          simp only [resolved] at second
          split at first
          · rename_i sameL
            split at second
            · rename_i sameR
              have same : l = r := (eq_of_beq sameL).symm.trans (eq_of_beq sameR)
              rw [same, ih first second]
            · cases r; cases second
          · cases l; cases first

theorem selection_of_resolved {program : CheckedProgram} {key : Key}
    {predicates : List ProgramPredicate} {environment : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key predicates = .ok environment)
    (index : Nat) : SourceCompilationPlan.validateRuntimeEvidenceSelection program.signatures key index predicates environment = .ok () := by
  induction predicates generalizing environment index with
  | nil => cases resolved; rfl
  | cons predicate predicates ih =>
    simp only [SourceCompilationPlan.resolveRuntimeEvidenceEnvironment] at resolved
    split at resolved
    · cases resolved
    · cases resolved
    · rename_i chosen resolution
      cases chosen with
      | byImpl goal implementation premises =>
        simp only at resolved
        split at resolved
        · cases resolved
        · cases tail : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key predicates with
          | error error => simp [tail, bind, Except.bind] at resolved
          | ok remaining =>
            simp only [tail, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at resolved
            subst environment
            simp only [SourceCompilationPlan.validateRuntimeEvidenceSelection, resolution, BEq.rfl, ↓reduceIte]
            exact ih tail (index + 1)

/-- Actual authenticated dictionaries equal the canonical resolver output as
ordered lists of complete implementation trees. -/
theorem authenticated_evidence_eq {program : CheckedProgram} {key : Key}
    {predicates : List ProgramPredicate} {actual canonical : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (accepted : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key predicates actual = .ok ())
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key predicates = .ok canonical) : actual = canonical := by
  unfold SourceCompilationPlan.validateAuthenticatedRuntimeEvidence at accepted
  cases goals : SourceCompilationPlan.validateRuntimeEvidence key predicates actual with
  | error error => simp [goals, bind, Except.bind] at accepted
  | ok value =>
    simp only [goals, bind, Except.bind] at accepted
    exact selected_evidence_unique accepted (selection_of_resolved resolved 0)

/-- The independent evidence carrier retains all goals, implementation IDs,
order and recursive premises. This function traverses metadata only. -/
def evidence : TypedTraitResolution.Evidence → TraitEvidence
  | .byImpl goal implementation premises => .implementation goal implementation (premises.map evidence)

def environment (retained : SourceTypedRuntime.RuntimeEvidenceEnvironment) : Dynamic.EvidenceEnvironment :=
  retained.map fun item => (SourceTypedRuntime.runtimeEvidenceGoal item, evidence item)

theorem evidence_represents (retained : TypedTraitResolution.Evidence) :
    ImplementationEvidenceRepresents retained (evidence retained) := by
  induction retained using TraitResolution.Evidence.rec
    (motive_2 := fun entries => Forall₂ ImplementationEvidenceRepresents entries (entries.map evidence)) with
  | byImpl goal implementation premises ih => simpa only [evidence] using (ImplementationEvidenceRepresents.byImpl (goal := goal) (implId := implementation) ih)
  | nil => exact .nil
  | cons head rest headIH restIH => exact .cons headIH restIH

/-- Any independently represented dictionary has this exact ordered metadata
view; recursive implementation evidence cannot be replaced by goal equality. -/
theorem environment_eq_of_represents {retained : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {source : Dynamic.EvidenceEnvironment}
    (represented : Forall₂ (fun item entry =>
      entry.1 = SourceTypedRuntime.runtimeEvidenceGoal item ∧ ImplementationEvidenceRepresents item entry.2) retained source) :
    source = environment retained := by
  induction represented with
  | nil => rfl
  | @cons raw semantic rest remaining head tail ih =>
    have same := head.2.functional (evidence_represents raw)
    have pair : semantic = (SourceTypedRuntime.runtimeEvidenceGoal raw, evidence raw) := Prod.ext head.1 same
    simp only [environment, List.map_cons]
    rw [pair, ih]
    rfl


def global (specialized : Specialized) (retained : SourceTypedRuntime.RuntimeEvidenceEnvironment) : Dynamic.GlobalFunction :=
  ⟨instantiation specialized, environment retained⟩

/-- The final source value agrees in its complete declaration header and its
complete evidence environment. Canonical substitution order is a separate
retained-occurrence receipt, not a consequence of key selection. -/
theorem global_eq {program : CheckedProgram} {plan : Plan} {key : Key}
    {source : DeclarationInstantiation} {specialized : Specialized}
    {actual canonical : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (selected : SourceCompilationPlan.exactInstantiationKey plan source = .ok key)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok specialized)
    (domain : specialized.parameterSubstitution.map Prod.fst = source.parameterSubstitution.map Prod.fst)
    (accepted : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key specialized.assumptions actual = .ok ())
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key specialized.assumptions = .ok canonical) :
    (⟨source, environment actual⟩ : Dynamic.GlobalFunction) = global specialized canonical := by
  rw [(matches_of_exact selected record).canonical domain, authenticated_evidence_eq accepted resolved]
  rfl

/-- Full global agreement also applies to an independently represented source
dictionary; it does not assume that source evidence is a bare key or goal list. -/
theorem global_eq_of_represents {program : CheckedProgram} {plan : Plan} {key : Key}
    {source : DeclarationInstantiation} {specialized : Specialized}
    {actual canonical : SourceTypedRuntime.RuntimeEvidenceEnvironment} {semantic : Dynamic.EvidenceEnvironment}
    (selected : SourceCompilationPlan.exactInstantiationKey plan source = .ok key)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok specialized)
    (domain : specialized.parameterSubstitution.map Prod.fst = source.parameterSubstitution.map Prod.fst)
    (accepted : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key specialized.assumptions actual = .ok ())
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key specialized.assumptions = .ok canonical)
    (represented : Forall₂ (fun item entry => entry.1 = SourceTypedRuntime.runtimeEvidenceGoal item ∧
      ImplementationEvidenceRepresents item entry.2) actual semantic) :
    (⟨source, semantic⟩ : Dynamic.GlobalFunction) = global specialized canonical := by
  rw [environment_eq_of_represents represented]
  exact global_eq selected record domain accepted resolved

/-- The compiler's singleton native slot check, retained independently of
source metadata and of closure/body meaning. -/
def Slot (globals : List SourceCoreCalls.Signature) (index : Nat) (signature : SourceCoreCalls.Signature) : Prop :=
  globals.zipIdx.filter (fun item => decide (item.1.key = signature.key)) = [(signature, index)]

theorem Slot.selected {globals : List SourceCoreCalls.Signature} {index : Nat} {signature : SourceCoreCalls.Signature}
    (slot : Slot globals index signature) : globals[index]? = some signature := by
  have member : (signature, index) ∈ [(signature, index)] := .head _
  rw [← slot] at member
  exact List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp member).1

theorem Slot.unique {globals : List SourceCoreCalls.Signature} {first second : Nat}
    {left right : SourceCoreCalls.Signature} (a : Slot globals first left) (b : Slot globals second right)
    (same : left.key = right.key) : left = right ∧ first = second := by
  unfold Slot at a b
  rw [same] at a
  exact Prod.mk.inj (List.cons.inj (a.symm.trans b)).1

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem slot_of_selected_signature
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {metadata : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node metadata isReference = .ok (index, signature)) :
    Slot compilation.globals index signature := by
  unfold SourceCoreFunctions.selectedSignature at accepted
  by_cases owner : source.owner = compilation.owner.declaration
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
    obtain ⟨caller, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨target, _, accepted⟩ := bind_ok accepted
      obtain ⟨key, _, accepted⟩ := bind_ok accepted
      obtain ⟨specialized, _, accepted⟩ := bind_ok accepted
      split at accepted
      · split at accepted
        · cases accepted
        · split at accepted
          all_goals simp only [pure, Except.pure, bind, Except.bind] at accepted
          all_goals try contradiction
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨selection, globalReceipt, accepted⟩ := bind_ok accepted
          rcases selection with ⟨selectedIndex, selectedSignature⟩
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          cases accepted
          change ((match compilation.globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) with
            | [] => .error (.callPreparation (.missingSpecialization key))
            | [(signature, index)] => .ok (index, signature)
            | candidates => .error (.callPreparation (.duplicateSpecialization key candidates.length))) :
              Except SourceCoreBasic.Error (Nat × SourceCoreCalls.Signature)) = .ok (selectedIndex, selectedSignature) at globalReceipt
          split at globalReceipt
          · cases globalReceipt
          · rename_i chosen position filtered
            cases globalReceipt
            have member : (selectedSignature, selectedIndex) ∈ compilation.globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) := by
              rw [filtered]; exact .head _
            have keyEq : selectedSignature.key = key := of_decide_eq_true (List.mem_filter.mp member).2
            simpa only [Slot, keyEq] using filtered
          · cases globalReceipt
      · cases accepted
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  · simp [owner, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted

/-- Ordinary selectedSignature acceptance provides the plan record and every
retained field comparison. Canonical list order is deliberately not inferred. -/
theorem metadata_of_selected_signature
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {metadata : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node metadata isReference = .ok (index, signature)) :
    ∃ specialized, SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized ∧
      Matches specialized metadata ∧ specialized.assumptions = [] ∧ Slot compilation.globals index signature := by
  obtain ⟨_, _, specialized, _, _, _, _, _, record, assumptions, _⟩ := NamedCalls.selected_signature_facts accepted
  exact ⟨specialized, record, matches_of_exact (NamedCalls.selected_signature_target accepted).1 record,
    assumptions, slot_of_selected_signature accepted⟩

end Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
