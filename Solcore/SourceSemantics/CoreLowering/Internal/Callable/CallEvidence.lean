import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedCalls
import Solcore.SourceSemantics.Dynamic.Value
import Solcore.SourceSemantics.TraitResolutionSoundness
import Solcore.SourceSemantics.Dynamic.Evidence
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.Frontend.SourceCore.GeneralFunctions

/-!
# Call evidence

Named metadata, the evidence environment, call evidence and its certificates, and requirement layouts.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableEvidenceEnvironment
/-! Exact ordered evidence metadata and independent semantic dictionaries.
Lookup uses the first matching goal, including when later goals repeat. Resolver
success supplies validity through the existing independent soundness bridge. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableEvidenceEnvironment
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallableNamedMetadata (evidence environment evidence_represents)

@[simp] theorem evidence_goal (retained : TypedTraitResolution.Evidence) :
    (evidence retained).goal = SourceCompilationPlan.runtimeEvidenceGoal retained := by
  cases retained; simp [evidence, TraitEvidence.goal, SourceCompilationPlan.runtimeEvidenceGoal]

/-- The raw executable list is kept in full; equal goals do not identify trees. -/
theorem lookup_of_find {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {goal : ProgramPredicate} {retained : TypedTraitResolution.Evidence}
    (found : available.find? (fun item => decide (SourceCompilationPlan.runtimeEvidenceGoal item = goal)) = some retained) :
    (environment available).LooksUp goal (evidence retained) := by
  induction available with
  | nil => cases found
  | cons head tail ih =>
    by_cases same : SourceCompilationPlan.runtimeEvidenceGoal head = goal
    · simp only [List.find?_cons, same, decide_true, Option.some.injEq] at found
      subst retained
      change EvidenceEnvironment.LooksUp ((_, _) :: _) _ _
      rw [same]
      exact .head
    · simp only [List.find?_cons, same, decide_false] at found
      exact .tail same (ih found)

/-- Every semantic first-match lookup comes from the same raw list entry. -/
theorem find_of_lookup {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {goal : ProgramPredicate} {selected : TraitEvidence}
    (found : (environment available).LooksUp goal selected) :
    ∃ retained, available.find? (fun item => decide (SourceCompilationPlan.runtimeEvidenceGoal item = goal)) = some retained ∧
      selected = evidence retained := by
  induction available with
  | nil => cases found
  | cons head tail ih =>
    cases found with
    | head => exact ⟨head, by simp, rfl⟩
    | tail different found =>
      obtain ⟨retained, chosen, same⟩ := ih found
      exact ⟨retained, by simp [different, chosen], same⟩

/-- Closed implementation trees contain no assumption leaves to replace. -/
theorem closes_self (caller : EvidenceEnvironment) (retained : TypedTraitResolution.Evidence) :
    EvidenceCloses caller (evidence retained) (evidence retained) := by
  induction retained using TraitResolution.Evidence.rec
    (motive_2 := fun entries => Forall₂ (EvidenceCloses caller) (entries.map evidence) (entries.map evidence)) with
  | byImpl goal implementation premises ih => simpa only [evidence] using (EvidenceCloses.implementation (goal := goal) (implementation := implementation) ih)
  | nil => exact .nil
  | cons head rest headIH restIH => exact .cons headIH restIH

mutual
  theorem closes_functional {caller : EvidenceEnvironment} {openTree first second : TraitEvidence}
      (left : EvidenceCloses caller openTree first) (right : EvidenceCloses caller openTree second) : first = second := by
    cases left with
    | assumption first => cases right with | assumption second => exact first.functional second
    | implementation premises =>
      cases right with
      | implementation others => exact congrArg (TraitEvidence.implementation _ _) (closes_spine_functional premises others)

  theorem closes_spine_functional {caller : EvidenceEnvironment} {openTrees first second : List TraitEvidence}
      (left : Forall₂ (EvidenceCloses caller) openTrees first) (right : Forall₂ (EvidenceCloses caller) openTrees second) : first = second := by
    cases left with
    | nil => cases right; rfl
    | cons head tail =>
      cases right with
      | cons otherHead otherTail => rw [closes_functional head otherHead, closes_spine_functional tail otherTail]
end

def predicateEvidence : PredicateEvidence → TraitEvidence
  | .assumption goal => .assumption goal
  | .implementation retained => evidence retained

theorem predicate_represents (retained : PredicateEvidence) :
    PredicateEvidenceRepresents retained (predicateEvidence retained) := by
  cases retained with
  | assumption goal => exact .assumption goal
  | implementation retained => exact .implementation (evidence_represents retained)

theorem retained_valid {context : Context} {solved : SolvedRequirement}
    (valid : SolvedRequirementValid context solved) :
    EvidenceValid context.assumptions context.signatures.resolutionRules solved.predicate (predicateEvidence solved.evidence) := by
  cases valid with
  | intro retained =>
    cases retained with
    | intro represents valid =>
      rw [← represents.functional (predicate_represents _)]
      exact valid

/-- Actual resolver output is valid as the complete semantic tree, not merely
as a list of goals. No caller validity premise is required here. -/
theorem resolved_valid {program : CheckedProgram} {key : SourceCompilationPlan.Key}
    {predicates : List ProgramPredicate} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key predicates = .ok available) :
    (environment available).Valid program.signatures.resolutionRules ∧
      (environment available).map Prod.fst = predicates := by
  induction predicates generalizing available with
  | nil =>
    cases resolved
    refine ⟨?_, rfl⟩
    intro goal selected found
    cases found
  | cons predicate predicates ih =>
    simp only [SourceCompilationPlan.resolveRuntimeEvidenceEnvironment] at resolved
    split at resolved
    · cases resolved
    · cases resolved
    · rename_i chosen resolution
      have valid := TraitResolutionSoundness.resolve_success_evidenceValid resolution
      obtain ⟨semantic, represents, nativeValid⟩ := valid
      have nativeValid : EvidenceValid [] program.signatures.resolutionRules predicate (evidence chosen) := by
        rwa [represents.functional (evidence_represents _)] at nativeValid
      have goalEq := nativeValid.evidence_goal_eq
      cases chosen with
      | byImpl goal implementation premises =>
        simp only at resolved
        split at resolved
        · cases resolved
        · cases tail : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key predicates with
          | error error => simp [tail, bind, Except.bind] at resolved
          | ok remaining =>
            simp only [tail, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at resolved
            subst available
            obtain ⟨tailValid, tailGoals⟩ := ih tail
            have same : goal = predicate := by simpa [evidence, TraitEvidence.goal] using goalEq
            refine ⟨?_, ?_⟩
            · intro selected output found
              cases found with
              | head => simpa only [← same, SourceCompilationPlan.runtimeEvidenceGoal] using nativeValid
              | tail _ found => exact tailValid _ _ found
            · change goal :: (environment remaining).map Prod.fst = _
              rw [same, tailGoals]

theorem resolved_covers {program : CheckedProgram} {key : SourceCompilationPlan.Key}
    {context : Context} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (signatures : context.signatures = program.signatures)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key context.assumptions = .ok available) :
    (environment available).Covers context := by
  obtain ⟨valid, keys⟩ := resolved_valid resolved
  refine ⟨by simpa only [signatures] using valid, ?_⟩
  intro predicate member
  exact EvidenceEnvironment.LooksUp.exists_of_key_mem (keys ▸ member)

end Solcore.SourceSemantics.CoreLowering.CallableEvidenceEnvironment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCallEvidence
/-! The real call-dictionary materializer produces the independent ordered
requirement judgment. Retained-ledger validity and exact caller evidence remain
explicit; a successful goal check alone cannot establish either condition.
Coercion ledger slicing and method dictionary assembly are separate boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCallEvidence
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallableNamedMetadata (evidence environment)
open CallableEvidenceEnvironment

abbrev Selected (caller : SourceSpecialization.SpecializedFunction) (id : RequirementId)
    (solved : SolvedRequirement) : Prop :=
  caller.function.solvedRequirements.filter (fun row => decide (row.id = id)) = [solved]

theorem Selected.contains {caller : SourceSpecialization.SpecializedFunction} {id : RequirementId}
    {solved : SolvedRequirement} (selected : Selected caller id solved)
    {context : Context} (ledger : context.solvedRequirements = caller.function.solvedRequirements) :
    ContainsRequirement context id solved := by
  have member : solved ∈ caller.function.solvedRequirements.filter (fun row => decide (row.id = id)) := by
    rw [selected]; simp
  have matched := List.mem_filter.mp member
  exact ⟨ledger ▸ matched.1, of_decide_eq_true matched.2⟩

theorem Selected.unique {caller : SourceSpecialization.SpecializedFunction} {id : RequirementId}
    {solved other : SolvedRequirement} (selected : Selected caller id solved)
    {context : Context} (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (contains : ContainsRequirement context id other) : other = solved := by
  have member : other ∈ caller.function.solvedRequirements.filter (fun row => decide (row.id = id)) :=
    List.mem_filter.mpr ⟨ledger ▸ contains.1, by simp [contains.2]⟩
  rw [selected] at member
  exact List.mem_singleton.mp member

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) : ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem map_ok {α β ε : Type} {action : Except ε α} {f : α → β} {result : β}
    (accepted : f <$> action = .ok result) : ∃ value, action = .ok value ∧ result = f value := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, (Except.ok.inj accepted).symm⟩

/-- One successful step retains its actual singleton ledger selection and the
complete evidence closure. This also records the exact remaining ordered call. -/
theorem cons_accepted {caller : SourceSpecialization.SpecializedFunction} {occurrence : ExpressionId}
    {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {id : RequirementId} {ids : List RequirementId} {predicate : ProgramPredicate} {predicates : List ProgramPredicate}
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available
      (id :: ids) (predicate :: predicates) = .ok result) :
    ∃ solved head tail, Selected caller id solved ∧ solved.predicate = predicate ∧
      EvidenceCloses (environment available) (predicateEvidence solved.evidence) (evidence head) ∧
      SourceCompilationPlan.runtimeEvidenceGoal head = predicate ∧
      SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok tail ∧
      result = head :: tail := by
  simp only [SourceCompilationPlan.materializeCallEvidence] at accepted
  obtain ⟨solved, picked, accepted⟩ := bind_ok accepted
  have selected : Selected caller id solved := by
    change (match caller.function.solvedRequirements.filter (fun row => decide (row.id = id)) with
      | [] => .error (.missingSolvedRequirement caller.key occurrence id)
      | [row] => .ok row
      | rows => .error (.duplicateSolvedRequirements caller.key occurrence id rows.length) : Except SourceTypedRuntime.RuntimeError SolvedRequirement) = .ok solved at picked
    cases filtered : caller.function.solvedRequirements.filter (fun row => decide (row.id = id)) with
    | nil => simp [filtered] at picked
    | cons row rest =>
      cases rest with
      | nil => simp only [filtered, Except.ok.injEq] at picked; subst solved; exact filtered
      | cons other rest => simp [filtered] at picked
  rcases solved with ⟨solvedId, solvedPredicate, retained⟩
  split at accepted
  · cases accepted
  · rename_i equalPredicate
    have matchedPredicate : solvedPredicate = predicate := by simpa using equalPredicate
    split at accepted
    · cases accepted
    · rename_i equalGoal
      have matchedGoal : retained.goal = solvedPredicate := by simpa using equalGoal
      cases retained with
      | implementation raw =>
        change (List.cons raw <$> SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates) = .ok result at accepted
        obtain ⟨tail, remaining, same⟩ := map_ok accepted
        refine ⟨_, raw, tail, selected, matchedPredicate, closes_self _ raw, ?_, remaining, same⟩
        cases raw
        exact matchedGoal.trans matchedPredicate
      | assumption goal =>
        change (match available.find? (fun item => decide (SourceCompilationPlan.runtimeEvidenceGoal item = goal)) with
          | some raw => List.cons raw <$> SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates
          | none => .error (.missingRuntimeAssumptionEvidence caller.key occurrence id goal)) = .ok result at accepted
        cases found : available.find? (fun item => decide (SourceCompilationPlan.runtimeEvidenceGoal item = goal)) with
        | none => simp [found] at accepted
        | some raw =>
          rw [found] at accepted
          obtain ⟨tail, remaining, same⟩ := map_ok accepted
          refine ⟨_, raw, tail, selected, matchedPredicate, .assumption (lookup_of_find found), ?_, remaining, same⟩
          have rawGoal := List.find?_some found
          have rawSame : SourceCompilationPlan.runtimeEvidenceGoal raw = goal := of_decide_eq_true rawGoal
          exact rawSame.trans (matchedGoal.trans matchedPredicate)

/-- Compiler success becomes the independent requirement-production judgment
when the same retained ledger and caller dictionary have source validity. -/
theorem produces {caller : SourceSpecialization.SpecializedFunction} {occurrence : ExpressionId}
    {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment} {ids : List RequirementId}
    {predicates : List ProgramPredicate} {context : Context}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (retained : SolvedRequirementsValid context caller.function.solvedRequirements)
    (valid : (environment available).Valid context.signatures.resolutionRules)
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok result) :
    RequirementsProduceEnvironment context (environment available) ids predicates (environment result) := by
  induction ids generalizing predicates result with
  | nil =>
    cases predicates with
    | nil => cases accepted; exact .nil
    | cons predicate predicates => cases accepted
  | cons id ids ih =>
    cases predicates with
    | nil => cases accepted
    | cons predicate predicates =>
      obtain ⟨solved, head, tail, selected, samePredicate, closed, goal, remaining, rfl⟩ := cons_accepted accepted
      have contains := selected.contains ledger
      have rowValid := retained solved (ledger ▸ contains.1)
      have closedValid := EvidenceCloses.preserves_valid valid closed (retained_valid rowValid)
      have headProduces : RequirementProducesEvidence context (environment available) id predicate (evidence head) :=
        .intro contains samePredicate (predicate_represents _) rowValid closed (samePredicate ▸ closedValid)
      change RequirementsProduceEnvironment context (environment available) (id :: ids) (predicate :: predicates)
        ((SourceCompilationPlan.runtimeEvidenceGoal head, evidence head) :: environment tail)
      rw [goal]
      exact .cons headProduces (ih remaining)

/-- A resolver-created caller dictionary discharges the caller-validity
premise. The retained source ledger remains independently checked. -/
theorem produces_of_resolved {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {occurrence : ExpressionId} {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate} {context : Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (retained : SolvedRequirementsValid context caller.function.solvedRequirements)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok result) :
    RequirementsProduceEnvironment context (environment available) ids predicates (environment result) :=
  produces ledger retained (by simpa only [signatures] using (resolved_valid resolved).1) accepted

/-- Exact singleton selection is sufficient for agreement at reached IDs;
no global uniqueness assumption is imposed on unrelated ledger entries. -/
theorem agrees {caller : SourceSpecialization.SpecializedFunction} {occurrence : ExpressionId}
    {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment} {ids : List RequirementId}
    {predicates : List ProgramPredicate} {context : Context} {semantic : EvidenceEnvironment}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok result)
    (independent : RequirementsProduceEnvironment context (environment available) ids predicates semantic) :
    semantic = environment result := by
  induction independent generalizing result with
  | nil => cases accepted; rfl
  | @cons id ids predicate predicates selected rest head tail ih =>
    obtain ⟨solved, raw, remaining, singleton, samePredicate, closed, goal, acceptedTail, rfl⟩ := cons_accepted accepted
    cases head with
    | intro contains _ represents _ closes _ =>
      have sameRow := singleton.unique ledger contains
      cases sameRow
      have sameOpen := represents.functional (predicate_represents _)
      rw [sameOpen] at closes
      have sameEvidence := closes_functional closes closed
      change (predicate, selected) :: rest = (SourceCompilationPlan.runtimeEvidenceGoal raw, evidence raw) :: environment remaining
      rw [sameEvidence, goal, ih acceptedTail]

end Solcore.SourceSemantics.CoreLowering.CallableCallEvidence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedCallEvidence
/-! Actual callee authentication validates every returned evidence tree. Together
with the real caller resolver and materializer receipts, it validates precisely
the retained rows consumed by a call; unrelated local templates are not required
to be valid declaration assumptions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedCallEvidence
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallableNamedMetadata (evidence environment evidence_represents)
open CallableEvidenceEnvironment

private instance : LawfulBEq ProgramTraitId where
  eq_of_beq := by
    intro a b same
    cases a <;> cases b <;> simp_all [BEq.beq, instBEqProgramTraitId.beq]
  rfl := by intro a; cases a with
    | builtin id => cases id <;> rfl
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
  rfl := by intro a; cases a with
    | builtin id => cases id <;> rfl
    | declaration id => simp [BEq.beq, instBEqProgramImplId.beq]

/-- All positions are authenticated, including later entries shadowed by the
same goal. This is stronger than validity of observable first-match lookups. -/
theorem selection_valid {signatures : ProgramSignatures} {key : SourceCompilationPlan.Key} {index : Nat}
    {predicates : List ProgramPredicate} {actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (accepted : SourceCompilationPlan.validateRuntimeEvidenceSelection signatures key index predicates actual = .ok ()) :
    Forall₂ (fun goal raw => EvidenceValid [] signatures.resolutionRules goal (evidence raw)) predicates actual := by
  induction predicates generalizing actual index with
  | nil => cases actual <;> simp_all [SourceCompilationPlan.validateRuntimeEvidenceSelection]; exact .nil
  | cons goal rest ih =>
    cases actual with
    | nil => simp [SourceCompilationPlan.validateRuntimeEvidenceSelection] at accepted
    | cons raw remaining =>
      simp only [SourceCompilationPlan.validateRuntimeEvidenceSelection] at accepted
      split at accepted
      · cases accepted
      · cases accepted
      · rename_i selected resolved
        split at accepted
        · rename_i same
          have equal : selected = raw := eq_of_beq same
          obtain ⟨semantic, represents, valid⟩ := TraitResolutionSoundness.resolve_success_evidenceValid resolved
          have valid : EvidenceValid [] signatures.resolutionRules goal (evidence raw) := by
            rw [represents.functional (evidence_represents selected)] at valid
            simpa only [equal] using valid
          exact .cons valid (ih accepted)
        · cases raw; cases accepted

theorem authenticated_valid {signatures : ProgramSignatures} {key : SourceCompilationPlan.Key}
    {predicates : List ProgramPredicate} {actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (accepted : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence signatures key predicates actual = .ok ()) :
    Forall₂ (fun goal raw => EvidenceValid [] signatures.resolutionRules goal (evidence raw)) predicates actual := by
  unfold SourceCompilationPlan.validateAuthenticatedRuntimeEvidence at accepted
  cases goals : SourceCompilationPlan.validateRuntimeEvidence key predicates actual with
  | error error => simp [goals, bind, Except.bind] at accepted
  | ok value =>
    simp only [goals, bind, Except.bind] at accepted
    exact selection_valid accepted

/-- A retained implementation is the authenticated returned tree. A retained
assumption is justified by an actual caller dictionary key, not by its ID. -/
theorem retained_of_closed {context : Context} {caller : EvidenceEnvironment}
    {row : SolvedRequirement} {result : TraitEvidence}
    (keys : ∀ goal, goal ∈ caller.map Prod.fst → goal ∈ context.assumptions)
    (goal : row.evidence.goal = row.predicate)
    (closed : EvidenceCloses caller (predicateEvidence row.evidence) result)
    (valid : EvidenceValid [] context.signatures.resolutionRules row.predicate result) :
    SolvedRequirementValid context row := by
  cases row with
  | mk id predicate retained =>
    cases retained with
    | assumption assumed =>
      cases closed with
      | assumption found =>
        exact .intro (.intro (.assumption assumed) (by
          change EvidenceValid context.assumptions context.signatures.resolutionRules predicate (.assumption assumed)
          have same : assumed = predicate := goal
          cases same
          exact .assumption (keys _ found.key_mem)))
    | implementation raw =>
      have same := closes_functional closed (closes_self caller raw)
      rw [same] at valid
      exact .intro (.intro (.implementation (evidence_represents raw))
        (valid.weakenAssumptions (by simp)))

private theorem predicate_goal (retained : PredicateEvidence) :
    (predicateEvidence retained).goal = retained.goal := by
  cases retained with
  | assumption goal => rfl
  | implementation raw => cases raw; simp [predicateEvidence, evidence, TraitEvidence.goal, PredicateEvidence.goal]

/-- Only reached rows acquire validity. No validity premise is imposed on the
whole ledger, including unbound local-scheme templates. -/
theorem produces_of_authenticated {caller : SourceSpecialization.SpecializedFunction} {occurrence : ExpressionId}
    {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment} {ids : List RequirementId}
    {predicates : List ProgramPredicate} {context : Context}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (keys : ∀ goal, goal ∈ (environment available).map Prod.fst → goal ∈ context.assumptions)
    (callerValid : (environment available).Valid context.signatures.resolutionRules)
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok result)
    (authenticated : Forall₂ (fun goal raw => EvidenceValid [] context.signatures.resolutionRules goal (evidence raw)) predicates result) :
    RequirementsProduceEnvironment context (environment available) ids predicates (environment result) := by
  induction ids generalizing predicates result with
  | nil => cases predicates with
    | nil => cases accepted; exact .nil
    | cons => cases accepted
  | cons id ids ih =>
    cases predicates with
    | nil => cases accepted
    | cons predicate predicates =>
      obtain ⟨row, head, tail, selected, rowGoal, closed, headGoal, remaining, rfl⟩ := CallableCallEvidence.cons_accepted accepted
      cases authenticated with
      | cons valid validTail =>
        have openGoal : row.evidence.goal = row.predicate := by
          have same := EvidenceCloses.goal_eq callerValid closed
          rw [evidence_goal, predicate_goal, headGoal] at same
          exact same.symm.trans rowGoal.symm
        have retained := retained_of_closed keys openGoal closed (rowGoal ▸ valid)
        change RequirementsProduceEnvironment context (environment available) (id :: ids) (predicate :: predicates)
          ((SourceCompilationPlan.runtimeEvidenceGoal head, evidence head) :: environment tail)
        rw [headGoal]
        exact .cons (.intro (selected.contains ledger) rowGoal (predicate_represents _) retained closed valid)
          (ih remaining validTail)

/-- The three real compiler receipts close caller and reached-row validity.
Source context alignment is explicit and may include extra lexical assumptions. -/
theorem produces {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {occurrence : ExpressionId} {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate} {context : Context} {callee : SourceCompilationPlan.Key}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok result)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures callee predicates result = .ok ()) :
    RequirementsProduceEnvironment context (environment available) ids predicates (environment result) := by
  have keys : ∀ goal, goal ∈ (environment available).map Prod.fst → goal ∈ context.assumptions := by
    intro goal member
    exact assumptions _ ((resolved_valid resolved).2 ▸ member)
  exact produces_of_authenticated ledger keys
    (by simpa only [signatures] using (resolved_valid resolved).1) accepted
    (by simpa only [signatures] using authenticated_valid authenticated)

end Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedCallEvidence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableNamedReversal
/-! Reversing the ordered parameter ledger preserves the real instantiation
selector while changing the independently retained source metadata. Equality of
source values is transported by an explicit involution, never by identifying
parameter lists that only denote the same mapping. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableNamedReversal
open Frontend SourceInference TypeSystem

/-- Only the parameter ledger order changes; source header and evidence are
left intact. -/
def instantiation (source : DeclarationInstantiation) : DeclarationInstantiation :=
  {source with parameterSubstitution := source.parameterSubstitution.reverse}

@[simp] theorem instantiation_twice (source : DeclarationInstantiation) :
    instantiation (instantiation source) = source := by
  cases source; simp [instantiation]

private theorem exact_binding_reverse (source : ParameterSubstitution) (parameter : TypeParameterId) :
    SourceCompilationPlan.exactParameterBinding? source.reverse parameter =
      SourceCompilationPlan.exactParameterBinding? source parameter := by
  unfold SourceCompilationPlan.exactParameterBinding?
  rw [List.filter_reverse]
  generalize source.filter (fun entry => entry.1 == parameter) = entries
  cases entries with
  | nil => rfl
  | cons head rest =>
    cases rest with
    | nil => rfl
    | cons second remaining =>
      cases reversed : (head :: second :: remaining).reverse with
      | nil => rfl
      | cons first tail =>
        cases tail with
        | nil =>
          have length := congrArg List.length reversed
          simp only [List.length_reverse, List.length_cons, List.length_nil] at length
          omega
        | cons next after => rfl

/-- The matcher looks up each key exactly once and compares all entries. Its
right ledger traversal order does not alter the accepted mapping. -/
theorem substitutions_reverse_right (left right : ParameterSubstitution) :
    SourceCompilationPlan.parameterSubstitutionsEquivalent left right.reverse =
      SourceCompilationPlan.parameterSubstitutionsEquivalent left right := by
  simp only [SourceCompilationPlan.parameterSubstitutionsEquivalent, List.length_reverse,
    exact_binding_reverse, List.all_reverse]

/-- The actual compiler checks every other declaration field unchanged. -/
theorem matcher_reverse (specialized : SourceSpecialization.SpecializedFunction) (source : DeclarationInstantiation) :
    SourceCompilationPlan.specializationMatchesInstantiation specialized (instantiation source) =
      SourceCompilationPlan.specializationMatchesInstantiation specialized source := by
  simp only [SourceCompilationPlan.specializationMatchesInstantiation, instantiation, substitutions_reverse_right]

/-- Even missing/duplicate-target errors are unchanged by ledger reversal. -/
theorem target_reverse (plan : SourceCompilationPlan.Plan) (source : DeclarationInstantiation) :
    SourceCompilationPlan.exactInstantiationKey plan (instantiation source) =
      SourceCompilationPlan.exactInstantiationKey plan source := by
  simp only [SourceCompilationPlan.exactInstantiationKey, SourceCompilationPlan.specializationMatchesInstantiation,
    instantiation, substitutions_reverse_right]

def global (source : Dynamic.GlobalFunction) : Dynamic.GlobalFunction :=
  {source with instantiation := instantiation source.instantiation}

@[simp] theorem global_twice (source : Dynamic.GlobalFunction) : global (global source) = source := by
  cases source; simp [global]

def value : Dynamic.Value → Dynamic.Value
  | .global function => .global (global function)
  | other => other

@[simp] theorem value_twice (source : Dynamic.Value) : value (value source) = source := by
  cases source <;> simp [value]

theorem value_injective : Function.Injective value := by
  intro left right same
  have inverted := congrArg value same
  simpa only [value_twice] using inverted

/-- Evidence order and tree identity are preserved independently of the
parameter ledger permutation. -/
@[simp] theorem global_evidence (source : Dynamic.GlobalFunction) : (global source).evidence = source.evidence := rfl

@[simp] theorem global_type (source : Dynamic.GlobalFunction) : (global source).instantiation.type = source.instantiation.type := rfl

end Solcore.SourceSemantics.CoreLowering.CallableNamedReversal
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableNamedCanonicalOrder
/-! Actual declaration inference and specialization keep opposite ordered
parameter ledgers. This module relates those exact records without identifying
source functions merely because their substitutions denote the same mapping. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableNamedCanonicalOrder
open Frontend SourceInference TypeSystem

/-- The canonical source record uses the reverse order retained by inference.
All other metadata fields are those authenticated by the real matcher. -/
def retainedInstantiation (specialized : SourceSpecialization.SpecializedFunction) : DeclarationInstantiation :=
  {CallableNamedMetadata.instantiation specialized with
    parameterSubstitution := specialized.parameterSubstitution.reverse}

@[simp] theorem reverse_retained (specialized : SourceSpecialization.SpecializedFunction) :
    CallableNamedReversal.instantiation (retainedInstantiation specialized) =
      CallableNamedMetadata.instantiation specialized := by
  simp [retainedInstantiation, CallableNamedReversal.instantiation, CallableNamedMetadata.instantiation]

/-- The record produced by declaration inference, followed by final flexible
solving and caller specialization. Both passes retain the ordered rigid keys. -/
def inferredInstantiation (signature : ProgramFunctionSignature) (next : Nat)
    (final : Substitution) (caller : ParameterSubstitution) : DeclarationInstantiation :=
  SourceSpecialization.applyInstantiation caller
    ((DeclarationInstantiation.ofInstantiated signature (signature.scheme.instantiate next)).applySubstitution final)

@[simp] theorem inferred_parameterDomain (signature : ProgramFunctionSignature) (next : Nat)
    (final : Substitution) (caller : ParameterSubstitution)
    (unique : signature.scheme.parameters.Nodup) :
    (inferredInstantiation signature next final caller).parameterSubstitution.map Prod.fst =
      signature.scheme.parameters.reverse := by
  simp only [inferredInstantiation, SourceSpecialization.applyInstantiation_parameterDomain,
    DeclarationInstantiation.applySubstitution_parameterDomain, DeclarationInstantiation.ofInstantiated]
  exact ConstrainedDeclarationScheme.instantiate_parameterSubstitution_domain_reverse signature.scheme next unique
end Solcore.SourceSemantics.CoreLowering.CallableNamedCanonicalOrder

namespace Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
open Frontend SourceInference TypeSystem
open CallableNamedCanonicalOrder

/-- The real matcher plus the checker's reverse domain order determines every
ordered field of the independently retained source instantiation. -/
theorem Matches.retained_canonical {specialized : SourceSpecialization.SpecializedFunction}
    {source : DeclarationInstantiation} (matched : Matches specialized source)
    (domain : source.parameterSubstitution.map Prod.fst =
      (specialized.parameterSubstitution.map Prod.fst).reverse) :
    source = retainedInstantiation specialized := by
  have reversed : Matches specialized (CallableNamedReversal.instantiation source) := by
    refine ⟨matched.ownership, matched.arguments, matched.declaration, ?_, matched.type,
      matched.predicates, matched.parameterComptime, matched.returnComptime⟩
    simpa only [CallableNamedReversal.instantiation, CallableNamedReversal.substitutions_reverse_right] using matched.substitution
  have ordered : specialized.parameterSubstitution.map Prod.fst =
      (CallableNamedReversal.instantiation source).parameterSubstitution.map Prod.fst := by
    simp only [CallableNamedReversal.instantiation, List.map_reverse, domain, List.reverse_reverse]
  have canonical := reversed.canonical ordered
  have inverted := congrArg CallableNamedReversal.instantiation canonical
  change CallableNamedReversal.instantiation (CallableNamedReversal.instantiation source) =
    retainedInstantiation specialized at inverted
  simpa only [CallableNamedReversal.instantiation_twice] using inverted

/-- Actual successful specialization and actual inferred-record formation close
the domain-order condition. The matcher continues to authenticate all fields. -/
theorem Matches.retained_of_specialization {signature : ProgramFunctionSignature}
    {function : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature function supplied = .ok specialized)
    (unique : signature.scheme.parameters.Nodup) (next : Nat) (final : Substitution) (caller : ParameterSubstitution)
    (matched : Matches specialized (inferredInstantiation signature next final caller)) :
    inferredInstantiation signature next final caller = retainedInstantiation specialized := by
  apply matched.retained_canonical
  rw [inferred_parameterDomain signature next final caller unique,
    SourceSpecialization.specializeFunction_parameterDomain accepted]
end Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCallRequirementLayouts
/-! Exact source-ordered call requirement layouts recovered from successful
compiler selection. Coercion requirements stay on both sides of the selected
signature spine; no unordered set of requirement IDs is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCallRequirementLayouts
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallableNamedMetadata (evidence environment)

private instance : LawfulBEq RequirementId where
  eq_of_beq := by
    intro a b same
    cases a; cases b
    simp_all [BEq.beq, instBEqRequirementId.beq]
  rfl := by intro a; cases a; simp [BEq.beq, instBEqRequirementId.beq]

/-- The source split includes every coercion step and every retained ID. -/
def Split (node : ExpressionNode) (count : Nat) (ids : List RequirementId) : Prop :=
  ∃ before after, node.coercions = before ++ after ∧
    node.requirements = coercionRequirementIds before ++ (ids ++ coercionRequirementIds after) ∧ ids.length = count

private def candidateAt (node : ExpressionNode) (count split : Nat) : Option (List RequirementId) :=
  let before := coercionRequirementIds (node.coercions.take split)
  let after := coercionRequirementIds (node.coercions.drop split)
  let middleAndAfter := node.requirements.drop before.length
  let middle := middleAndAfter.take count
  if node.requirements.take before.length = before &&
      middle.length = count && middleAndAfter.drop count = after then some middle else none

private def uniqueLists (candidates : List (List RequirementId)) : List (List RequirementId) :=
  candidates.foldl (fun unique candidate => if unique.contains candidate then unique else unique ++ [candidate]) []

private def candidates (node : ExpressionNode) (count : Nat) : List (List RequirementId) :=
  uniqueLists ((List.range (node.coercions.length + 1)).filterMap (candidateAt node count))

private theorem uniqueLists_mem {id : List RequirementId} {items : List (List RequirementId)} :
    id ∈ uniqueLists items ↔ id ∈ items := by
  have general : ∀ initial, id ∈ items.foldl (fun unique candidate => if unique.contains candidate then unique else unique ++ [candidate]) initial ↔
      id ∈ initial ∨ id ∈ items := by
    induction items with
    | nil => intro initial; simp
    | cons head tail ih =>
      intro initial
      simp only [List.foldl_cons]
      split
      · rename_i present
        rw [ih]
        have member : head ∈ initial := List.contains_iff_mem.mp present
        simp only [List.mem_cons]
        constructor
        · intro accepted; exact accepted.elim Or.inl (fun h => .inr (.inr h))
        · rintro (h | h | h)
          · exact .inl h
          · exact .inl (h ▸ member)
          · exact .inr h
      · rw [ih]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · rintro ((h | h) | h)
          · exact .inl h
          · exact .inr (.inl h)
          · exact .inr (.inr h)
        · rintro (h | h | h)
          · exact .inl (.inl h)
          · exact .inl (.inr h)
          · exact .inr h
  simpa only [uniqueLists, List.not_mem_nil, false_or] using general []

private theorem candidateAt_sound {node : ExpressionNode} {count split : Nat} {ids : List RequirementId}
    (found : candidateAt node count split = some ids) : Split node count ids := by
  simp only [candidateAt] at found
  split at found
  · rename_i checks
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checks
    have same := Option.some.inj found
    subst ids
    refine ⟨node.coercions.take split, node.coercions.drop split, (List.take_append_drop ..).symm, ?_, checks.1.2⟩
    calc
      node.requirements = node.requirements.take (coercionRequirementIds (node.coercions.take split)).length ++
          node.requirements.drop (coercionRequirementIds (node.coercions.take split)).length := (List.take_append_drop ..).symm
      _ = coercionRequirementIds (node.coercions.take split) ++
          node.requirements.drop (coercionRequirementIds (node.coercions.take split)).length := by rw [checks.1.1]
      _ = _ := by
        congr 1
        have parts := List.take_append_drop count (node.requirements.drop (coercionRequirementIds (node.coercions.take split)).length)
        rw [checks.2] at parts
        exact parts.symm
  · cases found

private theorem candidateAt_complete {node : ExpressionNode} {count : Nat} {ids : List RequirementId}
    {before after : List CoercionStep}
    (steps : node.coercions = before ++ after)
    (requirements : node.requirements = coercionRequirementIds before ++ (ids ++ coercionRequirementIds after))
    (length : ids.length = count) : candidateAt node count before.length = some ids := by
  simp [candidateAt, steps, requirements, ← length]

private theorem candidates_iff {node : ExpressionNode} {count : Nat} {ids : List RequirementId} :
    ids ∈ candidates node count ↔ Split node count ids := by
  rw [candidates, uniqueLists_mem, List.mem_filterMap]
  constructor
  · rintro ⟨split, _, found⟩
    exact candidateAt_sound found
  · rintro ⟨before, after, steps, requirements, length⟩
    exact ⟨before.length, by simp only [List.mem_range, steps, List.length_append]; omega, candidateAt_complete steps requirements length⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩


private def predicateMatches (caller : SourceSpecialization.SpecializedFunction)
    (requirements : List RequirementId) (predicates : List ProgramPredicate) : Bool :=
  requirements.length == predicates.length &&
    (List.zip requirements predicates).all fun pair =>
      match (match caller.function.solvedRequirements.filter (fun solved => solved.id == pair.1) with
        | [solved] => some solved
        | _ => none) with
      | some solved => solved.predicate == pair.2 && solved.evidence.goal == pair.2
      | none => false

private theorem direct_selected {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (accepted : SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation = .ok actual) :
    ∃ ids, Split node instantiation.predicates.length ids ∧
      SourceCompilationPlan.materializeCallEvidence caller node.id available ids instantiation.predicates = .ok actual ∧
      (candidates node instantiation.predicates.length = [ids] ∨
        (candidates node instantiation.predicates.length).filter (fun ids => predicateMatches caller ids instantiation.predicates) = [ids]) := by
  unfold SourceCompilationPlan.exactDirectCallRuntimeEvidence at accepted
  obtain ⟨ids, chosen, materialized⟩ := bind_ok accepted
  change (do
    if node.coercions.isEmpty && node.requirements.length != instantiation.predicates.length then
      throw (.callRequirementCountMismatch caller.key node.id instantiation.predicates.length node.requirements.length)
    match (_ : Option RequirementId) with
    | some requirement => throw (.duplicateCallRequirement caller.key node.id requirement)
    | none => pure ()
    let structural := candidates node instantiation.predicates.length
    let matched := structural.filter fun ids => predicateMatches caller ids instantiation.predicates
    match structural with
    | [requirements] => return requirements
    | _ => pure ()
    match matched with
    | [requirements] => pure requirements
    | _ => throw (.invalidDirectCallRequirementLayout caller.key node.id node.requirements)
    : Except SourceTypedRuntime.RuntimeError (List RequirementId)) = .ok ids at chosen
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at chosen
  split at chosen
  · simp at chosen
  · split at chosen
    · cases chosen
    · split at chosen
      · rename_i selected same
        cases chosen
        exact ⟨ids, candidates_iff.mp (by rw [same]; simp), materialized, .inl same⟩
      · split at chosen
        · rename_i selected same
          cases chosen
          exact ⟨ids, candidates_iff.mp (List.mem_filter.mp (show ids ∈ (candidates node instantiation.predicates.length).filter (fun ids => predicateMatches caller ids instantiation.predicates) from by rw [same]; simp)).1, materialized, .inr same⟩
        · cases chosen

/-- The actual chosen signature dictionary has the independent interleaving
required for a source direct call. Full callee authentication validates only
its reached rows; no source ledger validity input is required. -/
theorem direct_produces {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment} {context : Context} {callee : SourceCompilationPlan.Key}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation = .ok actual)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures callee instantiation.predicates actual = .ok ()) :
    DirectCallProducesEvidence context (environment available) node.requirements node.coercions instantiation.predicates (environment actual) := by
  obtain ⟨ids, ⟨before, after, steps, requirements, _⟩, materialized, _⟩ := direct_selected accepted
  exact .intro steps requirements
    (CallableAuthenticatedCallEvidence.produces signatures ledger assumptions resolved materialized authenticated)


private instance : LawfulBEq ProgramTraitId where
  eq_of_beq := by intro a b same; cases a <;> cases b <;> simp_all [BEq.beq, instBEqProgramTraitId.beq]
  rfl := by
    intro a
    cases a with
    | builtin id => cases id <;> rfl
    | declaration id => simp [BEq.beq, instBEqProgramTraitId.beq]

private instance : LawfulBEq ProgramPredicate where
  eq_of_beq := by
    intro first second same
    cases first with
    | mk a b c =>
      cases second with
      | mk x y z =>
        change ((a == x) && ((b == y) && (c == z))) = true at same
        simp only [Bool.and_eq_true, beq_iff_eq] at same
        rcases same with ⟨rfl, rfl, rfl⟩
        rfl
  rfl := by
    intro value
    change ((value.trait == value.trait) && ((value.subject == value.subject) && (value.arguments == value.arguments))) = true
    simp

/-- Exact singleton rows are needed only for IDs reachable at this occurrence.
This is stronger than identifying two equal rows in a duplicated ledger. -/
def Singletons (caller : SourceSpecialization.SpecializedFunction) (context : Context) (node : ExpressionNode) : Prop :=
  ∀ id, id ∈ node.requirements → ∀ row, ContainsRequirement context id row → CallableCallEvidence.Selected caller id row

private theorem filter_singleton {rows : List SolvedRequirement} {row : SolvedRequirement}
    (unique : (rows.map (·.id)).Nodup) (member : row ∈ rows) :
    rows.filter (fun candidate => decide (candidate.id = row.id)) = [row] := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | member
    · have empty : rest.filter (fun candidate => decide (candidate.id = row.id)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro candidate present
        have different : candidate.id ≠ row.id := by
          intro same
          exact distinct.1 (List.mem_map.mpr ⟨candidate, present, same⟩)
        simp [different]
      simp [empty]
    · have different : first.id ≠ row.id := by
        intro same
        exact distinct.1 (List.mem_map.mpr ⟨row, member, same.symm⟩)
      simpa [different] using ih distinct.2 member

/-- The ordinary source identity invariant supplies the reached singleton
condition without imposing validity on unrelated retained rows. -/
theorem singletons_of_unique {caller : SourceSpecialization.SpecializedFunction}
    {context : Context} {node : ExpressionNode}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (unique : RequirementIdsUnique context) : Singletons caller context node := by
  intro id _ row contains
  obtain ⟨member, same⟩ := contains
  change caller.function.solvedRequirements.filter (fun candidate => decide (candidate.id = id)) = [row]
  rw [← ledger, ← same]
  exact filter_singleton unique member

private theorem predicateMatches_of_produces {caller : SourceSpecialization.SpecializedFunction} {context : Context}
    {available result : EvidenceEnvironment} {ids : List RequirementId} {predicates : List ProgramPredicate}
    (singleton : ∀ id, id ∈ ids → ∀ row, ContainsRequirement context id row → CallableCallEvidence.Selected caller id row)
    (produced : RequirementsProduceEnvironment context available ids predicates result) : predicateMatches caller ids predicates = true := by
  induction produced with
  | nil => rfl
  | @cons id ids predicate predicates selected result head tail ih =>
    have rest := ih (fun id member row contains => singleton id (List.mem_cons_of_mem _ member) row contains)
    cases head with
    | intro contains same represents valid closes closedValid =>
      rename_i row openEvidence
      have chosen := singleton _ (by simp) _ contains
      have chosen : caller.function.solvedRequirements.filter (fun solved => solved.id == id) = [row] := by
        have predicates : (fun solved : SolvedRequirement => solved.id == id) =
            (fun solved : SolvedRequirement => decide (solved.id = id)) := by
          funext solved
          apply Bool.eq_iff_iff.mpr
          simp only [beq_iff_eq, decide_eq_true_eq]
        rw [predicates]
        exact chosen
      have goal := valid.evidence_goal_eq
      simp only [predicateMatches, Bool.and_eq_true] at rest ⊢
      refine ⟨by simp [tail.length_eq.1], ?_⟩
      simp only [List.zip_cons_cons, List.all_cons, chosen, same, goal, BEq.rfl, Bool.true_and]
      exact rest.2

/-- Any independent source split whose reached ledger rows are singleton has
exactly the dictionary returned by the real compiler selection. -/
theorem direct_agrees {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {context : Context} {semantic : EvidenceEnvironment}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (singleton : Singletons caller context node)
    (accepted : SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation = .ok actual)
    (independent : DirectCallProducesEvidence context (environment available) node.requirements node.coercions instantiation.predicates semantic) :
    semantic = environment actual := by
  obtain ⟨ids, layout, materialized, chosen⟩ := direct_selected accepted
  cases independent with
  | @intro before after sourceIds sourceResult steps requirements produced =>
    have member : sourceIds ∈ candidates node instantiation.predicates.length :=
      candidates_iff.mpr ⟨before, after, steps, requirements, produced.length_eq.1⟩
    have same : sourceIds = ids := by
      rcases chosen with structural | filtered
      · rw [structural] at member
        exact List.mem_singleton.mp member
      · have matched := predicateMatches_of_produces (caller := caller) (fun id member row contains =>
          singleton id (by rw [requirements]; simp only [List.mem_append]; exact .inr (.inl member)) row contains) produced
        have inFilter : sourceIds ∈ (candidates node instantiation.predicates.length).filter
            (fun ids => predicateMatches caller ids instantiation.predicates) :=
          List.mem_filter.mpr ⟨member, matched⟩
        rw [filtered] at inFilter
        exact List.mem_singleton.mp inFilter
    subst sourceIds
    exact CallableCallEvidence.agrees ledger materialized produced

/-- Standalone references retain their signature requirements before the whole
output coercion path, including repeated requirement IDs in that path. -/
theorem ordinary_owned {node : ExpressionNode} {ids : List RequirementId}
    (selected : SourceCompilationPlan.ordinaryOwnedRequirements? node = some ids) :
    OrdinaryRequirementLayout node.requirements node.coercions ids := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements? at selected
  dsimp only at selected
  split at selected
  · cases selected
  · split at selected
    · rename_i same
      cases selected
      exact same
    · cases selected

private theorem reference_selected {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (accepted : SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence caller node available instantiation = .ok actual) :
    ∃ ids, OrdinaryRequirementLayout node.requirements node.coercions ids ∧
      SourceCompilationPlan.materializeCallEvidence caller node.id available ids instantiation.predicates = .ok actual := by
  unfold SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence at accepted
  obtain ⟨ids, chosen, materialized⟩ := bind_ok accepted
  change (do
    let requirements ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
      | some requirements => pure requirements
      | none => throw (.invalidDeclarationReferenceRequirementLayout caller.key node.id node.requirements)
    if requirements.length != instantiation.predicates.length then
      throw (.callRequirementCountMismatch caller.key node.id instantiation.predicates.length requirements.length)
    match (_ : List RequirementId → Option RequirementId) requirements with
    | some requirement => throw (.duplicateCallRequirement caller.key node.id requirement)
    | none => pure ()
    unless predicateMatches caller requirements instantiation.predicates do
      throw (.invalidDeclarationReferenceRequirementLayout caller.key node.id requirements)
    pure requirements : Except SourceTypedRuntime.RuntimeError (List RequirementId)) = .ok ids at chosen
  cases found : SourceCompilationPlan.ordinaryOwnedRequirements? node with
  | none => simp [found, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at chosen
  | some requirements =>
    simp only [found, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at chosen
    split at chosen
    · cases chosen
    · split at chosen
      · cases chosen
      · split at chosen
        · cases chosen
          exact ⟨ids, ordinary_owned found, materialized⟩
        · cases chosen

theorem reference_produces {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment} {context : Context} {callee : SourceCompilationPlan.Key}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence caller node available instantiation = .ok actual)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures callee instantiation.predicates actual = .ok ()) :
    ∃ ids, OrdinaryRequirementLayout node.requirements node.coercions ids ∧
      RequirementsProduceEnvironment context (environment available) ids instantiation.predicates (environment actual) := by
  obtain ⟨ids, layout, materialized⟩ := reference_selected accepted
  exact ⟨ids, layout, CallableAuthenticatedCallEvidence.produces signatures ledger assumptions resolved materialized authenticated⟩

theorem reference_agrees {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {context : Context} {ids : List RequirementId} {semantic : EvidenceEnvironment}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (accepted : SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence caller node available instantiation = .ok actual)
    (layout : OrdinaryRequirementLayout node.requirements node.coercions ids)
    (independent : RequirementsProduceEnvironment context (environment available) ids instantiation.predicates semantic) :
    semantic = environment actual := by
  obtain ⟨chosen, selected, materialized⟩ := reference_selected accepted
  have same : ids = chosen := List.append_cancel_right (layout.symm.trans selected)
  subst ids
  exact CallableCallEvidence.agrees ledger materialized independent

end Solcore.SourceSemantics.CoreLowering.CallableCallRequirementLayouts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCallEvidenceCertificates
/-! Successful declaration branches of the actual evidence lowering retain
caller resolution, exact target selection and the complete authenticated
callee dictionary. Returning none only delegates ordinary lowering; indirect
local calls do not select a declaration through this interface. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCallEvidenceCertificates
open Core Frontend SourceInference
open CallableNamedMetadata (environment)
abbrev Context := SourceCoreFunctions.Context
abbrev Key := SourceCompilationPlan.Key
abbrev Specialized := SourceSpecialization.SpecializedFunction
abbrev RuntimeEvidence := SourceTypedRuntime.RuntimeEvidenceEnvironment

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem edge_target {plan : SourceCompilationPlan.Plan} {caller target selected : Key}
    {id : ExpressionId} {reference : Bool}
    (accepted : (if reference then SourceCompilationPlan.exactReferenceKey plan caller id target
      else SourceCompilationPlan.exactCallKey plan caller id target) = .ok selected) : selected = target := by
  cases reference <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
  all_goals
    first | unfold SourceCompilationPlan.exactCallKey at accepted
          | unfold SourceCompilationPlan.exactReferenceKey at accepted
    split at accepted
    · cases accepted
    · rename_i edge filtered
      cases accepted
      have member : edge ∈ [edge] := .head _
      rw [← filtered] at member
      have facts := (List.mem_filter.mp member).2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at facts
      exact facts.2
    · cases accepted

/-- Receipts for the real selected plan record and the exact ordered raw
result. Full metadata matching is derived from the two actual selectors. -/
structure Selection (program : CheckedProgram) (caller : Specialized) (compilation : Context)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) (reference : Bool) where private mk ::
  available : RuntimeEvidence
  actual : RuntimeEvidence
  target : Key
  key : Key
  specialized : Specialized
  coercionsValid : node.hasValidCoercionPath = true
  owner : caller.key = compilation.owner
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available
  materialized : (if reference then SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence caller node available instantiation
    else SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation) = .ok actual
  targetSelected : SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok target
  edge : (if reference then SourceCompilationPlan.exactReferenceKey compilation.plan compilation.owner node.id target
    else SourceCompilationPlan.exactCallKey compilation.plan compilation.owner node.id target) = .ok key
  selected : SourceCompilationPlan.exactSpecialization compilation.plan key = .ok specialized
  authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key specialized.assumptions actual = .ok ()

namespace Selection
variable {program : CheckedProgram} {caller : Specialized} {compilation : Context}
  {node : ExpressionNode} {instantiation : DeclarationInstantiation} {reference : Bool}

theorem key_eq (receipt : Selection program caller compilation node instantiation reference) : receipt.key = receipt.target :=
  edge_target receipt.edge

theorem metadata (receipt : Selection program caller compilation node instantiation reference) :
    CallableNamedMetadata.Matches receipt.specialized instantiation :=
  CallableNamedMetadata.matches_of_exact receipt.targetSelected (receipt.key_eq ▸ receipt.selected)

theorem authenticated_predicates (receipt : Selection program caller compilation node instantiation reference) :
    SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures receipt.key instantiation.predicates receipt.actual = .ok () := by
  rw [← receipt.metadata.predicates]
  exact receipt.authenticated

end Selection

/-- The source callee carries the complete same declaration instantiation,
including ordered predicates and parameter metadata. -/
theorem callee_metadata {source : TypedSource} {id callee : ExpressionId}
    {instantiation : DeclarationInstantiation}
    (accepted : SourceCompilationPlan.validateDirectDeclarationCallee source id callee instantiation = .ok ()) :
    ∃ node name, source.lookupExpression? callee = some node ∧
      node.form = .reference name (.declaration instantiation) ∧ node.type = instantiation.type := by
  unfold SourceCompilationPlan.validateDirectDeclarationCallee at accepted
  split at accepted
  · rename_i found
    split at accepted
    · rename_i matched
      simp only [Bool.and_eq_true, decide_eq_true_eq] at matched
      obtain ⟨rfl, same⟩ := matched
      exact ⟨_, _, found, rfl, same⟩
    · cases accepted
  · cases accepted

/-- Actual outer lowering supplies the previously independent resolver,
materializer and authenticator receipts. The raw call/callee metadata and
argument arity are obtained before any child compilation or output coercion. -/
theorem direct_of_accepted {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {caller : Specialized} {compilation : Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreEvidence.Scope} {id callee : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    {lowered : SourceCoreEvidence.Lowered}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program projectType caller compilation child fuel source scope id reasonAt callables = .ok (some lowered)) :
    ∃ receipt : Selection program caller compilation node instantiation false,
      SourceCompilationPlan.validateDirectDeclarationCallee source id callee instantiation = .ok () ∧
      arguments.length = receipt.specialized.function.typedBody.inputs.length := by
  unfold SourceCoreEvidence.lowerWithProjector at accepted
  simp only [found, form, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted
  · cases accepted
  · by_cases path : node.hasValidCoercionPath = true
    · by_cases owned : caller.key = compilation.owner
      · simp only [path, ↓reduceIte, owned, ne_eq, not_true_eq_false] at accepted
        obtain ⟨available, resolved, accepted⟩ := bind_ok accepted
        obtain ⟨validated, calleeAccepted, branch⟩ := bind_ok accepted
        obtain ⟨actual, materialized, branch⟩ := bind_ok branch
        obtain ⟨target, targeted, branch⟩ := bind_ok branch
        obtain ⟨key, edge, branch⟩ := bind_ok branch
        obtain ⟨specialized, selected, branch⟩ := bind_ok branch
        obtain ⟨authenticatedUnit, authenticated, branch⟩ := bind_ok branch
        split at branch
        · cases branch
        · rename_i arity
          let receipt : Selection program caller compilation node instantiation false := {
            available, actual, target, key, specialized
            coercionsValid := path
            owner := owned
            resolved := by simpa only [owned] using mapError_ok resolved
            materialized := mapError_ok materialized
            targetSelected := mapError_ok targeted
            edge := by simpa only [(lookupExpression?_sound found).2, Bool.false_eq_true, ↓reduceIte] using mapError_ok edge
            selected := mapError_ok selected
            authenticated := by cases authenticatedUnit; exact mapError_ok authenticated }
          exact ⟨receipt, by cases validated; exact mapError_ok calleeAccepted, by simpa using arity⟩
      · simp [owned, path] at accepted
    · simp [path] at accepted

/-- Standalone declaration references use their actual owned requirement
prefix and selected plan edge, even with retained output coercions. -/
theorem reference_of_accepted {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {caller : Specialized} {compilation : Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreEvidence.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {name : String} {instantiation : DeclarationInstantiation}
    {lowered : SourceCoreEvidence.Lowered}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program projectType caller compilation child fuel source scope id reasonAt callables = .ok (some lowered)) :
    Nonempty (Selection program caller compilation node instantiation true) := by
  unfold SourceCoreEvidence.lowerWithProjector at accepted
  simp only [found, form, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted
  · cases accepted
  · by_cases path : node.hasValidCoercionPath = true
    · by_cases owned : caller.key = compilation.owner
      · simp only [path, ↓reduceIte, owned, ne_eq, not_true_eq_false] at accepted
        obtain ⟨available, resolved, branch⟩ := bind_ok accepted
        obtain ⟨actual, materialized, branch⟩ := bind_ok branch
        obtain ⟨target, targeted, branch⟩ := bind_ok branch
        obtain ⟨key, edge, branch⟩ := bind_ok branch
        obtain ⟨specialized, selected, branch⟩ := bind_ok branch
        obtain ⟨authenticatedUnit, authenticated, _⟩ := bind_ok branch
        exact ⟨{
          available, actual, target, key, specialized
          coercionsValid := path
          owner := owned
          resolved := by simpa only [owned] using mapError_ok resolved
          materialized := mapError_ok materialized
          targetSelected := mapError_ok targeted
          edge := by simpa only [(lookupExpression?_sound found).2, ↓reduceIte] using mapError_ok edge
          selected := mapError_ok selected
          authenticated := by cases authenticatedUnit; exact mapError_ok authenticated }⟩
      · simp [owned, path] at accepted
    · simp [path] at accepted

namespace Selection
variable {program : CheckedProgram} {caller : Specialized} {compilation : Context}
  {node : ExpressionNode} {instantiation : DeclarationInstantiation} {context : SourceSemantics.Context}

/-- Source context alignment remains independent of native projection and of
the actual compiler's administrative environment. -/
theorem direct_produces (receipt : Selection program caller compilation node instantiation false)
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions) :
    Dynamic.DirectCallProducesEvidence context (environment receipt.available) node.requirements node.coercions
      instantiation.predicates (environment receipt.actual) :=
  CallableCallRequirementLayouts.direct_produces signatures ledger assumptions receipt.resolved receipt.materialized receipt.authenticated_predicates

theorem direct_agrees (receipt : Selection program caller compilation node instantiation false)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (singleton : CallableCallRequirementLayouts.Singletons caller context node)
    {semantic : Dynamic.EvidenceEnvironment}
    (independent : Dynamic.DirectCallProducesEvidence context (environment receipt.available) node.requirements node.coercions instantiation.predicates semantic) :
    semantic = environment receipt.actual :=
  CallableCallRequirementLayouts.direct_agrees ledger singleton receipt.materialized independent

theorem reference_produces (receipt : Selection program caller compilation node instantiation true)
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions) :
    ∃ ids, Dynamic.OrdinaryRequirementLayout node.requirements node.coercions ids ∧
      Dynamic.RequirementsProduceEnvironment context (environment receipt.available) ids instantiation.predicates (environment receipt.actual) :=
  CallableCallRequirementLayouts.reference_produces signatures ledger assumptions receipt.resolved receipt.materialized receipt.authenticated_predicates

theorem reference_agrees (receipt : Selection program caller compilation node instantiation true)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    {ids : List RequirementId} {semantic : Dynamic.EvidenceEnvironment}
    (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions ids)
    (independent : Dynamic.RequirementsProduceEnvironment context (environment receipt.available) ids instantiation.predicates semantic) :
    semantic = environment receipt.actual :=
  CallableCallRequirementLayouts.reference_agrees ledger receipt.materialized layout independent

end Selection

/-- The ordinary fast path returns before checking either the caller or the
callee. Its none result must not be used as a declaration-selection receipt. -/
theorem direct_bypass {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {caller : Specialized} {compilation : Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreEvidence.Scope} {id callee : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (assumptions : caller.assumptions = []) :
    SourceCoreEvidence.lowerWithProjector program projectType caller compilation child fuel source scope id reasonAt callables = .ok none := by
  simp [SourceCoreEvidence.lowerWithProjector, found, form, requirements, coercions, assumptions, bind, Except.bind, pure, Except.pure]

end Solcore.SourceSemantics.CoreLowering.CallableCallEvidenceCertificates
end
