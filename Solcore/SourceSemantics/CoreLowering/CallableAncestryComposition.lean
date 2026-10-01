import Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles

/-! Composition through quantified source metadata requires closed substitution
ranges. These syntax laws do not assert dictionary or execution correctness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles
open Frontend SourceInference TypeSystem
open CallableAncestryMetadata

namespace SourceComposition

private theorem except_bind {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

def RangesClosed (substitution : Substitution) : Prop :=
  ∀ entry ∈ substitution, entry.2.freeVariables = []

theorem RangesClosed.without {substitution : Substitution} (closed : RangesClosed substitution)
    (variables : List TypeVarId) : RangesClosed (substitution.without variables) :=
  fun entry member => closed entry (Substitution.mem_of_mem_without member)

theorem fixed {type : Ty} (closed : type.freeVariables = []) (substitution : Substitution) :
    substitution.apply type = type :=
  Ty.apply_eq_self_of_domain_disjoint_freeVariables substitution type (by simp [closed])

theorem lookup_without (substitution : Substitution) (variables : List TypeVarId) (metavariable : TypeVarId) :
    (substitution.without variables).lookup? metavariable =
      if metavariable ∈ variables then none else substitution.lookup? metavariable := by
  by_cases member : metavariable ∈ variables
  · simp [member, Substitution.lookup?_without_of_mem substitution member]
  · rw [if_neg member]
    induction variables generalizing substitution with
    | nil => rfl
    | cons head rest ih =>
      change ((substitution.erase head).without rest).lookup? metavariable = _
      rw [ih (substitution.erase head) (by simp_all)]
      exact Substitution.lookup?_erase_of_ne substitution (by simp_all)

theorem apply_lookup_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) (type : Ty) :
    left.apply type = right.apply type := by
  induction type <;> simp_all [Substitution.apply]

theorem mask_twice (substitution : Substitution) (variables : List TypeVarId) (type : Ty) :
    ((substitution.without variables).without variables).apply type =
      (substitution.without variables).apply type := by
  apply apply_lookup_congr
  intro metavariable
  simp only [lookup_without]
  split <;> rfl

/-- Closed earlier replacements cannot introduce a quantified metavariable into
a binder. This is the additional condition needed beyond type composition. -/
theorem masked_compose (newer older : Substitution) (closed : RangesClosed older)
    (variables : List TypeVarId) (type : Ty) :
    ((newer.compose older).without variables).apply type =
      (newer.without variables).apply ((older.without variables).apply type) := by
  induction type with
  | «variable» metavariable =>
    by_cases boundKey : metavariable ∈ variables
    · simp [Substitution.apply, lookup_without, boundKey]
    · cases found : older.lookup? metavariable with
      | none => simp [Substitution.apply, lookup_without, boundKey, Substitution.lookup?_compose, found]
      | some replacement =>
        have range := closed (metavariable, replacement) (Substitution.lookup?_eq_some_mem found)
        simp [Substitution.apply, lookup_without, boundKey, Substitution.lookup?_compose, found,
          fixed range newer, fixed range (newer.without variables)]
  | parameter | constructor | error => rfl
  | application _ _ left right | function _ _ left right | product _ _ left right | mapping _ _ left right =>
    simp only [Substitution.apply, left, right]
  | proxy _ ih | comptime _ ih => simp only [Substitution.apply, ih]

theorem scheme (newer older : Substitution) (closed : RangesClosed older) (value : Scheme) :
    value.apply (newer.compose older) = (value.apply older).apply newer := by
  simp only [Scheme.apply]
  rw [masked_compose newer older closed]

@[simp] theorem predicate (newer older : Substitution) (value : ProgramPredicate) :
    TypedTraitResolution.applySubstitution (newer.compose older) value =
      TypedTraitResolution.applySubstitution newer (TypedTraitResolution.applySubstitution older value) := by
  simp only [TypedTraitResolution.applySubstitution, Substitution.compose_apply, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro type _
  exact Substitution.compose_apply newer older type

theorem masked_predicate (newer older : Substitution) (closed : RangesClosed older)
    (variables : List TypeVarId) (value : ProgramPredicate) :
    TypedTraitResolution.applySubstitution ((newer.compose older).without variables) value =
      TypedTraitResolution.applySubstitution (newer.without variables)
        (TypedTraitResolution.applySubstitution (older.without variables) value) := by
  simp only [TypedTraitResolution.applySubstitution, masked_compose newer older closed,
    List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro type _
  exact masked_compose newer older closed variables type

@[simp] theorem requirement (newer older : Substitution) (value : LocalSchemeRequirement) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [LocalSchemeRequirement.applySubstitution]

@[simp] theorem binder (newer older : Substitution) (closed : RangesClosed older) (value : TypedBinder) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp only [TypedBinder.applySubstitution, Scheme.apply, mask_twice]
  rw [masked_compose newer older closed]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro requirement _
  simp only [Function.comp_def, LocalSchemeRequirement.applySubstitution, masked_predicate newer older closed]

@[simp] theorem type_function (newer older : Substitution) :
    Substitution.apply (newer.compose older) = (fun type => newer.apply (older.apply type)) :=
  funext (Substitution.compose_apply newer older)

@[simp] theorem predicate_function (newer older : Substitution) :
    TypedTraitResolution.applySubstitution (newer.compose older) =
      (fun value => TypedTraitResolution.applySubstitution newer (TypedTraitResolution.applySubstitution older value)) :=
  funext (predicate newer older)

theorem binder_function (newer older : Substitution) (closed : RangesClosed older) :
    TypedBinder.applySubstitution (newer.compose older) =
      (fun value => (value.applySubstitution older).applySubstitution newer) := funext (binder newer older closed)

@[simp] theorem integerResolution (newer older : Substitution) (value : IntegerLiteralResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [IntegerLiteralResolution.applySubstitution]

@[simp] theorem declaration (newer older : Substitution) (value : DeclarationInstantiation) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  unfold DeclarationInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map (fun (p : TypeParameterId × Ty) => (p.1, (newer.compose older).apply p.2))
    type := (newer.compose older).apply value.type
    predicates := value.predicates.map (TypedTraitResolution.applySubstitution (newer.compose older)) } =
    { value with
      parameterSubstitution := (value.parameterSubstitution.map (fun (p : TypeParameterId × Ty) => (p.1, older.apply p.2))).map (fun (p : TypeParameterId × Ty) => (p.1, newer.apply p.2))
      type := newer.apply (older.apply value.type)
      predicates := (value.predicates.map (TypedTraitResolution.applySubstitution older)).map (TypedTraitResolution.applySubstitution newer) }
  simp [List.map_map, Function.comp_def]

@[simp] theorem constructor (newer older : Substitution) (value : DataConstructorInstantiation) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  unfold DataConstructorInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map (fun (p : TypeParameterId × Ty) => (p.1, (newer.compose older).apply p.2))
    payloadTypes := value.payloadTypes.map (Substitution.apply (newer.compose older))
    resultType := (newer.compose older).apply value.resultType } =
    { value with
      parameterSubstitution := (value.parameterSubstitution.map (fun (p : TypeParameterId × Ty) => (p.1, older.apply p.2))).map (fun (p : TypeParameterId × Ty) => (p.1, newer.apply p.2))
      payloadTypes := (value.payloadTypes.map (Substitution.apply older)).map (Substitution.apply newer)
      resultType := newer.apply (older.apply value.resultType) }
  simp [List.map_map, Function.comp_def]

@[simp] theorem coercion (newer older : Substitution) (value : CoercionStep) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [CoercionStep.applySubstitution]

@[simp] theorem coercion_function (newer older : Substitution) :
    CoercionStep.applySubstitution (newer.compose older) =
      (fun value => (value.applySubstitution older).applySubstitution newer) := funext (coercion newer older)

@[simp] theorem indirect (newer older : Substitution) (value : IndirectCallResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value
  simp [IndirectCallResolution.applySubstitution]

@[simp] theorem reference (newer older : Substitution) (value : ReferenceResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [ReferenceResolution.applySubstitution]

@[simp] theorem call (newer older : Substitution) (value : CallResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [CallResolution.applySubstitution]

@[simp] theorem expressionForm (newer older : Substitution) (closed : RangesClosed older) (value : ExpressionForm) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [ExpressionForm.applySubstitution, binder_function newer older closed, List.map_map, Function.comp_def]

@[simp] theorem expression (newer older : Substitution) (closed : RangesClosed older) (value : ExpressionNode) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [ExpressionNode.applySubstitution, expressionForm newer older closed, List.map_map, Function.comp_def]

@[simp] theorem instruction (newer older : Substitution) (closed : RangesClosed older) (value : MatchPatternInstruction) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [MatchPatternInstruction.applySubstitution, binder newer older closed]

theorem instruction_function (newer older : Substitution) (closed : RangesClosed older) :
    MatchPatternInstruction.applySubstitution (newer.compose older) =
      (fun value => (value.applySubstitution older).applySubstitution newer) := funext (instruction newer older closed)

@[simp] theorem resolution (newer older : Substitution) (closed : RangesClosed older) (value : MatchPatternResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [MatchPatternResolution.applySubstitution, binder newer older closed,
    instruction_function newer older closed, List.map_map, Function.comp_def]

@[simp] theorem pattern (newer older : Substitution) (closed : RangesClosed older) (value : TypedMatchPattern) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [TypedMatchPattern.applySubstitution, resolution newer older closed]

@[simp] theorem matchCase (newer older : Substitution) (closed : RangesClosed older) (value : TypedMatchCase) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [TypedMatchCase.applySubstitution, pattern newer older closed]

theorem matchCase_function (newer older : Substitution) (closed : RangesClosed older) :
    TypedMatchCase.applySubstitution (newer.compose older) =
      (fun value => (value.applySubstitution older).applySubstitution newer) := funext (matchCase newer older closed)

@[simp] theorem matchResolution (newer older : Substitution) (closed : RangesClosed older) (value : MatchResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [MatchResolution.applySubstitution, matchCase_function newer older closed, List.map_map, Function.comp_def]

@[simp] theorem place (newer older : Substitution) (value : PlaceResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [PlaceResolution.applySubstitution]

@[simp] theorem assignment (newer older : Substitution) (value : AssignmentResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [AssignmentResolution.applySubstitution]

@[simp] theorem forItem (newer older : Substitution) (closed : RangesClosed older) (value : ForItemForm) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [ForItemForm.applySubstitution, binder newer older closed]

theorem forItem_function (newer older : Substitution) (closed : RangesClosed older) :
    ForItemForm.applySubstitution (newer.compose older) =
      (fun value => (value.applySubstitution older).applySubstitution newer) := funext (forItem newer older closed)

@[simp] theorem statementForm (newer older : Substitution) (closed : RangesClosed older) (value : StatementForm) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [StatementForm.applySubstitution, binder newer older closed,
    forItem_function newer older closed, matchResolution newer older closed, List.map_map, Function.comp_def]

@[simp] theorem statement (newer older : Substitution) (closed : RangesClosed older) (value : StatementNode) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [StatementNode.applySubstitution, statementForm newer older closed]

@[simp] theorem node (newer older : Substitution) (closed : RangesClosed older) (value : Node) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [Node.applySubstitution, expression newer older closed, statement newer older closed]

theorem node_function (newer older : Substitution) (closed : RangesClosed older) :
    Node.applySubstitution (newer.compose older) =
      (fun value => (value.applySubstitution older).applySubstitution newer) := funext (node newer older closed)

theorem source (newer older : Substitution) (closed : RangesClosed older) (value : TypedSource) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [TypedSource.applySubstitution, binder_function newer older closed,
    node_function newer older closed, List.map_map, Function.comp_def]

theorem RangesClosed.empty : RangesClosed [] := by intro entry member; cases member

theorem RangesClosed.compose {older newer : Substitution}
    (oldClosed : RangesClosed older) (newClosed : RangesClosed newer) : RangesClosed (newer.compose older) := by
  intro ⟨metavariable, replacement⟩ member
  rcases Substitution.mem_compose_iff.mp member with ⟨previous, oldMember, rfl⟩ | ⟨newMember, _⟩
  · rw [fixed (oldClosed _ oldMember) newer]
    exact oldClosed _ oldMember
  · exact newClosed _ newMember

theorem bindings_matched {caller : SourceSpecialization.SpecializedFunction}
    {binder : TypedBinder} {node : ExpressionNode} {substitution : Substitution}
    {bindings : List SourceCompilationPlan.LocalRequirementBinding}
    (accepted : SourceCompilationPlan.localRequirementBindings caller binder node = .ok (substitution, bindings)) :
    SourceSpecialization.matchClosedSchemeInstance? binder.scheme node.rawType = some substitution := by
  unfold SourceCompilationPlan.localRequirementBindings at accepted
  simp (maxSteps := 1000000) only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  rename_i matched matchEq
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  obtain ⟨final, _, accepted⟩ := except_bind accepted
  cases accepted
  exact matchEq

theorem witnesses_matched {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceCompilationPlan.EvidenceEnvironment} {binder : TypedBinder} {node : ExpressionNode}
    {substitution : Substitution} {witnesses : List Witness}
    (accepted : SourceCompilationPlan.localRequirementWitnesses caller available binder node = .ok (substitution, witnesses)) :
    SourceSpecialization.matchClosedSchemeInstance? binder.scheme node.rawType = some substitution := by
  unfold SourceCompilationPlan.localRequirementWitnesses at accepted
  obtain ⟨⟨matched, bindings⟩, selected, accepted⟩ := except_bind accepted
  obtain ⟨final, _, accepted⟩ := except_bind accepted
  cases accepted
  exact bindings_matched selected

/-- The real structural matcher only adds types occurring in the actual
closed type. Existing assignments retain their already established closure. -/
theorem matchBody_closed (quantified : List TypeVarId) (expected actual : Ty)
    {initial final : Substitution} (initialClosed : RangesClosed initial)
    (actualClosed : actual.freeVariables = [])
    (matched : Scheme.matchBody? quantified expected actual initial = some final) : RangesClosed final := by
  induction expected generalizing actual initial final with
  | «variable» metavariable =>
    simp only [Scheme.matchBody?] at matched
    split at matched
    · split at matched
      · split at matched <;> try contradiction
        cases matched
        exact initialClosed
      · cases matched
        intro entry member
        rcases List.mem_cons.mp member with rfl | previous
        · exact actualClosed
        · exact initialClosed entry previous
    · split at matched <;> try contradiction
      cases matched
      exact initialClosed
  | parameter | constructor =>
    cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
    split at matched <;> try contradiction
    cases matched
    exact initialClosed
  | error =>
    cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
    cases matched
    exact initialClosed
  | application left right ihLeft ihRight
  | function left right ihLeft ihRight
  | product left right ihLeft ihRight
  | mapping left right ihLeft ihRight =>
    cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
    rename_i actualLeft actualRight
    have closedParts : actualLeft.freeVariables = [] ∧ actualRight.freeVariables = [] := by
      simp only [List.eq_nil_iff_forall_not_mem] at actualClosed ⊢
      constructor <;> intro metavariable occurs <;> apply actualClosed metavariable <;> simp [occurs]
    obtain ⟨middle, leftMatched, rightMatched⟩ := Option.bind_eq_some_iff.mp matched
    exact ihRight actualRight (ihLeft actualLeft initialClosed closedParts.1 leftMatched) closedParts.2 rightMatched
  | proxy inner ih | comptime inner ih =>
    cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
    rename_i actualInner
    exact ih actualInner initialClosed actualClosed matched

private theorem mapM_closed {matched : Substitution} (closed : RangesClosed matched)
    {variables : List TypeVarId} {result : Substitution}
    (accepted : variables.mapM (fun metavariable => do
      pure (metavariable, ← matched.lookup? metavariable)) = some result) : RangesClosed result := by
  induction variables generalizing result with
  | nil => cases accepted; exact RangesClosed.empty
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, found, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨rest, remainder, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    cases accepted
    cases lookup : matched.lookup? head with
    | none => simp [lookup] at found
    | some replacement =>
      simp only [lookup, pure, bind, Option.bind, Option.some.injEq] at found
      cases found
      intro entry member
      rcases List.mem_cons.mp member with rfl | previous
      · exact closed _ (Substitution.lookup?_eq_some_mem lookup)
      · exact ih remainder entry previous

theorem matchInstance_closed {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (actualClosed : actual.freeVariables = [])
    (matched : scheme.matchInstance? actual = some substitution) : RangesClosed substitution := by
  unfold Scheme.matchInstance? at matched
  cases certified : Scheme.matchInstanceCertificate? scheme actual with
  | none => simp [certified] at matched
  | some certificate =>
    simp only [certified, Option.map_some, Option.some.injEq] at matched
    subst substitution
    unfold Scheme.matchInstanceCertificate? at certified
    split at certified <;> try contradiction
    obtain ⟨first, shape, certified⟩ := Option.bind_eq_some_iff.mp certified
    obtain ⟨reordered, ordering, certified⟩ := Option.bind_eq_some_iff.mp certified
    have closed := mapM_closed (matchBody_closed scheme.quantified scheme.body actual RangesClosed.empty actualClosed shape) ordering
    split at certified <;> try contradiction
    split at certified <;> try contradiction
    cases certified
    exact closed

theorem concrete_closed {actual : Ty} (concrete : SourceSpecialization.firstNonConcrete actual = none) :
    actual.freeVariables = [] := by
  induction actual with
  | «variable» => cases concrete
  | parameter | constructor | error => rfl
  | application left right ihLeft ihRight
  | function left right ihLeft ihRight
  | product left right ihLeft ihRight
  | mapping left right ihLeft ihRight =>
    simp only [SourceSpecialization.firstNonConcrete] at concrete
    cases leftConcrete : SourceSpecialization.firstNonConcrete left with
    | some issue => simp [leftConcrete] at concrete
    | none =>
      have rightConcrete : SourceSpecialization.firstNonConcrete right = none := by simpa [leftConcrete] using concrete
      have leftClosed := ihLeft leftConcrete
      have rightClosed := ihRight rightConcrete
      simp only [List.eq_nil_iff_forall_not_mem] at leftClosed rightClosed ⊢
      intro metavariable
      simp [leftClosed metavariable, rightClosed metavariable]
  | proxy _ ih | comptime _ ih => exact ih concrete

theorem matchClosed_ranges {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? scheme actual = some substitution) : RangesClosed substitution := by
  have concrete := (SourceSpecialization.matchClosedSchemeInstance?_sound matched).1
  apply matchInstance_closed (concrete_closed concrete)
  simpa [SourceSpecialization.matchClosedSchemeInstance?, concrete] using matched

theorem ViewStep.rangesClosed {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target} {before : CallableAncestryMetadata.State}
    (step : ViewStep view before) : RangesClosed step.substitution :=
  matchClosed_ranges (witnesses_matched step.factory)

/-- An actual authenticated ancestry source agrees, after requirement erasure,
with its owned original source under the full cumulative type substitution.
Closed range evidence comes from the actual matcher, not an extra caller law. -/
theorem Authenticates.canonical {checked : Checked} {base : Base checked} {owned : Owned base}
    {frame : ContextFrame} {state : CallableAncestryMetadata.State}
    (authenticated : Authenticates owned frame (some state)) :
    ∃ (id : Core.Word) (named : Named owned id), state.owner = named.state.owner ∧
      RangesClosed state.active ∧
      eraseRequirements state.source = eraseRequirements (named.state.source.applySubstitution state.active) := by
  generalize resultEq : some state = result at authenticated
  induction authenticated generalizing state with
  | empty => cases resultEq
  | named receipt =>
    cases resultEq
    exact ⟨_, receipt, rfl, RangesClosed.empty, by simp only [Named.state, EmptySourceSubstitution.source]⟩
  | lambda parent receipt metadata ih => exact ih resultEq
  | view parent receipt step ih =>
    cases resultEq
    obtain ⟨id, named, owner, closed, canonical⟩ := ih rfl
    refine ⟨id, named, owner, RangesClosed.compose closed (ViewStep.rangesClosed step), ?_⟩
    change eraseRequirements (SourceTypedRuntime.rewriteLocalRequirements step.witnesses
      (TypedSource.applySubstitution step.substitution _)) =
      eraseRequirements (named.state.source.applySubstitution (step.substitution.compose _))
    rw [rewrite_erased, erase_substitute, canonical, ← erase_substitute,
      source step.substitution _ closed]

private theorem named_source_eq {checked : Checked} {base : Base checked} {owned : Owned base}
    {leftId rightId : Core.Word} (left : Named owned leftId) (right : Named owned rightId)
    (same : left.state.owner = right.state.owner) : left.state.source = right.state.source := by
  have found := right.found
  change left.owner = right.owner at same
  rw [← same] at found
  have caller := Except.ok.inj (left.found.symm.trans found)
  exact congrArg (fun selected : SourceSpecialization.SpecializedFunction => selected.function.typedBody) caller

/-- The lookup key forgets arbitrary repetitions of lambda frames, but keeps
every occurrence-specific requirement ID. It is not a key by native type. -/
structure StateKey where
  owner : Key
  active : Substitution
  profile : List (List RequirementId)
  deriving DecidableEq, Repr

def stateKey (state : CallableAncestryMetadata.State) : StateKey :=
  ⟨state.owner, state.active, requirementProfile state.source⟩

/-- Within actually authenticated metadata recipes this finite-profile key
determines the complete source metadata. Frame history itself is intentionally
not reconstructed or authenticated by equality of these keys. -/
theorem stateKey_injective {checked : Checked} {base : Base checked} {owned : Owned base}
    {leftFrame rightFrame : ContextFrame} {left right : CallableAncestryMetadata.State}
    (leftAuthenticated : Authenticates owned leftFrame (some left))
    (rightAuthenticated : Authenticates owned rightFrame (some right))
    (same : stateKey left = stateKey right) : left = right := by
  have owner : left.owner = right.owner := congrArg StateKey.owner same
  have active : left.active = right.active := congrArg StateKey.active same
  have profile : requirementProfile left.source = requirementProfile right.source := congrArg StateKey.profile same
  obtain ⟨_, leftNamed, leftOwner, _, leftCanonical⟩ := Authenticates.canonical leftAuthenticated
  obtain ⟨_, rightNamed, rightOwner, _, rightCanonical⟩ := Authenticates.canonical rightAuthenticated
  have roots := named_source_eq leftNamed rightNamed (leftOwner.symm.trans (owner.trans rightOwner))
  have erased : eraseRequirements left.source = eraseRequirements right.source := by
    rw [leftCanonical, rightCanonical, roots, active]
  have sources := FiniteProfiles.source_unique erased profile
  cases left
  cases right
  cases owner
  cases active
  cases sources
  rfl

end SourceComposition

end Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles
