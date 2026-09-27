import Solcore.TypeSystem.SubstitutionProperties

set_option autoImplicit false

namespace Solcore.TypeSystem

structure Constraint where
  left : Ty
  right : Ty
  deriving Repr, DecidableEq

namespace Constraint

def apply (substitution : Substitution) (constraint : Constraint) : Constraint :=
  { left := substitution.apply constraint.left
    right := substitution.apply constraint.right }

/-- Every variable in both sides of a constraint lies below the allocator
bound. -/
def VariablesBelow (next : Nat) (constraint : Constraint) : Prop :=
  constraint.left.VariablesBelow next ∧ constraint.right.VariablesBelow next

@[simp] theorem variablesBelow_mk_iff
    (next : Nat) (left right : Ty) :
    VariablesBelow next { left, right } ↔
      left.VariablesBelow next ∧ right.VariablesBelow next := by
  rfl

theorem VariablesBelow.apply
    {next : Nat} {constraint : Constraint} {substitution : Substitution}
    (solved : substitution.SolvedBelow next)
    (below : constraint.VariablesBelow next) :
    (constraint.apply substitution).VariablesBelow next := by
  exact ⟨solved.variablesBelow_apply below.1,
    solved.variablesBelow_apply below.2⟩

/-- Every variable on both sides of a constraint lies outside a
substitution's domain. -/
def VariablesOutsideDomain (substitution : Substitution)
    (constraint : Constraint) : Prop :=
  (∀ metavariable, metavariable ∈ constraint.left.freeVariables →
    metavariable ∉ substitution.domain) ∧
  (∀ metavariable, metavariable ∈ constraint.right.freeVariables →
    metavariable ∉ substitution.domain)

/-- Applying a substitution whose range avoids an older domain preserves
constraint-level avoidance of that domain. -/
theorem VariablesOutsideDomain.apply
    {constraint : Constraint} {newer older : Substitution}
    (cross : newer.RangeAvoidsDomain older)
    (outside : constraint.VariablesOutsideDomain older) :
    (constraint.apply newer).VariablesOutsideDomain older := by
  exact
    ⟨cross.apply_variables_outside_older_domain constraint.left outside.1,
      cross.apply_variables_outside_older_domain constraint.right outside.2⟩

/-- A substitution satisfies a constraint when it makes both sides equal. -/
def SatisfiedBy (constraint : Constraint)
    (substitution : Substitution) : Prop :=
  substitution.apply constraint.left = substitution.apply constraint.right

/-- A normalized equality can be transported back through a substitution
which is semantically extended by the final result. -/
theorem SatisfiedBy.of_normalized
    {constraint : Constraint} {current result : Substitution}
    (extension : result.SemanticallyExtends current)
    (normalized : result.apply (current.apply constraint.left) =
      result.apply (current.apply constraint.right)) :
    constraint.SatisfiedBy result := by
  exact (extension constraint.left).symm.trans
    (normalized.trans (extension constraint.right))

end Constraint

/-- Every pending unification constraint is bounded by the same allocator
limit. -/
def ConstraintsBelow (next : Nat) (constraints : List Constraint) : Prop :=
  ∀ constraint, constraint ∈ constraints → constraint.VariablesBelow next

/-- Every pending constraint avoids the domain of an older substitution. -/
def ConstraintsOutsideDomain (substitution : Substitution)
    (constraints : List Constraint) : Prop :=
  ∀ constraint, constraint ∈ constraints →
    constraint.VariablesOutsideDomain substitution

/-- A substitution simultaneously satisfies every pending constraint. -/
def ConstraintsSatisfiedBy (substitution : Substitution)
    (constraints : List Constraint) : Prop :=
  ∀ constraint, constraint ∈ constraints → constraint.SatisfiedBy substitution

/-- Every finite constraint set admits a common flexible-variable bound. -/
private theorem constraintsBelow_exists (constraints : List Constraint) :
    ∃ next, ConstraintsBelow next constraints := by
  induction constraints with
  | nil =>
      exact ⟨0, by intro constraint member; simp at member⟩
  | cons constraint rest induction =>
      obtain ⟨restNext, restBelow⟩ := induction
      let next := max constraint.left.nextVariable
        (max constraint.right.nextVariable restNext)
      refine ⟨next, ?_⟩
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · constructor
        · exact (Ty.variablesBelow_nextVariable candidate.left).weaken
            (by exact Nat.le_max_left _ _)
        · exact (Ty.variablesBelow_nextVariable candidate.right).weaken
            (by
              exact Nat.le_trans (Nat.le_max_left _ _)
                (Nat.le_max_right _ _))
      · have below := restBelow candidate member
        have bound : restNext ≤ next := by
          exact Nat.le_trans (Nat.le_max_right _ _)
            (Nat.le_max_right _ _)
        exact ⟨below.1.weaken bound, below.2.weaken bound⟩

namespace ConstraintsSatisfiedBy

theorem cons
    {substitution : Substitution} {constraint : Constraint}
    {constraints : List Constraint}
    (head : constraint.SatisfiedBy substitution)
    (tail : ConstraintsSatisfiedBy substitution constraints) :
    ConstraintsSatisfiedBy substitution (constraint :: constraints) := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail candidate member

end ConstraintsSatisfiedBy

namespace Unification

inductive Error where
  | occursCheck (metavariable : TypeVarId) (type : Ty)
  | mismatch (left right : Ty)
  | exhausted
  deriving Repr, DecidableEq

private def loop : Nat → Substitution → List Constraint → Except Error Substitution
  | 0, _, _ => .error .exhausted
  | fuel + 1, substitution, constraints =>
      match constraints with
      | [] => .ok substitution
      | constraint :: rest =>
          let left := substitution.apply constraint.left
          let right := substitution.apply constraint.right
          if left = right then
            loop fuel substitution rest
          else
            match left, right with
            | .variable metavariable, type
            | type, .variable metavariable =>
                if type.containsVariable metavariable then
                  .error (.occursCheck metavariable type)
                else
                  let binding : Substitution := [(metavariable, type)]
                  loop fuel (binding.compose substitution) rest
            | .application leftFunction leftArgument,
                .application rightFunction rightArgument
            | .function leftFunction leftArgument,
                .function rightFunction rightArgument
            | .product leftFunction leftArgument,
                .product rightFunction rightArgument
            | .mapping leftFunction leftArgument,
                .mapping rightFunction rightArgument =>
                  loop fuel substitution
                    ({ left := leftFunction, right := rightFunction } ::
                     { left := leftArgument, right := rightArgument } :: rest)
            | .proxy leftInner, .proxy rightInner
            | .comptime leftInner, .comptime rightInner =>
                loop fuel substitution ({ left := leftInner, right := rightInner } :: rest)
            | _, _ => .error (.mismatch left right)

private theorem bind_solvedBelow
    {substitution : Substitution} {next : Nat}
    {metavariable : TypeVarId} {type : Ty}
    (solved : substitution.SolvedBelow next)
    (metavariableBelow : metavariable.index < next)
    (typeBelow : type.VariablesBelow next)
    (typeOutside : ∀ rangeVariable,
      rangeVariable ∈ type.freeVariables →
        rangeVariable ∉ substitution.domain)
    (occursCheck : type.containsVariable metavariable = false) :
    Substitution.SolvedBelow
      (Substitution.compose [(metavariable, type)] substitution) next := by
  have bindingSolved :
      Substitution.SolvedBelow [(metavariable, type)] next :=
    Substitution.SolvedBelow.mono metavariableBelow typeBelow
      ((Ty.containsVariable_eq_false_iff type metavariable).mp occursCheck)
  apply bindingSolved.compose solved
  intro candidate replacement member
  simp only [List.mem_singleton] at member
  cases member
  exact typeOutside

private theorem singleton_satisfies_variable
    {metavariable : TypeVarId} {type : Ty}
    (occursCheck : type.containsVariable metavariable = false) :
    Substitution.apply [(metavariable, type)] (.variable metavariable) =
      Substitution.apply [(metavariable, type)] type := by
  have typeFixed : Substitution.apply [(metavariable, type)] type = type := by
    apply Ty.apply_eq_self_of_domain_disjoint_freeVariables
    intro candidate domainMember occurs
    have same : candidate = metavariable := by
      simpa [Substitution.domain] using domainMember
    subst candidate
    exact ((Ty.containsVariable_eq_false_iff type metavariable).mp
      occursCheck) occurs
  rw [typeFixed]
  simp [Substitution.apply, Substitution.lookup?]

private theorem loop_sound
    {fuel next : Nat} {substitution result : Substitution}
    {constraints : List Constraint}
    (solved : substitution.SolvedBelow next)
    (constraintsBelow : ConstraintsBelow next constraints)
    (success : loop fuel substitution constraints = .ok result) :
    result.SolvedBelow next ∧
      result.SemanticallyExtends substitution ∧
        ConstraintsSatisfiedBy result constraints := by
  induction fuel generalizing substitution constraints result with
  | zero =>
      simp [loop] at success
  | succ fuel induction =>
      cases constraints with
      | nil =>
          simp only [loop, Except.ok.injEq] at success
          subst result
          exact ⟨solved,
            Substitution.SemanticallyExtends.refl_of_solved solved,
            by intro constraint member; simp at member⟩
      | cons constraint rest =>
          have constraintBelow : constraint.VariablesBelow next :=
            constraintsBelow constraint (by simp)
          have restBelow : ConstraintsBelow next rest := by
            intro candidate member
            exact constraintsBelow candidate (by simp [member])
          let left := substitution.apply constraint.left
          let right := substitution.apply constraint.right
          have leftBelow : left.VariablesBelow next :=
            solved.variablesBelow_apply constraintBelow.1
          have rightBelow : right.VariablesBelow next :=
            solved.variablesBelow_apply constraintBelow.2
          have leftOutside : ∀ metavariable,
              metavariable ∈ left.freeVariables →
                metavariable ∉ substitution.domain :=
            solved.apply_variables_outside_domain constraint.left
          have rightOutside : ∀ metavariable,
              metavariable ∈ right.freeVariables →
                metavariable ∉ substitution.domain :=
            solved.apply_variables_outside_domain constraint.right
          simp only [loop] at success
          split at success
          · rename_i normalized
            rcases induction solved restBelow success with
              ⟨resultSolved, extension, restSatisfied⟩
            exact ⟨resultSolved, extension,
              ConstraintsSatisfiedBy.cons
                (Constraint.SatisfiedBy.of_normalized extension
                  (congrArg result.apply normalized))
                restSatisfied⟩
          · split at success
            · rename_i _ _ metavariable leftEq
              have metavariableBelow : metavariable.index < next := by
                have normalized :
                    (Ty.variable metavariable).VariablesBelow next := by
                  rw [← leftEq]
                  exact leftBelow
                exact (Ty.variablesBelow_variable_iff next metavariable).mp
                  normalized
              cases occursCheck :
                  (substitution.apply constraint.right).containsVariable
                    metavariable with
              | false =>
                  rw [occursCheck] at success
                  let binding : Substitution :=
                    [(metavariable, substitution.apply constraint.right)]
                  let extended := binding.compose substitution
                  have extendedSolved : extended.SolvedBelow next :=
                    bind_solvedBelow solved metavariableBelow rightBelow
                      rightOutside occursCheck
                  have bindingSatisfied :
                      constraint.SatisfiedBy extended := by
                    simpa [Constraint.SatisfiedBy, extended, binding,
                      Substitution.compose_apply, leftEq] using
                      (singleton_satisfies_variable occursCheck)
                  rcases induction extendedSolved restBelow success with
                    ⟨resultSolved, resultExtended, restSatisfied⟩
                  have extendedCurrent :
                      extended.SemanticallyExtends substitution := by
                    exact Substitution.SemanticallyExtends.compose_left
                      binding solved
                  have resultCurrent :
                      result.SemanticallyExtends substitution :=
                    resultExtended.trans extendedCurrent
                  exact ⟨resultSolved, resultCurrent,
                    ConstraintsSatisfiedBy.cons
                      (Constraint.SatisfiedBy.of_normalized resultExtended
                        (congrArg result.apply bindingSatisfied))
                      restSatisfied⟩
              | true =>
                  simp [occursCheck] at success
            · rename_i _ _ metavariable rightEq _
              have metavariableBelow : metavariable.index < next := by
                have normalized :
                    (Ty.variable metavariable).VariablesBelow next := by
                  rw [← rightEq]
                  exact rightBelow
                exact (Ty.variablesBelow_variable_iff next metavariable).mp
                  normalized
              cases occursCheck :
                  (substitution.apply constraint.left).containsVariable
                    metavariable with
              | false =>
                  rw [occursCheck] at success
                  let binding : Substitution :=
                    [(metavariable, substitution.apply constraint.left)]
                  let extended := binding.compose substitution
                  have extendedSolved : extended.SolvedBelow next :=
                    bind_solvedBelow solved metavariableBelow leftBelow
                      leftOutside occursCheck
                  have bindingSatisfied :
                      constraint.SatisfiedBy extended := by
                    simpa [Constraint.SatisfiedBy, extended, binding,
                      Substitution.compose_apply, rightEq] using
                      (singleton_satisfies_variable occursCheck).symm
                  rcases induction extendedSolved restBelow success with
                    ⟨resultSolved, resultExtended, restSatisfied⟩
                  have extendedCurrent :
                      extended.SemanticallyExtends substitution := by
                    exact Substitution.SemanticallyExtends.compose_left
                      binding solved
                  have resultCurrent :
                      result.SemanticallyExtends substitution :=
                    resultExtended.trans extendedCurrent
                  exact ⟨resultSolved, resultCurrent,
                    ConstraintsSatisfiedBy.cons
                      (Constraint.SatisfiedBy.of_normalized resultExtended
                        (congrArg result.apply bindingSatisfied))
                      restSatisfied⟩
              | true =>
                  simp [occursCheck] at success
            · rename_i _ _ leftFunction leftArgument rightFunction
                rightArgument leftEq rightEq
              have normalizedLeft :
                  (Ty.application leftFunction leftArgument).VariablesBelow
                    next := by
                rw [← leftEq]
                exact leftBelow
              have normalizedRight :
                  (Ty.application rightFunction rightArgument).VariablesBelow
                    next := by
                rw [← rightEq]
                exact rightBelow
              have leftParts :=
                (Ty.variablesBelow_application_iff next leftFunction
                  leftArgument).mp normalizedLeft
              have rightParts :=
                (Ty.variablesBelow_application_iff next rightFunction
                  rightArgument).mp normalizedRight
              have decomposedBelow : ConstraintsBelow next
                  ({ left := leftFunction, right := rightFunction } ::
                    { left := leftArgument, right := rightArgument } :: rest) := by
                intro candidate member
                rcases List.mem_cons.mp member with rfl | member
                · exact ⟨leftParts.1, rightParts.1⟩
                · rcases List.mem_cons.mp member with rfl | member
                  · exact ⟨leftParts.2, rightParts.2⟩
                  · exact restBelow candidate member
              rcases induction solved decomposedBelow success with
                ⟨resultSolved, extension, decomposedSatisfied⟩
              have functionSatisfied := decomposedSatisfied
                { left := leftFunction, right := rightFunction } (by simp)
              change result.apply leftFunction = result.apply rightFunction at functionSatisfied
              have argumentSatisfied := decomposedSatisfied
                { left := leftArgument, right := rightArgument } (by simp)
              change result.apply leftArgument = result.apply rightArgument at argumentSatisfied
              have normalized :
                  result.apply (substitution.apply constraint.left) =
                    result.apply (substitution.apply constraint.right) := by
                rw [leftEq, rightEq]
                simp only [Substitution.apply]
                rw [functionSatisfied, argumentSatisfied]
              have restSatisfied : ConstraintsSatisfiedBy result rest := by
                intro candidate member
                exact decomposedSatisfied candidate (by simp [member])
              exact ⟨resultSolved, extension,
                ConstraintsSatisfiedBy.cons
                  (Constraint.SatisfiedBy.of_normalized extension normalized)
                  restSatisfied⟩
            · rename_i _ _ leftFunction leftArgument rightFunction
                rightArgument leftEq rightEq
              have normalizedLeft :
                  (Ty.function leftFunction leftArgument).VariablesBelow
                    next := by
                rw [← leftEq]
                exact leftBelow
              have normalizedRight :
                  (Ty.function rightFunction rightArgument).VariablesBelow
                    next := by
                rw [← rightEq]
                exact rightBelow
              have leftParts :=
                (Ty.variablesBelow_function_iff next leftFunction
                  leftArgument).mp normalizedLeft
              have rightParts :=
                (Ty.variablesBelow_function_iff next rightFunction
                  rightArgument).mp normalizedRight
              have decomposedBelow : ConstraintsBelow next
                  ({ left := leftFunction, right := rightFunction } ::
                    { left := leftArgument, right := rightArgument } :: rest) := by
                intro candidate member
                rcases List.mem_cons.mp member with rfl | member
                · exact ⟨leftParts.1, rightParts.1⟩
                · rcases List.mem_cons.mp member with rfl | member
                  · exact ⟨leftParts.2, rightParts.2⟩
                  · exact restBelow candidate member
              rcases induction solved decomposedBelow success with
                ⟨resultSolved, extension, decomposedSatisfied⟩
              have parameterSatisfied := decomposedSatisfied
                { left := leftFunction, right := rightFunction } (by simp)
              change result.apply leftFunction = result.apply rightFunction at parameterSatisfied
              have resultSatisfied := decomposedSatisfied
                { left := leftArgument, right := rightArgument } (by simp)
              change result.apply leftArgument = result.apply rightArgument at resultSatisfied
              have normalized :
                  result.apply (substitution.apply constraint.left) =
                    result.apply (substitution.apply constraint.right) := by
                rw [leftEq, rightEq]
                simp only [Substitution.apply]
                rw [parameterSatisfied, resultSatisfied]
              have restSatisfied : ConstraintsSatisfiedBy result rest := by
                intro candidate member
                exact decomposedSatisfied candidate (by simp [member])
              exact ⟨resultSolved, extension,
                ConstraintsSatisfiedBy.cons
                  (Constraint.SatisfiedBy.of_normalized extension normalized)
                  restSatisfied⟩
            · rename_i _ _ leftFunction leftArgument rightFunction
                rightArgument leftEq rightEq
              have normalizedLeft :
                  (Ty.product leftFunction leftArgument).VariablesBelow
                    next := by
                rw [← leftEq]
                exact leftBelow
              have normalizedRight :
                  (Ty.product rightFunction rightArgument).VariablesBelow
                    next := by
                rw [← rightEq]
                exact rightBelow
              have leftParts :=
                (Ty.variablesBelow_product_iff next leftFunction
                  leftArgument).mp normalizedLeft
              have rightParts :=
                (Ty.variablesBelow_product_iff next rightFunction
                  rightArgument).mp normalizedRight
              have decomposedBelow : ConstraintsBelow next
                  ({ left := leftFunction, right := rightFunction } ::
                    { left := leftArgument, right := rightArgument } :: rest) := by
                intro candidate member
                rcases List.mem_cons.mp member with rfl | member
                · exact ⟨leftParts.1, rightParts.1⟩
                · rcases List.mem_cons.mp member with rfl | member
                  · exact ⟨leftParts.2, rightParts.2⟩
                  · exact restBelow candidate member
              rcases induction solved decomposedBelow success with
                ⟨resultSolved, extension, decomposedSatisfied⟩
              have leftSatisfied := decomposedSatisfied
                { left := leftFunction, right := rightFunction } (by simp)
              change result.apply leftFunction = result.apply rightFunction at leftSatisfied
              have rightSatisfied := decomposedSatisfied
                { left := leftArgument, right := rightArgument } (by simp)
              change result.apply leftArgument = result.apply rightArgument at rightSatisfied
              have normalized :
                  result.apply (substitution.apply constraint.left) =
                    result.apply (substitution.apply constraint.right) := by
                rw [leftEq, rightEq]
                simp only [Substitution.apply]
                rw [leftSatisfied, rightSatisfied]
              have restSatisfied : ConstraintsSatisfiedBy result rest := by
                intro candidate member
                exact decomposedSatisfied candidate (by simp [member])
              exact ⟨resultSolved, extension,
                ConstraintsSatisfiedBy.cons
                  (Constraint.SatisfiedBy.of_normalized extension normalized)
                  restSatisfied⟩
            · rename_i _ _ leftFunction leftArgument rightFunction
                rightArgument leftEq rightEq
              have normalizedLeft :
                  (Ty.mapping leftFunction leftArgument).VariablesBelow
                    next := by
                rw [← leftEq]
                exact leftBelow
              have normalizedRight :
                  (Ty.mapping rightFunction rightArgument).VariablesBelow
                    next := by
                rw [← rightEq]
                exact rightBelow
              have leftParts :=
                (Ty.variablesBelow_mapping_iff next leftFunction
                  leftArgument).mp normalizedLeft
              have rightParts :=
                (Ty.variablesBelow_mapping_iff next rightFunction
                  rightArgument).mp normalizedRight
              have decomposedBelow : ConstraintsBelow next
                  ({ left := leftFunction, right := rightFunction } ::
                    { left := leftArgument, right := rightArgument } :: rest) := by
                intro candidate member
                rcases List.mem_cons.mp member with rfl | member
                · exact ⟨leftParts.1, rightParts.1⟩
                · rcases List.mem_cons.mp member with rfl | member
                  · exact ⟨leftParts.2, rightParts.2⟩
                  · exact restBelow candidate member
              rcases induction solved decomposedBelow success with
                ⟨resultSolved, extension, decomposedSatisfied⟩
              have keySatisfied := decomposedSatisfied
                { left := leftFunction, right := rightFunction } (by simp)
              change result.apply leftFunction = result.apply rightFunction at keySatisfied
              have valueSatisfied := decomposedSatisfied
                { left := leftArgument, right := rightArgument } (by simp)
              change result.apply leftArgument = result.apply rightArgument at valueSatisfied
              have normalized :
                  result.apply (substitution.apply constraint.left) =
                    result.apply (substitution.apply constraint.right) := by
                rw [leftEq, rightEq]
                simp only [Substitution.apply]
                rw [keySatisfied, valueSatisfied]
              have restSatisfied : ConstraintsSatisfiedBy result rest := by
                intro candidate member
                exact decomposedSatisfied candidate (by simp [member])
              exact ⟨resultSolved, extension,
                ConstraintsSatisfiedBy.cons
                  (Constraint.SatisfiedBy.of_normalized extension normalized)
                  restSatisfied⟩
            · rename_i _ _ leftInner rightInner leftEq rightEq
              have normalizedLeft :
                  (Ty.proxy leftInner).VariablesBelow next := by
                rw [← leftEq]
                exact leftBelow
              have normalizedRight :
                  (Ty.proxy rightInner).VariablesBelow next := by
                rw [← rightEq]
                exact rightBelow
              have decomposedBelow : ConstraintsBelow next
                  ({ left := leftInner, right := rightInner } :: rest) := by
                intro candidate member
                rcases List.mem_cons.mp member with rfl | member
                · exact
                    ⟨(Ty.variablesBelow_proxy_iff next leftInner).mp
                        normalizedLeft,
                      (Ty.variablesBelow_proxy_iff next rightInner).mp
                        normalizedRight⟩
                · exact restBelow candidate member
              rcases induction solved decomposedBelow success with
                ⟨resultSolved, extension, decomposedSatisfied⟩
              have innerSatisfied := decomposedSatisfied
                { left := leftInner, right := rightInner } (by simp)
              change result.apply leftInner = result.apply rightInner at innerSatisfied
              have normalized :
                  result.apply (substitution.apply constraint.left) =
                    result.apply (substitution.apply constraint.right) := by
                rw [leftEq, rightEq]
                simp only [Substitution.apply]
                rw [innerSatisfied]
              have restSatisfied : ConstraintsSatisfiedBy result rest := by
                intro candidate member
                exact decomposedSatisfied candidate (by simp [member])
              exact ⟨resultSolved, extension,
                ConstraintsSatisfiedBy.cons
                  (Constraint.SatisfiedBy.of_normalized extension normalized)
                  restSatisfied⟩
            · rename_i _ _ leftInner rightInner leftEq rightEq
              have normalizedLeft :
                  (Ty.comptime leftInner).VariablesBelow next := by
                rw [← leftEq]
                exact leftBelow
              have normalizedRight :
                  (Ty.comptime rightInner).VariablesBelow next := by
                rw [← rightEq]
                exact rightBelow
              have decomposedBelow : ConstraintsBelow next
                  ({ left := leftInner, right := rightInner } :: rest) := by
                intro candidate member
                rcases List.mem_cons.mp member with rfl | member
                · exact
                    ⟨(Ty.variablesBelow_comptime_iff next leftInner).mp
                        normalizedLeft,
                      (Ty.variablesBelow_comptime_iff next rightInner).mp
                        normalizedRight⟩
                · exact restBelow candidate member
              rcases induction solved decomposedBelow success with
                ⟨resultSolved, extension, decomposedSatisfied⟩
              have innerSatisfied := decomposedSatisfied
                { left := leftInner, right := rightInner } (by simp)
              change result.apply leftInner = result.apply rightInner at innerSatisfied
              have normalized :
                  result.apply (substitution.apply constraint.left) =
                    result.apply (substitution.apply constraint.right) := by
                rw [leftEq, rightEq]
                simp only [Substitution.apply]
                rw [innerSatisfied]
              have restSatisfied : ConstraintsSatisfiedBy result rest := by
                intro candidate member
                exact decomposedSatisfied candidate (by simp [member])
              exact ⟨resultSolved, extension,
                ConstraintsSatisfiedBy.cons
                  (Constraint.SatisfiedBy.of_normalized extension normalized)
                  restSatisfied⟩
            · simp at success

private theorem loop_solvedBelow
    {fuel next : Nat} {substitution result : Substitution}
    {constraints : List Constraint}
    (solved : substitution.SolvedBelow next)
    (constraintsBelow : ConstraintsBelow next constraints)
    (success : loop fuel substitution constraints = .ok result) :
    result.SolvedBelow next :=
  (loop_sound solved constraintsBelow success).1

private theorem variablesOutside_parts
    {older : Substitution} {whole first second : Ty}
    (outside : ∀ metavariable, metavariable ∈ whole.freeVariables →
      metavariable ∉ older.domain)
    (firstMember : ∀ metavariable, metavariable ∈ first.freeVariables →
      metavariable ∈ whole.freeVariables)
    (secondMember : ∀ metavariable, metavariable ∈ second.freeVariables →
      metavariable ∈ whole.freeVariables) :
    (∀ metavariable, metavariable ∈ first.freeVariables →
      metavariable ∉ older.domain) ∧
    (∀ metavariable, metavariable ∈ second.freeVariables →
      metavariable ∉ older.domain) := by
  exact
    ⟨fun metavariable member => outside metavariable
        (firstMember metavariable member),
      fun metavariable member => outside metavariable
        (secondMember metavariable member)⟩

private theorem binaryConstraintsOutsideDomain
    {older : Substitution}
    {leftFirst leftSecond rightFirst rightSecond : Ty}
    {rest : List Constraint}
    (leftFirstOutside : ∀ metavariable,
      metavariable ∈ leftFirst.freeVariables →
        metavariable ∉ older.domain)
    (leftSecondOutside : ∀ metavariable,
      metavariable ∈ leftSecond.freeVariables →
        metavariable ∉ older.domain)
    (rightFirstOutside : ∀ metavariable,
      metavariable ∈ rightFirst.freeVariables →
        metavariable ∉ older.domain)
    (rightSecondOutside : ∀ metavariable,
      metavariable ∈ rightSecond.freeVariables →
        metavariable ∉ older.domain)
    (restOutside : ConstraintsOutsideDomain older rest) :
    ConstraintsOutsideDomain older
      ({ left := leftFirst, right := rightFirst } ::
       { left := leftSecond, right := rightSecond } :: rest) := by
  intro constraint member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨leftFirstOutside, rightFirstOutside⟩
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨leftSecondOutside, rightSecondOutside⟩
    · exact restOutside constraint member

private theorem loop_rangeAvoidsDomain
    {fuel : Nat} {substitution older result : Substitution}
    {constraints : List Constraint}
    (cross : substitution.RangeAvoidsDomain older)
    (constraintsOutside : ConstraintsOutsideDomain older constraints)
    (success : loop fuel substitution constraints = .ok result) :
    result.RangeAvoidsDomain older := by
  induction fuel generalizing substitution constraints result with
  | zero =>
      simp [loop] at success
  | succ fuel induction =>
      cases constraints with
      | nil =>
          simp only [loop, Except.ok.injEq] at success
          subst result
          exact cross
      | cons constraint rest =>
          have constraintOutside :
              constraint.VariablesOutsideDomain older :=
            constraintsOutside constraint (by simp)
          have restOutside : ConstraintsOutsideDomain older rest := by
            intro candidate member
            exact constraintsOutside candidate (by simp [member])
          have leftOutside : ∀ metavariable,
              metavariable ∈
                  (substitution.apply constraint.left).freeVariables →
                metavariable ∉ older.domain :=
            cross.apply_variables_outside_older_domain constraint.left
              constraintOutside.1
          have rightOutside : ∀ metavariable,
              metavariable ∈
                  (substitution.apply constraint.right).freeVariables →
                metavariable ∉ older.domain :=
            cross.apply_variables_outside_older_domain constraint.right
              constraintOutside.2
          simp only [loop] at success
          split at success
          · apply induction (substitution := substitution)
              (constraints := rest) (result := result)
            · exact cross
            · exact restOutside
            · exact success
          · split at success
            · rename_i _ _ metavariable leftEq
              cases occursCheck :
                  (substitution.apply constraint.right).containsVariable
                    metavariable with
              | false =>
                  rw [occursCheck] at success
                  have bindingAvoids :
                      Substitution.RangeAvoidsDomain
                        [(metavariable, substitution.apply constraint.right)]
                        older := by
                    intro candidate replacement member
                    simp only [List.mem_singleton] at member
                    cases member
                    exact rightOutside
                  apply induction
                    (substitution := Substitution.compose
                      [(metavariable, substitution.apply constraint.right)]
                      substitution)
                    (constraints := rest) (result := result)
                  · exact bindingAvoids.compose cross
                  · exact restOutside
                  · exact success
              | true =>
                  simp [occursCheck] at success
            · rename_i _ _ metavariable rightEq _
              cases occursCheck :
                  (substitution.apply constraint.left).containsVariable
                    metavariable with
              | false =>
                  rw [occursCheck] at success
                  have bindingAvoids :
                      Substitution.RangeAvoidsDomain
                        [(metavariable, substitution.apply constraint.left)]
                        older := by
                    intro candidate replacement member
                    simp only [List.mem_singleton] at member
                    cases member
                    exact leftOutside
                  apply induction
                    (substitution := Substitution.compose
                      [(metavariable, substitution.apply constraint.left)]
                      substitution)
                    (constraints := rest) (result := result)
                  · exact bindingAvoids.compose cross
                  · exact restOutside
                  · exact success
              | true =>
                  simp [occursCheck] at success
            · rename_i _ _ leftFunction leftArgument rightFunction
                rightArgument leftEq rightEq
              have leftParts := variablesOutside_parts
                (whole := substitution.apply constraint.left)
                (first := leftFunction) (second := leftArgument) leftOutside
                (fun metavariable member => by
                  rw [leftEq]
                  exact (Ty.mem_freeVariables_application_iff metavariable
                    leftFunction leftArgument).mpr (Or.inl member))
                (fun metavariable member => by
                  rw [leftEq]
                  exact (Ty.mem_freeVariables_application_iff metavariable
                    leftFunction leftArgument).mpr (Or.inr member))
              have rightParts := variablesOutside_parts
                (whole := substitution.apply constraint.right)
                (first := rightFunction) (second := rightArgument) rightOutside
                (fun metavariable member => by
                  rw [rightEq]
                  exact (Ty.mem_freeVariables_application_iff metavariable
                    rightFunction rightArgument).mpr (Or.inl member))
                (fun metavariable member => by
                  rw [rightEq]
                  exact (Ty.mem_freeVariables_application_iff metavariable
                    rightFunction rightArgument).mpr (Or.inr member))
              apply induction (substitution := substitution)
                (constraints :=
                  { left := leftFunction, right := rightFunction } ::
                  { left := leftArgument, right := rightArgument } :: rest)
                (result := result)
              · exact cross
              · exact binaryConstraintsOutsideDomain leftParts.1 leftParts.2
                  rightParts.1 rightParts.2 restOutside
              · exact success
            · rename_i _ _ leftFunction leftArgument rightFunction
                rightArgument leftEq rightEq
              have leftParts := variablesOutside_parts
                (whole := substitution.apply constraint.left)
                (first := leftFunction) (second := leftArgument) leftOutside
                (fun metavariable member => by
                  rw [leftEq]
                  exact (Ty.mem_freeVariables_function_iff metavariable
                    leftFunction leftArgument).mpr (Or.inl member))
                (fun metavariable member => by
                  rw [leftEq]
                  exact (Ty.mem_freeVariables_function_iff metavariable
                    leftFunction leftArgument).mpr (Or.inr member))
              have rightParts := variablesOutside_parts
                (whole := substitution.apply constraint.right)
                (first := rightFunction) (second := rightArgument) rightOutside
                (fun metavariable member => by
                  rw [rightEq]
                  exact (Ty.mem_freeVariables_function_iff metavariable
                    rightFunction rightArgument).mpr (Or.inl member))
                (fun metavariable member => by
                  rw [rightEq]
                  exact (Ty.mem_freeVariables_function_iff metavariable
                    rightFunction rightArgument).mpr (Or.inr member))
              apply induction (substitution := substitution)
                (constraints :=
                  { left := leftFunction, right := rightFunction } ::
                  { left := leftArgument, right := rightArgument } :: rest)
                (result := result)
              · exact cross
              · exact binaryConstraintsOutsideDomain leftParts.1 leftParts.2
                  rightParts.1 rightParts.2 restOutside
              · exact success
            · rename_i _ _ leftFunction leftArgument rightFunction
                rightArgument leftEq rightEq
              have leftParts := variablesOutside_parts
                (whole := substitution.apply constraint.left)
                (first := leftFunction) (second := leftArgument) leftOutside
                (fun metavariable member => by
                  rw [leftEq]
                  exact (Ty.mem_freeVariables_product_iff metavariable
                    leftFunction leftArgument).mpr (Or.inl member))
                (fun metavariable member => by
                  rw [leftEq]
                  exact (Ty.mem_freeVariables_product_iff metavariable
                    leftFunction leftArgument).mpr (Or.inr member))
              have rightParts := variablesOutside_parts
                (whole := substitution.apply constraint.right)
                (first := rightFunction) (second := rightArgument) rightOutside
                (fun metavariable member => by
                  rw [rightEq]
                  exact (Ty.mem_freeVariables_product_iff metavariable
                    rightFunction rightArgument).mpr (Or.inl member))
                (fun metavariable member => by
                  rw [rightEq]
                  exact (Ty.mem_freeVariables_product_iff metavariable
                    rightFunction rightArgument).mpr (Or.inr member))
              apply induction (substitution := substitution)
                (constraints :=
                  { left := leftFunction, right := rightFunction } ::
                  { left := leftArgument, right := rightArgument } :: rest)
                (result := result)
              · exact cross
              · exact binaryConstraintsOutsideDomain leftParts.1 leftParts.2
                  rightParts.1 rightParts.2 restOutside
              · exact success
            · rename_i _ _ leftFunction leftArgument rightFunction
                rightArgument leftEq rightEq
              have leftParts := variablesOutside_parts
                (whole := substitution.apply constraint.left)
                (first := leftFunction) (second := leftArgument) leftOutside
                (fun metavariable member => by
                  rw [leftEq]
                  exact (Ty.mem_freeVariables_mapping_iff metavariable
                    leftFunction leftArgument).mpr (Or.inl member))
                (fun metavariable member => by
                  rw [leftEq]
                  exact (Ty.mem_freeVariables_mapping_iff metavariable
                    leftFunction leftArgument).mpr (Or.inr member))
              have rightParts := variablesOutside_parts
                (whole := substitution.apply constraint.right)
                (first := rightFunction) (second := rightArgument) rightOutside
                (fun metavariable member => by
                  rw [rightEq]
                  exact (Ty.mem_freeVariables_mapping_iff metavariable
                    rightFunction rightArgument).mpr (Or.inl member))
                (fun metavariable member => by
                  rw [rightEq]
                  exact (Ty.mem_freeVariables_mapping_iff metavariable
                    rightFunction rightArgument).mpr (Or.inr member))
              apply induction (substitution := substitution)
                (constraints :=
                  { left := leftFunction, right := rightFunction } ::
                  { left := leftArgument, right := rightArgument } :: rest)
                (result := result)
              · exact cross
              · exact binaryConstraintsOutsideDomain leftParts.1 leftParts.2
                  rightParts.1 rightParts.2 restOutside
              · exact success
            · rename_i _ _ leftInner rightInner leftEq rightEq
              apply induction (substitution := substitution)
                (constraints := { left := leftInner, right := rightInner } :: rest)
                (result := result) cross
              · intro candidate member
                rcases List.mem_cons.mp member with rfl | member
                · constructor
                  · intro metavariable occurs
                    apply leftOutside metavariable
                    rw [leftEq]
                    exact occurs
                  · intro metavariable occurs
                    apply rightOutside metavariable
                    rw [rightEq]
                    exact occurs
                · exact restOutside candidate member
              · exact success
            · rename_i _ _ leftInner rightInner leftEq rightEq
              apply induction (substitution := substitution)
                (constraints := { left := leftInner, right := rightInner } :: rest)
                (result := result) cross
              · intro candidate member
                rcases List.mem_cons.mp member with rfl | member
                · constructor
                  · intro metavariable occurs
                    apply leftOutside metavariable
                    rw [leftEq]
                    exact occurs
                  · intro metavariable occurs
                    apply rightOutside metavariable
                    rw [rightEq]
                    exact occurs
                · exact restOutside candidate member
              · exact success
            · simp at success

def constraintSize (constraint : Constraint) : Nat :=
  constraint.left.size + constraint.right.size

/-- A bounded polynomial budget; pathological expansion reports `exhausted`. -/
def defaultFuel (constraints : List Constraint) : Nat :=
  let scale := constraints.foldl
    (fun size constraint => size + constraintSize constraint) (constraints.length + 1)
  scale * scale

def unifyWithFuel (fuel : Nat) (constraints : List Constraint) :
    Except Error Substitution :=
  loop fuel [] constraints

/-- Successful bounded unification of bounded constraints produces a solved
substitution under the same allocator limit. -/
theorem unifyWithFuel_solvedBelow
    {fuel next : Nat} {constraints : List Constraint}
    {result : Substitution}
    (below : ConstraintsBelow next constraints)
    (success : unifyWithFuel fuel constraints = .ok result) :
    result.SolvedBelow next := by
  apply loop_solvedBelow (Substitution.SolvedBelow.empty next) below
  exact success

/-- A shared allocator bound exposes successful bounded unification's
constraint-satisfaction proof directly from the strengthened loop invariant. -/
theorem unifyWithFuel_sound_of_below
    {fuel next : Nat} {constraints : List Constraint}
    {result : Substitution}
    (below : ConstraintsBelow next constraints)
    (success : unifyWithFuel fuel constraints = .ok result) :
    ConstraintsSatisfiedBy result constraints := by
  exact (loop_sound (Substitution.SolvedBelow.empty next) below success).2.2

/-- Successful bounded unification satisfies every input constraint after
applying the resulting substitution. -/
theorem unifyWithFuel_sound
    {fuel : Nat} {constraints : List Constraint} {result : Substitution}
    (success : unifyWithFuel fuel constraints = .ok result) :
    ConstraintsSatisfiedBy result constraints := by
  obtain ⟨next, below⟩ := constraintsBelow_exists constraints
  exact unifyWithFuel_sound_of_below (next := next) below success

/-- Successful bounded-fuel unification cannot introduce an older domain
variable into its result range when all input constraints avoid that domain. -/
theorem unifyWithFuel_rangeAvoidsDomain
    {fuel : Nat} {older result : Substitution}
    {constraints : List Constraint}
    (outside : ConstraintsOutsideDomain older constraints)
    (success : unifyWithFuel fuel constraints = .ok result) :
    result.RangeAvoidsDomain older := by
  apply loop_rangeAvoidsDomain (substitution := [])
  · intro metavariable replacement member
    simp at member
  · exact outside
  · exact success

@[simp]
theorem unifyWithFuel_empty (fuel : Nat) :
    unifyWithFuel (fuel + 1) [] = .ok [] := by
  simp [unifyWithFuel, loop]

@[simp]
theorem unifyWithFuel_reflexive (fuel : Nat) (type : Ty) :
    unifyWithFuel (fuel + 2) [{ left := type, right := type }] = .ok [] := by
  simp [unifyWithFuel, loop]

@[simp]
theorem unifyWithFuel_variable_constructor (fuel : Nat) (metavariable : TypeVarId)
    (constructor : TypeConstructorId) :
    unifyWithFuel (fuel + 2)
      [{ left := .variable metavariable, right := .constructor constructor }] =
        .ok [(metavariable, .constructor constructor)] := by
  simp [unifyWithFuel, loop, Substitution.compose, Substitution.apply,
    Substitution.lookup?, Ty.containsVariable, Ty.freeVariables]

/-- First-order unification with an occurs check. -/
def unify (constraints : List Constraint) : Except Error Substitution :=
  unifyWithFuel (defaultFuel constraints) constraints

/-- The default-fuel unifier inherits the solved-substitution guarantee. -/
theorem unify_solvedBelow
    {next : Nat} {constraints : List Constraint} {result : Substitution}
    (below : ConstraintsBelow next constraints)
    (success : unify constraints = .ok result) :
    result.SolvedBelow next := by
  exact unifyWithFuel_solvedBelow below success

/-- A shared allocator bound exposes the default-fuel unifier's successful
constraint-satisfaction proof. -/
theorem unify_sound_of_below
    {next : Nat} {constraints : List Constraint} {result : Substitution}
    (below : ConstraintsBelow next constraints)
    (success : unify constraints = .ok result) :
    ConstraintsSatisfiedBy result constraints := by
  exact unifyWithFuel_sound_of_below below success

/-- The default-fuel unifier satisfies every input constraint whenever it
returns successfully. -/
theorem unify_sound
    {constraints : List Constraint} {result : Substitution}
    (success : unify constraints = .ok result) :
    ConstraintsSatisfiedBy result constraints := by
  exact unifyWithFuel_sound success

/-- The default-fuel unifier preserves avoidance of an older substitution
domain. -/
theorem unify_rangeAvoidsDomain
    {older result : Substitution} {constraints : List Constraint}
    (outside : ConstraintsOutsideDomain older constraints)
    (success : unify constraints = .ok result) :
    result.RangeAvoidsDomain older := by
  exact unifyWithFuel_rangeAvoidsDomain outside success

def unifyTypes (left right : Ty) : Except Error Substitution :=
  unify [{ left, right }]

/-- Binary unification preserves the common variable bound of its inputs. -/
theorem unifyTypes_solvedBelow
    {next : Nat} {left right : Ty} {result : Substitution}
    (leftBelow : left.VariablesBelow next)
    (rightBelow : right.VariablesBelow next)
    (success : unifyTypes left right = .ok result) :
    result.SolvedBelow next := by
  apply unify_solvedBelow (constraints := [{ left, right }])
  · intro constraint member
    have same : constraint = { left, right } := by
      simpa using member
    subst constraint
    exact ⟨leftBelow, rightBelow⟩
  · exact success

/-- Successful binary unification makes its two input types equal under the
resulting substitution. -/
theorem unifyTypes_sound
    {left right : Ty} {result : Substitution}
    (success : unifyTypes left right = .ok result) :
    result.apply left = result.apply right := by
  have satisfied := unify_sound (constraints := [{ left, right }]) success
  exact satisfied { left, right } (by simp)

/-- Binary unification cannot reintroduce an older substitution-domain
variable when neither normalized input contains one. -/
theorem unifyTypes_rangeAvoidsDomain
    {older result : Substitution} {left right : Ty}
    (leftOutside : ∀ metavariable,
      metavariable ∈ left.freeVariables → metavariable ∉ older.domain)
    (rightOutside : ∀ metavariable,
      metavariable ∈ right.freeVariables → metavariable ∉ older.domain)
    (success : unifyTypes left right = .ok result) :
    result.RangeAvoidsDomain older := by
  apply unify_rangeAvoidsDomain (constraints := [{ left, right }])
  · intro constraint member
    have same : constraint = { left, right } := by
      simpa using member
    subst constraint
    exact ⟨leftOutside, rightOutside⟩
  · exact success

end Unification

end Solcore.TypeSystem
