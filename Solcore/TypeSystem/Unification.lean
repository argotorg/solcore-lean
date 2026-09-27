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

end Constraint

/-- Every pending unification constraint is bounded by the same allocator
limit. -/
def ConstraintsBelow (next : Nat) (constraints : List Constraint) : Prop :=
  ∀ constraint, constraint ∈ constraints → constraint.VariablesBelow next

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

private theorem loop_solvedBelow
    {fuel next : Nat} {substitution result : Substitution}
    {constraints : List Constraint}
    (solved : substitution.SolvedBelow next)
    (constraintsBelow : ConstraintsBelow next constraints)
    (success : loop fuel substitution constraints = .ok result) :
    result.SolvedBelow next := by
  induction fuel generalizing substitution constraints result with
  | zero =>
      simp [loop] at success
  | succ fuel induction =>
      cases constraints with
      | nil =>
          simp only [loop, Except.ok.injEq] at success
          subst result
          exact solved
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
          · exact induction solved restBelow success
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
                  exact induction
                    (bind_solvedBelow solved metavariableBelow rightBelow
                      rightOutside occursCheck)
                    restBelow success
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
                  exact induction
                    (bind_solvedBelow solved metavariableBelow leftBelow
                      leftOutside occursCheck)
                    restBelow success
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
              exact induction solved decomposedBelow success
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
              exact induction solved decomposedBelow success
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
              exact induction solved decomposedBelow success
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
              exact induction solved decomposedBelow success
            · rename_i _ _ leftInner rightInner leftEq rightEq
              have normalizedLeft :
                  (Ty.proxy leftInner).VariablesBelow next := by
                rw [← leftEq]
                exact leftBelow
              have normalizedRight :
                  (Ty.proxy rightInner).VariablesBelow next := by
                rw [← rightEq]
                exact rightBelow
              apply induction
                (constraints := { left := leftInner, right := rightInner } :: rest)
                solved
              · intro candidate member
                rcases List.mem_cons.mp member with same | member
                · subst candidate
                  exact
                    ⟨(Ty.variablesBelow_proxy_iff next leftInner).mp
                        normalizedLeft,
                      (Ty.variablesBelow_proxy_iff next rightInner).mp
                        normalizedRight⟩
                · exact restBelow candidate member
              · exact success
            · rename_i _ _ leftInner rightInner leftEq rightEq
              have normalizedLeft :
                  (Ty.comptime leftInner).VariablesBelow next := by
                rw [← leftEq]
                exact leftBelow
              have normalizedRight :
                  (Ty.comptime rightInner).VariablesBelow next := by
                rw [← rightEq]
                exact rightBelow
              apply induction
                (constraints := { left := leftInner, right := rightInner } :: rest)
                solved
              · intro candidate member
                rcases List.mem_cons.mp member with same | member
                · subst candidate
                  exact
                    ⟨(Ty.variablesBelow_comptime_iff next leftInner).mp
                        normalizedLeft,
                      (Ty.variablesBelow_comptime_iff next rightInner).mp
                        normalizedRight⟩
                · exact restBelow candidate member
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

end Unification

end Solcore.TypeSystem
