import Solcore.Frontend.SourceInference.TypedIR

/-! The bindings a closure copies. A lambda copies its captured cells when it
is created and again at each call. A binding is copied when its identifier has
a single declaration in the closure's source and that declaration is
monomorphic. A generalized local holds an immutable principal, and a hidden
match scrutinee has no declaration, so both keep their cells. The source
semantics and the source-to-Core lowering make the same decision from the same
source, so no invariant relates the two. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CaptureBinders

open Frontend
open Frontend.SourceInference

/-- The binders an instruction stream of a match pattern declares. -/
def instructionBinders (instructions : List MatchPatternInstruction) : List TypedBinder :=
  instructions.filterMap fun | .binder binder => some binder | _ => none

/-- The binders a match pattern declares. -/
def patternBinders (pattern : TypedMatchPattern) : List TypedBinder :=
  match pattern.resolution with
  | .binder binder => [binder]
  | .constructor _ children | .tuple children => instructionBinders children
  | _ => []

/-- The `let` binders of a `for` header. -/
def forBinders (items : List ForItemForm) : List TypedBinder :=
  items.filterMap fun | .letDecl binder _ => some binder | _ => none

/-- The binders one source node declares: a lambda's parameters and the
binders of `let`, `for` and `match`. -/
def nodeBinders : Node → List TypedBinder
  | .expression node => match node.form with
      | .lambda parameters _ _ => parameters
      | _ => []
  | .statement node => match node.form with
      | .letDecl binder _ => [binder]
      | .forLoop initial _ post _ => forBinders (initial ++ post)
      | .matchWith resolution => resolution.cases.flatMap (fun arm => patternBinders arm.pattern)
      | _ => []

/-- Every binder declared by a source body: its inputs, lambda parameters, and
the binders of `let`, `for` and `match`. -/
def declaredBinders (source : TypedSource) : List TypedBinder :=
  source.inputs ++ source.nodes.flatMap nodeBinders

/-- The declaration of a binding that a closure copies: the identifier's only
declaration, when it is monomorphic. -/
def copiedBinder? (source : TypedSource) (id : Resolved.LocalId) : Option TypedBinder :=
  match (declaredBinders source).filter (fun binder => decide (binder.id = id)) with
  | [binder] => if binder.scheme.quantified.isEmpty then some binder else none
  | _ => none

/-! ## Substitution

A substitution changes binder types but keeps binder identifiers, the order of
declarations and every scheme's quantified variables, so it keeps the copy
decision. -/

private theorem filterMap_congr {α β : Type} {f g : α → Option β} {items : List α}
    (same : ∀ item ∈ items, f item = g item) : items.filterMap f = items.filterMap g := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.filterMap_cons, same head (by simp), ih (fun item member => same item (by simp [member]))]

private theorem flatMap_congr {α β : Type} {f g : α → List β} {items : List α}
    (same : ∀ item ∈ items, f item = g item) : items.flatMap f = items.flatMap g := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.flatMap_cons, same head (by simp), ih (fun item member => same item (by simp [member]))]

theorem instructionBinders_applySubstitution (substitution : TypeSystem.Substitution)
    (instructions : List MatchPatternInstruction) :
    instructionBinders (instructions.map (MatchPatternInstruction.applySubstitution substitution)) =
      (instructionBinders instructions).map (TypedBinder.applySubstitution substitution) := by
  unfold instructionBinders
  rw [List.filterMap_map, List.map_filterMap]
  apply filterMap_congr
  intro instruction _
  cases instruction <;> rfl

theorem patternBinders_applySubstitution (substitution : TypeSystem.Substitution)
    (pattern : TypedMatchPattern) :
    patternBinders (pattern.applySubstitution substitution) =
      (patternBinders pattern).map (TypedBinder.applySubstitution substitution) := by
  unfold patternBinders TypedMatchPattern.applySubstitution
  cases pattern.resolution <;>
    simp [MatchPatternResolution.applySubstitution, instructionBinders_applySubstitution]

theorem forBinders_applySubstitution (substitution : TypeSystem.Substitution) (items : List ForItemForm) :
    forBinders (items.map (ForItemForm.applySubstitution substitution)) =
      (forBinders items).map (TypedBinder.applySubstitution substitution) := by
  unfold forBinders
  rw [List.filterMap_map, List.map_filterMap]
  apply filterMap_congr
  intro item _
  cases item <;> rfl

theorem nodeBinders_applySubstitution (substitution : TypeSystem.Substitution) (node : Node) :
    nodeBinders (node.applySubstitution substitution) =
      (nodeBinders node).map (TypedBinder.applySubstitution substitution) := by
  cases node with
  | expression node =>
    simp only [Node.applySubstitution, ExpressionNode.applySubstitution, nodeBinders]
    cases node.form <;> simp [ExpressionForm.applySubstitution]
  | statement node =>
    simp only [Node.applySubstitution, StatementNode.applySubstitution, nodeBinders]
    cases node.form with
    | forLoop initial condition post body =>
      simp only [StatementForm.applySubstitution]
      rw [← List.map_append, forBinders_applySubstitution]
    | matchWith resolution =>
      simp only [StatementForm.applySubstitution, MatchResolution.applySubstitution, List.flatMap_map,
        List.map_flatMap]
      apply flatMap_congr
      intro arm _
      exact patternBinders_applySubstitution substitution arm.pattern
    | _ => simp [StatementForm.applySubstitution]

theorem declaredBinders_applySubstitution (substitution : TypeSystem.Substitution) (source : TypedSource) :
    declaredBinders (source.applySubstitution substitution) =
      (declaredBinders source).map (TypedBinder.applySubstitution substitution) := by
  unfold declaredBinders
  simp only [TypedSource.applySubstitution, List.map_append, List.flatMap_map, List.map_flatMap]
  congr 1
  apply flatMap_congr
  intro node _
  exact nodeBinders_applySubstitution substitution node

theorem copiedBinder?_applySubstitution (substitution : TypeSystem.Substitution) (source : TypedSource)
    (id : Resolved.LocalId) :
    copiedBinder? (source.applySubstitution substitution) id =
      (copiedBinder? source id).map (TypedBinder.applySubstitution substitution) := by
  unfold copiedBinder?
  rw [declaredBinders_applySubstitution, List.filter_map]
  have same : ((fun binder : TypedBinder => decide (binder.id = id)) ∘
      TypedBinder.applySubstitution substitution) = fun binder => decide (binder.id = id) := by
    funext binder
    rfl
  rw [same]
  cases (declaredBinders source).filter (fun binder => decide (binder.id = id)) with
  | nil => rfl
  | cons head tail =>
    cases tail with
    | nil =>
      by_cases empty : head.scheme.quantified.isEmpty <;>
        simp [empty, TypedBinder.applySubstitution, TypeSystem.Scheme.apply]
    | cons _ _ => rfl

/-- Two sources copy the same identifiers when one is a substitution instance
of the other. -/
theorem copied_isSome_applySubstitution (substitution : TypeSystem.Substitution) (source : TypedSource)
    (id : Resolved.LocalId) :
    (copiedBinder? (source.applySubstitution substitution) id).isSome = (copiedBinder? source id).isSome := by
  rw [copiedBinder?_applySubstitution, Option.isSome_map]

end Solcore.SourceSemantics.CaptureBinders
