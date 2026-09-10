import Solcore.Frontend.RuntimeValueProperties

/-! Structural nonprojectability tests. These witnesses describe finite value
subterms, never reachable heap contents, source admission or execution. -/
set_option autoImplicit false
namespace Tests.RuntimeValueBoundaries
open Solcore Solcore.Frontend

private inductive ContainsSource : RuntimeValue → Prop where
  | source (source : Syntax.Expr) (owner : Resolved.DeclarationId)
      (names : List (String × Resolved.LocalId)) (captured : List (Resolved.LocalId × RuntimeValue)) :
      ContainsSource (.sourceClosure source owner names captured)
  | pairLeft {left right : RuntimeValue} : ContainsSource left → ContainsSource (.pair left right)
  | pairRight {left right : RuntimeValue} : ContainsSource right → ContainsSource (.pair left right)
  | inLeft {type : Core.Ty} {payload : RuntimeValue} :
      ContainsSource payload → ContainsSource (.inLeft type payload)
  | inRight {type : Core.Ty} {payload : RuntimeValue} :
      ContainsSource payload → ContainsSource (.inRight type payload)
  | constructed {constructor : Core.ConstructorId} {payload : RuntimeValue} :
      ContainsSource payload → ContainsSource (.constructed constructor payload)
  | coreCapture {a b : Core.Ty} {body : Core.Expr} {captured : List RuntimeValue} {value : RuntimeValue} :
      value ∈ captured → ContainsSource value → ContainsSource (.coreClosure a b body captured)

private theorem project_attached (values : List RuntimeValue) :
    values.attach.mapM (fun value => RuntimeValue.toCore? value.val) = values.mapM RuntimeValue.toCore? := by
  change values.attach.mapM (RuntimeValue.toCore? ∘ Subtype.val) = _
  rw [← List.mapM_map, List.attach_map_subtype_val]

private theorem list_fails_at_member {value : RuntimeValue} (values : List RuntimeValue)
    (member : value ∈ values) (absent : value.toCore? = none) :
    values.mapM RuntimeValue.toCore? = none := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      simp only [List.mapM_cons, bind]
      rcases member with same | member
      · subst head
        simp only [absent, Option.bind_none]
      · rw [ih member]
        cases head.toCore? <;> rfl

theorem every_finite_source_occurrence_blocks_projection {value : RuntimeValue}
    (contains : ContainsSource value) : value.toCore? = none := by
  induction contains with
  | source => simp only [RuntimeValue.toCore?]
  | pairLeft _ ih => simp only [RuntimeValue.toCore?, ih, bind, Option.bind_none]
  | @pairRight left _ _ ih =>
      simp only [RuntimeValue.toCore?, ih, bind]
      cases left.toCore? <;> rfl
  | inLeft _ ih | inRight _ ih | constructed _ ih =>
      simp only [RuntimeValue.toCore?, ih, Option.map_none]
  | coreCapture member _ ih =>
      simp only [RuntimeValue.toCore?, project_attached, list_fails_at_member _ member ih,
        Option.map_none]

theorem source_closures_are_outside_the_entire_core_image
    (source : Syntax.Expr) (owner : Resolved.DeclarationId)
    (names : List (String × Resolved.LocalId)) (captured : List (Resolved.LocalId × RuntimeValue))
    (core : Core.Value) : RuntimeValue.sourceClosure source owner names captured ≠ RuntimeValue.ofCore core := by
  intro same
  have projected := congrArg RuntimeValue.toCore? same
  rw [RuntimeValue.toCore?_ofCore] at projected
  simp only [RuntimeValue.toCore?, reduceCtorEq] at projected

theorem projection_failure_exactly_excludes_an_old_value (value : RuntimeValue) :
    value.toCore? = none ↔ ¬ ∃ core, value = RuntimeValue.ofCore core := by
  constructor
  · intro absent ⟨core, same⟩
    have projected := RuntimeValue.toCore?_eq_some_iff.mpr same
    rw [absent] at projected
    cases projected
  · intro noImage
    cases projected : value.toCore? with
    | none => rfl
    | some core => exact False.elim (noImage ⟨core, RuntimeValue.toCore?_eq_some_iff.mp projected⟩)

theorem raw_store_failure_does_not_drop_unobserved_slots
    (leading trailing : List RuntimeValue) {value : RuntimeValue} (contains : ContainsSource value) :
    (leading ++ value :: trailing).mapM RuntimeValue.toCore? = none :=
  list_fails_at_member _ (by simp) (every_finite_source_occurrence_blocks_projection contains)

theorem even_an_unused_core_capture_prevents_projection
    (source : Syntax.Expr) (owner : Resolved.DeclarationId)
    (names : List (String × Resolved.LocalId)) (captured : List (Resolved.LocalId × RuntimeValue))
    (leading trailing : List RuntimeValue) (a b : Core.Ty) :
    (RuntimeValue.coreClosure a b .unit
      (leading ++ .sourceClosure source owner names captured :: trailing)).toCore? = none :=
  every_finite_source_occurrence_blocks_projection
    (.coreCapture (value := .sourceClosure source owner names captured) (by simp) (.source _ _ _ _))

theorem projection_does_not_dereference_the_ambient_store
    (source : Syntax.Expr) (owner : Resolved.DeclarationId)
    (names : List (String × Resolved.LocalId)) (captured : List (Resolved.LocalId × RuntimeValue))
    (type : Core.Ty) :
    (RuntimeValue.cellRef type 0).toCore? = some (.cellRef type 0) ∧
    ([RuntimeValue.sourceClosure source owner names captured] : List RuntimeValue).mapM
      RuntimeValue.toCore? = none :=
  ⟨by simp only [RuntimeValue.toCore?], raw_store_failure_does_not_drop_unobserved_slots [] [] (.source _ _ _ _)⟩

theorem projection_preserves_even_unbound_core_code_and_arbitrary_captures
    (a b : Core.Ty) (captured : List Core.Value) :
    (RuntimeValue.coreClosure a b (.var (captured.length + 99)) (captured.map RuntimeValue.ofCore)).toCore? =
      some (.closure a b (.var (captured.length + 99)) captured) := by
  have roundtrip := RuntimeValue.toCore?_ofCore (.closure a b (.var (captured.length + 99)) captured)
  simpa only [RuntimeValue.ofCore, List.attach_map_val] using roundtrip

end Tests.RuntimeValueBoundaries
