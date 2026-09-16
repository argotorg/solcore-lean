import Solcore.Syntax.Term

set_option autoImplicit false

namespace Solcore.Frontend

/-- A maximal finite group spine ending at the original immediate conditional. -/
inductive ConditionalGroupSpine :
    Syntax.Expr → List Syntax.SourceSpan → Syntax.Expr → Prop where
  | conditional {span question colon : Syntax.SourceSpan}
      {condition yes no : Syntax.Expr} :
      ConditionalGroupSpine
        ⟨span, .conditional condition question yes colon no⟩ []
        ⟨span, .conditional condition question yes colon no⟩
  | group {span : Syntax.SourceSpan} {inner terminal : Syntax.Expr}
      {spans : List Syntax.SourceSpan}
      (child : ConditionalGroupSpine inner spans terminal) :
      ConditionalGroupSpine ⟨span, .group inner⟩ (span :: spans) terminal

/-- Collect all original group spans and return the original terminal conditional. -/
def peelConditionalGroupSpine?
    : (source : Syntax.Expr) → Option (List Syntax.SourceSpan × Syntax.Expr) :=
  WellFounded.fix (measure sizeOf).wf fun source recurse =>
    match source with
    | terminal@⟨_, .conditional _ _ _ _ _⟩ => some ([], terminal)
    | ⟨span, .group inner⟩ => do
        let (spans, terminal) ← recurse inner (by decreasing_tactic)
        some (span :: spans, terminal)
    | _ => none

@[simp] theorem peelConditionalGroupSpine?_conditional
    (span question colon : Syntax.SourceSpan) (condition yes no : Syntax.Expr) :
    peelConditionalGroupSpine?
      ⟨span, .conditional condition question yes colon no⟩ =
        some ([], ⟨span, .conditional condition question yes colon no⟩) := by
  rw [peelConditionalGroupSpine?, WellFounded.fix_eq]

@[simp] theorem peelConditionalGroupSpine?_group
    (span : Syntax.SourceSpan) (inner : Syntax.Expr) :
    peelConditionalGroupSpine? ⟨span, .group inner⟩ = (do
      let (spans, terminal) ← peelConditionalGroupSpine? inner
      some (span :: spans, terminal)) := by
  rw [peelConditionalGroupSpine?, WellFounded.fix_eq]

private theorem peelConditionalGroupSpine?_sound
    {source terminal : Syntax.Expr} {spans : List Syntax.SourceSpan}
    (accepted : peelConditionalGroupSpine? source = some (spans, terminal)) :
    ConditionalGroupSpine source spans terminal := by
  revert spans terminal
  apply (measure sizeOf).wf.induction source
  intro source ih spans terminal accepted
  cases source with
  | mk span kind =>
    cases kind <;>
      try { rw [peelConditionalGroupSpine?, WellFounded.fix_eq] at accepted; cases accepted }
    case conditional condition question yes colon no =>
      simp only [peelConditionalGroupSpine?_conditional, Option.some.injEq,
        Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact .conditional
    case group inner =>
      cases checked : peelConditionalGroupSpine? inner with
      | none => simp [peelConditionalGroupSpine?_group, checked] at accepted
      | some result =>
        rcases result with ⟨innerSpans, argument⟩
        simp [peelConditionalGroupSpine?_group, checked] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact .group (ih inner (by simp_wf; omega) checked)

private theorem peelConditionalGroupSpine?_complete
    {source terminal : Syntax.Expr} {spans : List Syntax.SourceSpan}
    (spine : ConditionalGroupSpine source spans terminal) :
    peelConditionalGroupSpine? source = some (spans, terminal) := by
  induction spine with
  | conditional => simp only [peelConditionalGroupSpine?_conditional]
  | group child ih => simp [peelConditionalGroupSpine?_group, ih]

/-- Exact executable/declarative correspondence for the maximal spine. -/
theorem peelConditionalGroupSpine?_iff
    {source terminal : Syntax.Expr} {spans : List Syntax.SourceSpan} :
    peelConditionalGroupSpine? source = some (spans, terminal) ↔
      ConditionalGroupSpine source spans terminal :=
  ⟨peelConditionalGroupSpine?_sound, peelConditionalGroupSpine?_complete⟩

end Solcore.Frontend
