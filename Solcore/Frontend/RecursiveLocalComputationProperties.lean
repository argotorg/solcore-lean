import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalExpressionTypingProperties

/-! Exact static provenance for recursive calls and transparent groups.
The pure/group overlap is reconciled internally, without restricting callers
or adding a non-group premise to either independent relation. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem pure_dispatch {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr}
    (resolution : ResolvesLocalExpression table source resolved) :
    elaborateRecursiveLocalComputation? table context source =
      elaborateLocalExpression? table context source := by
  induction resolution <;> rw [elaborateRecursiveLocalComputation?] <;> try simp
  case group span inner resolved child ih =>
    simpa only [elaborateLocalExpression?, resolveLocalExpression?] using ih

private theorem application_children {table : LocalNameTable} {context : Resolved.Context}
    {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty} :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ = some (core, type) ↔
      ∃ functionCore argumentCore parameterType,
        elaborateRecursiveLocalComputation? table context callee =
          some (functionCore, .function parameterType type) ∧
        elaborateRecursiveLocalComputation? table context argument = some (argumentCore, parameterType) ∧
        core = .apply functionCore argumentCore := by
  simp only [elaborateRecursiveLocalComputation?, bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨functionCore, functionType⟩, functionAccepted,
      ⟨argumentCore, argumentType⟩, argumentAccepted, result⟩
    cases functionType <;> try cases result
    case function parameterType resultType =>
      dsimp only at result
      split at result
      next same =>
        cases result
        exact ⟨functionCore, argumentCore, parameterType, functionAccepted, same ▸ argumentAccepted, rfl⟩
      next => cases result
  · rintro ⟨functionCore, argumentCore, parameterType, functionAccepted, argumentAccepted, rfl⟩
    exact ⟨(functionCore, .function parameterType type), functionAccepted,
      (argumentCore, parameterType), argumentAccepted, by simp⟩

private theorem complete {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type) :
    elaborateRecursiveLocalComputation? table context source = some (core, type) := by
  induction elaboration with
  | pure resolution lowered typing =>
      rw [pure_dispatch resolution]
      exact elaborateLocalExpression?_complete resolution lowered typing
  | group _ ih => simpa only [elaborateRecursiveLocalComputation?] using ih
  | application _ _ functionIH argumentIH =>
      exact application_children.mpr ⟨_, _, _, functionIH, argumentIH, rfl⟩

private theorem pure_sound {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type)) :
    RecursiveLocalComputationElaborates table context source core type := by
  obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound accepted
  exact .pure resolution lowered typing

private theorem sound {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateRecursiveLocalComputation? table context source = some (core, type)) :
    RecursiveLocalComputationElaborates table context source core type := by
  cases source with
  | mk span payload =>
      cases payload
      case group inner =>
        exact .group (sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted))
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan arguments =>
            cases arguments with
            | nil => exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
            | cons argument rest =>
                cases rest with
                | nil =>
                    obtain ⟨functionCore, argumentCore, parameterType, functionAccepted, argumentAccepted, rfl⟩ :=
                      application_children.mp accepted
                    exact .application (sound functionAccepted) (sound argumentAccepted)
                | cons _ _ => exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
      all_goals exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?] using accepted)
termination_by sizeOf source

theorem elaborateRecursiveLocalComputation?_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateRecursiveLocalComputation? table context source = some (core, type) ↔
      RecursiveLocalComputationElaborates table context source core type :=
  ⟨sound, complete⟩

theorem recursiveLocalComputationHasType_iff_elaborates
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty} :
    RecursiveLocalComputationHasType table context source type ↔
      ∃ core, RecursiveLocalComputationElaborates table context source core type := by
  constructor
  · intro typing
    induction typing with
    | pure child =>
        obtain ⟨resolved, resolution, typed⟩ := child.resolves
        obtain ⟨core, lowered, _⟩ := typed.lowers
        exact ⟨core, .pure resolution lowered typed⟩
    | group _ ih =>
        obtain ⟨core, child⟩ := ih
        exact ⟨core, .group child⟩
    | application _ _ functionIH argumentIH =>
        obtain ⟨functionCore, functionElaborated⟩ := functionIH
        obtain ⟨argumentCore, argumentElaborated⟩ := argumentIH
        exact ⟨.apply functionCore argumentCore, .application functionElaborated argumentElaborated⟩
  · rintro ⟨core, elaboration⟩
    induction elaboration with
    | pure resolution _ typing => exact .pure (resolution.reflects_type typing)
    | group _ ih => exact .group ih
    | application _ _ functionIH argumentIH => exact .application functionIH argumentIH

theorem RecursiveLocalComputationElaborates.core_hasType
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type) :
    Core.HasType context.values core type := by
  induction elaboration with
  | pure _ lowered typing => exact lowered.preserves_type typing
  | group _ ih => exact ih
  | application _ _ functionIH argumentIH => exact .apply functionIH argumentIH

end Solcore.Frontend
