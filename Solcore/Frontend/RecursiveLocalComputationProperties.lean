import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalExpressionTypingProperties
import Solcore.Frontend.DirectWordBinaryProperties

/-! Exact static provenance for recursive calls, groups and direct binaries.
Pure overlap is reconciled internally without restricting source or callers. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem binary_children {table : LocalNameTable} {context : Resolved.Context}
    {span operatorSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
    {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} {core : Core.Expr} {type : Core.Ty}
    (operator : DirectWordBinary sourceOp op) :
    elaborateRecursiveLocalComputation? table context
        ⟨span, .binary left ⟨operatorSpan, sourceOp⟩ right⟩ = some (core, type) ↔
      ∃ leftCore rightCore,
        elaborateRecursiveLocalComputation? table context left = some (leftCore, op.leftType) ∧
        elaborateRecursiveLocalComputation? table context right = some (rightCore, op.rightType) ∧
        core = .binary op leftCore rightCore ∧ type = op.resultType := by
  simp only [elaborateRecursiveLocalComputation?, directWordBinary?_iff.mpr operator,
    bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨leftCore, leftType⟩, leftAccepted, ⟨rightCore, rightType⟩, rightAccepted, result⟩
    dsimp only at result
    split at result
    next same =>
      cases result
      exact ⟨leftCore, rightCore, same.1 ▸ leftAccepted, same.2 ▸ rightAccepted, rfl, rfl⟩
    next => cases result
  · rintro ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩
    exact ⟨(leftCore, op.leftType), leftAccepted, (rightCore, op.rightType), rightAccepted, by simp⟩

private theorem pure_complete {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr} {core : Core.Expr} {type : Core.Ty}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers context.ids resolved core)
    (typing : Resolved.HasType context resolved type) :
    elaborateRecursiveLocalComputation? table context source = some (core, type) := by
  induction resolution generalizing core type with
  | group _ ih => simpa only [elaborateRecursiveLocalComputation?] using ih lowered typing
  | add _ _ leftIH rightIH | subtract _ _ leftIH rightIH
  | multiply _ _ leftIH rightIH | divide _ _ leftIH rightIH
  | modulo _ _ leftIH rightIH | greater _ _ leftIH rightIH | equal _ _ leftIH rightIH
  | bitAnd _ _ leftIH rightIH | bitOr _ _ leftIH rightIH | bitXor _ _ leftIH rightIH =>
      cases lowered with
      | binary leftLowered rightLowered =>
          cases typing with
          | binary leftTyped rightTyped =>
              rw [elaborateRecursiveLocalComputation?]
              simp [directWordBinary?, leftIH leftLowered leftTyped, rightIH rightLowered rightTyped]
  | _ =>
      rw [elaborateRecursiveLocalComputation?] <;> try simp [directWordBinary?]
      exact elaborateLocalExpression?_complete (by constructor <;> assumption) lowered typing

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
      exact pure_complete resolution lowered typing
  | group _ ih => simpa only [elaborateRecursiveLocalComputation?] using ih
  | application _ _ functionIH argumentIH =>
      exact application_children.mpr ⟨_, _, _, functionIH, argumentIH, rfl⟩
  | binary operator _ _ leftIH rightIH =>
      exact (binary_children operator).mpr ⟨_, _, leftIH, rightIH, rfl, rfl⟩

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
      case binary left operator right =>
        cases operator with
        | mk operatorSpan sourceOp =>
            cases mapped : directWordBinary? sourceOp with
            | none => exact pure_sound (by simpa only [elaborateRecursiveLocalComputation?, mapped] using accepted)
            | some op =>
                have operator := directWordBinary?_iff.mp mapped
                obtain ⟨leftCore, rightCore, leftAccepted, rightAccepted, rfl, rfl⟩ :=
                  (binary_children operator).mp accepted
                exact .binary operator (sound leftAccepted) (sound rightAccepted)
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
    | binary operator _ _ leftIH rightIH =>
        obtain ⟨leftCore, leftElaborated⟩ := leftIH
        obtain ⟨rightCore, rightElaborated⟩ := rightIH
        exact ⟨.binary _ leftCore rightCore, .binary operator leftElaborated rightElaborated⟩
  · rintro ⟨core, elaboration⟩
    induction elaboration with
    | pure resolution _ typing => exact .pure (resolution.reflects_type typing)
    | group _ ih => exact .group ih
    | application _ _ functionIH argumentIH => exact .application functionIH argumentIH
    | binary operator _ _ leftIH rightIH => exact .binary operator leftIH rightIH

theorem RecursiveLocalComputationElaborates.core_hasType
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : RecursiveLocalComputationElaborates table context source core type) :
    Core.HasType context.values core type := by
  induction elaboration with
  | pure _ lowered typing => exact lowered.preserves_type typing
  | group _ ih => exact ih
  | application _ _ functionIH argumentIH => exact .apply functionIH argumentIH
  | binary _ _ _ leftIH rightIH => exact .binary leftIH rightIH

end Solcore.Frontend
