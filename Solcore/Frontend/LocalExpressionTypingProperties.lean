import Solcore.Frontend.LocalExpressionTypingResolution

/-! Independent canonical-fragment typing agrees exactly with resolved typing
and the executable Core checker. All conditional branches and short-circuit
operands are checked, even when dynamic evaluation would skip them. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ResolvesLocalExpression.reflects_type {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr} {type : Core.Ty}
    (resolution : ResolvesLocalExpression table source resolved)
    (typing : Resolved.HasType context resolved type) :
    LocalExpressionHasType table context source type := by
  induction resolution generalizing type with
  | unit =>
      cases typing with
      | unit => exact .unit
  | identifier named =>
      cases typing with
      | var found => exact .identifier named found
  | wordLiteral meaning =>
      cases typing with
      | word => exact .wordLiteral meaning
  | group _ ih => exact .group (ih typing)
  | pair _ _ leftIH rightIH =>
      cases typing with
      | pair leftTyped rightTyped => exact .pair (leftIH leftTyped) (rightIH rightTyped)
  | many _ _ headIH tailIH =>
      cases typing with
      | pair headTyped tailTyped => exact .many (headIH headTyped) (tailIH tailTyped)
  | logicalNot _ ih =>
      cases typing with
      | unary operandTyped => exact .logicalNot (ih operandTyped)
  | bitNot _ ih =>
      cases typing with
      | unary operandTyped => exact .bitNot (ih operandTyped)
  | add _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .add (leftIH leftTyped) (rightIH rightTyped)
  | subtract _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .subtract (leftIH leftTyped) (rightIH rightTyped)
  | multiply _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .multiply (leftIH leftTyped) (rightIH rightTyped)
  | divide _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .divide (leftIH leftTyped) (rightIH rightTyped)
  | modulo _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .modulo (leftIH leftTyped) (rightIH rightTyped)
  | greater _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .greater (leftIH leftTyped) (rightIH rightTyped)
  | equal _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .equal (leftIH leftTyped) (rightIH rightTyped)
  | notEqual _ _ leftIH rightIH =>
      cases typing with
      | unary equalityTyped =>
          cases equalityTyped with
          | binary leftTyped rightTyped => exact .notEqual (leftIH leftTyped) (rightIH rightTyped)
  | lessEqual _ _ leftIH rightIH =>
      cases typing with
      | unary comparisonTyped =>
          cases comparisonTyped with
          | binary leftTyped rightTyped => exact .lessEqual (leftIH leftTyped) (rightIH rightTyped)
  | less _ _ leftIH rightIH =>
      cases typing with
      | wordLt leftTyped rightTyped => exact .less (leftIH leftTyped) (rightIH rightTyped)
  | greaterEqual _ _ leftIH rightIH =>
      cases typing with
      | unary comparisonTyped =>
          cases comparisonTyped with
          | wordLt leftTyped rightTyped => exact .greaterEqual (leftIH leftTyped) (rightIH rightTyped)
  | bitAnd _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .bitAnd (leftIH leftTyped) (rightIH rightTyped)
  | bitOr _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .bitOr (leftIH leftTyped) (rightIH rightTyped)
  | bitXor _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped => exact .bitXor (leftIH leftTyped) (rightIH rightTyped)
  | logicalAnd _ _ leftIH rightIH =>
      cases typing with
      | ifE leftTyped rightTyped falseTyped =>
          cases falseTyped
          exact .logicalAnd (leftIH leftTyped) (rightIH rightTyped)
  | logicalOr _ _ leftIH rightIH =>
      cases typing with
      | ifE leftTyped trueTyped rightTyped =>
          cases trueTyped
          exact .logicalOr (leftIH leftTyped) (rightIH rightTyped)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases typing with
      | ifE conditionTyped thenTyped elseTyped =>
          exact .conditional (conditionIH conditionTyped) (thenIH thenTyped) (elseIH elseTyped)

theorem ResolvesLocalExpression.preserves_type {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr} {type : Core.Ty}
    (resolution : ResolvesLocalExpression table source resolved)
    (typing : LocalExpressionHasType table context source type) :
    Resolved.HasType context resolved type := by
  obtain ⟨other, otherResolution, otherTyped⟩ := typing.resolves
  cases otherResolution.deterministic resolution
  exact otherTyped

theorem ResolvesLocalExpression.typing_iff {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr} {type : Core.Ty}
    (resolution : ResolvesLocalExpression table source resolved) :
    LocalExpressionHasType table context source type ↔ Resolved.HasType context resolved type :=
  ⟨resolution.preserves_type, resolution.reflects_type⟩

theorem localExpressionHasType_iff_resolves {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {type : Core.Ty} :
    LocalExpressionHasType table context source type ↔
      ∃ resolved, ResolvesLocalExpression table source resolved ∧ Resolved.HasType context resolved type :=
  ⟨LocalExpressionHasType.resolves, fun ⟨_, resolution, typing⟩ => resolution.reflects_type typing⟩

/-- Every successful result retains its exact resolved expression, positional
Core expression, and independently assigned type. -/
theorem elaborateLocalExpression?_sound {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type)) :
    ∃ resolved, ResolvesLocalExpression table source resolved ∧
      Resolved.Lowers (Resolved.LocalScope.ids context) resolved core ∧
      Resolved.HasType context resolved type := by
  simp only [elaborateLocalExpression?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨resolved, resolution, actualCore, lowering, actualType, inferred, result⟩ := accepted
  cases result
  have lowered := Resolved.Expr.lower?_sound lowering
  exact ⟨resolved, resolveLocalExpression?_sound resolution, lowered,
    lowered.reflects_type (Core.infer_sound inferred)⟩

theorem elaborateLocalExpression?_complete {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {resolved : Resolved.Expr} {core : Core.Expr} {type : Core.Ty}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids context) resolved core)
    (typing : Resolved.HasType context resolved type) :
    elaborateLocalExpression? table context source = some (core, type) := by
  simp [elaborateLocalExpression?, resolution.complete, lowered.complete,
    Core.infer_complete (lowered.preserves_type typing)]

theorem elaborateLocalExpression?_iff {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalExpression? table context source = some (core, type) ↔
      ∃ resolved, ResolvesLocalExpression table source resolved ∧
        Resolved.Lowers (Resolved.LocalScope.ids context) resolved core ∧
        Resolved.HasType context resolved type :=
  ⟨elaborateLocalExpression?_sound,
    fun ⟨_, resolution, lowered, typing⟩ => elaborateLocalExpression?_complete resolution lowered typing⟩

theorem localExpressionHasType_iff_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {type : Core.Ty} :
    LocalExpressionHasType table context source type ↔
      ∃ core, elaborateLocalExpression? table context source = some (core, type) := by
  constructor
  · intro typing
    obtain ⟨resolved, resolution, resolvedTyped⟩ := typing.resolves
    obtain ⟨core, lowered, _⟩ := resolvedTyped.lowers
    exact ⟨core, elaborateLocalExpression?_complete resolution lowered resolvedTyped⟩
  · rintro ⟨core, accepted⟩
    obtain ⟨resolved, resolution, _, typing⟩ := elaborateLocalExpression?_sound accepted
    exact resolution.reflects_type typing

theorem elaborateLocalExpression?_core_hasType {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  obtain ⟨resolved, _, lowered, typing⟩ := elaborateLocalExpression?_sound accepted
  exact lowered.preserves_type typing

theorem LocalExpressionHasType.type_unique {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {left right : Core.Ty}
    (first : LocalExpressionHasType table context source left)
    (second : LocalExpressionHasType table context source right) : left = right := by
  obtain ⟨resolved, resolution, typed⟩ := first.resolves
  exact Resolved.typing_deterministic typed (resolution.preserves_type second)

theorem elaborateLocalExpression?_type_unique {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {leftCore rightCore : Core.Expr} {left right : Core.Ty}
    (first : elaborateLocalExpression? table context source = some (leftCore, left))
    (second : elaborateLocalExpression? table context source = some (rightCore, right)) : left = right :=
  (localExpressionHasType_iff_elaborates.mpr ⟨leftCore, first⟩).type_unique
    (localExpressionHasType_iff_elaborates.mpr ⟨rightCore, second⟩)

/-- Failure includes unsupported/unmapped syntax, missing local IDs, and
ill-typed operands or conditionals; none is promoted to whole-language rejection. -/
theorem elaborateLocalExpression?_eq_none_iff {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} : elaborateLocalExpression? table context source = none ↔
      ¬ ∃ type, LocalExpressionHasType table context source type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := localExpressionHasType_iff_elaborates.mp typing
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateLocalExpression? table context source with
    | none => rfl
    | some pair =>
        exact False.elim (missing ⟨pair.2, localExpressionHasType_iff_elaborates.mpr ⟨pair.1, result⟩⟩)

end Solcore.Frontend
