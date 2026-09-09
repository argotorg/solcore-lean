import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.LocalExpressionTypingProperties

/-! Exact static correspondence for one known Function application. Actual
closures, their stores and their body costs are separate dynamic obligations. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Both original children check in the same scope; the result is their ordered
application, not an arbitrary replacement with the same type. -/
theorem elaborateLocalFunctionApplication?_children {table : LocalNameTable}
    {context : Resolved.Context} {span argumentsSpan : Syntax.SourceSpan}
    {callee argument : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalFunctionApplication? table context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ = some (core, type) ↔
      ∃ functionCore argumentCore parameterType,
        elaborateLocalExpression? table context callee = some (functionCore, .function parameterType type) ∧
        elaborateLocalExpression? table context argument = some (argumentCore, parameterType) ∧
        core = .apply functionCore argumentCore := by
  simp only [elaborateLocalFunctionApplication?, bind, Option.bind_eq_some_iff]
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

theorem LocalFunctionApplicationElaborates.complete {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type) :
    elaborateLocalFunctionApplication? table context source = some (core, type) := by
  cases elaboration with
  | call functionResolution functionLowered functionTyped argumentResolution argumentLowered argumentTyped =>
      exact elaborateLocalFunctionApplication?_children.mpr ⟨_, _, _,
        elaborateLocalExpression?_complete functionResolution functionLowered functionTyped,
        elaborateLocalExpression?_complete argumentResolution argumentLowered argumentTyped, rfl⟩

theorem elaborateLocalFunctionApplication?_sound {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalFunctionApplication? table context source = some (core, type)) :
    LocalFunctionApplicationElaborates table context source core type := by
  rcases source with ⟨span, payload⟩
  cases payload <;> try cases accepted
  case call callee arguments =>
    rcases arguments with ⟨argumentsSpan, arguments⟩
    cases arguments with
    | nil => cases accepted
    | cons argument rest =>
        cases rest with
        | cons _ _ => cases accepted
        | nil =>
            obtain ⟨functionCore, argumentCore, parameterType, functionAccepted, argumentAccepted, rfl⟩ :=
              elaborateLocalFunctionApplication?_children.mp accepted
            obtain ⟨resolvedFunction, functionResolution, functionLowered, functionTyped⟩ :=
              elaborateLocalExpression?_sound functionAccepted
            obtain ⟨resolvedArgument, argumentResolution, argumentLowered, argumentTyped⟩ :=
              elaborateLocalExpression?_sound argumentAccepted
            exact .call functionResolution functionLowered functionTyped
              argumentResolution argumentLowered argumentTyped

theorem elaborateLocalFunctionApplication?_iff {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalFunctionApplication? table context source = some (core, type) ↔
      LocalFunctionApplicationElaborates table context source core type :=
  ⟨elaborateLocalFunctionApplication?_sound, LocalFunctionApplicationElaborates.complete⟩

theorem LocalFunctionApplicationElaborates.hasType {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type) :
    LocalFunctionApplicationHasType table context source type := by
  cases elaboration with
  | call functionResolution _ functionTyped argumentResolution _ argumentTyped =>
      exact .call (functionResolution.reflects_type functionTyped)
        (argumentResolution.reflects_type argumentTyped)

theorem LocalFunctionApplicationHasType.elaborates_exact {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalFunctionApplicationHasType table context source type) :
    ∃ core, LocalFunctionApplicationElaborates table context source core type := by
  cases typing with
  | call functionTyped argumentTyped =>
      obtain ⟨resolvedFunction, functionResolution, functionTyping⟩ := functionTyped.resolves
      obtain ⟨functionCore, functionLowered, _⟩ := functionTyping.lowers
      obtain ⟨resolvedArgument, argumentResolution, argumentTyping⟩ := argumentTyped.resolves
      obtain ⟨argumentCore, argumentLowered, _⟩ := argumentTyping.lowers
      exact ⟨.apply functionCore argumentCore, .call functionResolution functionLowered functionTyping
        argumentResolution argumentLowered argumentTyping⟩

theorem localFunctionApplicationHasType_iff_elaborates {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty} :
    LocalFunctionApplicationHasType table context source type ↔
      ∃ core, LocalFunctionApplicationElaborates table context source core type :=
  ⟨LocalFunctionApplicationHasType.elaborates_exact, fun ⟨_, elaboration⟩ => elaboration.hasType⟩

theorem LocalFunctionApplicationElaborates.result_unique {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {leftCore rightCore : Core.Expr}
    {leftType rightType : Core.Ty}
    (left : LocalFunctionApplicationElaborates table context source leftCore leftType)
    (right : LocalFunctionApplicationElaborates table context source rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

theorem LocalFunctionApplicationHasType.type_unique {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {left right : Core.Ty}
    (leftTyped : LocalFunctionApplicationHasType table context source left)
    (rightTyped : LocalFunctionApplicationHasType table context source right) : left = right := by
  obtain ⟨_, leftElaboration⟩ := leftTyped.elaborates_exact
  obtain ⟨_, rightElaboration⟩ := rightTyped.elaborates_exact
  exact (leftElaboration.result_unique rightElaboration).2

/-- Static typing requires no actual argument or closure inhabitants and adds
no claim about stores, runtime worlds, local-fragment membership or fuel. -/
theorem LocalFunctionApplicationElaborates.core_hasType {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalFunctionApplicationElaborates table context source core type) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  cases elaboration with
  | call _ functionLowered functionTyped _ argumentLowered argumentTyped =>
      exact .apply (functionLowered.preserves_type functionTyped) (argumentLowered.preserves_type argumentTyped)

theorem elaborateLocalFunctionApplication?_core_hasType {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalFunctionApplication? table context source = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type :=
  (elaborateLocalFunctionApplication?_sound accepted).core_hasType

theorem elaborateLocalFunctionApplication?_eq_none_iff {table : LocalNameTable}
    {context : Resolved.Context} {source : Syntax.Expr} :
    elaborateLocalFunctionApplication? table context source = none ↔
      ¬ ∃ type, LocalFunctionApplicationHasType table context source type := by
  constructor
  · intro rejected ⟨_, typing⟩
    obtain ⟨_, elaboration⟩ := typing.elaborates_exact
    have accepted := elaboration.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateLocalFunctionApplication? table context source with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, (elaborateLocalFunctionApplication?_sound result).hasType⟩)

end Solcore.Frontend
