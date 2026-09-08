import Solcore.Frontend.ConditionalReturnBody

/-! Independent typing and exact elaboration characterize the separate terminal
conditional checker. Both original return arms remain mandatory premises. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateConditionalReturnBody?_children
    {table : LocalNameTable} {context : Resolved.Context}
    {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context
      ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, type)) :
    ∃ conditionCore thenCore elseCore,
      elaborateLocalExpression? table context condition = some (conditionCore, .bool) ∧
      elaborateReturnBody? table context thenBody = some (thenCore, type) ∧
      elaborateReturnBody? table context elseBody = some (elseCore, type) ∧
      core = .ifE conditionCore thenCore elseCore := by
  simp only [elaborateConditionalReturnBody?, bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨conditionCore, conditionType⟩, conditionAccepted, remaining⟩ := accepted
  split at remaining
  next conditionBool =>
    change conditionType = .bool at conditionBool
    subst conditionType
    simp only [Option.bind_eq_some_iff] at remaining
    obtain ⟨⟨thenCore, thenType⟩, thenAccepted, ⟨elseCore, elseType⟩, elseAccepted, result⟩ := remaining
    split at result
    next sameType =>
      change thenType = elseType at sameType
      subst elseType
      change some (.ifE conditionCore thenCore elseCore, thenType) = some (core, type) at result
      simp only [Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨conditionCore, thenCore, elseCore, conditionAccepted, thenAccepted, elseAccepted, rfl⟩
    next different => cases result
  next notBool => cases remaining

theorem ConditionalReturnBodyElaborates.complete {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalReturnBodyElaborates table context body core type) :
    elaborateConditionalReturnBody? table context body = some (core, type) := by
  cases elaboration with
  | intro resolution lowered typing thenArm elseArm =>
      simp [elaborateConditionalReturnBody?,
        elaborateLocalExpression?_complete resolution lowered typing, thenArm.complete, elseArm.complete]

theorem elaborateConditionalReturnBody?_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type)) :
    ConditionalReturnBodyElaborates table context body core type := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => simp only [elaborateConditionalReturnBody?, reduceCtorEq] at accepted
  | cons statement rest =>
      cases rest with
      | cons next rest => simp only [elaborateConditionalReturnBody?, reduceCtorEq] at accepted
      | nil =>
          rcases statement with ⟨ifSpan, payload⟩
          cases payload <;> try simp only [elaborateConditionalReturnBody?, reduceCtorEq] at accepted
          case ifThen condition thenBody optionalElse =>
            cases optionalElse with
            | none => simp only [reduceCtorEq] at accepted
            | some elseBody =>
                obtain ⟨conditionCore, thenCore, elseCore, conditionAccepted,
                  thenAccepted, elseAccepted, rfl⟩ :=
                  elaborateConditionalReturnBody?_children (blockSpan := blockSpan) (ifSpan := ifSpan) accepted
                obtain ⟨resolved, resolution, lowered, typing⟩ :=
                  elaborateLocalExpression?_sound conditionAccepted
                exact .intro resolution lowered typing
                  (elaborateReturnBody?_elaborates thenAccepted) (elaborateReturnBody?_elaborates elseAccepted)

theorem elaborateConditionalReturnBody?_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateConditionalReturnBody? table context body = some (core, type) ↔
      ConditionalReturnBodyElaborates table context body core type :=
  ⟨elaborateConditionalReturnBody?_elaborates, ConditionalReturnBodyElaborates.complete⟩

theorem ConditionalReturnBodyElaborates.hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalReturnBodyElaborates table context body core type) :
    ConditionalReturnBodyHasType table context body type := by
  cases elaboration with
  | intro resolution _ typing thenArm elseArm =>
      exact .intro (resolution.reflects_type typing) thenArm.hasType elseArm.hasType

theorem ConditionalReturnBodyHasType.elaborates_exact {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : ConditionalReturnBodyHasType table context body type) :
    ∃ core, ConditionalReturnBodyElaborates table context body core type := by
  cases typing with
  | intro conditionTyping thenTyping elseTyping =>
      obtain ⟨resolved, resolution, typed⟩ := conditionTyping.resolves
      obtain ⟨conditionCore, lowered, _⟩ := typed.lowers
      obtain ⟨thenCore, thenArm⟩ := thenTyping.elaborates_exact
      obtain ⟨elseCore, elseArm⟩ := elseTyping.elaborates_exact
      exact ⟨.ifE conditionCore thenCore elseCore, .intro resolution lowered typed thenArm elseArm⟩

theorem ConditionalReturnBodyHasType.elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : ConditionalReturnBodyHasType table context body type) :
    ∃ core, elaborateConditionalReturnBody? table context body = some (core, type) := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact ⟨core, elaboration.complete⟩

theorem elaborateConditionalReturnBody?_sound {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type)) :
    ConditionalReturnBodyHasType table context body type :=
  (elaborateConditionalReturnBody?_elaborates accepted).hasType

theorem conditionalReturnBodyHasType_iff_elaborates {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} : ConditionalReturnBodyHasType table context body type ↔
      ∃ core, elaborateConditionalReturnBody? table context body = some (core, type) :=
  ⟨ConditionalReturnBodyHasType.elaborates, fun ⟨_, accepted⟩ => elaborateConditionalReturnBody?_sound accepted⟩

theorem elaborateConditionalReturnBody?_core_hasType {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  cases elaborateConditionalReturnBody?_elaborates accepted with
  | intro _ lowered typing thenArm elseArm =>
      exact .ifE (lowered.preserves_type typing)
        (elaborateReturnBody?_core_hasType thenArm.complete) (elaborateReturnBody?_core_hasType elseArm.complete)

theorem ConditionalReturnBodyElaborates.result_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : ConditionalReturnBodyElaborates table context body leftCore leftType)
    (right : ConditionalReturnBodyElaborates table context body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

theorem ConditionalReturnBodyHasType.type_unique {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {left right : Core.Ty}
    (first : ConditionalReturnBodyHasType table context body left)
    (second : ConditionalReturnBodyHasType table context body right) : left = right := by
  cases first with
  | intro _ thenTyping _ =>
      cases second with
      | intro _ otherTyping _ => exact thenTyping.type_unique otherTyping

theorem elaborateConditionalReturnBody?_eq_none_iff {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} : elaborateConditionalReturnBody? table context body = none ↔
      ¬ ∃ type, ConditionalReturnBodyHasType table context body type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := typing.elaborates
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateConditionalReturnBody? table context body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, elaborateConditionalReturnBody?_sound result⟩)

/-- Only the enclosing block and conditional-statement ranges change; the
original condition and both original arm trees are retained. -/
theorem elaborateConditionalReturnBody?_spans (table : LocalNameTable) (context : Resolved.Context)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block)
    (blockSpan ifSpan otherBlockSpan otherIfSpan : Syntax.SourceSpan) :
    elaborateConditionalReturnBody? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =
      elaborateConditionalReturnBody? table context
        ⟨otherBlockSpan, [⟨otherIfSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ := rfl

end Solcore.Frontend
