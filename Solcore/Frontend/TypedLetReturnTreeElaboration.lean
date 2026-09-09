import Solcore.Frontend.TypedLetReturnTree

/-! Exact independent provenance characterizes recursive typed let/return trees.
Child decomposition retains both source arms and each old-scope initializer. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTypedLetReturnTree?_single (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) :
    elaborateTypedLetReturnTree? types owner inputs ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =
      elaborateReturnBody? inputs.names inputs.context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ := by
  rw [elaborateTypedLetReturnTree?]

theorem elaborateTypedLetReturnTree?_binding_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs
      ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ = some (core, type)) :
    ∃ declaredType initializerCore tailCore,
      name.value ∉ inputs.names.map Prod.fst ∧ interpretStructuralType? types annotation = some declaredType ∧
      elaborateLocalExpression? inputs.names inputs.context initializer = some (initializerCore, declaredType) ∧
      elaborateTypedLetReturnTree? types owner (inputs.bindFresh owner name.value declaredType)
        ⟨blockSpan, rest⟩ = some (tailCore, type) ∧ core = .letE initializerCore tailCore := by
  rw [elaborateTypedLetReturnTree?] at accepted
  split at accepted
  next unused =>
    simp only [bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨declaredType, meaning, ⟨initializerCore, initializerType⟩, initializerAccepted, remaining⟩ := accepted
    split at remaining
    next sameType =>
      change initializerType = declaredType at sameType
      subst initializerType
      simp only [Option.bind_eq_some_iff] at remaining
      obtain ⟨⟨tailCore, returnType⟩, tailAccepted, result⟩ := remaining
      change some (.letE initializerCore tailCore, returnType) = some (core, type) at result
      simp only [Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨declaredType, initializerCore, tailCore, unused, meaning, initializerAccepted, tailAccepted, rfl⟩
    next different => cases remaining
  next used => cases accepted

theorem elaborateTypedLetReturnTree?_conditional_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs
      ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, type)) :
    ∃ conditionCore thenCore elseCore,
      elaborateLocalExpression? inputs.names inputs.context condition = some (conditionCore, .bool) ∧
      elaborateTypedLetReturnTree? types owner inputs thenBody = some (thenCore, type) ∧
      elaborateTypedLetReturnTree? types owner inputs elseBody = some (elseCore, type) ∧
      core = .ifE conditionCore thenCore elseCore := by
  rw [elaborateTypedLetReturnTree?] at accepted
  simp only [bind, Option.bind_eq_some_iff] at accepted
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

theorem TypedLetReturnTreeElaborates.complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates types owner inputs body core type) :
    elaborateTypedLetReturnTree? types owner inputs body = some (core, type) := by
  induction elaboration with
  | single child =>
      have accepted := child.complete
      cases child <;> simpa only [elaborateTypedLetReturnTree?] using accepted
  | binding meaning unused resolution lowered typing _ ih =>
      have initializerAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      rw [elaborateTypedLetReturnTree?]
      simp only [if_pos unused, meaning.complete, initializerAccepted, ih, bind,
        Option.bind_some, ite_true, pure, Pure.pure]
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      have conditionAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      rw [elaborateTypedLetReturnTree?]
      simp [conditionAccepted, thenIH, elseIH]

theorem elaborateTypedLetReturnTree?_elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type)) :
    TypedLetReturnTreeElaborates types owner inputs body core type := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
              case returnStmt returned =>
                cases rest with
                | nil => exact .single (elaborateReturnBody?_elaborates
                    (by simpa only [elaborateTypedLetReturnTree?_single] using accepted))
                | cons _ _ => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
              case letDecl name optionalType optionalInitializer =>
                cases optionalType with
                | none => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
                | some annotation =>
                    cases optionalInitializer with
                    | none => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
                    | some initializer =>
                        obtain ⟨declaredType, initializerCore, tailCore, unused, meaning,
                          initializerAccepted, tailAccepted, rfl⟩ :=
                          elaborateTypedLetReturnTree?_binding_children accepted
                        obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound initializerAccepted
                        exact .binding (interpretStructuralType?_sound meaning) unused resolution
                          (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
                          (elaborateTypedLetReturnTree?_elaborates tailAccepted)
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
                | nil =>
                    cases optionalElse with
                    | none => simp only [elaborateTypedLetReturnTree?, reduceCtorEq] at accepted
                    | some elseBody =>
                        obtain ⟨conditionCore, thenCore, elseCore, conditionAccepted,
                          thenAccepted, elseAccepted, rfl⟩ := elaborateTypedLetReturnTree?_conditional_children accepted
                        obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound conditionAccepted
                        exact .conditional resolution
                          (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
                          (elaborateTypedLetReturnTree?_elaborates thenAccepted)
                          (elaborateTypedLetReturnTree?_elaborates elseAccepted)
termination_by sizeOf body

theorem elaborateTypedLetReturnTree?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateTypedLetReturnTree? types owner inputs body = some (core, type) ↔
      TypedLetReturnTreeElaborates types owner inputs body core type :=
  ⟨elaborateTypedLetReturnTree?_elaborates, TypedLetReturnTreeElaborates.complete⟩

end Solcore.Frontend
