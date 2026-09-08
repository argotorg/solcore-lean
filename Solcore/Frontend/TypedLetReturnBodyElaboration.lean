import Solcore.Frontend.TypedLetReturnBody

/-! Exact whole-source provenance characterizes the total typed-prefix checker.
The initializer keeps the old scope and the remaining source keeps its order. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateTypedLetReturnBody?_binding_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs
      ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ =
        some (core, type)) :
    ∃ declaredType initializerCore tailCore,
      name.value ∉ inputs.names.map Prod.fst ∧
      interpretTypeName? types annotation = some declaredType ∧
      elaborateLocalExpression? inputs.names inputs.context initializer = some (initializerCore, declaredType) ∧
      elaborateTypedLetReturnBody? types owner (inputs.bindFresh owner name.value declaredType)
        ⟨blockSpan, rest⟩ = some (tailCore, type) ∧ core = .letE initializerCore tailCore := by
  rw [elaborateTypedLetReturnBody?] at accepted
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

theorem TypedLetReturnBodyElaborates.complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnBodyElaborates types owner inputs body core type) :
    elaborateTypedLetReturnBody? types owner inputs body = some (core, type) := by
  induction elaboration with
  | terminal child =>
      have accepted := child.complete
      cases child with
      | single returned => cases returned <;> simpa only [elaborateTypedLetReturnBody?] using accepted
      | conditional => simpa only [elaborateTypedLetReturnBody?] using accepted
  | binding meaning unused resolution lowered typing _ ih =>
      have initializerAccepted := elaborateLocalExpression?_complete resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
      rw [elaborateTypedLetReturnBody?]
      simp only [if_pos unused, meaning.complete, initializerAccepted, ih, bind,
        Option.bind_some, ite_true, pure, Pure.pure]

theorem elaborateTypedLetReturnBody?_elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type)) :
    TypedLetReturnBodyElaborates types owner inputs body core type := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => exact .terminal (elaborateTerminalReturnTree?_elaborates
          (by simpa only [elaborateTypedLetReturnBody?] using accepted))
      | cons statement rest =>
          cases statement with
          | mk letSpan payload =>
              cases payload <;> try exact .terminal (elaborateTerminalReturnTree?_elaborates
                (by simpa only [elaborateTypedLetReturnBody?] using accepted))
              case letDecl name optionalType optionalInitializer =>
                cases optionalType with
                | none => exact .terminal (elaborateTerminalReturnTree?_elaborates
                    (by simpa only [elaborateTypedLetReturnBody?] using accepted))
                | some annotation =>
                    cases optionalInitializer with
                    | none => exact .terminal (elaborateTerminalReturnTree?_elaborates
                        (by simpa only [elaborateTypedLetReturnBody?] using accepted))
                    | some initializer =>
                        obtain ⟨declaredType, initializerCore, tailCore, unused, meaning,
                          initializerAccepted, tailAccepted, rfl⟩ :=
                          elaborateTypedLetReturnBody?_binding_children accepted
                        obtain ⟨resolved, resolution, lowered, typing⟩ :=
                          elaborateLocalExpression?_sound initializerAccepted
                        exact .binding (interpretTypeName?_sound meaning) unused resolution
                          (by simpa only [LocalTypeInputs.context_ids] using lowered) typing
                          (elaborateTypedLetReturnBody?_elaborates tailAccepted)
termination_by body.value.length

theorem elaborateTypedLetReturnBody?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateTypedLetReturnBody? types owner inputs body = some (core, type) ↔
      TypedLetReturnBodyElaborates types owner inputs body core type :=
  ⟨elaborateTypedLetReturnBody?_elaborates, TypedLetReturnBodyElaborates.complete⟩

end Solcore.Frontend
