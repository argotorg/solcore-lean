import Solcore.Frontend.LocalComputationReturnTree
import Solcore.Frontend.LocalComputationProperties
import Solcore.Frontend.StructuralTypeProperties

/-! Whole mixed-body checking is equivalent to independent exact provenance.
The recursive calls retain the original tail and branch syntax and input scope. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem binding_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalComputationReturnTree? types owner inputs
      ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ = some (core, type)) :
    ∃ declaredType initializerCore tailCore,
      name.value ∉ inputs.names.map Prod.fst ∧ interpretStructuralType? types annotation = some declaredType ∧
      elaborateLocalComputation? inputs.names inputs.context initializer = some (initializerCore, declaredType) ∧
      elaborateLocalComputationReturnTree? types owner (inputs.bindFresh owner name.value declaredType)
        ⟨blockSpan, rest⟩ = some (tailCore, type) ∧ core = .letE initializerCore tailCore := by
  rw [elaborateLocalComputationReturnTree?] at accepted
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

private theorem inferred_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {rest : List Syntax.Statement} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalComputationReturnTree? types owner inputs
      ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ = some (core, type)) :
    ∃ initializerType initializerCore tailCore,
      name.value ∉ inputs.names.map Prod.fst ∧
      elaborateLocalComputation? inputs.names inputs.context initializer = some (initializerCore, initializerType) ∧
      elaborateLocalComputationReturnTree? types owner (inputs.bindFresh owner name.value initializerType)
        ⟨blockSpan, rest⟩ = some (tailCore, type) ∧ core = .letE initializerCore tailCore := by
  rw [elaborateLocalComputationReturnTree?] at accepted
  split at accepted
  next unused =>
    simp only [bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨⟨initializerCore, initializerType⟩, initializerAccepted,
      ⟨tailCore, returnType⟩, tailAccepted, result⟩ := accepted
    change some (.letE initializerCore tailCore, returnType) = some (core, type) at result
    simp only [Option.some.injEq, Prod.mk.injEq] at result
    rcases result with ⟨rfl, rfl⟩
    exact ⟨initializerType, initializerCore, tailCore, unused, initializerAccepted, tailAccepted, rfl⟩
  next used => cases accepted

private theorem conditional_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalComputationReturnTree? types owner inputs
      ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, type)) :
    ∃ conditionCore thenCore elseCore,
      elaborateLocalComputation? inputs.names inputs.context condition = some (conditionCore, .bool) ∧
      elaborateLocalComputationReturnTree? types owner inputs thenBody = some (thenCore, type) ∧
      elaborateLocalComputationReturnTree? types owner inputs elseBody = some (elseCore, type) ∧
      core = .ifE conditionCore thenCore elseCore := by
  rw [elaborateLocalComputationReturnTree?] at accepted
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

private theorem discard_children
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {blockSpan statementSpan : Syntax.SourceSpan} {source : Syntax.Expr}
    {rest : List Syntax.Statement} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalComputationReturnTree? types owner inputs
      ⟨blockSpan, ⟨statementSpan, .expression source true⟩ :: rest⟩ = some (core, type)) :
    ∃ expressionType expressionCore tailCore,
      elaborateLocalComputation? inputs.names inputs.context source = some (expressionCore, expressionType) ∧
      elaborateLocalComputationReturnTree? types owner inputs ⟨blockSpan, rest⟩ = some (tailCore, type) ∧
      core = .letE expressionCore (tailCore.weakenAt 0) := by
  rw [elaborateLocalComputationReturnTree?] at accepted
  simp only [bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨expressionCore, expressionType⟩, expressionAccepted,
    ⟨tailCore, returnType⟩, tailAccepted, result⟩ := accepted
  change some (.letE expressionCore (tailCore.weakenAt 0), returnType) = some (core, type) at result
  simp only [Option.some.injEq, Prod.mk.injEq] at result
  rcases result with ⟨rfl, rfl⟩
  exact ⟨expressionType, expressionCore, tailCore, expressionAccepted, tailAccepted, rfl⟩

private theorem complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type) :
    elaborateLocalComputationReturnTree? types owner inputs body = some (core, type) := by
  induction elaboration with
  | bare => simp only [elaborateLocalComputationReturnTree?]
  | expression child =>
      simpa only [elaborateLocalComputationReturnTree?] using elaborateLocalComputation?_iff.mpr child
  | block _ ih => simpa only [elaborateLocalComputationReturnTree?] using ih
  | binding meaning unused initializer _ ih =>
      rw [elaborateLocalComputationReturnTree?]
      simp only [if_pos unused, meaning.complete, elaborateLocalComputation?_iff.mpr initializer,
        ih, bind, Option.bind_some, ite_true, pure, Pure.pure]
  | inferred unused initializer _ ih =>
      rw [elaborateLocalComputationReturnTree?]
      simp only [if_pos unused, elaborateLocalComputation?_iff.mpr initializer,
        ih, bind, Option.bind_some, pure, Pure.pure]
  | discard expression _ ih =>
      rw [elaborateLocalComputationReturnTree?]
      simp only [elaborateLocalComputation?_iff.mpr expression, ih, bind, Option.bind_some, pure, Pure.pure]
  | conditional condition _ _ thenIH elseIH =>
      rw [elaborateLocalComputationReturnTree?]
      simp [elaborateLocalComputation?_iff.mpr condition, thenIH, elseIH]

private theorem sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalComputationReturnTree? types owner inputs body = some (core, type)) :
    LocalComputationReturnTreeElaborates types owner inputs body core type := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
              case returnStmt returned =>
                cases rest with
                | nil =>
                    cases returned with
                    | none =>
                        simp only [elaborateLocalComputationReturnTree?, Option.some.injEq, Prod.mk.injEq] at accepted
                        rcases accepted with ⟨rfl, rfl⟩
                        exact .bare
                    | some source => exact .expression (elaborateLocalComputation?_iff.mp
                        (by simpa only [elaborateLocalComputationReturnTree?] using accepted))
                | cons _ _ => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
              case block statements =>
                cases rest with
                | nil => exact .block (sound
                    (by simpa only [elaborateLocalComputationReturnTree?] using accepted))
                | cons _ _ => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
              case letDecl name optionalType optionalInitializer =>
                cases optionalType with
                | none =>
                    cases optionalInitializer with
                    | none => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
                    | some initializer =>
                        obtain ⟨initializerType, initializerCore, tailCore, unused,
                          initializerAccepted, tailAccepted, rfl⟩ := inferred_children accepted
                        exact .inferred unused (elaborateLocalComputation?_iff.mp initializerAccepted)
                          (sound tailAccepted)
                | some annotation =>
                    cases optionalInitializer with
                    | none => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
                    | some initializer =>
                        obtain ⟨declaredType, initializerCore, tailCore, unused, meaning,
                          initializerAccepted, tailAccepted, rfl⟩ := binding_children accepted
                        exact .binding (interpretStructuralType?_sound meaning) unused
                          (elaborateLocalComputation?_iff.mp initializerAccepted) (sound tailAccepted)
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
                | nil =>
                    cases optionalElse with
                    | none => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
                    | some elseBody =>
                        obtain ⟨conditionCore, thenCore, elseCore, conditionAccepted,
                          thenAccepted, elseAccepted, rfl⟩ := conditional_children accepted
                        exact .conditional (elaborateLocalComputation?_iff.mp conditionAccepted)
                          (sound thenAccepted) (sound elseAccepted)
              case expression source trailingSemicolon =>
                cases trailingSemicolon with
                | false => simp only [elaborateLocalComputationReturnTree?, reduceCtorEq] at accepted
                | true =>
                    obtain ⟨expressionType, expressionCore, tailCore,
                      expressionAccepted, tailAccepted, rfl⟩ := discard_children accepted
                    exact .discard (elaborateLocalComputation?_iff.mp expressionAccepted) (sound tailAccepted)
termination_by sizeOf body

theorem elaborateLocalComputationReturnTree?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalComputationReturnTree? types owner inputs body = some (core, type) ↔
      LocalComputationReturnTreeElaborates types owner inputs body core type :=
  ⟨sound, complete⟩

end Solcore.Frontend
