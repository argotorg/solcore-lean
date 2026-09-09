import Solcore.Frontend.ComputationReturnTreeCheckingProperties
import Solcore.Frontend.StructuralTypeProperties

/-! Shared checking uses only the child's exact checker correspondence.
Original tails, branches and fresh scopes stay independent of runtime laws. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}

private theorem binding_children
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateComputationReturnTree? checkChild types owner inputs
      ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ = some (core, type)) :
    ∃ declaredType initializerCore tailCore,
      name.value ∉ inputs.names.map Prod.fst ∧ interpretStructuralType? types annotation = some declaredType ∧
      checkChild inputs.names inputs.context initializer = some (initializerCore, declaredType) ∧
      elaborateComputationReturnTree? checkChild types owner (inputs.bindFresh owner name.value declaredType)
        ⟨blockSpan, rest⟩ = some (tailCore, type) ∧ core = .letE initializerCore tailCore := by
  rw [elaborateComputationReturnTree?] at accepted
  split at accepted
  next unused =>
    simp only [bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨declaredType, meaning, ⟨initializerCore, initializerType⟩, initializerAccepted, remaining⟩ := accepted
    split at remaining
    next sameType =>
      change initializerType = declaredType at sameType; subst initializerType
      simp only [Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at remaining
      obtain ⟨⟨tailCore, returnType⟩, tailAccepted, rfl, rfl⟩ := remaining
      exact ⟨declaredType, initializerCore, tailCore, unused, meaning, initializerAccepted, tailAccepted, rfl⟩
    next different => cases remaining
  next used => cases accepted

private theorem conditional_children
    {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateComputationReturnTree? checkChild types owner inputs
      ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ = some (core, type)) :
    ∃ conditionCore thenCore elseCore,
      checkChild inputs.names inputs.context condition = some (conditionCore, .bool) ∧
      elaborateComputationReturnTree? checkChild types owner inputs thenBody = some (thenCore, type) ∧
      elaborateComputationReturnTree? checkChild types owner inputs elseBody = some (elseCore, type) ∧
      core = .ifE conditionCore thenCore elseCore := by
  rw [elaborateComputationReturnTree?] at accepted
  simp only [bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨conditionCore, conditionType⟩, conditionAccepted, remaining⟩ := accepted
  split at remaining
  next conditionBool =>
    change conditionType = .bool at conditionBool; subst conditionType
    simp only [Option.bind_eq_some_iff] at remaining
    obtain ⟨⟨thenCore, thenType⟩, thenAccepted, ⟨elseCore, elseType⟩, elseAccepted, result⟩ := remaining
    split at result
    next sameType =>
      change thenType = elseType at sameType; subst elseType
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at result
      rcases result with ⟨rfl, rfl⟩
      exact ⟨conditionCore, thenCore, elseCore, conditionAccepted, thenAccepted, elseAccepted, rfl⟩
    next different => cases result
  next notBool => cases remaining

private theorem complete
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type) :
    elaborateComputationReturnTree? checkChild types owner inputs body = some (core, type) := by
  induction elaboration with
  | bare => simp only [elaborateComputationReturnTree?]
  | expression child => simpa only [elaborateComputationReturnTree?] using childCorrect.mpr child
  | block _ ih => simpa only [elaborateComputationReturnTree?] using ih
  | binding meaning unused initializer _ ih =>
      rw [elaborateComputationReturnTree?]
      simp [unused, meaning.complete, childCorrect.mpr initializer, ih]
  | inferred unused initializer _ ih =>
      rw [elaborateComputationReturnTree?]
      simp [unused, childCorrect.mpr initializer, ih]
  | discard expression _ ih =>
      rw [elaborateComputationReturnTree?]
      simp only [childCorrect.mpr expression, ih, bind, Option.bind_some, pure, Pure.pure]
  | conditional condition _ _ thenIH elseIH =>
      rw [elaborateComputationReturnTree?]
      simp [childCorrect.mpr condition, thenIH, elseIH]
  | wordMatch scrutinee ordered patterns compatible _ defaultOrdered _ lowered branchIH defaultIH =>
      exact ComputationReturnTreeChecking.match_iff.mpr
        ⟨_, _, childCorrect.mpr scrutinee, _, _, _, ordered, patterns, compatible, branchIH, defaultOrdered, defaultIH, lowered, rfl⟩

private theorem sound
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateComputationReturnTree? checkChild types owner inputs body = some (core, type)) :
    ComputationReturnTreeElaborates ChildElab types owner inputs body core type := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
              case returnStmt returned =>
                cases rest with
                | nil =>
                    cases returned with
                    | none =>
                        simp only [elaborateComputationReturnTree?, Option.some.injEq, Prod.mk.injEq] at accepted
                        rcases accepted with ⟨rfl, rfl⟩
                        exact .bare
                    | some source => exact .expression (childCorrect.mp
                        (by simpa only [elaborateComputationReturnTree?] using accepted))
                | cons _ _ => simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
              case block statements =>
                cases rest with
                | nil => exact .block (sound childCorrect
                    (by simpa only [elaborateComputationReturnTree?] using accepted))
                | cons _ _ => simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
              case letDecl name optionalType optionalInitializer =>
                cases optionalInitializer with
                | none => cases optionalType <;> simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
                | some initializer =>
                    cases optionalType with
                    | none =>
                        rw [elaborateComputationReturnTree?] at accepted
                        split at accepted
                        next unused =>
                          simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at accepted
                          obtain ⟨⟨initializerCore, initializerType⟩, initializerAccepted,
                            ⟨tailCore, returnType⟩, tailAccepted, rfl, rfl⟩ := accepted
                          exact .inferred unused (childCorrect.mp initializerAccepted) (sound childCorrect tailAccepted)
                        next used => cases accepted
                    | some annotation =>
                        obtain ⟨declaredType, initializerCore, tailCore, unused, meaning,
                          initializerAccepted, tailAccepted, rfl⟩ := binding_children accepted
                        exact .binding (interpretStructuralType?_sound meaning) unused
                          (childCorrect.mp initializerAccepted) (sound childCorrect tailAccepted)
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
                | nil =>
                    cases optionalElse with
                    | none => simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
                    | some elseBody =>
                        obtain ⟨conditionCore, thenCore, elseCore, conditionAccepted,
                          thenAccepted, elseAccepted, rfl⟩ := conditional_children accepted
                        exact .conditional (childCorrect.mp conditionAccepted)
                          (sound childCorrect thenAccepted) (sound childCorrect elseAccepted)
              case expression source trailingSemicolon =>
                cases trailingSemicolon with
                | false => simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted
                | true =>
                    rw [elaborateComputationReturnTree?] at accepted
                    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at accepted
                    obtain ⟨⟨expressionCore, expressionType⟩, expressionAccepted,
                      ⟨tailCore, returnType⟩, tailAccepted, rfl, rfl⟩ := accepted
                    exact .discard (childCorrect.mp expressionAccepted) (sound childCorrect tailAccepted)
              case matchWith scrutinees arms =>
                rcases scrutineeShape : scrutinees with ⟨scrutineeSpan, elements⟩
                rcases elementsShape : elements with ⟨scrutinee, scrutineeRest⟩
                rcases armsShape : arms with ⟨armsSpan, armValues⟩
                rcases valuesShape : armValues with ⟨cases, optionalDefault⟩
                rw [scrutineeShape, elementsShape, armsShape, valuesShape] at accepted
                cases rest <;> cases scrutineeRest <;>
                  try (solve | simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted)
                obtain ⟨scrutineeCore, scrutineeType, scrutineeAccepted, bodyCore, entries, defaults, ordered, patterns,
                  compatible, branches, defaultOrdered, defaultBranches, lowered, rfl⟩ :=
                    ComputationReturnTreeChecking.match_iff.mp accepted
                refine .wordMatch (childCorrect.mp scrutineeAccepted) ordered patterns compatible ?_ defaultOrdered ?_ lowered
                · intro entry member
                  have originalMember : entry.1 ∈ cases := ordered ▸ List.mem_map.mpr ⟨entry, member, rfl⟩
                  exact sound childCorrect (branches entry member)
                · intro entry member
                  have originalDefault : optionalDefault = some entry.1 := by
                    rw [← defaultOrdered, Option.mem_toList.mp member]; rfl
                  exact sound childCorrect (defaultBranches entry member)
termination_by sizeOf body
decreasing_by
  all_goals simp_all
  all_goals try omega
  have member := List.sizeOf_lt_of_mem originalMember
  have child : sizeOf entry.1.value.body < sizeOf entry.1 := by
    rcases entry.1 with ⟨span, ⟨pattern, body⟩⟩; simp; omega
  omega

theorem elaborateComputationReturnTree?_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateComputationReturnTree? checkChild types owner inputs body = some (core, type) ↔
      ComputationReturnTreeElaborates ChildElab types owner inputs body core type :=
  ⟨sound childCorrect, complete childCorrect⟩

end Solcore.Frontend
