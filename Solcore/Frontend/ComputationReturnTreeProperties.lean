import Solcore.Frontend.ComputationReturnTree
import Solcore.Frontend.StructuralTypeProperties
import Solcore.Frontend.WordLiteralProperties

/-! Shared checking uses only the child's exact checker correspondence.
Original tails, branches and fresh scopes stay independent of runtime laws. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}

private def check_arm (check : Syntax.Block → Option (Core.Expr × Core.Ty)) (type : Core.Ty)
    (arm : Syntax.MatchCase) : Option (Option Core.Word × Core.Expr) := do
  let tag ← match arm.value.pattern.value with
    | .literal literal => (interpretWordLiteral? literal).map some
    | .wildcard _ => some none
    | _ => none
  let branch ← check arm.value.body
  if branch.2 = type then return (tag, branch.1) else none

private theorem check_arm_map {check : Syntax.Block → Option (Core.Expr × Core.Ty)}
    {type : Core.Ty} {arm : Syntax.MatchCase} :
    (check_arm check type arm).map (arm, ·) = (do
      let tag ← match arm.value.pattern.value with
        | .literal literal => (interpretWordLiteral? literal).map some
        | .wildcard _ => some none
        | _ => none
      let branch ← check arm.value.body
      if branch.2 = type then return (arm, tag, branch.1) else none) := by
  cases shape : arm.value.pattern.value <;>
    simp [check_arm, shape, bind, Option.map_bind, Function.comp_def, apply_ite]

private theorem check_arm_iff {check : Syntax.Block → Option (Core.Expr × Core.Ty)}
    {type : Core.Ty} {arm : Syntax.MatchCase} {tag : Option Core.Word} {core : Core.Expr} :
    check_arm check type arm = some (tag, core) ↔
      (match tag with
        | none => ∃ marker, arm.value.pattern.value = .wildcard marker
        | some word => WordMatchPatternDenotes arm.value.pattern word) ∧
      check arm.value.body = some (core, type) := by
  have branch (found : Option Core.Word) :
      ((check arm.value.body).bind fun branch =>
        if branch.2 = type then some (found, branch.1) else none) = some (tag, core) ↔
      found = tag ∧ check arm.value.body = some (core, type) := by
    simp only [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨⟨branchCore, branchType⟩, accepted, result⟩
      split at result <;> simp_all [Option.some.injEq, Prod.mk.injEq]
    · rintro ⟨rfl, accepted⟩
      exact ⟨(core, type), accepted, by simp⟩
  cases shape : arm.value.pattern.value <;> cases tag <;>
    simp [check_arm, shape, WordMatchPatternDenotes, bind, branch,
      Option.bind_eq_some_iff, Option.map_eq_some_iff, interpretWordLiteral?_iff]
  constructor
  · rintro ⟨_, ⟨word, meaning, rfl⟩, same, accepted⟩
    cases same; exact ⟨meaning, accepted⟩
  · rintro ⟨meaning, accepted⟩
    exact ⟨_, ⟨_, meaning, rfl⟩, rfl, accepted⟩

private theorem entries_check_iff {α β : Type} {check : α → Option β}
    {cases : List α} {entries : List (α × β)} :
    cases.attach.mapM (fun arm => (check arm.val).map (arm.val, ·)) = some entries ↔
      entries.map Prod.fst = cases ∧ ∀ entry ∈ entries, check entry.1 = some entry.2 := by
  change cases.attach.mapM ((fun arm => (check arm).map (arm, ·)) ∘ Subtype.val) = some entries ↔ _
  rw [← List.mapM_map, List.attach_map_subtype_val]
  induction cases generalizing entries with
  | nil => cases entries <;> simp
  | cons arm rest ih =>
      cases entries with
      | nil => simp [List.mapM_cons, bind, Option.bind_eq_some_iff]
      | cons entry entries =>
          simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.map_eq_some_iff,
            pure, Option.some.injEq, List.cons.injEq, List.map_cons,
            List.mem_cons, forall_eq_or_imp, ih]
          constructor
          · rintro ⟨_, ⟨value, accepted, rfl⟩, _, ⟨ordered, checked⟩, rfl, rfl⟩
            exact ⟨⟨rfl, ordered⟩, accepted, checked⟩
          · rintro ⟨⟨rfl, ordered⟩, accepted, checked⟩
            exact ⟨entry, ⟨entry.2, accepted, by cases entry; rfl⟩, entries,
              ⟨ordered, checked⟩, rfl, rfl⟩

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
  | @wordMatch inputs _ _ _ _ _ cases _ _ _ type entries scrutinee ordered patterns _ _ branchIH defaultIH =>
      have checked := entries_check_iff.mpr ⟨ordered,
        fun entry member => check_arm_iff.mpr ⟨patterns entry member, branchIH entry member⟩⟩
      rw [elaborateComputationReturnTree?]
      simp only [childCorrect.mpr scrutinee, bind, Option.bind_some, ite_true, defaultIH]
      simp only [check_arm_map, bind] at checked
      exact Option.bind_eq_some_iff.mpr ⟨entries, checked, rfl⟩

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
                cases rest <;> cases scrutineeRest <;> cases optionalDefault <;>
                  try (solve | simp only [elaborateComputationReturnTree?, reduceCtorEq] at accepted)
                rename_i defaultBody
                rw [elaborateComputationReturnTree?] at accepted
                simp only [bind, Option.bind_eq_some_iff] at accepted
                obtain ⟨⟨scrutineeCore, scrutineeType⟩, scrutineeAccepted, remaining⟩ := accepted
                split at remaining
                next isWord =>
                  change scrutineeType = .word at isWord
                  subst scrutineeType
                  simp only [Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at remaining
                  obtain ⟨⟨defaultCore, returnType⟩, defaultAccepted, entries, entriesAccepted, rfl, rfl⟩ := remaining
                  have checked : entries.map Prod.fst = cases ∧ ∀ entry ∈ entries,
                      check_arm (elaborateComputationReturnTree? checkChild types owner inputs) returnType entry.1 =
                        some entry.2 := entries_check_iff.mp (by simp only [check_arm_map, bind]; exact entriesAccepted)
                  refine .wordMatch (childCorrect.mp scrutineeAccepted) checked.1
                    (fun entry member => (check_arm_iff.mp (checked.2 entry member)).1) ?_
                    (sound childCorrect defaultAccepted)
                  intro entry member
                  have originalMember : entry.1 ∈ cases := checked.1 ▸ List.mem_map.mpr ⟨entry, member, rfl⟩
                  exact sound childCorrect (check_arm_iff.mp (checked.2 entry member)).2
                next notWord => cases remaining
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
