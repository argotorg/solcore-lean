import Solcore.Frontend.ComputationBindingScope

/-! Exact source-only name protection, including rejection and restriction to
fewer protected names. No child checker, typing or runtime law is assumed. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem preserves_tail {names : List String} {span : Syntax.SourceSpan}
    {statement : Syntax.Statement} {rest : List Syntax.Statement}
    (accepted : computationBlockPreservesNames names ⟨span, statement :: rest⟩ = true) :
    computationBlockPreservesNames names ⟨span, rest⟩ = true := by
  rcases statement with ⟨statementSpan, payload⟩
  cases payload with
  | ifThen condition thenBody elseBody =>
      cases elseBody <;> simp_all only [computationBlockPreservesNames, Bool.and_eq_true]
  | _ => simp_all only [computationBlockPreservesNames, Bool.and_eq_true]

private theorem sound {names : List String} {body : Syntax.Block}
    (accepted : computationBlockPreservesNames names body = true) :
    ComputationNamesProtected names body := by
  intro name exposed
  induction exposed with
  | binding spelling =>
      subst name
      simp only [computationBlockPreservesNames, Bool.and_eq_true, decide_eq_true_eq] at accepted
      exact accepted.1
  | tail exposed ih => exact ih (preserves_tail accepted)
  | @thenBranch blockSpan ifSpan condition thenBody elseBody rest exposed ih =>
      cases elseBody <;> simp only [computationBlockPreservesNames, Bool.and_eq_true] at accepted
      · exact ih accepted.1
      · exact ih accepted.1.1
  | elseBranch exposed ih =>
      simp only [computationBlockPreservesNames, Bool.and_eq_true] at accepted
      exact ih accepted.1.2

private theorem complete {names : List String} {body : Syntax.Block}
    (protection : ComputationNamesProtected names body) :
    computationBlockPreservesNames names body = true := by
  match body with
  | ⟨_, []⟩ => simp only [computationBlockPreservesNames]
  | ⟨span, statement :: rest⟩ =>
      have tail : ComputationNamesProtected names ⟨span, rest⟩ :=
        fun name exposed => protection name (.tail exposed)
      cases statementShape : statement with
      | mk statementSpan payload =>
          cases payloadShape : payload with
          | letDecl identifier annotation initializer =>
              simp only [statementShape, payloadShape] at protection
              simp only [computationBlockPreservesNames, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨protection identifier.value (.binding rfl), complete tail⟩
          | ifThen condition thenBody elseBody =>
              simp only [statementShape, payloadShape] at protection
              have yes : ComputationNamesProtected names thenBody :=
                fun name exposed => protection name (.thenBranch exposed)
              cases elseBody with
              | none =>
                  simp only [computationBlockPreservesNames, Bool.and_eq_true]
                  exact ⟨complete yes, complete tail⟩
              | some noBody =>
                  have no : ComputationNamesProtected names noBody :=
                    fun name exposed => protection name (.elseBranch exposed)
                  simp only [computationBlockPreservesNames, Bool.and_eq_true]
                  exact ⟨⟨complete yes, complete no⟩, complete tail⟩
          | _ => simpa only [computationBlockPreservesNames] using complete (body := ⟨span, rest⟩) tail
termination_by sizeOf body
decreasing_by all_goals simp_wf; all_goals simp_all; all_goals omega

/-- Acceptance is exactly absence of an exposed original let spelling from the
protected list, regardless of source spans or unsupported child expressions. -/
theorem computationBlockPreservesNames_iff {names : List String} {body : Syntax.Block} :
    computationBlockPreservesNames names body = true ↔ ComputationNamesProtected names body :=
  ⟨sound, complete⟩

/-- A rejected guard has an actual exposed source occurrence of a protected name. -/
theorem computationBlockPreservesNames_eq_false_iff {names : List String} {body : Syntax.Block} :
    computationBlockPreservesNames names body = false ↔
      ∃ name, name ∈ names ∧ ExposesComputationLetName name body := by
  rw [Bool.eq_false_iff]
  change (¬ computationBlockPreservesNames names body = true) ↔ _
  rw [computationBlockPreservesNames_iff]
  constructor
  · intro rejected
    apply Classical.byContradiction
    intro noWitness
    exact rejected (fun name exposed member => noWitness ⟨name, member, exposed⟩)
  · rintro ⟨name, member, exposed⟩ protection
    exact protection name exposed member

/-- Protection persists for any list whose spellings occur in the protected list. -/
theorem ComputationNamesProtected.subset {small large : List String} {body : Syntax.Block}
    (protection : ComputationNamesProtected large body) (included : small ⊆ large) :
    ComputationNamesProtected small body :=
  fun name exposed member => protection name exposed (included member)

end Solcore.Frontend
