import Solcore.Frontend.SourceCoreCompatibleDataMatches
import Solcore.Core.DefinitionExtension

/-! A successful pattern check remains valid in an extended definition table.
Only its empty-context matcher typing is transported. The source metadata,
full requirement ledger, allocator and actual child callbacks stay fixed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchAmbientLowering
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
abbrev Compilation := SourceCoreCompatibleDataMatches.Context

/-- Keep the actual lowering context, selecting only its final native table. -/
abbrev withDefinitions (compilation : Compilation) (definitions : DataEnvironment) : Compilation :=
  {compilation with ambientDefinitions := some definitions}

@[simp] theorem definitions (compilation : Compilation) (native : DataEnvironment) :
    (withDefinitions compilation native).definitions = native := rfl

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) : ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem compile_same (fuel : Nat) (compilation : Compilation) (native : DataEnvironment)
    (source : TypedSource) (site : StatementId) (span : Syntax.SourceSpan) (scope : Scope) :
    (∀ expected instructions,
      compileOne (withDefinitions compilation native) source site span scope fuel expected instructions =
        compileOne compilation source site span scope fuel expected instructions) ∧
    (∀ types instructions,
      compileMany (withDefinitions compilation native) source site span scope fuel types instructions =
        compileMany compilation source site span scope fuel types instructions) := by
  induction fuel with
  | zero =>
    constructor
    · intro expected instructions; rfl
    · intro types instructions; cases types <;> rfl
  | succ fuel ih =>
    constructor
    · intro expected instructions
      cases instructions with
      | nil => rfl
      | cons instruction rest =>
        cases instruction <;>
          simp only [compileOne, ih.2]
          <;> rfl
    · intro types instructions
      cases types with
      | nil => rfl
      | cons type rest => simp only [compileMany, ih.1, ih.2]

private theorem root_same (compilation : Compilation) (native : DataEnvironment)
    (source : MatchPatternSource) (resolution : MatchPatternResolution) :
    rootInstructions (withDefinitions compilation native) source resolution =
      rootInstructions compilation source resolution := by
  induction source generalizing resolution <;> cases resolution <;>
    simp_all only [rootInstructions]
    <;> rfl

/-- The returned raw pattern is unchanged, including every ordered binder and
requirement. Its original pure matcher proof is extended to the final table. -/
theorem compilePattern_success
    (compilation : Compilation) (native : DataEnvironment) (extension : compilation.definitions.Extends native)
    {fuel : Nat} {source : TypedSource} {scope : Scope} {site : StatementId} {span : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : CertifiedPattern compilation.definitions}
    (accepted : compilePattern compilation fuel source scope site span expected pattern = .ok compiled) :
    compilePattern (withDefinitions compilation native) fuel source scope site span expected pattern =
      .ok ⟨compiled.pattern, compiled.typed.extend_definitions extension⟩ := by
  unfold compilePattern at accepted ⊢
  simp only [root_same, (compile_same fuel compilation native source site span scope).1]
  by_cases owned : site.occurrence.owner ≠ source.owner
  · simp [owned, throw, bind, Except.bind] at accepted
  · simp only [owned, ↓reduceIte] at accepted ⊢
    by_cases shape : pattern.type = expected
    · simp only [shape, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted ⊢
      obtain ⟨instructions, root, accepted⟩ := bind_ok accepted
      rw [root]
      dsimp only
      obtain ⟨⟨actual, rest⟩, compiledOne, accepted⟩ := bind_ok accepted
      rw [compiledOne]
      dsimp only
      by_cases remaining : rest.isEmpty && decide (actual.requirements = pattern.requirements)
      · simp only [remaining, ↓reduceIte] at accepted ⊢
        by_cases distinct : (decide (actual.bindings.map (·.1.id)).Nodup && decide (actual.bindings.map (·.1.name)).Nodup) = true
        · simp only [distinct, ↓reduceIte] at accepted ⊢
          split at accepted
          · rename_i checked
            cases accepted
            simp only [definitions, infer_complete ((infer_sound checked).extend_definitions extension), ↓reduceDIte]
          · cases accepted
        · simp [distinct, throw] at accepted
      · simp [remaining, throw] at accepted
    · simp [shape, throw, bind, Except.bind] at accepted


private theorem arms_success
    (compilation : Compilation) (native : DataEnvironment) (extension : compilation.definitions.Extends native)
    (lowerBody : BodyLowerer) (fuel : Nat) (source : TypedSource) (scope : Scope) (site : StatementId)
    (expected : TypeSystem.Ty) (result : Ty) (reasonAt : ExpressionId → Word) (reason : Word)
    (cases : List TypedMatchCase) {arms : List (Pattern × Expr)}
    (accepted : cases.mapM (fun arm => do
      let pattern ← compilePattern compilation fuel source scope site arm.span expected arm.pattern
      let body ← lowerBody fuel source (pattern.pattern.bindings.foldl (fun scope (binding : TypedBinder × Ty) => (binding.1.id, binding.2) :: scope) scope)
        arm.body result reasonAt reason
      pure (pattern.pattern, body)) = .ok arms) :
    cases.mapM (fun arm => do
      let pattern ← compilePattern (withDefinitions compilation native) fuel source scope site arm.span expected arm.pattern
      let body ← lowerBody fuel source (pattern.pattern.bindings.foldl (fun scope (binding : TypedBinder × Ty) => (binding.1.id, binding.2) :: scope) scope)
        arm.body result reasonAt reason
      pure (pattern.pattern, body)) = .ok arms := by
  induction cases generalizing arms with
  | nil => simpa only [List.mapM_nil] using accepted
  | cons arm rest ih =>
    rw [List.mapM_cons] at accepted ⊢
    obtain ⟨head, acceptedHead, accepted⟩ := bind_ok accepted
    obtain ⟨tail, acceptedTail, accepted⟩ := bind_ok accepted
    cases accepted
    obtain ⟨pattern, compiled, acceptedHead⟩ := bind_ok acceptedHead
    obtain ⟨body, bodyAccepted, acceptedHead⟩ := bind_ok acceptedHead
    cases acceptedHead
    rw [ih acceptedTail]
    simp only [compilePattern_success compilation native extension compiled, bodyAccepted,
      pure, Except.pure, bind, Except.bind]

/-- Only successful lowering is transported. The original source, callbacks,
budgets, scopes, ordered arms, default and complete emitted code are unchanged. -/
theorem lowerWithReasons_success
    (compilation : Compilation) (native : DataEnvironment) (extension : compilation.definitions.Extends native)
    {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer} {fuel : Nat}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reasonAt : ExpressionId → Word} {reason : Word} {code : Expr}
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution result reasonAt reason = .ok code) :
    lowerWithReasons (withDefinitions compilation native) lowerExpression lowerBody fuel source scope id resolution result reasonAt reason = .ok code := by
  cases fuel with
  | zero => simpa only [lowerWithReasons] using accepted
  | succ fuel =>
    simp only [lowerWithReasons] at accepted ⊢
    obtain ⟨⟨node, statementType⟩, read, accepted⟩ := bind_ok accepted
    change SourceCoreCompatibleDataExpressions.readStatement compilation.checked source id >>= _ = .ok code
    rw [read]
    by_cases allowed : statementType = .unit ∨ statementType = result
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at accepted ⊢
      simp only [allowed, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted ⊢
      by_cases form : node.form = .matchWith resolution
      · simp only [form, ↓reduceIte] at accepted ⊢
        by_cases requirements : resolution.requirements = resolution.cases.flatMap (·.pattern.requirements)
        · simp only [requirements, ↓reduceIte] at accepted ⊢
          by_cases hiddenOwned : resolution.hiddenScrutinee.owner = source.owner
          · simp only [hiddenOwned, ne_eq, not_true_eq_false, ↓reduceIte] at accepted ⊢
            cases hiddenFresh : scope.any (fun entry => decide (entry.1 = resolution.hiddenScrutinee)) with
            | true => simp [hiddenFresh] at accepted
            | false =>
              simp only [hiddenFresh, Bool.false_eq_true, ↓reduceIte] at accepted ⊢
              by_cases scrutineeOwned : resolution.scrutinee.occurrence.owner = source.owner
              · simp only [scrutineeOwned, not_true_eq_false, ↓reduceIte] at accepted ⊢
                cases found : source.lookupExpression? resolution.scrutinee with
                | none => simp [found] at accepted
                | some node =>
                  simp only [found] at accepted ⊢
                  obtain ⟨type, projectedType, accepted⟩ := bind_ok accepted
                  change (projected compilation source node.type >>= _) = .ok code
                  rw [projectedType]
                  simp only [bind, Except.bind]
                  obtain ⟨scrutinee, expression, accepted⟩ := bind_ok accepted
                  rw [expression]
                  dsimp only
                  obtain ⟨checked, sameType, accepted⟩ := bind_ok accepted
                  cases checked
                  rw [sameType]
                  dsimp only
                  obtain ⟨arms, compiledArms, accepted⟩ := bind_ok accepted
                  have liftedArms := arms_success compilation native extension lowerBody fuel source
                    ((resolution.hiddenScrutinee, type) :: scope) id node.type result reasonAt reason resolution.cases compiledArms
                  simp only [bind, Except.bind, pure, Except.pure] at liftedArms
                  rw [liftedArms]
                  simpa only [bind, Except.bind, bindArmWithAllocator, withDefinitions] using accepted
              · simp [scrutineeOwned] at accepted
          · simp [hiddenOwned] at accepted
        · simp [requirements] at accepted
      · simp [form] at accepted
    · simp [allowed, bind, Except.bind] at accepted

/-- Static success transport for the actual selected match callback. All
compiler arguments and the complete returned code are fixed by the occurrence. -/
def PolicySuccess (policy : SourceCoreLoops.Policy) (compilation : Compilation) : Prop :=
  ∀ {lower}, policy.lowerMatch = some lower →
    ∀ {lowerExpression lowerBody fuel source scope id resolution result reasonAt reason code},
      lower lowerExpression lowerBody fuel source scope id resolution result reasonAt reason = .ok code →
      lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution result reasonAt reason = .ok code

/-- The exact-policy interface is an identity instance of successful transport. -/
theorem PolicySuccess.of_eq {policy : SourceCoreLoops.Policy} {compilation : Compilation}
    (same : policy.lowerMatch = some (lowerWithReasons compilation)) :
    PolicySuccess policy compilation := by
  intro lower selected
  have exactLower := Option.some.inj (selected.symm.trans same)
  subst lower
  intro lowerExpression lowerBody fuel source scope id resolution result reasonAt reason code accepted
  exact accepted

/-- A real base-table callback can be consumed under the final native table.
This does not replace its callback, recompile a child, or change source metadata. -/
theorem PolicySuccess.extend {policy : SourceCoreLoops.Policy} {compilation : Compilation}
    (same : policy.lowerMatch = some (lowerWithReasons compilation))
    {native : DataEnvironment} (extension : compilation.definitions.Extends native) :
    PolicySuccess policy (withDefinitions compilation native) := by
  intro lower selected
  have exactLower := Option.some.inj (selected.symm.trans same)
  subst lower
  intro lowerExpression lowerBody fuel source scope id resolution result reasonAt reason code accepted
  exact lowerWithReasons_success compilation native extension accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchAmbientLowering
