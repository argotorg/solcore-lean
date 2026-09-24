import Solcore.Frontend.SourceInference.Program

/-! Success projections for source-inference finalization. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

private theorem unify_toTypedSource
    {state next : State} {left right : Ty} {roots : List NodeId}
    (result : unify state left right = .ok next) :
    next.toTypedSource roots = state.toTypedSource roots := by
  unfold unify at result
  cases unified : state.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at result
  cases result
  rfl

private theorem defaultIntegerPatternTarget_toTypedSource
    {state next : State} {origin : IntegerPatternOrigin}
    {roots : List NodeId}
    (result : defaultIntegerPatternTarget state origin = .ok next) :
    next.toTypedSource roots = state.toTypedSource roots := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerPatternTarget, resolved] at result
  · exact unify_toTypedSource result
  all_goals cases result <;> rfl

private theorem defaultIntegerPatternTargets_toTypedSource
    {origins : List IntegerPatternOrigin} {state next : State}
    {roots : List NodeId}
    (result : defaultIntegerPatternTargets origins state = .ok next) :
    next.toTypedSource roots = state.toTypedSource roots := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerPatternTargets] at result
      cases result
      rfl
  | cons origin rest induction =>
      cases headResult : defaultIntegerPatternTarget state origin with
      | error error =>
          simp [defaultIntegerPatternTargets, headResult, bind, Except.bind]
            at result
      | ok middle =>
          have tailResult :
              defaultIntegerPatternTargets rest middle = .ok next := by
            simpa [defaultIntegerPatternTargets, headResult, bind, Except.bind]
              using result
          exact (induction tailResult).trans
            (defaultIntegerPatternTarget_toTypedSource headResult)

private theorem defaultIntegerLiteralTarget_toTypedSource
    {state next : State} {origin : IntegerLiteralOrigin}
    {roots : List NodeId}
    (result : defaultIntegerLiteralTarget state origin = .ok next) :
    next.toTypedSource roots = state.toTypedSource roots := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerLiteralTarget, resolved] at result
  · exact unify_toTypedSource result
  all_goals cases result <;> rfl

private theorem defaultIntegerLiteralTargets_toTypedSource
    {origins : List IntegerLiteralOrigin} {state next : State}
    {roots : List NodeId}
    (result : defaultIntegerLiteralTargets origins state = .ok next) :
    next.toTypedSource roots = state.toTypedSource roots := by
  induction origins generalizing state with
  | nil =>
      simp [defaultIntegerLiteralTargets] at result
      cases result
      rfl
  | cons origin rest induction =>
      cases headResult : defaultIntegerLiteralTarget state origin with
      | error error =>
          simp [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
            at result
      | ok middle =>
          have tailResult :
              defaultIntegerLiteralTargets rest middle = .ok next := by
            simpa [defaultIntegerLiteralTargets, headResult, bind, Except.bind]
              using result
          exact (induction tailResult).trans
            (defaultIntegerLiteralTarget_toTypedSource headResult)

/-- A successful finalization reports the input type under its final inference
substitution. -/
theorem finalize_type
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.type = result.substitution.apply type := by
  unfold finalize at success
  cases patternResult :
      defaultIntegerPatternTargets state.integerPatterns state with
  | error error =>
      simp [patternResult, bind, Except.bind] at success
  | ok patternState =>
      cases literalResult :
          defaultIntegerLiteralTargets patternState.integerLiterals
            patternState with
      | error error =>
          simp [patternResult, literalResult, bind, Except.bind] at success
      | ok finalState =>
          cases validationResult :
              validateIntegerLiteralTargets finalState
                finalState.integerLiterals with
          | error error =>
              simp [patternResult, literalResult, validationResult, bind,
                Except.bind] at success
          | ok _validation =>
              cases requirementsResult :
                  solveRequirements context finalState finalState.requirements with
              | error error =>
                  simp [patternResult, literalResult, validationResult,
                    requirementsResult, bind, Except.bind] at success
              | ok requirements =>
                  simp [patternResult, literalResult, validationResult,
                    requirementsResult, bind, Except.bind] at success
                  cases success
                  rfl

/-- Finalization changes only inference metadata before applying the final
substitution to the source carrier supplied by its input state. -/
theorem finalize_typedSource
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.typedSource =
      (state.toTypedSource roots).applySubstitution result.substitution := by
  unfold finalize at success
  cases patternResult :
      defaultIntegerPatternTargets state.integerPatterns state with
  | error error =>
      simp [patternResult, bind, Except.bind] at success
  | ok patternState =>
      cases literalResult :
          defaultIntegerLiteralTargets patternState.integerLiterals
            patternState with
      | error error =>
          simp [patternResult, literalResult, bind, Except.bind] at success
      | ok finalState =>
          cases validationResult :
              validateIntegerLiteralTargets finalState
                finalState.integerLiterals with
          | error error =>
              simp [patternResult, literalResult, validationResult, bind,
                Except.bind] at success
          | ok _validation =>
              cases requirementsResult :
                  solveRequirements context finalState finalState.requirements with
              | error error =>
                  simp [patternResult, literalResult, validationResult,
                    requirementsResult, bind, Except.bind] at success
              | ok requirements =>
                  simp [patternResult, literalResult, validationResult,
                    requirementsResult, bind, Except.bind] at success
                  cases success
                  rw [defaultIntegerLiteralTargets_toTypedSource literalResult,
                    defaultIntegerPatternTargets_toTypedSource patternResult]

end Solcore.Frontend.SourceInference.Detail
