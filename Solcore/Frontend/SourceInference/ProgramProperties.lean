import Solcore.Frontend.SourceInference.Program
import Solcore.Frontend.SourceInference.TypedIRProperties

/-! Success projections for source-inference finalization. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

theorem unify_localSchemeAssumptions
    {state next : State} {left right : Ty}
    (result : unify state left right = .ok next) :
    next.localSchemeAssumptions = state.localSchemeAssumptions := by
  unfold unify at result
  cases unified : state.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at result
  cases result
  rfl

theorem defaultIntegerPatternTarget_localSchemeAssumptions
    {state next : State} {origin : IntegerPatternOrigin}
    (result : defaultIntegerPatternTarget state origin = .ok next) :
    next.localSchemeAssumptions = state.localSchemeAssumptions := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerPatternTarget, resolved] at result
  · exact unify_localSchemeAssumptions result
  all_goals cases result <;> rfl

theorem defaultIntegerPatternTargets_localSchemeAssumptions
    {origins : List IntegerPatternOrigin} {state next : State}
    (result : defaultIntegerPatternTargets origins state = .ok next) :
    next.localSchemeAssumptions = state.localSchemeAssumptions := by
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
            (defaultIntegerPatternTarget_localSchemeAssumptions headResult)

theorem defaultIntegerLiteralTarget_localSchemeAssumptions
    {state next : State} {origin : IntegerLiteralOrigin}
    (result : defaultIntegerLiteralTarget state origin = .ok next) :
    next.localSchemeAssumptions = state.localSchemeAssumptions := by
  cases resolved : state.resolve (.variable origin.metavariable) <;>
    simp [defaultIntegerLiteralTarget, resolved] at result
  · exact unify_localSchemeAssumptions result
  all_goals cases result <;> rfl

theorem defaultIntegerLiteralTargets_localSchemeAssumptions
    {origins : List IntegerLiteralOrigin} {state next : State}
    (result : defaultIntegerLiteralTargets origins state = .ok next) :
    next.localSchemeAssumptions = state.localSchemeAssumptions := by
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
            (defaultIntegerLiteralTarget_localSchemeAssumptions headResult)

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

/-- Finalization preserves the declaration owning the inferred source. -/
theorem finalize_typedSource_owner
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.typedSource.owner = state.owner := by
  rw [finalize_typedSource success]
  rfl

/-- Final substitution preserves the stable identities of every input. -/
theorem finalize_typedSource_inputIds
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.typedSource.inputs.map (fun binder => binder.id) =
      state.inputs.map (fun binder => binder.id) := by
  rw [finalize_typedSource success]
  simp [State.toTypedSource]

/-- Final substitution cannot rename the inputs retained by finalization. -/
theorem finalize_typedSource_inputNames
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.typedSource.inputs.map (fun binder => binder.name) =
      state.inputs.map (fun binder => binder.name) := by
  rw [finalize_typedSource success]
  simp [State.toTypedSource]

/-- Final substitution cannot change input staging markers. -/
theorem finalize_typedSource_inputComptime
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.typedSource.inputs.map (fun binder => binder.comptime) =
      state.inputs.map (fun binder => binder.comptime) := by
  rw [finalize_typedSource success]
  simp [State.toTypedSource]

end Solcore.Frontend.SourceInference.Detail

namespace Solcore.Frontend.SourceInference

open TypeSystem

/-- Successful checking retains the callable type assembled by the signature
builder. -/
theorem checkFunctionBody_success_type
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.type = signature.scheme.body := by
  obtain ⟨_, _, _, _, _, _, _, _, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  rfl

/-- Successful checking retains the signature's independent return-staging
marker. -/
theorem checkFunctionBody_success_returnComptime
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.returnComptime = signature.returnComptime := by
  obtain ⟨_, _, _, _, _, _, _, _, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  rfl

/-- The checked body's reported result type is the declared return bundle
under the final inference substitution. -/
theorem checkFunctionBody_success_inferredBodyType
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.inferredBodyType = checked.substitution.apply
      (Ty.productMany signature.returnTypes) := by
  obtain ⟨_, _, _, _, _, _, _, finalizeEq, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  exact Detail.finalize_type finalizeEq

end Solcore.Frontend.SourceInference
