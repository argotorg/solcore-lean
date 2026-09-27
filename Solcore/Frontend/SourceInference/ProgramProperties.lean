import Solcore.Frontend.ProgramEnvironmentProperties
import Solcore.Frontend.ProgramSignatureFormationProperties
import Solcore.Frontend.ProgramSignaturesProperties
import Solcore.Frontend.SourceInference.ExpressionProperties
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

/-- A successful finalization applies its final inference substitution
pointwise to the exact input binders retained by the input state. -/
theorem finalize_typedSource_inputs
    {context : Context} {type : Ty} {state : State} {roots : List NodeId}
    {result : Result}
    (success : finalize context type state roots = .ok result) :
    result.typedSource.inputs =
      state.inputs.map (TypedBinder.applySubstitution result.substitution) := by
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

private theorem functionParameterEnvironment_names
    (parameters : List ProgramFunctionParameter) :
    ((((parameters.map (fun parameter => parameter.name)).zip
        (parameters.map (fun parameter => parameter.type))).map
          fun parameter => (parameter.1, Scheme.mono parameter.2)).map
      fun entry => entry.1) =
        parameters.map (fun parameter => parameter.name) := by
  induction parameters with
  | nil => rfl
  | cons parameter rest induction => simp [induction]

private theorem functionParameterEnvironment_eq
    (parameters : List ProgramFunctionParameter) :
    (((parameters.map (fun parameter => parameter.name)).zip
        (parameters.map (fun parameter => parameter.type))).map
      fun parameter => (parameter.1, Scheme.mono parameter.2)) =
        parameters.map fun parameter =>
          (parameter.name, Scheme.mono parameter.type) := by
  induction parameters with
  | nil => rfl
  | cons parameter rest induction => simp [induction]

private theorem map_mapIdx {alpha beta gamma : Type}
    (items : List alpha) (prepare : alpha → beta)
    (indexed : Nat → beta → gamma) :
    (items.map prepare).mapIdx indexed =
      items.mapIdx fun index item => indexed index (prepare item) := by
  induction items generalizing indexed with
  | nil => rfl
  | cons item rest induction =>
      simp only [List.map_cons, List.mapIdx_cons]
      exact congrArg (indexed 0 (prepare item) :: ·)
        (induction (fun index item => indexed (index + 1) item))

/-- Pointwise substitution invariance of every parameter type makes a
source-ordered row of monomorphic parameter binders invariant too.  The
indexed constructor is abstract so the result also covers the stable IDs,
names, staging markers, and spans assigned by `State.initial`. -/
private theorem functionParameterBinders_applySubstitution_eq_self
    {parameters : List ProgramFunctionParameter}
    (substitution : Substitution)
    (typesFixed :
      (parameters.map fun parameter => parameter.type).map
          substitution.apply =
        parameters.map fun parameter => parameter.type)
    (indexed : Nat → ProgramFunctionParameter → TypedBinder)
    (schemes : ∀ index parameter,
      (indexed index parameter).scheme = Scheme.mono parameter.type)
    (requirements : ∀ index parameter,
      (indexed index parameter).schemeRequirements = []) :
    (parameters.mapIdx indexed).map
        (TypedBinder.applySubstitution substitution) =
      parameters.mapIdx indexed := by
  induction parameters generalizing indexed with
  | nil => rfl
  | cons parameter parameters induction =>
      simp only [List.map_cons, List.cons.injEq] at typesFixed
      rcases typesFixed with ⟨headFixed, tailFixed⟩
      simp only [List.mapIdx_cons, List.map_cons, List.cons.injEq]
      constructor
      · have schemeEq := schemes 0 parameter
        have requirementsEq := requirements 0 parameter
        cases binderEq : indexed 0 parameter with
        | mk id name scheme schemeRequirements comptime span =>
            simp only [binderEq] at schemeEq requirementsEq
            subst scheme
            subst schemeRequirements
            simp [TypedBinder.applySubstitution, Scheme.apply,
              Scheme.mono, Substitution.without, headFixed]
      · exact induction tailFixed
          (fun index parameter => indexed (index + 1) parameter)
          (fun index parameter => schemes (index + 1) parameter)
          (fun index parameter => requirements (index + 1) parameter)

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

/-- Once executable formation has closed the signature's return row, final
inference substitution cannot change its declared return bundle. -/
theorem checkFunctionBody_success_inferredBodyType_eq_declared
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (formation : SignatureTypesFormationValidated signatures signature.id
      signature.scheme.parameters signature.returnTypes)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.inferredBodyType = Ty.productMany signature.returnTypes := by
  rw [checkFunctionBody_success_inferredBodyType success,
    formation.apply_productMany_eq_self checked.substitution]

/-- Successful body inference and finalization retain the source declaration
that owns the checked function. -/
theorem checkFunctionBody_success_typedBody_owner
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.typedBody.owner = signature.id := by
  obtain ⟨declaration, body, finalState, result, declarationEq, bodyEq,
    unifyEq, finalizeEq, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  have bodyHeader := Detail.inferStatementsFuel_state_header bodyEq
  have finalHeader := Detail.unify_state_header unifyEq
  have finalOwner : finalState.owner = declaration.id := by
    have headerOwner := congrArg (fun header : State.Header => header.owner)
      (finalHeader.trans bodyHeader)
    simpa [State.header] using headerOwner
  exact (Detail.finalize_typedSource_owner finalizeEq).trans
    (finalOwner.trans
      (ProgramEnvironment.declaration?_sound declarationEq).2)

/-- Successful body inference retains the exact initial function-parameter
binders and applies only the final flexible inference substitution to them. -/
theorem checkFunctionBody_success_typedBody_inputs
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.typedBody.inputs =
      (State.initial signature.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime).inputs.map
          (TypedBinder.applySubstitution checked.substitution) := by
  obtain ⟨declaration, body, finalState, result, declarationEq, bodyEq,
    unifyEq, finalizeEq, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  have bodyHeader := Detail.inferStatementsFuel_state_header bodyEq
  have finalHeader := Detail.unify_state_header unifyEq
  have finalInputs : finalState.inputs =
      (State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime).inputs := by
    exact congrArg (fun header : State.Header => header.inputs)
      (finalHeader.trans bodyHeader)
  rw [Detail.finalize_typedSource_inputs finalizeEq, finalInputs,
    (ProgramEnvironment.declaration?_sound declarationEq).2]

/-- If the final inference substitution fixes every declared parameter type,
it leaves the complete initial monomorphic input-binder row unchanged. -/
theorem checkFunctionBody_success_typedBody_inputs_eq_initial_of_types_fixed
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (typesFixed : signature.parameterTypes.map checked.substitution.apply =
      signature.parameterTypes)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.typedBody.inputs =
      (State.initial signature.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime).inputs := by
  rw [checkFunctionBody_success_typedBody_inputs success]
  rw [State.initial_inputs_definition]
  simp only [ProgramFunctionSignature.parameterNames,
    ProgramFunctionSignature.parameterTypes,
    ProgramFunctionSignature.parameterComptime,
    functionParameterEnvironment_eq, map_mapIdx]
  apply functionParameterBinders_applySubstitution_eq_self
  · simpa [ProgramFunctionSignature.parameterTypes] using typesFixed
  · intro index parameter
    rfl
  · intro index parameter
    rfl

/-- Once executable signature formation has closed all declared parameter
types, the final inference substitution leaves the complete initial input
binder row unchanged. -/
theorem checkFunctionBody_success_typedBody_inputs_eq_initial
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (formation : SignatureTypesFormationValidated signatures signature.id
      signature.scheme.parameters signature.parameterTypes)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.typedBody.inputs =
      (State.initial signature.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime).inputs := by
  exact checkFunctionBody_success_typedBody_inputs_eq_initial_of_types_fixed
    (formation.apply_eq_self checked.substitution) success

/-- Successful checking preserves the exact source-order input names from the
function signature in the finalized typed body. -/
theorem checkFunctionBody_success_typedBody_inputNames
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.typedBody.inputs.map (fun binder => binder.name) =
      signature.parameterNames := by
  obtain ⟨declaration, body, finalState, result, _, bodyEq, unifyEq,
    finalizeEq, checkedEq⟩ := checkFunctionBody_success_witness success
  subst checked
  have bodyHeader := Detail.inferStatementsFuel_state_header bodyEq
  have finalHeader := Detail.unify_state_header unifyEq
  have finalInputs : finalState.inputs =
      (State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime).inputs := by
    exact congrArg (fun header : State.Header => header.inputs)
      (finalHeader.trans bodyHeader)
  rw [Detail.finalize_typedSource_inputNames finalizeEq, finalInputs,
    State.initial_input_names]
  simpa [ProgramFunctionSignature.parameterNames,
    ProgramFunctionSignature.parameterTypes] using
      functionParameterEnvironment_names signature.parameters

/-- Successful checking preserves the exact source-order staging markers from
the function signature in the finalized typed body. -/
theorem checkFunctionBody_success_typedBody_inputComptime
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    checked.typedBody.inputs.map (fun binder => binder.comptime) =
      signature.parameterComptime := by
  obtain ⟨declaration, body, finalState, result, _, bodyEq, unifyEq,
    finalizeEq, checkedEq⟩ := checkFunctionBody_success_witness success
  subst checked
  have bodyHeader := Detail.inferStatementsFuel_state_header bodyEq
  have finalHeader := Detail.unify_state_header unifyEq
  have finalInputs : finalState.inputs =
      (State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime).inputs := by
    exact congrArg (fun header : State.Header => header.inputs)
      (finalHeader.trans bodyHeader)
  rw [Detail.finalize_typedSource_inputComptime finalizeEq, finalInputs]
  apply State.initial_input_comptime_eq
  simp

end Solcore.Frontend.SourceInference
