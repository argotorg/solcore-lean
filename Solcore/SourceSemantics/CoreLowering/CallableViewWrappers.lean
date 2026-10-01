import Solcore.Frontend.SourceCoreCallableViewWrappers
import Solcore.Core.Safety
import Solcore.Core.Correspondence

/-! Finite Core transparency of a callable view wrapper. The store and both
the original closure environment and outer wrapper environment are arbitrary.
Only the actual original closure body is executed; no heap is copied, no cell
is allocated by the wrapper, and no general exact weakening claim is needed.
These are Core library laws, not a source compiler correctness theorem. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableViewWrappers
open Core Frontend.SourceCoreCallableViewWrappers

theorem body_hasType {definitions : DataEnvironment} {context : Context}
    (parameter result : Ty) (view : Word) :
    HasType (parameter :: CallableContract.functionType parameter result :: context)
      (body view) (LanguageResult.resultType result) definitions :=
  .letE .word (.apply (.second (.first (.var rfl))) (.var rfl))

theorem repack_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} (view : Word)
    (parameterWF : parameter.WellFormed definitions) (resultWF : result.WellFormed definitions) :
    HasType (CallableContract.functionType parameter result :: context)
      (repack parameter result view) (CallableContract.functionType parameter result) definitions :=
  .pair (.pair (.first (.first (.var rfl)))
    (.lambda parameterWF (LanguageResult.resultType_wellFormed resultWF) (body_hasType _ _ _)))
    (.second (.var rfl))

theorem lower_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} {read : Expr} (view : Word)
    (parameterWF : parameter.WellFormed definitions) (resultWF : result.WellFormed definitions)
    (readTyped : HasType context read (LanguageResult.resultType (CallableContract.functionType parameter result)) definitions) :
    HasType context (lower parameter result view read)
      (LanguageResult.resultType (CallableContract.functionType parameter result)) definitions :=
  LanguageResult.bind_hasType (CallableContract.functionType_wellFormed parameterWF resultWF) readTyped
    (LanguageResult.success_hasType (repack_hasType view parameterWF resultWF))

theorem wrapped_runtime_typed {definitions : DataEnvironment} {world : StoreTyping}
    {parameter result : Ty} {identity payload : Value} {contract : Word}
    {outer : Environment} {context : Context} (view : Word)
    (originalTyped : RuntimeValueHasType world (originalValue identity payload contract)
      (CallableContract.functionType parameter result) definitions)
    (outerTyped : RuntimeEnvironmentHasTypes world outer context definitions) :
    RuntimeValueHasType world (wrappedValue parameter result view identity payload contract outer)
      (CallableContract.functionType parameter result) definitions := by
  cases originalTyped with
  | pair taggedTyped descriptorTyped =>
    cases taggedTyped with
    | pair identityTyped payloadTyped =>
      exact .pair (.pair identityTyped
        (.closure (.cons (.pair (.pair identityTyped payloadTyped) descriptorTyped) outerTyped)
          (body_hasType _ _ _))) .word

theorem repack_evaluates (parameter result : Ty) (view : Word)
    (identity payload : Value) (contract : Word) (outer : Environment) (store : Store) :
    Evaluates (originalValue identity payload contract :: outer) store
      (repack parameter result view) (wrappedValue parameter result view identity payload contract outer) store :=
  .pair (.pair (.first (.first (.var rfl))) .lambda) (.second (.var rfl))

theorem lower_success {environment : Environment} {before after : Store}
    {parameter result : Ty} {read : Expr} {identity payload : Value} {contract : Word} (view : Word)
    (readEvaluation : Evaluates environment before read
      (.inRight .word (originalValue identity payload contract)) after) :
    Evaluates environment before (lower parameter result view read)
      (.inRight .word (wrappedValue parameter result view identity payload contract environment)) after :=
  LanguageResult.bind_success _ readEvaluation
    (.inRight (repack_evaluates _ _ _ _ _ _ _ _))

theorem lower_failure {environment : Environment} {before after : Store}
    {parameter result : Ty} {read : Expr} {reason : Word} (view : Word)
    (readEvaluation : Evaluates environment before read
      (.inLeft (CallableContract.functionType parameter result) (.word reason)) after) :
    Evaluates environment before (lower parameter result view read)
      (.inLeft (CallableContract.functionType parameter result) (.word reason)) after :=
  LanguageResult.bind_failure _ readEvaluation

/-- The same arbitrary body result includes both successful payloads and
language failures. All original writes/allocations and their final store pass
through exactly once. -/
theorem body_evaluates {parameter result : Ty} {code : Expr}
    {captured outer : Environment} {before after : Store}
    {identity argument value : Value} {contract : Word} (view : Word)
    (originalEvaluation : Evaluates (argument :: captured) before code value after) :
    Evaluates (argument :: originalValue identity
      (.closure parameter (LanguageResult.resultType result) code captured) contract :: outer)
      before (body view) value after :=
  .letE .word (.apply (.second (.first (.var rfl))) (.var rfl) originalEvaluation)

theorem body_reflects {parameter result : Ty} {code : Expr}
    {captured outer : Environment} {before after : Store}
    {identity argument value : Value} {contract view : Word}
    (evaluation : Evaluates (argument :: originalValue identity
      (.closure parameter (LanguageResult.resultType result) code captured) contract :: outer)
      before (body view) value after) :
    Evaluates (argument :: captured) before code value after := by
  cases evaluation with
  | letE manifest applied =>
    cases manifest
    cases applied with
    | apply callee argumentEvaluation invoked =>
      cases callee with
      | second tagged =>
        cases tagged with
        | first original =>
          cases original with
          | var found =>
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
              originalValue, Value.pair.injEq, Value.closure.injEq] at found
            rcases found with ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
            cases argumentEvaluation with
            | var found =>
              simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
              cases found
              exact invoked

theorem body_iff {parameter result : Ty} {code : Expr}
    {captured outer : Environment} {before after : Store}
    {identity argument value : Value} {contract view : Word} :
    Evaluates (argument :: originalValue identity
      (.closure parameter (LanguageResult.resultType result) code captured) contract :: outer)
      before (body view) value after ↔
    Evaluates (argument :: captured) before code value after :=
  ⟨body_reflects, body_evaluates view⟩

/-- The payload-application step used after the existing descriptor guards. -/
def invoke : Expr := .apply (.second (.first (.var 0))) (.var 1)

theorem invoke_evaluates {parameter result : Ty} {code : Expr}
    {captured outer caller : Environment} {before after : Store}
    {identity argument value : Value} {contract : Word} (view : Word)
    (originalEvaluation : Evaluates (argument :: captured) before code value after) :
    Evaluates (wrappedValue parameter result view identity
      (.closure parameter (LanguageResult.resultType result) code captured) contract outer :: argument :: caller)
      before invoke value after :=
  .apply (.second (.first (.var rfl))) (.var rfl) (body_evaluates view originalEvaluation)

theorem invoke_reflects {parameter result : Ty} {code : Expr}
    {captured outer caller : Environment} {before after : Store}
    {identity argument value : Value} {contract view : Word}
    (evaluation : Evaluates (wrappedValue parameter result view identity
      (.closure parameter (LanguageResult.resultType result) code captured) contract outer :: argument :: caller)
      before invoke value after) :
    Evaluates (argument :: captured) before code value after := by
  cases evaluation with
  | apply callee argumentEvaluation invoked =>
    cases callee with
    | second tagged =>
      cases tagged with
      | first wrapped =>
        cases wrapped with
        | var found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, wrappedValue,
            Value.pair.injEq, Value.closure.injEq] at found
          rcases found with ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
          cases argumentEvaluation with
          | var found =>
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
            cases found
            exact body_reflects invoked

theorem invoke_iff {parameter result : Ty} {code : Expr}
    {captured outer caller : Environment} {before after : Store}
    {identity argument value : Value} {contract view : Word} :
    Evaluates (wrappedValue parameter result view identity
      (.closure parameter (LanguageResult.resultType result) code captured) contract outer :: argument :: caller)
      before invoke value after ↔
    Evaluates (argument :: captured) before code value after :=
  ⟨invoke_reflects, invoke_evaluates view⟩

/-- Completion is equivalent up to sufficient machine fuel, not equal step
counts. This also reflects a completed wrapper call without presupposing a
finite evaluation of the original body. -/
theorem invoke_run_done_iff {parameter result : Ty} {code : Expr}
    {captured outer caller : Environment} {before after : Store}
    {identity argument value : Value} {contract view : Word} :
    (∃ fuel, runStateful fuel (.initial invoke
      (wrappedValue parameter result view identity
        (.closure parameter (LanguageResult.resultType result) code captured) contract outer :: argument :: caller)
      before) = .done value after) ↔
    Evaluates (argument :: captured) before code value after := by
  constructor
  · rintro ⟨fuel, completed⟩
    exact invoke_reflects (runStateful_evaluation_sound completed)
  · intro original
    exact evaluation_runStateful_complete (invoke_evaluates view original)

/-- The public projections do not inspect the wrapper or original closure. -/
theorem copied_identity (parameter result : Ty) (view : Word) (identity payload : Value)
    (contract : Word) (outer environment : Environment) (store : Store) :
    Evaluates (wrappedValue parameter result view identity payload contract outer :: environment)
      store (.first (.first (.var 0))) identity store := .first (.first (.var rfl))

theorem copied_contract (parameter result : Ty) (view : Word) (identity payload : Value)
    (contract : Word) (outer environment : Environment) (store : Store) :
    Evaluates (wrappedValue parameter result view identity payload contract outer :: environment)
      store (.second (.var 0)) (.word contract) store := .second (.var rfl)

theorem dispatch_unchanged {parameter result : Ty} {view contract : Word}
    {identity payload : Value} {outer environment : Environment} {store : Store}
    (gates : List CallableContract.Gate) (phase : CallableContract.Phase) (unknown : Word) :
    Evaluates (wrappedValue parameter result view identity payload contract outer :: environment) store
      (CallableContract.dispatch gates phase unknown (.second (.var 0)))
      (CallableContract.resultValue (CallableContract.decision gates phase unknown contract)) store :=
  CallableContract.dispatch_evaluates _ _ _ _ (copied_contract _ _ _ _ _ _ _ _ _)

theorem equality_identified {leftParameter leftResult rightParameter rightResult : Ty}
    {leftView rightView leftIdentity rightIdentity leftContract rightContract : Word}
    {leftPayload rightPayload : Value} {leftOuter rightOuter environment : Environment} {store : Store} :
    Evaluates
      (wrappedValue rightParameter rightResult rightView (.inRight .unit (.word rightIdentity)) rightPayload rightContract rightOuter ::
       wrappedValue leftParameter leftResult leftView (.inRight .unit (.word leftIdentity)) leftPayload leftContract leftOuter :: environment)
      store CallableContract.equalBody (.bool (leftIdentity == rightIdentity)) store :=
  CallableContract.equalBody_identified

theorem equality_anonymous_left {leftParameter leftResult rightParameter rightResult : Ty}
    {leftView rightView leftContract rightContract : Word} {rightIdentity leftPayload rightPayload : Value}
    {leftOuter rightOuter environment : Environment} {store : Store} :
    Evaluates
      (wrappedValue rightParameter rightResult rightView rightIdentity rightPayload rightContract rightOuter ::
       wrappedValue leftParameter leftResult leftView (.inLeft .word .unit) leftPayload leftContract leftOuter :: environment)
      store CallableContract.equalBody (.bool false) store :=
  CallableContract.equalBody_anonymous_left

end Solcore.SourceSemantics.CoreLowering.CallableViewWrappers
