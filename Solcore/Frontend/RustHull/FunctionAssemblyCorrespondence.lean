import Solcore.Frontend.RustHull.FunctionBodyCorrespondence

/-! Installation of the actual global function cell used by the scalar Hull
compiler. The source heap omits this administrative cell; the closure still
captures its real mutable reference, exactly as in assemble. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

def singleFunctionScope (own : Signature) : Scope :=
  [⟨some (Effects.slotName ("function$" ++ own.name)), own.functionType, true⟩]

def singleFunctionInvocation (own : Signature) : Core.Expr :=
  Core.LanguageResult.bind own.result
    (Core.OptionalCell.read own.functionType (.var 0) (Core.Word.ofNatModulo 1))
    (.apply (.var 0) (.var 2))

def singleFunctionAllocation (own : Signature) (closure : Core.Expr) : Core.Expr :=
  .letE (Core.OptionalCell.allocate own.functionType)
    (.letE (.storeCell (.var 0) (.inRight .unit closure))
      ((singleFunctionInvocation own).weakenAt 0))

theorem signature_name {fuel : Nat} {function : Function} {own : Signature}
    (compiled : signature fuel function = .ok own) : own.name = function.name := by
  by_cases reserved : function.name.startsWith Effects.reservedPrefix
  · simp [signature, reserved, fail, Bind.bind, Except.bind] at compiled
  · simp only [signature, reserved, Bool.false_eq_true, ↓reduceIte] at compiled
    obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨_, _, returned⟩ := lower_bind_eq_ok.mp compiled
    cases returned
    rfl

/-- Successful assembly of one function exposes the actual signature,
lowered closure, allocation, installation and entry invocation. -/
theorem assemble_single_components {fuel : Nat} {function : Function} {entry : String}
    {own : Signature} {allocated : Core.Expr}
    (compiled : assemble [function] entry [] fuel = .ok (own, allocated)) :
    entry = function.name ∧ signature fuel function = .ok own ∧
      ∃ closure, lowerFunction fuel [own] (singleFunctionScope own) function own = .ok closure ∧
        allocated = singleFunctionAllocation own closure := by
  have unique : [function.name].eraseDups.length = 1 := by
    simp [List.eraseDups_cons, List.eraseDups_nil]
  cases signatureCompiled : signature fuel function with
  | error error =>
      simp [assemble, unique, signatureCompiled, List.mapM_cons, Bind.bind, Except.bind] at compiled
  | ok own' =>
      have sourceName := signature_name signatureCompiled
      by_cases names : own'.name = entry
      · have reduced : (do
            let closure ← lowerFunction fuel [own'] (singleFunctionScope own') function own'
            pure (own', singleFunctionAllocation own' closure)) = .ok (own, allocated) := by
          cases lowered : lowerFunction fuel [own'] (singleFunctionScope own') function own' with
          | error error =>
              have lowered' := lowered
              simp only [singleFunctionScope, names] at lowered'
              simp [assemble, unique, signatureCompiled, List.mapM_cons, names,
                lowered', Bind.bind, Except.bind, Pure.pure, Except.pure] at compiled
          | ok closure =>
              have lowered' := lowered
              simp only [singleFunctionScope, names] at lowered'
              simpa [assemble, unique, signatureCompiled, List.mapM_cons, names,
                singleFunctionScope, Scope.lookup, singleFunctionAllocation, singleFunctionInvocation,
                lowered', Bind.bind, Except.bind, Pure.pure, Except.pure] using compiled
        obtain ⟨closure, closureCompiled, returned⟩ := lower_bind_eq_ok.mp reduced
        cases returned
        exact ⟨names.symm.trans sourceName, rfl, closure, closureCompiled, rfl⟩
      · simp [assemble, unique, signatureCompiled, List.mapM_cons, names, fail, Bind.bind, Except.bind, Pure.pure, Except.pure] at compiled

def singleFunctionEnvironment (own : Signature) (input : Core.Value)
    (environment : Core.Environment) (store : Core.Store) : Core.Environment :=
  .cellRef (Core.OptionalCell.cellType own.functionType) store.length :: input :: environment

def singleFunctionStore (own : Signature) (body : Core.Expr) (input : Core.Value)
    (environment : Core.Environment) (store : Core.Store) : Core.Store :=
  store ++ [.inRight .unit (.closure (bundleType own.parameters)
    (Core.LanguageResult.resultType own.result) body
    (singleFunctionEnvironment own input environment store))]

/-- Executing the actual single-function installation calls the installed
closure with the input bundle. The premise concerns its real captured
environment after installation, not an alternate interpreter. -/
theorem singleFunctionAllocation_evaluates {own : Signature} {body : Core.Expr}
    {input result : Core.Value} {environment : Core.Environment} {initial final : Core.Store}
    (evaluated : Core.Evaluates
      (input :: singleFunctionEnvironment own input environment initial)
      (singleFunctionStore own body input environment initial) body result final) :
    Core.Evaluates (input :: environment) initial
      (singleFunctionAllocation own
        (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body))
      result final := by
  have written : (initial ++ [Core.Value.inLeft own.functionType .unit]).write? initial.length
      (.inRight .unit (.closure (bundleType own.parameters)
        (Core.LanguageResult.resultType own.result) body
        (singleFunctionEnvironment own input environment initial))) =
      some (singleFunctionStore own body input environment initial) := by
    simp [Core.Store.write?, singleFunctionStore]
  have installed : Core.Evaluates (singleFunctionEnvironment own input environment initial)
      (initial ++ [.inLeft own.functionType .unit])
      (.storeCell (.var 0) (.inRight .unit
        (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body)))
      .unit (singleFunctionStore own body input environment initial) :=
    Core.Evaluates.storeCell (oldValue := .inLeft own.functionType .unit)
      (.var rfl) (by simp [Core.Store.read?]) (.inRight .lambda) written
  apply Core.Evaluates.letE (Core.OptionalCell.allocate_evaluates _ _ _)
  apply Core.Evaluates.letE installed
  have invocation : (singleFunctionInvocation own).weakenAt 0 =
      Core.LanguageResult.bind own.result
        (Core.OptionalCell.read own.functionType (.var 1) (Core.Word.ofNatModulo 1))
        (.apply (.var 0) (.var 3)) := by
    simp [singleFunctionInvocation, Core.LanguageResult.bind, Core.OptionalCell.read,
      Core.LanguageResult.failure, Core.LanguageResult.success, Core.Expr.weakenAt]
  rw [invocation]
  change Core.Evaluates (.unit :: singleFunctionEnvironment own input environment initial)
    (singleFunctionStore own body input environment initial)
    (Core.LanguageResult.bind own.result
      (Core.OptionalCell.read own.functionType (.var 1) (Core.Word.ofNatModulo 1))
      (.apply (.var 0) (.var 3))) result final
  have initialized : (singleFunctionStore own body input environment initial).read? initial.length =
      some (.inRight .unit (.closure (bundleType own.parameters)
        (Core.LanguageResult.resultType own.result) body
        (singleFunctionEnvironment own input environment initial))) := by
    simp [singleFunctionStore, Core.Store.read?]
  apply Core.LanguageResult.bind_success own.result
    (Core.OptionalCell.read_success (Core.Word.ofNatModulo 1) (.var rfl) initialized)
  exact Core.Evaluates.apply (.var rfl) (.var rfl) evaluated

/-- Connect an application proved for the actual lowered function to its
public compiler wrapper, including evaluation of the caller's argument and
installation of the global function cell. -/
theorem singleFunction_apply {own : Signature} {body argument : Core.Expr}
    {input result : Core.Value} {environment : Core.Environment}
    {initial argumentStore final : Core.Store}
    (argumentEvaluated : Core.Evaluates environment initial argument input argumentStore)
    (evaluated : Core.Evaluates
      (singleFunctionEnvironment own input environment argumentStore)
      (singleFunctionStore own body input environment argumentStore)
      (.apply (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body)
        (.var 1)) result final) :
    Core.Evaluates environment initial
      (.apply (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result)
        (singleFunctionAllocation own
          (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body)))
        argument) result final := by
  cases evaluated with
  | apply functionEvaluated inputEvaluated bodyEvaluated =>
      cases functionEvaluated
      cases inputEvaluated with
      | var found =>
          simp only [singleFunctionEnvironment, List.getElem?_cons_succ,
            List.getElem?_cons_zero, Option.some.injEq] at found
          subst_vars
          exact Core.Evaluates.apply .lambda argumentEvaluated
            (singleFunctionAllocation_evaluates bodyEvaluated)

end Solcore.Frontend.RustHull.Correspondence
