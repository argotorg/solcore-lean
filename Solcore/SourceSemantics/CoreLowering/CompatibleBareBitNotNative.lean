import Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotCertificates
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotTail

/-! Bare-root execute prefixes do not allocate or evaluate source children.
An absent root fails at the unary modifier, before setter, write or continuation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotNative
open Core Frontend SourceInference GeneralHeap DataPatternValues CompatiblePayload CompatibleHeap
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {prepared : Prepared} {environment : Environment} {store : Store}
  {target : Location} {optional : Value}

theorem keys_evaluates (environment : Environment) (store : Store) :
    Evaluates environment store (shift 1 (SourceCoreCalls.packArguments []).expression) (.inRight .word .unit) store := by
  simp only [SourceCoreCalls.packArguments, shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success]
  exact .inRight .unit

theorem getter_evaluates (layout : Layout prepared)
    (read : store.read? target = some optional) :
    Evaluates (keysEnvironment prepared.route.rootType target .unit environment) store
      (.apply (getter prepared .unit) (.pair (.loadCell (.var 1)) (.var 0)))
      (.inRight .word optional) store := by
  simp only [getter, layout.steps, normalizeRoot, layout.ordinary]
  exact .apply .lambda (.pair (.loadCell (.var rfl) read) (.var rfl))
    (.inRight (.first (.var rfl)))

theorem setter_evaluates (layout : Layout prepared) (snapshot replacement : Value)
    (read : store.read? target = some optional) :
    Evaluates (modifiedEnvironment prepared.route.rootType target .unit snapshot .unit replacement environment) store
      (.apply (setter prepared .unit) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (.inRight .word replacement) store := by
  simp only [setter, layout.steps]
  exact .apply .lambda (.pair (.loadCell (.var rfl) read) (.pair (.var rfl) (.var rfl)))
    (.inRight (.second (.second (.var rfl))))

theorem prefix_plug (layout : Layout prepared) {index : Nat}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (read : store.read? target = some optional)
    {next : Expr} {outputType : Ty} {operator : Option BinaryOp} {invalid : Word} {result : Value} {after : Store}
    (tail : Evaluates (snapshotEnvironment prepared.route.rootType target .unit optional environment) store
      (CompatiblePlacePrefixReflection.remainder prepared .unit (LanguageResult.success .unit) next outputType operator true invalid)
      result after) :
    Evaluates environment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
      (LanguageResult.success .unit) next outputType operator true invalid) result after := by
  exact .letE (.var lookup) (LanguageResult.bind_success _ (keys_evaluates _ _)
    (LanguageResult.bind_success _ (getter_evaluates layout read) tail))

/-- Inversion recovers the actual continuation after the effect-free reference,
Unit key bundle and live load. Both omitted source-child phases stay absent. -/
theorem prefix_reflects (layout : Layout prepared) {index : Nat}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (read : store.read? target = some optional)
    {next : Expr} {outputType : Ty} {operator : Option BinaryOp} {invalid : Word} {result : Value} {after : Store}
    (completed : Evaluates environment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
      (LanguageResult.success .unit) next outputType operator true invalid) result after) :
    Evaluates (snapshotEnvironment prepared.route.rootType target .unit optional environment) store
      (CompatiblePlacePrefixReflection.remainder prepared .unit (LanguageResult.success .unit) next outputType operator true invalid)
      result after := by
  cases completed with
  | letE reference rest =>
    obtain ⟨same, stores⟩ := evaluation_deterministic reference (Evaluates.var lookup)
    subst_vars
    cases rest with
    | caseLeft keys failed =>
      have same := (evaluation_deterministic keys (keys_evaluates _ _)).1
      cases same
    | caseRight keys rest =>
      obtain ⟨same, stores⟩ := evaluation_deterministic keys (keys_evaluates _ _)
      cases same
      subst_vars
      cases rest with
      | caseLeft getter failed =>
        have same := (evaluation_deterministic getter (getter_evaluates layout read)).1
        cases same
      | caseRight getter rest =>
        obtain ⟨same, stores⟩ := evaluation_deterministic getter (getter_evaluates layout read)
        cases same
        subst_vars
        exact rest

/-- An uninitialized bare root is a unary-operand failure, not a projected-read
fault. No store cell is changed, even when the continuation would have effects. -/
theorem absent_evaluates (layout : Layout prepared) {index : Nat}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (read : store.read? target = some (.inLeft prepared.route.rootType .unit))
    (next : Expr) (outputType : Ty) (operator : Option BinaryOp) (invalid : Word) :
    Evaluates environment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
      (LanguageResult.success .unit) next outputType operator true invalid)
      (.inLeft outputType (.word invalid)) store := by
  apply prefix_plug layout lookup read
  apply LanguageResult.bind_success _ (show Evaluates _ _ (shift 3 (LanguageResult.success .unit))
    (.inRight .word .unit) store from by
      simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success]
      exact .inRight .unit)
  apply LanguageResult.bind_failure
  simp only [modified, if_true]
  exact .caseLeft (.var rfl) (.inLeft .word)

/-- Completed absent-root runs return exactly that failure and the original
store; no assumption about a source or native child execution is used. -/
theorem absent_reflects (layout : Layout prepared) {index : Nat}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (read : store.read? target = some (.inLeft prepared.route.rootType .unit))
    {next : Expr} {outputType : Ty} {operator : Option BinaryOp} {invalid : Word} {result : Value} {after : Store}
    (completed : Evaluates environment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
      (LanguageResult.success .unit) next outputType operator true invalid) result after) :
    result = .inLeft outputType (.word invalid) ∧ after = store :=
  evaluation_deterministic completed (absent_evaluates layout lookup read next outputType operator invalid)

end Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotNative
