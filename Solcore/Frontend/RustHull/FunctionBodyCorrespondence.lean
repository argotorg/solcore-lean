import Solcore.Frontend.RustHull.StraightLineCorrespondence
import Solcore.Frontend.RustHull.FunctionInstallationCorrespondence

/-! The actual function lowerer wraps a statement control result, then allocates
the declared parameters. This module relates that result wrapper to the
independent source function boundary. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StatementCorrespondence

open Correspondence ScalarExecution

private theorem mapM_length {α β : Type} {action : α → LowerM β}
    {inputs : List α} {outputs : List β} (accepted : inputs.mapM action = .ok outputs) :
    inputs.length = outputs.length := by
  induction inputs generalizing outputs with
  | nil => cases accepted; rfl
  | cons input rest ih =>
      simp only [List.mapM_cons] at accepted
      obtain ⟨head, _, accepted⟩ := lower_bind_eq_ok.mp accepted
      obtain ⟨tail, tailAccepted, returned⟩ := lower_bind_eq_ok.mp accepted
      cases returned
      exact congrArg Nat.succ (ih tailAccepted)

theorem signature_components {fuel : Nat} {function : Function} {own : Signature}
    (compiled : signature fuel function = .ok own) :
    function.args.length = own.parameters.length ∧ lowerType fuel function.ret = .ok own.result := by
  by_cases reserved : function.name.startsWith Effects.reservedPrefix
  · simp [signature, reserved, fail, Bind.bind, Except.bind] at compiled
  · simp only [signature, reserved, Bool.false_eq_true, ↓reduceIte] at compiled
    obtain ⟨parameters, parametersCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨result, resultCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
    cases returned
    exact ⟨mapM_length parametersCompiled, resultCompiled⟩

def finishedBody (type : Core.Ty) (statements : Core.Expr) : Core.Expr :=
  Core.LocalControl.finish type
    (Core.LocalLoop.toControl type statements (Core.Word.ofNatModulo 5))
    (if type = .unit then Core.LanguageResult.success .unit
     else Core.LanguageResult.failure type (.word (Core.Word.ofNatModulo 4)))

@[simp] theorem finishedBody_rename (type : Core.Ty) (statements : Core.Expr)
    (mapping : Core.Renaming) :
    (finishedBody type statements).rename mapping = finishedBody type (statements.rename mapping) := by
  by_cases unit : type = .unit <;>
    simp [finishedBody, unit, Core.LocalControl.finish, Core.LocalLoop.toControl,
      Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure,
      Core.Expr.rename, Core.Expr.weakenAt, Core.Renaming.lift]

theorem lowerFunction_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {function : Function} {own : Signature} {expression : Core.Expr}
    (compiled : lowerFunction fuel signatures scope function own = .ok expression) :
    ∃ statements,
      lowerStatements fuel signatures
        ((function.args.zip own.parameters).foldl
          (fun scope (argument, type) => scope.addLocal argument.name type)
          (scope.temporary (bundleType own.parameters))) own.result 0 function.body = .ok statements ∧
      expression = .lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result)
        (own.parameters.zipIdx.foldr (fun (type, index) body =>
          .letE (Core.OptionalCell.allocateInitialized type
            (projectArgument index own.parameters.length (.var index))) body)
          (finishedBody own.result statements)) := by
  by_cases unique : (function.args.map (·.name)).eraseDups.length = function.args.length
  · simp only [lowerFunction, unique, ↓reduceIte] at compiled
    obtain ⟨checked, _, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases checked
    obtain ⟨statements, bodyCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
    cases returned
    exact ⟨statements, bodyCompiled, rfl⟩
  · simp [lowerFunction, unique, fail, Bind.bind, Except.bind] at compiled

theorem finish_preserves {fuel : Nat} {sourceType : Ty} {type : Core.Ty}
    (typeCompiled : lowerType fuel sourceType = .ok type)
    {control : Semantics.Control} {target : Core.Value} (related : ControlRel type control target)
    {statements : Core.Expr} {mapping : Core.Renaming} {environment : Core.Environment}
    {initial final : Core.Store}
    (evaluated : Core.Evaluates environment initial (statements.rename mapping) target final) :
    ∃ result, ResultRel type (Semantics.finishFunction sourceType control) result ∧
      Core.Evaluates environment initial ((finishedBody type statements).rename mapping) result final := by
  rw [finishedBody_rename]
  cases related with
  | returned valueRelated =>
      exact ⟨_, .value valueRelated, Core.LocalControl.finish_returned _
        (Core.LocalLoop.toControl_normal _ _ evaluated)⟩
  | language reason =>
      exact ⟨_, .language reason, Core.LocalControl.finish_failure _
        (Core.LocalLoop.toControl_failure _ _ evaluated)⟩
  | breaking =>
      exact ⟨_, .language _, Core.LocalControl.finish_failure _
        (Core.LocalLoop.toControl_transfer _ _ evaluated)⟩
  | continuing =>
      exact ⟨_, .language _, Core.LocalControl.finish_failure _
        (Core.LocalLoop.toControl_transfer _ _ evaluated)⟩
  | fallthrough =>
      obtain ⟨shape, shapeFound, typeEqual⟩ := lowerType_shape typeCompiled
      by_cases unit : type = .unit
      · have shapeUnit : shape = .unit := coreType_injective (typeEqual.trans unit)
        subst shape
        subst type
        refine ⟨.inRight .word .unit, ?_, ?_⟩
        · simp only [Semantics.finishFunction, shapeFound]
          exact ResultRel.value ValueRel.unit
        · apply Core.LocalControl.finish_fallthrough _ (Core.LocalLoop.toControl_normal _ _ evaluated)
          simp only [↓reduceIte, Core.LanguageResult.success, Core.Expr.weakenAt]
          exact .inRight .unit
      · have shapeNotUnit : shape ≠ .unit := by
          intro same
          exact unit (typeEqual.symm.trans (congrArg coreType same))
        have guard : (shape == Semantics.Shape.unit) = false := by
          cases shape <;> first | contradiction | rfl
        refine ⟨.inLeft type (.word (Core.Word.ofNatModulo 4)), ?_, ?_⟩
        · simpa only [Semantics.finishFunction, shapeFound, Option.some_beq_some, guard,
            Bool.false_eq_true, ↓reduceIte] using ResultRel.language (type := type) (Core.Word.ofNatModulo 4)
        · apply Core.LocalControl.finish_fallthrough _ (Core.LocalLoop.toControl_normal _ _ evaluated)
          simp only [unit, ↓reduceIte, Core.LanguageResult.failure, Core.Expr.weakenAt]
          exact .inLeft .word

theorem straight_line_body {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {typeFuel fuel : Nat} {sourceType : Ty} {scope : Scope} {type : Core.Ty}
    {expression : Core.Expr} {statements : List Stmt}
    (typeCompiled : lowerType typeFuel sourceType = .ok type)
    (compiled : lowerStatements fuel signatures scope type 0 statements = .ok expression)
    (eligible : ∀ statement ∈ statements, StraightLine functions effects signatures external statement)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (sourceEvaluated : Semantics.EvalStatements functions effects sourceEnvironment statements initial control final)
    (normal : NormalControl control)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (externalRelated : external initial.external store) :
    ∃ extension targetValue finalStore,
      ResultRel type (Semantics.finishFunction sourceType control) targetValue ∧
      Core.Evaluates environment store ((finishedBody type expression).rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  obtain ⟨extension, controlValue, finalStore, related, evaluated, finalHeap, finalExternal⟩ :=
    straight_line_statements frame compiled eligible sourceEvaluated normal
      environmentRelated heapRelated externalRelated
  obtain ⟨value, resultRelated, finished⟩ := finish_preserves typeCompiled related evaluated
  exact ⟨extension, value, finalStore, resultRelated, finished, finalHeap, finalExternal⟩

/-- Calling the actual lowered function derives its parameter cells from the
supplied argument bundle, then preserves the independent source body execution.
No assumption supplies a preinitialized parameter environment or heap. -/
theorem lowerFunction_apply {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {typeFuel fuel : Nat} {scope : Scope} {function : Function} {own : Signature}
    {expression argument : Core.Expr}
    (signatureCompiled : signature typeFuel function = .ok own)
    (compiled : lowerFunction fuel signatures scope function own = .ok expression)
    (eligible : ∀ statement ∈ function.body, StraightLine functions effects signatures external statement)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial allocated final : Semantics.State σ} {sourceEnvironment : Semantics.Environment}
    (bound : Semantics.bindArguments function.args sources [] initial = some (sourceEnvironment, allocated))
    {control : Semantics.Control}
    (sourceEvaluated : Semantics.EvalStatements functions effects sourceEnvironment function.body allocated control final)
    (normal : NormalControl control)
    {world : World} {environment : Core.Environment} {initialStore callStore : Core.Store}
    (argumentEvaluated : Core.Evaluates environment initialStore argument (bundleValues targets) callStore)
    (heapRelated : HeapRel world initial.heap callStore)
    (externalRelated : external initial.external callStore) :
    ∃ extension targetValue finalStore,
      ResultRel own.result (Semantics.finishFunction function.ret control) targetValue ∧
      Core.Evaluates environment initialStore (.apply expression argument) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  obtain ⟨arity, resultCompiled⟩ := signature_components signatureCompiled
  obtain ⟨statements, statementsCompiled, rfl⟩ := lowerFunction_components compiled
  have emptyEnvironment : EnvironmentRel world [] (scope.temporary (bundleType own.parameters))
      Core.Renaming.id (bundleValues targets :: environment) := by
    intro name sourceLocation binding index found looked
    simp [Semantics.lookupLocation] at found
  obtain ⟨parameterExtension, sourceEnvironment', allocated', environment', store',
      sourceBound, cells, parametersRelated, allocatedHeap, allocatedExternal⟩ :=
    initialize_parameters values arity emptyEnvironment heapRelated externalRelated
      (fun _ _ _ _ hypothesis => frame.allocate hypothesis)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (bound.symm.trans sourceBound))
  obtain ⟨extension, targetValue, finalStore, related, executed, finalHeap, finalExternal⟩ :=
    straight_line_body frame resultCompiled statementsCompiled eligible sourceEvaluated normal
      parametersRelated allocatedHeap allocatedExternal
  have bodyExecuted : Core.Evaluates environment' store' (finishedBody own.result statements)
      targetValue finalStore := by
    simpa only [Core.Expr.rename_id] using executed
  have initialized := cells.evaluates (allValues := targets) (start := 0) rfl
    (fun index value found => by simpa only [Nat.zero_add] using found) bodyExecuted
  refine ⟨parameterExtension ++ extension, targetValue, finalStore, related, ?_, ?_, finalExternal⟩
  · apply Core.Evaluates.apply .lambda argumentEvaluated
    simpa only [parameterCode, values.length.2] using initialized
  · simpa only [List.append_assoc] using finalHeap

end Solcore.Frontend.RustHull.StatementCorrespondence
