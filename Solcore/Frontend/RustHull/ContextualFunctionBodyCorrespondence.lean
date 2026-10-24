import Solcore.Frontend.RustHull.ContextualStatementCorrespondence

/-! Function-body correspondence with real installed global functions. The
accepted parameter-name guard protects global bindings during initialization,
and the exact captured-environment renaming is retained through the body. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContextualStatementCorrespondence
open Correspondence ScalarExecution StatementCorrespondence NamedCallCorrespondence

def checkParameterNames (arguments : List Arg) : LowerM PUnit :=
  forIn arguments PUnit.unit fun argument _ => do
    if argument.name.startsWith Effects.reservedPrefix then fail "reserved runtime parameter name"
    pure (.yield PUnit.unit)

theorem checkParameterNames_allowed {arguments : List Arg}
    (checked : checkParameterNames arguments = .ok PUnit.unit) :
    ∀ argument ∈ arguments, argument.name.startsWith Effects.reservedPrefix = false := by
  induction arguments with
  | nil => intros; contradiction
  | cons argument rest ih =>
      cases allowed : argument.name.startsWith Effects.reservedPrefix with
      | true =>
          simp only [checkParameterNames, List.forIn_cons, allowed, ↓reduceIte, fail, Bind.bind, Except.bind] at checked
          cases checked
      | false =>
          have tailChecked : checkParameterNames rest = .ok PUnit.unit := by
            simpa only [checkParameterNames, List.forIn_cons, allowed, Bool.false_eq_true, ↓reduceIte,
              Bind.bind, Except.bind, Pure.pure, Except.pure] using checked
          intro selected member
          cases member with
          | head => exact allowed
          | tail _ member => exact ih tailChecked selected member

theorem lowerFunction_parameters_allowed {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {function : Function} {own : Signature} {expression : Core.Expr}
    (compiled : lowerFunction fuel signatures scope function own = .ok expression) :
    ∀ argument ∈ function.args, argument.name.startsWith Effects.reservedPrefix = false := by
  by_cases unique : (function.args.map (·.name)).eraseDups.length = function.args.length
  · simp only [lowerFunction, unique, ↓reduceIte] at compiled
    obtain ⟨checked, namesChecked, _⟩ := lower_bind_eq_ok.mp compiled
    cases checked
    exact checkParameterNames_allowed namesChecked
  · simp [lowerFunction, unique, fail, Bind.bind, Except.bind] at compiled

theorem straight_line_body {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {typeFuel fuel : Nat} {sourceType : Ty} {scope : Scope} {type : Core.Ty}
    {expression : Core.Expr} {statements : List Stmt}
    (typeCompiled : lowerType typeFuel sourceType = .ok type)
    (compiled : lowerStatements fuel signatures scope type 0 statements = .ok expression)
    (eligible : ∀ statement ∈ statements, StraightLine functions effects signatures codes locations captured statement)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {control : Semantics.Control}
    (sourceEvaluated : Semantics.EvalStatements functions effects sourceEnvironment statements initial control final)
    (normal : NormalControl control)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targetValue finalStore,
      ResultRel type (Semantics.finishFunction sourceType control) targetValue ∧
      Core.Evaluates environment store ((finishedBody type expression).rename mapping) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  obtain ⟨extension, controlValue, finalStore, related, evaluated, finalHeap, finalInstalled⟩ :=
    straight_line_statements compiled eligible sourceEvaluated normal
      environmentRelated globalsRelated heapRelated installed
  obtain ⟨value, resultRelated, finished⟩ := finish_preserves typeCompiled related evaluated
  exact ⟨extension, value, finalStore, resultRelated, finished, finalHeap, finalInstalled⟩

/-- The source function derivation reaches the actual lowered, renamed body.
Both its local cells and its global function references are derived from the
actual argument initializer; no parameter-heap correspondence is assumed. -/
theorem lowerFunction_body_contextual {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {typeFuel fuel : Nat} {scope : Scope} {function : Function} {own : Signature}
    {body : Core.Expr}
    (signatureCompiled : signature typeFuel function = .ok own)
    (compiled : lowerFunction fuel signatures scope function own =
      .ok (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body))
    (eligible : ∀ statement ∈ function.body, StraightLine functions effects signatures codes locations captured statement)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State σ} {sourceResult : Semantics.Result Semantics.Value}
    (sourceEvaluated : Semantics.EvalFunction functions effects function sources initial sourceResult final)
    (normal : ∃ value, sourceResult = .value value)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store)
    (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targetValue finalStore,
      ResultRel own.result sourceResult targetValue ∧
      Core.Evaluates (bundleValues targets :: environment) store (body.rename mapping.lift)
        targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  have allowed := lowerFunction_parameters_allowed compiled
  cases sourceEvaluated with
  | arity mismatch => obtain ⟨value, same⟩ := normal; contradiction
  | body bound sourceExecuted =>
      rename_i allocated sourceEnvironment control
      have controlNormal : NormalControl control := by
        obtain ⟨value, same⟩ := normal
        cases control <;> first | trivial | simp [Semantics.finishFunction] at same
      obtain ⟨arity, resultCompiled⟩ := signature_components signatureCompiled
      obtain ⟨statements, statementsCompiled, bodyShape⟩ := lowerFunction_components compiled
      have bodyEqual := Core.Expr.lambda.inj bodyShape
      rcases bodyEqual with ⟨_, _, rfl⟩
      have emptyEnvironment : EnvironmentRel world [] (scope.temporary (bundleType own.parameters))
          mapping.lift (bundleValues targets :: environment) := by
        intro name sourceLocation binding index found looked
        simp [Semantics.lookupLocation] at found
      obtain ⟨parameterExtension, sourceEnvironment', allocated', environment', store',
          sourceBound, cells, parametersRelated, allocatedHeap, allocatedGlobals⟩ :=
        initialize_parameters_renamed
          (external := fun (_ : σ) targetStore => InstalledGlobals codes locations captured targetStore)
          values arity emptyEnvironment heapRelated installed
          (fun _ _ _ _ hypothesis => hypothesis.append _)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (bound.symm.trans sourceBound))
      have parameterGlobals := cells.globalEnvironment arity allowed
        (globalsRelated.temporary (bundleType own.parameters) (bundleValues targets))
      obtain ⟨extension, targetValue, finalStore, related, executed, finalHeap, finalInstalled⟩ :=
        straight_line_body resultCompiled statementsCompiled eligible sourceExecuted controlNormal
          parametersRelated parameterGlobals allocatedHeap allocatedGlobals
      have initialized := cells.evaluates_renamed (allValues := targets) (start := 0)
        (mapping := mapping.lift) rfl
        (fun index value found => by simpa only [Nat.zero_add] using found) executed
      refine ⟨parameterExtension ++ extension, targetValue, finalStore, related, ?_, ?_, finalInstalled⟩
      · simpa only [parameterCode, values.length.2] using initialized
      · simpa only [List.append_assoc] using finalHeap

end Solcore.Frontend.RustHull.ContextualStatementCorrespondence
