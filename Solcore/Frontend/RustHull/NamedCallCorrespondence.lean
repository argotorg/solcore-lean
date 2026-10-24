import Solcore.Frontend.RustHull.PureCallCorrespondence
import Solcore.Frontend.RustHull.FunctionInstallationCorrespondence
import Solcore.Frontend.RustHull.GlobalFunctionCorrespondence

/-! Named calls use the actual function-slot read and argument pack emitted by
the Hull compiler. The captured closure is read before argument evaluation;
its application retains the store produced by those arguments. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.NamedCallCorrespondence

open Correspondence ScalarExecution PureCallCorrespondence

def checkArgumentTypes (arguments : List Lowered) (parameters : List Core.Ty) : LowerM PUnit :=
  forIn (arguments.zip parameters) PUnit.unit fun (argument, parameter) _ => do
    expectType parameter argument.type
    pure (.yield PUnit.unit)

theorem checkedArgumentTypes {arguments : List Lowered} {parameters : List Core.Ty}
    (arity : arguments.length = parameters.length)
    (checked : checkArgumentTypes arguments parameters = .ok PUnit.unit) :
    arguments.map Lowered.type = parameters := by
  induction arguments generalizing parameters with
  | nil => exact (List.eq_nil_of_length_eq_zero arity.symm).symm
  | cons argument rest ih =>
      cases parameters with
      | nil => simp at arity
      | cons parameter parameters =>
          by_cases same : parameter = argument.type
          · have tailChecked : checkArgumentTypes rest parameters = .ok PUnit.unit := by
              simpa [checkArgumentTypes, List.forIn_cons, expectType, same] using checked
            have tail := ih (Nat.succ.inj arity) tailChecked
            simp only [List.map_cons, same, tail]
          · simp [checkArgumentTypes, expectType, same, fail, Bind.bind, Except.bind] at checked

theorem call_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {name : String} {type : Ty} {arguments : List Expr} {span : Option Span} {lowered : Lowered}
    {own : Signature} (selected : signatures.find? (·.name == name) = some own)
    (compiled : lowerExpression (fuel + 1) signatures scope ⟨type, .call name arguments, span⟩ = .ok lowered) :
    ∃ codes functionCode,
      arguments.mapM (lowerExpression fuel signatures scope) = .ok codes ∧
      codes.map Lowered.type = own.parameters ∧
      scope.read (Effects.slotName ("function$" ++ name)) = .ok functionCode ∧
      functionCode.type = own.functionType ∧
      lowered = ⟨own.result, Core.LanguageResult.bind own.result functionCode.expression
        (Core.LanguageResult.bind own.result ((packArguments codes).expression.weakenAt 0)
          (.apply (.var 1) (.var 0)))⟩ := by
  simp only [lowerExpression] at compiled
  obtain ⟨_, _, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨codes, argumentsCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  simp only [selected] at compiled
  by_cases arity : codes.length = own.parameters.length
  · simp only [arity, ↓reduceIte, Pure.pure, Except.pure, Bind.bind, Except.bind] at compiled
    obtain ⟨checked, checkedArguments, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases checked
    have argumentTypes := checkedArgumentTypes arity checkedArguments
    obtain ⟨functionCode, functionCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
    obtain ⟨checked, functionMatched, compiled⟩ := lower_bind_eq_ok.mp compiled
    cases checked
    obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
    cases checked
    cases returned
    exact ⟨codes, functionCode, argumentsCompiled, argumentTypes, functionCompiled,
      (expectType_eq_of_ok functionMatched).symm, rfl⟩
  · simp [arity, fail, Bind.bind, Except.bind] at compiled

theorem ArgumentsRel.values {codes : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel codes sources targets) :
    ValuesRel (codes.map Lowered.type) sources targets := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

theorem call_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type : Ty} {name : String} {arguments : List Expr}
    {span : Option Span} {source : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .call name arguments, span⟩ initial (.value source) final) :
    ∃ middle values,
      Semantics.EvalExprs functions effects sourceEnvironment arguments initial (.value values) middle ∧
      Semantics.EvalCall functions effects name type values middle (.value source) final := by
  generalize resultEq : Semantics.Result.value source = result at evaluated
  cases evaluated <;> simp_all
  exact ⟨_, _, by assumption, by assumption⟩

theorem call_function_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {initial final : Semantics.State σ}
    {name : String} {type : Ty} {values : List Semantics.Value} {source : Semantics.Value}
    {function : Function} (found : functions.find? (·.name == name) = some function)
    (called : Semantics.EvalCall functions effects name type values initial (.value source) final) :
    Semantics.EvalFunction functions effects function values initial (.value source) final := by
  cases called with
  | function selected evaluated =>
      have same := Option.some.inj (found.symm.trans selected)
      cases same
      exact evaluated
  | primitive notFunction _ => rw [found] at notFunction; cases notFunction
  | external notFunction _ _ => rw [found] at notFunction; cases notFunction

/-- Reading the function slot, evaluating arguments, and entering the captured
body use the exact order and de Bruijn shifts generated by lowerExpression. -/
theorem call_evaluates {codes : List Lowered} {functionCode : Lowered} {resultType : Core.Ty}
    {inputType outputType : Core.Ty} {body : Core.Expr} {captured environment : Core.Environment}
    {mapping : Core.Renaming} {initial argumentStore final : Core.Store}
    {argumentValue result : Core.Value}
    (functionEvaluated : Core.Evaluates environment initial (functionCode.expression.rename mapping)
      (.inRight .word (.closure inputType outputType body captured)) initial)
    (argumentsEvaluated : Core.Evaluates (.closure inputType outputType body captured :: environment) initial
      ((packArguments codes).expression.rename (fun index => 1 + mapping index))
      (.inRight .word argumentValue) argumentStore)
    (bodyEvaluated : Core.Evaluates (argumentValue :: captured) argumentStore body result final) :
    Core.Evaluates environment initial
      ((Core.LanguageResult.bind resultType functionCode.expression
        (Core.LanguageResult.bind resultType ((packArguments codes).expression.weakenAt 0)
          (.apply (.var 1) (.var 0)))).rename mapping) result final := by
  have shifted : ((packArguments codes).expression.weakenAt 0).rename mapping.lift =
      (packArguments codes).expression.rename (fun index => 1 + mapping index) := by
    rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp, Core.Renaming.lift_comp_insertion_zero]
    congr 1
    funext index
    simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
  apply Core.LanguageResult.bind_success resultType functionEvaluated
  apply Core.LanguageResult.bind_success resultType
    (by simpa only [shifted] using argumentsEvaluated)
  exact Core.Evaluates.apply (.var rfl) (.var rfl) bodyEvaluated

theorem global_read_evaluates {codes : List GlobalCode} {locations : Nat → Nat}
    {scope : Scope} {mapping : Core.Renaming} {environment captured : Core.Environment}
    {store : Core.Store} {index : Nat} {code : GlobalCode} {lowered : Lowered}
    (found : codes[index]? = some code)
    (globals : GlobalEnvironmentRel codes locations scope mapping environment)
    (installed : InstalledGlobals codes locations captured store)
    (compiled : scope.read (Effects.slotName ("function$" ++ code.own.name)) = .ok lowered) :
    Core.Evaluates environment store (lowered.expression.rename mapping)
      (.inRight .word (.closure (bundleType code.own.parameters)
        (Core.LanguageResult.resultType code.own.result)
        (code.body.rename (globalShift index).lift)
        (installationEnvironment captured index))) store := by
  simp only [Scope.read] at compiled
  obtain ⟨⟨binding, slot⟩, looked, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  obtain ⟨sameType, reference, foundReference⟩ := globals.lookup found looked
  simp only [reference, ↓reduceIte]
  exact Core.OptionalCell.read_success (Core.Word.ofNatModulo 1)
    (.var (sameType ▸ foundReference)) (installed index code found)

/-- The function induction premise uses the closure installed by the real
assembler, including the binder shift from every earlier installation. -/
def FunctionExecutionPreserves {σ : Type} (functions : List Function)
    (effects : Semantics.ExternalSemantics σ) (codes : List GlobalCode) (locations : Nat → Nat)
    (captured : Core.Environment) (function : Function) (code : GlobalCode) (index : Nat)
    (sources : List Semantics.Value) (initial final : Semantics.State σ) (source : Semantics.Value) : Prop :=
  Semantics.EvalFunction functions effects function sources initial (.value source) final →
  ∀ {targets}, ValuesRel code.own.parameters sources targets →
    ∀ {world store}, HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension target finalStore,
        ValueRel code.own.result source target ∧
        Core.Evaluates (bundleValues targets :: installationEnvironment captured index) store
          (code.body.rename (globalShift index).lift) (.inRight .word target) finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore

/-- Context for named-call expressions, in addition to the source-local heap
relation. Pure expression proofs can be lifted because they are uniform in
the external store invariant. -/
def ContextualExprPreserves {σ : Type} (functions : List Function)
    (effects : Semantics.ExternalSemantics σ) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (expression : Expr) : Prop :=
  ∀ {sourceEnvironment initial final sourceValue},
    Semantics.EvalExpr functions effects sourceEnvironment expression initial (.value sourceValue) final →
    ∀ {fuel scope lowered}, lowerExpression fuel signatures scope expression = .ok lowered →
    ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment scope mapping environment →
      GlobalEnvironmentRel codes locations scope mapping environment →
      HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
      ∃ extension targetValue finalStore,
        ValueRel lowered.type sourceValue targetValue ∧
        Core.Evaluates environment store (lowered.expression.rename mapping)
          (.inRight .word targetValue) finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore

theorem contextual_of_normal {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment} {expression : Expr}
    (preserves : StatementCorrespondence.NormalExprPreserves functions effects signatures
      (fun _ store => InstalledGlobals codes locations captured store) expression) :
    ContextualExprPreserves functions effects signatures codes locations captured expression := by
  intro sourceEnvironment initial final sourceValue evaluated fuel scope lowered compiled
    world mapping environment store locals _ heap installed
  exact preserves evaluated compiled locals heap installed

/-- Named source calls reach the actual installed closure. The function
induction premise is applied after the ordered source arguments, with their
derived heap and the retained global cells. -/
theorem call {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat}
    {captured : Core.Environment} {name : String} {function : Function} {code : GlobalCode} {index : Nat}
    (foundFunction : functions.find? (·.name == name) = some function)
    (foundSignature : signatures.find? (·.name == name) = some code.own)
    (foundCode : codes[index]? = some code)
    (preservesFunction : ∀ sources initial final source,
      FunctionExecutionPreserves functions effects codes locations captured function code index sources initial final source)
    {arguments : List Expr}
    (preservesArguments : ∀ argument ∈ arguments,
      StatementCorrespondence.NormalExprPreserves functions effects signatures
        (fun _ store => InstalledGlobals codes locations captured store) argument)
    (type : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured
      ⟨type, .call name arguments, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨middle, sources, argumentsSource, called⟩ := call_source evaluated
  have functionSource := call_function_source foundFunction called
  intro fuel scope lowered compiled world mapping environment store locals globals heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨argumentCodes, functionCode, argumentsCompiled, argumentTypes, functionCompiled, _, rfl⟩ :=
        call_components foundSignature compiled
      have foundName : (code.own.name == name) = true :=
        List.find?_some (p := fun (own : Signature) => own.name == name) foundSignature
      have sameName : code.own.name = name := by simpa only [beq_iff_eq] using foundName
      rw [← sameName] at functionCompiled
      have functionEvaluation := global_read_evaluates foundCode globals installed functionCompiled
      let closure := Core.Value.closure (bundleType code.own.parameters)
        (Core.LanguageResult.resultType code.own.result) (code.body.rename (globalShift index).lift)
        (installationEnvironment captured index)
      have argumentLocals := locals.prepend [closure]
      obtain ⟨argumentExtension, targets, argumentStore, argumentsRelated,
        argumentsEvaluation, argumentHeap, argumentGlobals⟩ :=
        arguments_preserve preservesArguments argumentsSource argumentsCompiled argumentLocals heap installed
      have values : ValuesRel code.own.parameters sources targets :=
        argumentTypes ▸ ArgumentsRel.values argumentsRelated
      obtain ⟨callExtension, target, finalStore, related, bodyEvaluation, finalHeap, finalGlobals⟩ :=
        preservesFunction sources middle final sourceValue functionSource values argumentHeap argumentGlobals
      exact ⟨argumentExtension ++ callExtension, target, finalStore, related,
        call_evaluates functionEvaluation argumentsEvaluation bodyEvaluation,
        by simpa only [List.append_assoc] using finalHeap, finalGlobals⟩

end Solcore.Frontend.RustHull.NamedCallCorrespondence
