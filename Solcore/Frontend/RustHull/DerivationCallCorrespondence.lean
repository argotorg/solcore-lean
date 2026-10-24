import Solcore.Frontend.RustHull.ContextualExpressionCorrespondence
import Solcore.Frontend.RustHull.CompiledProgramLookup
import Solcore.Frontend.RustHull.DerivationCorrespondenceSupport

/-! Calls and argument lists composed along one independent source execution.
Only the operand and callee derivations already encountered by that execution
are used; recursive callees need no syntactic rank. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationCallCorrespondence
open Correspondence ScalarExecution NamedCallCorrespondence PureCallCorrespondence
open DerivationCorrespondence

theorem builtin_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {name : String} {type : Ty} {arguments : List Expr} {span : Option Span} {lowered : Lowered}
    (notSignature : signatures.find? (·.name == name) = none)
    (compiled : lowerExpression (fuel + 1) signatures scope ⟨type, .call name arguments, span⟩ = .ok lowered) :
    ∃ expected codes, lowerType (fuel + 1) type = .ok expected ∧
      arguments.mapM (lowerExpression fuel signatures scope) = .ok codes ∧
      lowerBuiltin scope name expected codes = .ok lowered := by
  simp only [lowerExpression] at compiled
  obtain ⟨expected, typeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨codes, argumentsCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  simp only [notSignature] at compiled
  obtain ⟨result, builtinCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  cases returned
  exact ⟨expected, codes, typeCompiled, argumentsCompiled, builtinCompiled⟩

theorem primitive_call_result {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {name : String} {type : Ty}
    {values : List Semantics.Value} {source : Semantics.Value} {initial final : Semantics.State σ}
    {operation : PureBuiltin} (classified : pureBuiltin? name = some operation)
    (notFunction : functions.find? (·.name == name) = none)
    (called : Semantics.EvalCall functions effects name type values initial (.value source) final) :
    final = initial ∧ Semantics.primitive? name type values = some (.value source) := by
  cases called with
  | function selected _ => rw [notFunction] at selected; cases selected
  | primitive _ computed => exact ⟨rfl, computed⟩
  | external _ notPrimitive _ =>
      have known := pureBuiltin_known classified type values
      rw [notPrimitive] at known
      cases known

theorem arguments_nil {σ : Type} (signatures : List Signature) (codes : List GlobalCode)
    (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (state : Semantics.State σ) :
    ExprsSimulation signatures codes locations captured sourceEnvironment [] state (.value []) state := by
  intro sources same fuel scope arguments compiled world mapping environment store locals globals heap installed
  cases same
  cases compiled
  exact ⟨[], [], store, .nil, .inRight .unit, by simpa using heap, installed⟩

theorem arguments_cons {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat}
    {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}
    {argument : Expr} {rest : List Expr} {initial middle final : Semantics.State σ}
    {source : Semantics.Value} {result : Semantics.Result (List Semantics.Value)}
    (tailEvaluated : Semantics.EvalExprs functions effects sourceEnvironment rest middle result final)
    (head : ExprSimulation signatures codes locations captured sourceEnvironment argument initial (.value source) middle)
    (tail : ExprsSimulation signatures codes locations captured sourceEnvironment rest middle result final) :
    ExprsSimulation signatures codes locations captured sourceEnvironment (argument :: rest)
      initial (result.map (source :: ·)) final := by
  intro sources normal
  cases result with
  | fault reason => cases normal
  | value sources' =>
      simp only [Semantics.Result.map, Semantics.Result.value.injEq] at normal
      subst sources
      intro fuel scope lowered compiled world mapping environment store locals globals heap installed
      simp only [List.mapM_cons] at compiled
      obtain ⟨headCode, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tailCode, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨headExtension, target, middleStore, related, headEvaluation, middleHeap, middleInstalled⟩ :=
        head rfl headCompiled locals globals heap installed
      cases rest with
      | nil =>
          cases tailCompiled
          cases tailEvaluated
          exact ⟨headExtension, [target], middleStore, .cons related .nil,
            headEvaluation, middleHeap, middleInstalled⟩
      | cons next rest =>
          have tailLocals := (locals.extendWorld headExtension).prepend [target]
          obtain ⟨tailExtension, targets, finalStore, tailRelated, tailEvaluation, finalHeap, finalInstalled⟩ :=
            tail rfl tailCompiled tailLocals (globals.prepend [target]) middleHeap middleInstalled
          have nonempty : tailCode ≠ [] := by
            intro empty
            subst tailCode
            simp only [List.mapM_cons] at tailCompiled
            obtain ⟨_, _, tailCompiled⟩ := lower_bind_eq_ok.mp tailCompiled
            obtain ⟨_, _, returned⟩ := lower_bind_eq_ok.mp tailCompiled
            cases returned
          have targetsNonempty : targets ≠ [] := by
            intro empty
            subst targets
            cases tailRelated
            exact nonempty rfl
          refine ⟨headExtension ++ tailExtension, target :: targets, finalStore,
            .cons related tailRelated, ?_, ?_, finalInstalled⟩
          · have renamed : ((packArguments tailCode).expression.rename mapping).weakenAt 0 =
                (packArguments tailCode).expression.rename (fun index => 1 + mapping index) := by
              simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
              congr 1
              funext index
              simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
            cases tailCode with
            | nil => exact (nonempty rfl).elim
            | cons nextCode restCode =>
                change Core.Evaluates environment store
                  ((Core.LocalSequence.pair headCode.type (packArguments (nextCode :: restCode)).type
                    headCode.expression (packArguments (nextCode :: restCode)).expression).rename mapping) _ _
                rw [ContextualExpressionCorrespondence.pair_rename]
                have tailEvaluation' : Core.Evaluates (target :: environment) middleStore
                    (((packArguments (nextCode :: restCode)).expression.rename mapping).weakenAt 0)
                    (.inRight .word (bundleValues targets)) finalStore := by
                  rw [renamed]
                  exact tailEvaluation
                have paired := Core.LocalSequence.pair_success headCode.type
                  (packArguments (nextCode :: restCode)).type headEvaluation tailEvaluation'
                cases targets with
                | nil => exact (targetsNonempty rfl).elim
                | cons firstTarget restTargets => exact paired
          · simpa only [List.append_assoc] using finalHeap

theorem call_function {σ : Type} {functions : List Function} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {name : String} {function : Function} {sources : List Semantics.Value}
    {initial final : Semantics.State σ} {result : Semantics.Result Semantics.Value}
    (selected : functions.find? (·.name == name) = some function)
    (continued : ∀ {name code index}, functions.find? (·.name == name) = some function →
      signatures.find? (·.name == name) = some code.own → codes[index]? = some code →
      FunctionSimulation codes locations captured code index sources initial result final) :
    CallSimulation functions signatures codes locations captured name sources initial result final := by
  intro other code index sourceSelected signatureSelected codeFound
  have same := Option.some.inj (sourceSelected.symm.trans selected)
  subst other
  intro source normal targets values world store heap installed
  exact continued selected signatureSelected codeFound normal values heap installed

theorem call_not_function {σ : Type} {functions : List Function} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {name : String} {sources : List Semantics.Value} {initial final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (absent : functions.find? (·.name == name) = none) :
    CallSimulation functions signatures codes locations captured name sources initial result final := by
  intro function code index selected
  rw [absent] at selected
  cases selected

/-- A particular normal call derivation uses only the argument-list IH and its
selected callee IH. Builtin computation uses the actual compiler branch and
does not assume any callee simulation. -/
theorem call {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {compilationFuel : Nat} {signatures : List Signature} {programScope : Scope}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    (signaturesCompiled : functions.mapM (signature compilationFuel) = .ok signatures)
    (codesCompiled : CompiledGlobals compilationFuel signatures programScope (functions.zip signatures).reverse codes)
    {sourceEnvironment : Semantics.Environment} {type : Ty} {name : String} {arguments : List Expr}
    {span : Option Span} {sources : List Semantics.Value} {initial middle final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (eligible : RecursiveExpression functions ⟨type, .call name arguments, span⟩)
    (called : Semantics.EvalCall functions effects name type sources middle result final)
    (argumentsIH : ExprsSimulation signatures codes locations captured sourceEnvironment arguments
      initial (.value sources) middle)
    (callIH : CallSimulation functions signatures codes locations captured name sources middle result final) :
    ExprSimulation signatures codes locations captured sourceEnvironment
      ⟨type, .call name arguments, span⟩ initial result final := by
  intro source normal fuel scope lowered compiled world mapping environment store locals globals heap installed
  subst result
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      cases eligible with
      | builtin classified notFunction argumentsEligible =>
          have notSignature := (SignatureNames.compiled signaturesCompiled).absent notFunction
          obtain ⟨rfl, computed⟩ := primitive_call_result classified notFunction called
          obtain ⟨expected, argumentCodes, typeCompiled, argumentsCompiled, builtinCompiled⟩ :=
            builtin_components notSignature compiled
          obtain ⟨extension, targets, finalStore, related, argumentsEvaluation, finalHeap, finalInstalled⟩ :=
            argumentsIH rfl argumentsCompiled locals globals heap installed
          obtain ⟨target, resultRelated, resultEvaluation⟩ :=
            builtin_preserves classified typeCompiled builtinCompiled computed related argumentsEvaluation
          exact ⟨extension, target, finalStore, resultRelated, resultEvaluation, finalHeap, finalInstalled⟩
      | named selected argumentsEligible =>
          obtain ⟨index, code, foundSignature, foundCode, _, _⟩ :=
            compiledFunction_resolve signaturesCompiled codesCompiled selected
          obtain ⟨argumentCodes, functionCode, argumentsCompiled, argumentTypes, functionCompiled, _, rfl⟩ :=
            call_components foundSignature compiled
          have sameName : code.own.name = name := by
            simpa only [beq_iff_eq] using List.find?_some foundSignature
          rw [← sameName] at functionCompiled
          have functionEvaluation := global_read_evaluates foundCode globals installed functionCompiled
          let closure := Core.Value.closure (bundleType code.own.parameters)
            (Core.LanguageResult.resultType code.own.result) (code.body.rename (globalShift index).lift)
            (installationEnvironment captured index)
          obtain ⟨argumentExtension, targets, argumentStore, argumentsRelated,
              argumentsEvaluation, argumentHeap, argumentInstalled⟩ :=
            argumentsIH rfl argumentsCompiled (locals.prepend [closure]) (globals.prepend [closure]) heap installed
          have values : ValuesRel code.own.parameters sources targets :=
            argumentTypes ▸ ArgumentsRel.values argumentsRelated
          obtain ⟨callExtension, target, finalStore, related, bodyEvaluation, finalHeap, finalInstalled⟩ :=
            callIH selected foundSignature foundCode rfl values argumentHeap argumentInstalled
          exact ⟨argumentExtension ++ callExtension, target, finalStore, related,
            call_evaluates functionEvaluation argumentsEvaluation bodyEvaluation,
            by simpa only [List.append_assoc] using finalHeap, finalInstalled⟩

end Solcore.Frontend.RustHull.DerivationCallCorrespondence
