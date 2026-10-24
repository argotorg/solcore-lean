import Solcore.Frontend.RustHull.ContextualExpressionCorrespondence
import Solcore.Frontend.RustHull.CompiledProgramLookup
import Solcore.Frontend.RustHull.DerivationCorrespondenceSupport
import Solcore.Frontend.RustHull.CallFaultCorrespondence

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
    {values : List Semantics.Value} {result : Semantics.Result Semantics.Value} {initial final : Semantics.State σ}
    {operation : PureBuiltin} (classified : pureBuiltin? name = some operation)
    (notFunction : functions.find? (·.name == name) = none)
    (called : Semantics.EvalCall functions effects name type values initial result final) :
    final = initial ∧ Semantics.primitive? name type values = some result := by
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
  intro _ fuel scope arguments compiled world mapping environment store locals globals heap installed
  cases compiled
  exact ⟨[], .inRight .word .unit, store, .value .nil, .inRight .unit,
    by simpa using heap, installed, ClosuresPreserved.refl store⟩

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
  intro safe
  cases result with
  | value sources =>
      intro fuel scope lowered compiled world mapping environment store locals globals heap installed
      simp only [List.mapM_cons] at compiled
      obtain ⟨headCode, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tailCode, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨headExtension, target, middleStore, related, headEvaluation, middleHeap, middleInstalled, headFrame⟩ :=
        head.value rfl headCompiled locals globals heap installed
      cases rest with
      | nil =>
          cases tailCompiled
          cases tailEvaluated
          exact ⟨headExtension, .inRight .word target, middleStore, .value (.cons related .nil),
            headEvaluation, middleHeap, middleInstalled, headFrame⟩
      | cons next rest =>
          have tailLocals := (locals.extendWorld headExtension).prepend [target]
          obtain ⟨tailExtension, targets, finalStore, tailRelated, tailEvaluation, finalHeap, finalInstalled, tailFrame⟩ :=
            tail.value rfl tailCompiled tailLocals (globals.prepend [target]) middleHeap middleInstalled
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
          refine ⟨headExtension ++ tailExtension, .inRight .word (bundleValues (target :: targets)), finalStore,
            .value (.cons related tailRelated), ?_, ?_, finalInstalled, headFrame.trans tailFrame⟩
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


  | fault reason =>
      cases reason <;> simp only [Semantics.Result.map, SafeResult] at safe
      rename_i reason
      intro fuel scope lowered compiled world mapping environment store locals globals heap installed
      simp only [List.mapM_cons] at compiled
      obtain ⟨headCode, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tailCode, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨headExtension, target, middleStore, related, headEvaluation, middleHeap, middleInstalled, headFrame⟩ :=
        head.value rfl headCompiled locals globals heap installed
      cases rest with
      | nil => cases tailEvaluated
      | cons next rest =>
          have tailLocals := (locals.extendWorld headExtension).prepend [target]
          obtain ⟨tailExtension, tailTarget, finalStore, tailRelated, tailEvaluation, finalHeap, finalInstalled, tailFrame⟩ :=
            tail safe tailCompiled tailLocals (globals.prepend [target]) middleHeap middleInstalled
          cases tailRelated
          have nonempty : tailCode ≠ [] := by
            intro empty
            subst tailCode
            simp only [List.mapM_cons] at tailCompiled
            obtain ⟨_, _, tailCompiled⟩ := lower_bind_eq_ok.mp tailCompiled
            obtain ⟨_, _, returned⟩ := lower_bind_eq_ok.mp tailCompiled
            cases returned
          cases tailCode with
          | nil => exact (nonempty rfl).elim
          | cons nextCode restCode =>
              refine ⟨headExtension ++ tailExtension, _, finalStore, .language reason, ?_,
                ?_, finalInstalled, headFrame.trans tailFrame⟩
              · change Core.Evaluates environment store
                  ((Core.LocalSequence.pair headCode.type (packArguments (nextCode :: restCode)).type
                    headCode.expression (packArguments (nextCode :: restCode)).expression).rename mapping) _ _
                rw [ContextualExpressionCorrespondence.pair_rename]
                apply Core.LocalSequence.pair_right_failure _ _ headEvaluation
                have renamed : ((packArguments (nextCode :: restCode)).expression.rename mapping).weakenAt 0 =
                    (packArguments (nextCode :: restCode)).expression.rename (fun index => 1 + mapping index) := by
                  simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
                  congr 1
                  funext index
                  simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
                simpa [renamed] using tailEvaluation
              · simpa only [List.append_assoc] using finalHeap

/-- A failed head skips the rest of the actual compiled argument bundle. -/
theorem arguments_fault {σ : Type} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {sourceEnvironment : Semantics.Environment} {argument : Expr} {rest : List Expr}
    {initial final : Semantics.State σ} {reason : Semantics.Fault}
    (head : ExprSimulation signatures codes locations captured sourceEnvironment argument
      initial (.fault reason) final) :
    ExprsSimulation signatures codes locations captured sourceEnvironment (argument :: rest)
      initial (.fault reason) final := by
  intro safe fuel scope lowered compiled world mapping environment store locals globals heap installed
  cases reason <;> simp only [SafeResult] at safe
  rename_i reason
  simp only [List.mapM_cons] at compiled
  obtain ⟨headCode, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨tailCode, _, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  obtain ⟨extension, target, finalStore, related, evaluation, finalHeap, finalInstalled, frame⟩ :=
    head safe headCompiled locals globals heap installed
  cases related
  cases tailCode with
  | nil =>
      exact ⟨extension, _, finalStore, .language reason, evaluation, finalHeap, finalInstalled, frame⟩
  | cons first remaining =>
      refine ⟨extension, _, finalStore, .language reason, ?_, finalHeap, finalInstalled, frame⟩
      change Core.Evaluates environment store
        ((Core.LocalSequence.pair headCode.type (packArguments (first :: remaining)).type
          headCode.expression (packArguments (first :: remaining)).expression).rename mapping) _ _
      rw [ContextualExpressionCorrespondence.pair_rename]
      exact Core.LocalSequence.pair_left_failure _ _ evaluation

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
  exact continued selected signatureSelected codeFound

theorem call_not_function {σ : Type} {functions : List Function} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {name : String} {sources : List Semantics.Value} {initial final : Semantics.State σ}
    {result : Semantics.Result Semantics.Value}
    (absent : functions.find? (·.name == name) = none) :
    CallSimulation functions signatures codes locations captured name sources initial result final := by
  intro function code index selected
  rw [absent] at selected
  cases selected

/-- A particular call derivation uses only the argument-list IH and its
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
  intro safe fuel scope lowered compiled world mapping environment store locals globals heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      cases eligible with
      | builtin classified notFunction argumentsEligible =>
          have notSignature := (SignatureNames.compiled signaturesCompiled).absent notFunction
          obtain ⟨rfl, computed⟩ := primitive_call_result classified notFunction called
          obtain ⟨expected, argumentCodes, typeCompiled, argumentsCompiled, builtinCompiled⟩ :=
            builtin_components notSignature compiled
          obtain ⟨extension, targets, finalStore, related, argumentsEvaluation, finalHeap, finalInstalled, tailFrame⟩ :=
            argumentsIH.value rfl argumentsCompiled locals globals heap installed
          cases result with
          | value source =>
              obtain ⟨target, resultRelated, resultEvaluation⟩ :=
                builtin_preserves classified typeCompiled builtinCompiled computed related argumentsEvaluation
              exact ⟨extension, .inRight .word target, finalStore, .value resultRelated,
                resultEvaluation, finalHeap, finalInstalled, tailFrame⟩
          | fault reason =>
              cases reason <;> simp only [SafeResult] at safe
              exact (primitive_not_language name type sources _ computed).elim
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
              argumentsEvaluation, argumentHeap, argumentInstalled, argumentFrame⟩ :=
            argumentsIH.value rfl argumentsCompiled (locals.prepend [closure]) (globals.prepend [closure]) heap installed
          have values : ValuesRel code.own.parameters sources targets :=
            argumentTypes ▸ ArgumentsRel.values argumentsRelated
          obtain ⟨callExtension, target, finalStore, related, bodyEvaluation, finalHeap, finalInstalled, tailFrame⟩ :=
            callIH selected foundSignature foundCode safe values argumentHeap argumentInstalled
          exact ⟨argumentExtension ++ callExtension, target, finalStore, related,
            call_evaluates functionEvaluation argumentsEvaluation bodyEvaluation,
            by simpa only [List.append_assoc] using finalHeap, finalInstalled, argumentFrame.trans tailFrame⟩


/-- Failed arguments preserve their actual heap and skip both builtin bodies
and named function invocation. The named closure read still precedes the pack. -/
theorem call_fault {σ : Type} {functions : List Function}
    {compilationFuel : Nat} {signatures : List Signature} {programScope : Scope}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    (signaturesCompiled : functions.mapM (signature compilationFuel) = .ok signatures)
    (codesCompiled : CompiledGlobals compilationFuel signatures programScope (functions.zip signatures).reverse codes)
    {sourceEnvironment : Semantics.Environment} {type : Ty} {name : String} {arguments : List Expr}
    {span : Option Span} {initial final : Semantics.State σ} {reason : Semantics.Fault}
    (eligible : RecursiveExpression functions ⟨type, .call name arguments, span⟩)
    (argumentsIH : ExprsSimulation signatures codes locations captured sourceEnvironment arguments
      initial (.fault reason) final) :
    ExprSimulation signatures codes locations captured sourceEnvironment
      ⟨type, .call name arguments, span⟩ initial (.fault reason) final := by
  intro safe fuel scope lowered compiled world mapping environment store locals globals heap installed
  cases reason <;> simp only [SafeResult] at safe
  rename_i reason
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      cases eligible with
      | builtin classified notFunction argumentsEligible =>
          have notSignature := (SignatureNames.compiled signaturesCompiled).absent notFunction
          obtain ⟨expected, argumentCodes, typeCompiled, argumentsCompiled, builtinCompiled⟩ :=
            builtin_components notSignature compiled
          obtain ⟨extension, target, finalStore, related, argumentsEvaluation, finalHeap, finalInstalled, frame⟩ :=
            argumentsIH safe argumentsCompiled locals globals heap installed
          cases related
          exact ⟨extension, _, finalStore, .language reason,
            BuiltinCorrespondence.argument_failure builtinCompiled argumentsEvaluation,
            finalHeap, finalInstalled, frame⟩
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
          obtain ⟨extension, target, finalStore, related, argumentsEvaluation, finalHeap, finalInstalled, frame⟩ :=
            argumentsIH safe argumentsCompiled (locals.prepend [closure]) (globals.prepend [closure]) heap installed
          cases related
          exact ⟨extension, _, finalStore, .language reason,
            call_argument_failure functionEvaluation argumentsEvaluation,
            finalHeap, finalInstalled, frame⟩

end Solcore.Frontend.RustHull.DerivationCallCorrespondence
