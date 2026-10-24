import Solcore.Frontend.RustHull.NamedCallCorrespondence
import Solcore.Frontend.RustHull.PureFunctionCorrespondence

/-! Structural Hull expressions can contain named calls while retaining their
actual installed function cells. Local and global environments are shifted
together under administrative binders; heap changes remain exact. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContextualExpressionCorrespondence
open Correspondence StatementCorrespondence NamedCallCorrespondence

theorem pure {σ : Type} {functions : List Function}
    (effects : Semantics.ExternalSemantics σ) {signatures : List Signature}
    (names : SignatureNames functions signatures)
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {expression : Expr} (eligible : PureExpression functions expression) :
    ContextualExprPreserves functions effects signatures codes locations captured expression :=
  contextual_of_normal (eligible.preserves effects names (fun _ store => InstalledGlobals codes locations captured store))

private theorem pair_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type : Ty} {left right : Expr}
    {span : Option Span} {sourceValue : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment ⟨type, .pair left right, span⟩
      initial (.value sourceValue) final) :
    ∃ leftValue rightValue middle,
      sourceValue = .pair leftValue rightValue ∧
      Semantics.EvalExpr functions effects sourceEnvironment left initial (.value leftValue) middle ∧
      Semantics.EvalExpr functions effects sourceEnvironment right middle (.value rightValue) final := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases evaluated <;> simp_all
  rename_i middle otherLeft otherRight leftValue rightResult kind first second
  cases rightResult with
  | fault reason => simp [Semantics.Result.map] at resultEq
  | value rightValue =>
      simp only [Semantics.Result.map, Semantics.Result.value.injEq] at resultEq
      exact ⟨leftValue, rightValue, resultEq, middle, first, second⟩

theorem pair_rename (leftType rightType : Core.Ty) (left right : Core.Expr)
    (mapping : Core.Renaming) :
    (Core.LocalSequence.pair leftType rightType left right).rename mapping =
      Core.LocalSequence.pair leftType rightType (left.rename mapping) (right.rename mapping) := by
  simp [Core.LocalSequence.pair, Core.LanguageResult.bind, Core.LanguageResult.success,
    Core.Expr.rename, Core.Renaming.lift]

theorem pair {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {left right : Expr} (leftPreserves : ContextualExprPreserves functions effects signatures codes locations captured left)
    (rightPreserves : ContextualExprPreserves functions effects signatures codes locations captured right)
    (type : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured ⟨type, .pair left right, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨leftValue, rightValue, middle, rfl, leftSource, rightSource⟩ := pair_source evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨leftCode, rightCode, leftCompiled, rightCompiled, rfl⟩ :=
        lowerExpression_pair_components compiled
      obtain ⟨leftExtension, targetLeft, middleStore, leftRelated, leftEvaluation, middleHeap, middleExternal⟩ :=
        leftPreserves leftSource leftCompiled environmentRelated globals heap externalRelated
      have middleEnvironment := (environmentRelated.extendWorld leftExtension).prepend [targetLeft]
      obtain ⟨rightExtension, targetRight, finalStore, rightRelated, rightEvaluation, finalHeap, finalExternal⟩ :=
        rightPreserves rightSource rightCompiled middleEnvironment (globals.prepend [targetLeft]) middleHeap middleExternal
      refine ⟨leftExtension ++ rightExtension, .pair targetLeft targetRight, finalStore,
        .pair leftRelated rightRelated, ?_, ?_, finalExternal⟩
      · have renamed : (rightCode.expression.rename mapping).weakenAt 0 =
            rightCode.expression.rename (fun index => 1 + mapping index) := by
          simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
          congr 1
          funext index
          simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
        change Core.Evaluates environment store
          ((Core.LocalSequence.pair leftCode.type rightCode.type
            leftCode.expression rightCode.expression).rename mapping) _ _
        rw [pair_rename]
        apply Core.LocalSequence.pair_success _ _ leftEvaluation
        simpa [renamed] using rightEvaluation
      · simpa only [List.append_assoc] using finalHeap

private theorem projection_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type : Ty} {operand : Expr}
    {span : Option Span} {sourceValue : Semantics.Value} (right : Bool)
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, if right then .snd operand else .fst operand, span⟩ initial (.value sourceValue) final) :
    ∃ value, Semantics.EvalExpr functions effects sourceEnvironment operand initial (.value value) final ∧
      Semantics.projectResult right value = .value sourceValue := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases right <;> cases evaluated <;> simp_all
  all_goals
    rename_i otherOperand operandResult kind evaluated
    cases operandResult with
    | fault reason => simp [Semantics.Result.bind] at resultEq
    | value value => exact ⟨value, evaluated, rfl⟩

theorem projection {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {operand : Expr} (preserves : ContextualExprPreserves functions effects signatures codes locations captured operand)
    (right : Bool) (type : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured
      ⟨type, if right then .snd operand else .fst operand, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨value, sourceEvaluation, projected⟩ := projection_source right evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, leftType, rightType, operandCompiled, operandType, rfl⟩ :=
        lowerExpression_projection_components right compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
        preserves sourceEvaluation operandCompiled environmentRelated globals heap externalRelated
      rw [operandType] at related
      cases related with
      | pair leftRelated rightRelated =>
          cases right <;> simp only [Semantics.projectResult, Bool.false_eq_true, ↓reduceIte,
            Semantics.Result.value.injEq] at projected ⊢
          all_goals cases projected
          · exact ⟨extension, _, finalStore, leftRelated,
              Core.LanguageResult.bind_success _ evaluation (.inRight (.first (.var rfl))),
              finalHeap, finalExternal⟩
          · exact ⟨extension, _, finalStore, rightRelated,
              Core.LanguageResult.bind_success _ evaluation (.inRight (.second (.var rfl))),
              finalHeap, finalExternal⟩

private theorem injection_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type target : Ty} {operand : Expr}
    {span : Option Span} {sourceValue : Semantics.Value} (right : Bool)
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, if right then .inr target operand else .inl target operand, span⟩
      initial (.value sourceValue) final) :
    ∃ value, Semantics.EvalExpr functions effects sourceEnvironment operand initial (.value value) final ∧
      sourceValue = (if right then .inr value else .inl value) := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases right <;> cases evaluated <;> simp_all
  all_goals
    rename_i otherTarget otherOperand operandResult kind evaluated
    cases operandResult with
    | fault reason => simp [Semantics.Result.bind] at resultEq
    | value value =>
        cases found : Semantics.shape otherTarget with
        | none => simp [Semantics.Result.bind, Semantics.sumInjectionResult, found] at resultEq
        | some shape =>
            cases shape <;> simp [Semantics.Result.bind, Semantics.sumInjectionResult, found] at resultEq
            exact ⟨value, evaluated, resultEq⟩

theorem injection {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {operand : Expr} (preserves : ContextualExprPreserves functions effects signatures codes locations captured operand)
    (right : Bool) (type target : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured
      ⟨type, if right then .inr target operand else .inl target operand, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨value, sourceEvaluation, rfl⟩ := injection_source right evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, leftType, rightType, _, operandCompiled, operandType, rfl⟩ :=
        lowerExpression_injection_components right compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
        preserves sourceEvaluation operandCompiled environmentRelated globals heap externalRelated
      rw [operandType] at related
      cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at related ⊢
      · exact ⟨extension, .inLeft rightType targetValue, finalStore, .inl related,
          Core.LanguageResult.bind_success _ evaluation (.inRight (.inLeft (.var rfl))),
          finalHeap, finalExternal⟩
      · exact ⟨extension, .inRight leftType targetValue, finalStore, .inr related,
          Core.LanguageResult.bind_success _ evaluation (.inRight (.inRight (.var rfl))),
          finalHeap, finalExternal⟩

private theorem conditional_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type target : Ty} {conditionExpr yes no : Expr}
    {span : Option Span} {sourceValue : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .ifThen target conditionExpr yes no, span⟩ initial (.value sourceValue) final) :
    ∃ middle value truth,
      Semantics.EvalExpr functions effects sourceEnvironment conditionExpr initial (.value value) middle ∧
      Semantics.condition? value = some truth ∧
      Semantics.EvalExpr functions effects sourceEnvironment (if truth then yes else no)
        middle (.value sourceValue) final := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases evaluated <;> simp_all
  case ifTrue => exact ⟨_, _, by assumption, Or.inr ⟨by assumption, by assumption⟩⟩
  case ifFalse => exact ⟨_, _, by assumption, Or.inl ⟨by assumption, by assumption⟩⟩

theorem choose_rename (type : Core.Ty) (conditionExpr yes no : Core.Expr) (mapping : Core.Renaming) :
    (Core.LocalControl.choose type conditionExpr yes no).rename mapping =
      Core.LocalControl.choose type (conditionExpr.rename mapping) (yes.rename mapping) (no.rename mapping) := by
  simp [Core.LocalControl.choose, Core.LanguageResult.bind, Core.Expr.rename, Core.Renaming.lift]

theorem conditional {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {conditionExpr yes no : Expr}
    (conditionPreserves : ContextualExprPreserves functions effects signatures codes locations captured conditionExpr)
    (yesPreserves : ContextualExprPreserves functions effects signatures codes locations captured yes)
    (noPreserves : ContextualExprPreserves functions effects signatures codes locations captured no)
    (type target : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured
      ⟨type, .ifThen target conditionExpr yes no, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨middle, conditionValue, truth, conditionSource, tested, branchSource⟩ := conditional_source evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, test, yesCode, noCode, conditionCompiled, testCompiled,
        yesCompiled, noCompiled, yesType, noType, expressionEqual⟩ :=
        lowerExpression_conditional_components compiled
      obtain ⟨conditionExtension, targetCondition, middleStore, conditionRelated,
        conditionEvaluation, middleHeap, middleExternal⟩ :=
        conditionPreserves conditionSource conditionCompiled environmentRelated globals heap externalRelated
      have testEvaluation := ExpressionCorrespondence.condition_evaluates
        testCompiled conditionRelated tested conditionEvaluation
      have middleEnvironment :=
        (environmentRelated.extendWorld conditionExtension).prepend [.bool truth]
      have branchPreserves : ContextualExprPreserves functions effects signatures codes locations captured
          (if truth then yes else no) := by cases truth <;> assumption
      have branchCompiled : lowerExpression fuel signatures scope (if truth then yes else no) =
          .ok (if truth then yesCode else noCode) := by cases truth <;> assumption
      obtain ⟨branchExtension, targetValue, finalStore, related, branchEvaluation, finalHeap, finalExternal⟩ :=
        branchPreserves branchSource branchCompiled middleEnvironment (globals.prepend [.bool truth]) middleHeap middleExternal
      refine ⟨conditionExtension ++ branchExtension, targetValue, finalStore, ?_, ?_, ?_, finalExternal⟩
      · cases truth <;> simpa only [Bool.false_eq_true, ↓reduceIte, yesType, noType] using related
      · have renamed (expression : Core.Expr) : (expression.rename mapping).weakenAt 0 =
            expression.rename (fun index => 1 + mapping index) := by
          simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
          congr 1
          funext index
          simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
        rw [expressionEqual, choose_rename]
        cases truth with
        | false =>
            apply Core.LocalControl.choose_false _ testEvaluation
            simpa [renamed] using branchEvaluation
        | true =>
            apply Core.LocalControl.choose_true _ testEvaluation
            simpa [renamed] using branchEvaluation
      · simpa only [List.append_assoc] using finalHeap

private theorem indexedInjection_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type target : Ty} {operand : Expr} {index : Nat}
    {span : Option Span} {sourceValue : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .inK index target operand, span⟩ initial (.value sourceValue) final) :
    ∃ value, Semantics.EvalExpr functions effects sourceEnvironment operand initial (.value value) final ∧
      Semantics.injectionResult index target value = .value sourceValue := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases evaluated <;> simp_all
  rename_i otherIndex otherTarget otherOperand operandResult kind evaluated
  cases operandResult with
  | fault reason => simp [Semantics.Result.bind] at resultEq
  | value value => exact ⟨value, evaluated, rfl⟩

theorem indexedInjection {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {operand : Expr} (preserves : ContextualExprPreserves functions effects signatures codes locations captured operand)
    (index : Nat) (type target : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured
      ⟨type, .inK index target operand, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨value, sourceEvaluation, sourceResult⟩ := indexedInjection_source evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, targetType, injected, targetCompiled, operandCompiled, injectionCompiled, rfl⟩ :=
        lowerExpression_indexedInjection_components compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
        preserves sourceEvaluation operandCompiled environmentRelated globals heap externalRelated
      obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape targetCompiled
      rw [← targetShape] at injectionCompiled
      have supplied : Core.Evaluates (targetValue :: environment) finalStore
          ((Core.Expr.var 0).rename (Core.Renaming.lift mapping)) targetValue finalStore := .var rfl
      obtain ⟨sourceInjected, targetInjected, sourceInjection, injectionRelated, injectionEvaluation⟩ :=
        PureExpressionCorrespondence.inject_evaluates shape related injectionCompiled supplied
      have same : sourceInjected = sourceValue := by
        simpa [Semantics.injectionResult, Semantics.inject?, sourceShape, sourceInjection] using sourceResult
      subst sourceInjected
      refine ⟨extension, targetInjected, finalStore, ?_, ?_, finalHeap, finalExternal⟩
      · simpa only [targetShape] using injectionRelated
      · exact Core.LanguageResult.bind_success _ evaluation (.inRight injectionEvaluation)

open PureCallCorrespondence ScalarExecution

private theorem exprs_cons {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {argument : Expr} {rest : List Expr} {initial final : Semantics.State σ}
    {sources : List Semantics.Value}
    (evaluated : Semantics.EvalExprs functions effects sourceEnvironment (argument :: rest)
      initial (.value sources) final) :
    ∃ source values middle, sources = source :: values ∧
      Semantics.EvalExpr functions effects sourceEnvironment argument initial (.value source) middle ∧
      Semantics.EvalExprs functions effects sourceEnvironment rest middle (.value values) final := by
  generalize resultEq : Semantics.Result.value sources = result at evaluated
  cases evaluated with
  | cons head tail =>
      rename_i middle source result
      cases result with
      | fault reason => simp [Semantics.Result.map] at resultEq
      | value values =>
          simp only [Semantics.Result.map, Semantics.Result.value.injEq] at resultEq
          exact ⟨source, values, middle, resultEq, head, tail⟩
  | fault => cases resultEq

theorem arguments_preserve {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment} {arguments : List Expr}
    (preserves : ∀ argument ∈ arguments, ContextualExprPreserves functions effects signatures codes locations captured argument)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {sources : List Semantics.Value}
    (evaluated : Semantics.EvalExprs functions effects sourceEnvironment arguments initial (.value sources) final)
    {fuel : Nat} {scope : Scope} {lowered : List Lowered}
    (compiled : arguments.mapM (lowerExpression fuel signatures scope) = .ok lowered)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globals : GlobalEnvironmentRel codes locations scope mapping environment)
    (heap : HeapRel world initial.heap store) (externalRelated : InstalledGlobals codes locations captured store) :
    ∃ extension targets finalStore,
      ArgumentsRel lowered sources targets ∧
      Core.Evaluates environment store ((packArguments lowered).expression.rename mapping)
        (.inRight .word (bundleValues targets)) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  induction arguments generalizing initial final sources lowered world mapping environment store with
  | nil =>
      cases compiled
      cases evaluated
      exact ⟨[], [], store, .nil, .inRight .unit, by simpa using heap, externalRelated⟩
  | cons argument rest ih =>
      obtain ⟨source, sources, middle, rfl, head, tail⟩ := exprs_cons evaluated
      simp only [List.mapM_cons] at compiled
      obtain ⟨headCode, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tailCode, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨headExtension, target, middleStore, related, headEvaluation, middleHeap, middleExternal⟩ :=
        preserves argument (by simp) head headCompiled environmentRelated globals heap externalRelated
      cases rest with
      | nil =>
          cases tailCompiled
          cases tail
          exact ⟨headExtension, [target], middleStore, .cons related .nil,
            headEvaluation, middleHeap, middleExternal⟩
      | cons next rest =>
          have tailPreserves : ∀ value ∈ next :: rest,
              ContextualExprPreserves functions effects signatures codes locations captured value := by
            intro value member
            exact preserves value (by simp [member])
          have middleEnvironment := (environmentRelated.extendWorld headExtension).prepend [target]
          obtain ⟨tailExtension, targets, finalStore, tailRelated, tailEvaluation, finalHeap, finalExternal⟩ :=
            ih tailPreserves tail tailCompiled middleEnvironment (globals.prepend [target]) middleHeap middleExternal
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
            .cons related tailRelated, ?_, ?_, finalExternal⟩
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
                rw [pair_rename]
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

theorem namedCall {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat}
    {captured : Core.Environment} {name : String} {function : Function} {code : GlobalCode} {index : Nat}
    (foundFunction : functions.find? (·.name == name) = some function)
    (foundSignature : signatures.find? (·.name == name) = some code.own)
    (foundCode : codes[index]? = some code)
    (preservesFunction : ∀ sources initial final source,
      FunctionExecutionPreserves functions effects codes locations captured function code index sources initial final source)
    {arguments : List Expr}
    (preservesArguments : ∀ argument ∈ arguments,
      ContextualExprPreserves functions effects signatures codes locations captured argument)
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
        arguments_preserve preservesArguments argumentsSource argumentsCompiled argumentLocals
          (globals.prepend [closure]) heap installed
      have values : ValuesRel code.own.parameters sources targets :=
        argumentTypes ▸ ArgumentsRel.values argumentsRelated
      obtain ⟨callExtension, target, finalStore, related, bodyEvaluation, finalHeap, finalGlobals⟩ :=
        preservesFunction sources middle final sourceValue functionSource values argumentHeap argumentGlobals
      exact ⟨argumentExtension ++ callExtension, target, finalStore, related,
        call_evaluates functionEvaluation argumentsEvaluation bodyEvaluation,
        by simpa only [List.append_assoc] using finalHeap, finalGlobals⟩

private theorem builtin_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {name : String} {type : Ty} {arguments : List Expr}
    {span : Option Span} {source : Semantics.Value} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    (notFunction : functions.find? (·.name == name) = none)
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .call name arguments, span⟩ initial (.value source) final) :
    ∃ values, Semantics.EvalExprs functions effects sourceEnvironment arguments initial (.value values) final ∧
      Semantics.primitive? name type values = some (.value source) := by
  generalize resultEq : Semantics.Result.value source = result at evaluated
  cases evaluated <;> simp_all
  rename_i middle otherName otherArguments values kind argumentsEvaluated called
  cases called with
  | function selected _ =>
      exact (notFunction _ (List.mem_of_find?_eq_some selected)
        (by simpa only [beq_iff_eq] using List.find?_some selected)).elim
  | primitive _ computed => exact ⟨values, argumentsEvaluated, computed⟩
  | external _ notPrimitive _ =>
      have known := pureBuiltin_known classified type values
      rw [notPrimitive] at known
      cases known

private theorem builtin_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
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

/-- A source call to a pure builtin is compositional through the public
expression lowerer. The only induction premises concern its source arguments;
function resolution and the complete builtin dispatch are proved here. -/
theorem builtinCall {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {name : String} {arguments : List Expr} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    (notFunction : functions.find? (·.name == name) = none)
    (notSignature : signatures.find? (·.name == name) = none)
    (preserves : ∀ argument ∈ arguments, ContextualExprPreserves functions effects signatures codes locations captured argument)
    (type : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured ⟨type, .call name arguments, span⟩ := by
  intro sourceEnvironment initial final source evaluated
  obtain ⟨values, argumentsEvaluated, computed⟩ := builtin_source classified notFunction evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨expected, codes, typeCompiled, argumentsCompiled, builtinCompiled⟩ :=
        builtin_components notSignature compiled
      obtain ⟨extension, targets, finalStore, related, argumentsEvaluation, finalHeap, finalExternal⟩ :=
        arguments_preserve preserves argumentsEvaluated argumentsCompiled environmentRelated globals heap externalRelated
      obtain ⟨target, resultRelated, resultEvaluation⟩ :=
        builtin_preserves classified typeCompiled builtinCompiled computed related argumentsEvaluation
      exact ⟨extension, target, finalStore, resultRelated, resultEvaluation, finalHeap, finalExternal⟩

end Solcore.Frontend.RustHull.ContextualExpressionCorrespondence
