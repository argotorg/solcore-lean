import Solcore.Frontend.RustHull.DerivationCorrespondenceSupport
import Solcore.Frontend.RustHull.PatternCorrespondence

/-! Independent match alternatives drive the actual emitted pattern tests and
binder allocation. Rejected alternatives keep the heap; a selected alternative
allocates exactly its source binder before running the existing statement IH. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MatchDerivationCorrespondence
open Correspondence DerivationCorrespondence StatementCorrespondence

/-- The scrutinee is already evaluated and resides at the compiler's temporary
slot. The relation follows the particular independent alternative derivation. -/
def AlternativesSimulation {σ : Type} (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (sourceType : Ty) (sourceValue : Semantics.Value)
    (alternatives : List Alt) (initial : Semantics.State σ) (control : Semantics.Control)
    (final : Semantics.State σ) : Prop :=
  SafeControl control →
  ∀ {typeFuel targetType}, lowerType typeFuel sourceType = .ok targetType →
  ∀ {fuel scope result loops expression},
    lowerAlternatives fuel signatures scope result loops targetType alternatives = .ok expression →
  ∀ {world mapping environment store targetValue},
    ValueRel targetType sourceValue targetValue → environment[mapping 0]? = some targetValue →
    EnvironmentRel world sourceEnvironment scope mapping environment →
    GlobalEnvironmentRel codes locations scope mapping environment →
    HeapRel world initial.heap store → InstalledGlobals codes locations captured store →
    ∃ extension target finalStore,
      ControlRel result control target ∧ Core.Evaluates environment store (expression.rename mapping) target finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧
      InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore

def AlternativesMotive {σ : Type} (functions : List Function) (signatures : List Signature)
    (codes : List GlobalCode) (locations : Nat → Nat) (captured : Core.Environment)
    (sourceEnvironment : Semantics.Environment) (sourceType : Ty) (sourceValue : Semantics.Value)
    (alternatives : List Alt) (initial : Semantics.State σ) (control : Semantics.Control)
    (final : Semantics.State σ) : Prop :=
  (∀ alternative ∈ alternatives, ∀ statement ∈ alternative.body, RecursiveStatement functions statement) →
  AlternativesSimulation signatures codes locations captured sourceEnvironment sourceType sourceValue
    alternatives initial control final

private theorem alternatives_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result target : Core.Ty} {loops : Nat} {alternative : Alt} {rest : List Alt} {expression : Core.Expr}
    (compiled : lowerAlternatives (fuel + 1) signatures scope result loops target
      (alternative :: rest) = .ok expression) :
    ∃ payload test body next,
      alternative.binder.startsWith Effects.reservedPrefix = false ∧
      testPattern target alternative.pat.kind = .ok (payload, test) ∧
      lowerStatements fuel signatures ((scope.temporary payload).addLocal alternative.binder payload)
        result loops alternative.body = .ok body ∧
      lowerAlternatives fuel signatures scope result loops target rest = .ok next ∧
      expression = .caseE (test (.var 0)) (next.weakenAt 0)
        (.letE (Core.OptionalCell.allocateInitialized payload (.var 0)) body) := by
  simp only [lowerAlternatives] at compiled
  have allowed : alternative.binder.startsWith Effects.reservedPrefix = false := by
    cases found : alternative.binder.startsWith Effects.reservedPrefix
    · rfl
    · simp [found, fail, Bind.bind, Except.bind] at compiled
  simp only [allowed, Bool.false_eq_true, ↓reduceIte] at compiled
  obtain ⟨⟨payload, test⟩, tested, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨body, bodyCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨next, nextCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  exact ⟨payload, test, body, next, allowed, tested, bodyCompiled, nextCompiled, rfl⟩

private theorem statement_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {result : Core.Ty} {loops : Nat} {target : Ty} {scrutinee : Expr} {alternatives : List Alt}
    {span : Option Span} {expression : Core.Expr}
    (compiled : lowerStatement (fuel + 1) signatures scope result loops
      ⟨.matchStmt target scrutinee alternatives, span⟩ = .ok expression) :
    ∃ targetType value arms,
      lowerType fuel target = .ok targetType ∧
      lowerExpression fuel signatures scope scrutinee = .ok value ∧
      targetType = value.type ∧
      lowerAlternatives fuel signatures (scope.temporary targetType) result loops targetType alternatives = .ok arms ∧
      expression = Core.LanguageResult.bind (Core.LocalLoop.controlType result) value.expression arms := by
  simp only [lowerStatement] at compiled
  obtain ⟨targetType, typeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨value, valueCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨checked, typeChecked, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  obtain ⟨arms, armsCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
  cases returned
  exact ⟨targetType, value, arms, typeCompiled, valueCompiled,
    expectType_eq_of_ok typeChecked, armsCompiled, rfl⟩

variable {σ : Type} {signatures : List Signature} {codes : List GlobalCode}
  {locations : Nat → Nat} {captured : Core.Environment} {sourceEnvironment : Semantics.Environment}

/-- Exhausted alternatives fall through without allocating a binder. -/
theorem nil {sourceType : Ty} {sourceValue : Semantics.Value} {state : Semantics.State σ} :
    AlternativesSimulation signatures codes locations captured sourceEnvironment sourceType sourceValue
      [] state .fallthrough state := by
  intro _ typeFuel targetType _ fuel scope result loops expression compiled world mapping environment store
    targetValue _ _ _ _ heap installed
  cases fuel with
  | zero => simp [lowerAlternatives, fail] at compiled
  | succ fuel =>
      simp only [lowerAlternatives] at compiled
      cases compiled
      exact ⟨[], _, store, .fallthrough, by
        simpa only [rename_fallthrough] using Core.LocalLoop.fallthrough_evaluates result environment store,
        by simpa only [List.append_nil] using heap, installed, ClosuresPreserved.refl store⟩

/-- A selected alternative binds its actual payload and retains the added cell
through arbitrary calls, loops, return or language failure in its body. -/
theorem matched {sourceType : Ty} {sourceValue payload : Semantics.Value}
    {alternative : Alt} {rest : List Alt} {initial final : Semantics.State σ} {control : Semantics.Control}
    (selected : Semantics.patternPayload? sourceType alternative.pat.kind sourceValue = some payload)
    (continued : StatementsSimulation signatures codes locations captured
      ((alternative.binder, initial.heap.length) :: sourceEnvironment) alternative.body
      (Semantics.allocate initial payload).2 control final) :
    AlternativesSimulation signatures codes locations captured sourceEnvironment sourceType sourceValue
      (alternative :: rest) initial control final := by
  intro safe typeFuel targetType typeCompiled fuel scope result loops expression compiled world mapping environment store
    targetValue related found locals globals heap installed
  cases fuel with
  | zero => simp [lowerAlternatives, fail] at compiled
  | succ fuel =>
      obtain ⟨payloadType, test, body, next, allowed, patternCompiled, bodyCompiled, _, rfl⟩ :=
        alternatives_components compiled
      obtain ⟨observed, patternRelated, patternEvaluated⟩ :=
        PatternCorrespondence.test_preserves (value := .var 0) (mapping := mapping)
          (store := store) typeCompiled related patternCompiled (.var found)
      rw [selected] at patternRelated
      cases patternRelated with
      | matched payloadRelated =>
          rename_i targetPayload
          have allocated := heap.allocate payloadRelated
          have entry : (world ++ [(payloadType, store.length)])[initial.heap.length]? =
              some (payloadType, store.length) := by
            rw [← heap.length_eq, List.getElem?_concat_length]
          have bodyLocals :=
            ((locals.extendWorld [(payloadType, store.length)]).temporary payloadType targetPayload).addLocal
              alternative.binder payloadType initial.heap.length store.length entry
          have bodyGlobals := (globals.temporary payloadType targetPayload).addLocal
            alternative.binder payloadType (.cellRef (Core.OptionalCell.cellType payloadType) store.length) allowed
          obtain ⟨extension, target, finalStore, controlRelated, bodyEvaluated, finalHeap, finalInstalled, frame⟩ :=
            continued safe bodyCompiled bodyLocals bodyGlobals allocated (installed.append _)
          refine ⟨[(payloadType, store.length)] ++ extension, target, finalStore, controlRelated,
            ?_, ?_, finalInstalled, ClosuresPreserved.trans (ClosuresPreserved.append _ _) frame⟩
          · exact .caseRight patternEvaluated
              (.letE (Core.OptionalCell.allocateInitialized_evaluates (.var rfl)) bodyEvaluated)
          · simpa only [List.append_assoc] using finalHeap

/-- Rejected patterns introduce only the case binder, whose renaming preserves
the same scrutinee and lexical environment for the remaining alternatives. -/
theorem next {sourceType : Ty} {sourceValue : Semantics.Value}
    {alternative : Alt} {rest : List Alt} {initial final : Semantics.State σ} {control : Semantics.Control}
    (rejected : Semantics.patternPayload? sourceType alternative.pat.kind sourceValue = none)
    (continued : AlternativesSimulation signatures codes locations captured sourceEnvironment sourceType sourceValue
      rest initial control final) :
    AlternativesSimulation signatures codes locations captured sourceEnvironment sourceType sourceValue
      (alternative :: rest) initial control final := by
  intro safe typeFuel targetType typeCompiled fuel scope result loops expression compiled world mapping environment store
    targetValue related found locals globals heap installed
  cases fuel with
  | zero => simp [lowerAlternatives, fail] at compiled
  | succ fuel =>
      obtain ⟨payloadType, test, body, next, _, patternCompiled, _, nextCompiled, rfl⟩ :=
        alternatives_components compiled
      obtain ⟨observed, patternRelated, patternEvaluated⟩ :=
        PatternCorrespondence.test_preserves (value := .var 0) (mapping := mapping)
          (store := store) typeCompiled related patternCompiled (.var found)
      rw [rejected] at patternRelated
      cases patternRelated with
      | missed =>
          have shiftedFound : (Core.Value.unit :: environment)[1 + mapping 0]? = some targetValue := by
            simpa [Nat.add_comm] using found
          obtain ⟨extension, target, finalStore, controlRelated, nextEvaluated, finalHeap, finalInstalled, frame⟩ :=
            continued safe typeCompiled nextCompiled related shiftedFound
              (locals.prepend [.unit]) (globals.prepend [.unit]) heap installed
          refine ⟨extension, target, finalStore, controlRelated, ?_, finalHeap, finalInstalled, frame⟩
          apply Core.Evaluates.caseLeft patternEvaluated
          have renamed : (next.weakenAt 0).rename (Core.Renaming.lift mapping) =
              next.rename (fun index => 1 + mapping index) := by
            rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
            congr 1
            funext index
            simp [Core.Renaming.comp, Core.Renaming.insertion, Core.Renaming.lift, Nat.add_comm]
          simpa only [renamed, List.length_cons, List.length_nil, Nat.zero_add,
            List.cons_append, List.nil_append] using nextEvaluated

/-- The actual match compiler first evaluates the scrutinee, then runs the
independent alternative derivation in its exact temporary scope. -/
theorem statement {statement : Stmt} {sourceType : Ty} {scrutinee : Expr} {alternatives : List Alt}
    {initial middle final : Semantics.State σ} {sourceValue : Semantics.Value} {control : Semantics.Control}
    (kind : statement.kind = .matchStmt sourceType scrutinee alternatives)
    (tested : ExprSimulation signatures codes locations captured sourceEnvironment scrutinee initial (.value sourceValue) middle)
    (selected : AlternativesSimulation signatures codes locations captured sourceEnvironment sourceType sourceValue
      alternatives middle control final) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial control final := by
  intro safe fuel scope result loops expression compiled world mapping environment store locals globals heap installed
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨targetType, value, arms, typeCompiled, valueCompiled, same, armsCompiled, rfl⟩ :=
        statement_components compiled
      obtain ⟨firstExtension, targetValue, middleStore, related, evaluated, middleHeap, middleInstalled, firstFrame⟩ :=
        tested.value rfl valueCompiled locals globals heap installed
      obtain ⟨extension, target, finalStore, controlRelated, armsEvaluated, finalHeap, finalInstalled, frame⟩ :=
        selected safe typeCompiled armsCompiled (same ▸ related) rfl
          ((locals.extendWorld firstExtension).temporary targetType targetValue)
          (globals.temporary targetType targetValue) middleHeap middleInstalled
      exact ⟨firstExtension ++ extension, target, finalStore, controlRelated,
        Core.LanguageResult.bind_success _ evaluated armsEvaluated,
        by simpa only [List.append_assoc] using finalHeap, finalInstalled, firstFrame.trans frame⟩

/-- A failed scrutinee skips every pattern and binder allocation. -/
theorem fault {statement : Stmt} {sourceType : Ty} {scrutinee : Expr} {alternatives : List Alt}
    {initial final : Semantics.State σ} {reason : Semantics.Fault}
    (kind : statement.kind = .matchStmt sourceType scrutinee alternatives)
    (tested : ExprSimulation signatures codes locations captured sourceEnvironment scrutinee initial (.fault reason) final) :
    StmtSimulation signatures codes locations captured sourceEnvironment statement initial (.fault reason) final := by
  intro safe fuel scope result loops expression compiled world mapping environment store locals globals heap installed
  obtain ⟨reason, rfl⟩ := (safeControl_fault_iff reason).mp safe
  cases statement with | mk statementKind span =>
  cases kind
  cases fuel with
  | zero => simp [lowerStatement, fail] at compiled
  | succ fuel =>
      obtain ⟨targetType, value, arms, _, valueCompiled, _, _, rfl⟩ := statement_components compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluated, finalHeap, finalInstalled, frame⟩ :=
        tested trivial valueCompiled locals globals heap installed
      cases related
      exact ⟨extension, _, finalStore, .language reason,
        Core.LanguageResult.bind_failure _ evaluated, finalHeap, finalInstalled, frame⟩

end Solcore.Frontend.RustHull.MatchDerivationCorrespondence
