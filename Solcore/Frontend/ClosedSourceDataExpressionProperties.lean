import Solcore.Frontend.ClosedSourceDataExpression
import Solcore.Frontend.ClosedSourceEvaluation
import Solcore.Frontend.LocalExpressionEvaluationProperties
import Solcore.Frontend.RuntimeValueProperties

/- Exact actual-output reflection for the common syntax; no evaluator or typing premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem lookup_embed {environment : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

private theorem lookup_reflect (environment : Resolved.Environment) {id : Resolved.LocalId}
    {actual : RuntimeValue}
    (found : Resolved.LocalScope.Lookup
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2))) id actual) :
    ∃ value, actual = RuntimeValue.ofCore value ∧ Resolved.LocalScope.Lookup environment id value := by
  induction environment generalizing actual with
  | nil => cases found
  | cons entry environment ih =>
      obtain ⟨key, value⟩ := entry
      cases found with
      | head => exact ⟨value, rfl, .head⟩
      | tail different found =>
          obtain ⟨value, same, previous⟩ := ih found
          exact ⟨value, same, .tail different previous⟩

private theorem reflect {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (evaluated : ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal) :
    ∃ value finalStore, actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      LocalExpressionEvaluates names environment initialStore source value finalStore := by
  induction fragment generalizing initialStore actualValue actualFinal with
  | reference =>
      cases evaluated with
      | reference named found =>
          obtain ⟨value, same, previous⟩ := lookup_reflect environment found
          exact ⟨value, initialStore, same, rfl, .identifier named previous⟩
      | creation shape => cases shape
  | literal =>
      cases evaluated with
      | wordLiteral meaning => exact ⟨.word _, initialStore,
          by simp only [RuntimeValue.ofCore], rfl, .wordLiteral meaning⟩
      | creation shape => cases shape
  | unit =>
      cases evaluated with
      | unit => exact ⟨.unit, initialStore, by simp only [RuntimeValue.ofCore], rfl, .unit⟩
      | creation shape => cases shape
  | group _ ih =>
      cases evaluated with
      | group child =>
          obtain ⟨value, finalStore, same, finalSame, previous⟩ := ih child
          exact ⟨value, finalStore, same, finalSame, .group previous⟩
      | creation shape => cases shape
  | pair _ _ leftIH rightIH =>
      cases evaluated with
      | pair left right =>
          obtain ⟨leftValue, middleStore, leftSame, middleSame, oldLeft⟩ := leftIH left
          rw [middleSame] at right
          obtain ⟨rightValue, finalStore, rightSame, finalSame, oldRight⟩ := rightIH right
          exact ⟨.pair leftValue rightValue, finalStore,
            by simp only [RuntimeValue.ofCore, leftSame, rightSame], finalSame, .pair oldLeft oldRight⟩
      | creation shape => cases shape
  | many _ _ headIH tailIH =>
      cases evaluated with
      | many head tail =>
          obtain ⟨headValue, middleStore, headSame, middleSame, oldHead⟩ := headIH head
          rw [middleSame] at tail
          obtain ⟨tailValue, finalStore, tailSame, finalSame, oldTail⟩ := tailIH tail
          exact ⟨.pair headValue tailValue, finalStore,
            by simp only [RuntimeValue.ofCore, headSame, tailSame], finalSame, .many oldHead oldTail⟩
      | creation shape => cases shape
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases evaluated with
      | conditionalTrue condition branch =>
          obtain ⟨decision, middleStore, decisionSame, middleSame, oldCondition⟩ := conditionIH condition
          have actualBool : Core.Value.bool true = decision := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using decisionSame)
          cases actualBool
          rw [middleSame] at branch
          obtain ⟨value, finalStore, same, finalSame, oldBranch⟩ := thenIH branch
          exact ⟨value, finalStore, same, finalSame, .ifTrue oldCondition oldBranch⟩
      | conditionalFalse condition branch =>
          obtain ⟨decision, middleStore, decisionSame, middleSame, oldCondition⟩ := conditionIH condition
          have actualBool : Core.Value.bool false = decision := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using decisionSame)
          cases actualBool
          rw [middleSame] at branch
          obtain ⟨value, finalStore, same, finalSame, oldBranch⟩ := elseIH branch
          exact ⟨value, finalStore, same, finalSame, .ifFalse oldCondition oldBranch⟩
      | creation shape => cases shape

  | logicalNot _ ih =>
      cases evaluated with
      | @logicalNot _ _ _ _ _ _ _ _ operandBool child =>
          obtain ⟨value, finalStore, same, finalSame, previous⟩ := ih child
          have actualBool : Core.Value.bool operandBool = value := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using same)
          cases actualBool
          exact ⟨.bool (!operandBool), finalStore,
            by simp only [RuntimeValue.ofCore], finalSame, .logicalNot previous⟩
      | creation shape => cases shape
  | bitNot _ ih =>
      cases evaluated with
      | @bitNot _ _ _ _ _ _ _ _ operandWord child =>
          obtain ⟨value, finalStore, same, finalSame, previous⟩ := ih child
          have actualWord : Core.Value.word operandWord = value := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using same)
          cases actualWord
          exact ⟨.word operandWord.bitNot, finalStore,
            by simp only [RuntimeValue.ofCore], finalSame, .bitNot previous⟩
      | creation shape => cases shape

  | logicalAnd _ _ leftIH rightIH =>
      cases evaluated with
      | andTrue left right =>
          obtain ⟨decision, middleStore, decisionSame, middleSame, oldLeft⟩ := leftIH left
          have actualBool : Core.Value.bool true = decision := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using decisionSame)
          cases actualBool
          rw [middleSame] at right
          obtain ⟨value, finalStore, same, finalSame, oldRight⟩ := rightIH right
          exact ⟨value, finalStore, same, finalSame, .andTrue oldLeft oldRight⟩
      | andFalse left =>
          obtain ⟨decision, finalStore, decisionSame, finalSame, oldLeft⟩ := leftIH left
          have actualBool : Core.Value.bool false = decision := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using decisionSame)
          cases actualBool
          exact ⟨.bool false, finalStore,
            by simp only [RuntimeValue.ofCore], finalSame, .andFalse oldLeft⟩
      | creation shape => cases shape
      | strictWordBinary _ _ meaning => cases meaning
  | logicalOr _ _ leftIH rightIH =>
      cases evaluated with
      | orTrue left =>
          obtain ⟨decision, finalStore, decisionSame, finalSame, oldLeft⟩ := leftIH left
          have actualBool : Core.Value.bool true = decision := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using decisionSame)
          cases actualBool
          exact ⟨.bool true, finalStore,
            by simp only [RuntimeValue.ofCore], finalSame, .orTrue oldLeft⟩
      | orFalse left right =>
          obtain ⟨decision, middleStore, decisionSame, middleSame, oldLeft⟩ := leftIH left
          have actualBool : Core.Value.bool false = decision := RuntimeValue.ofCore_injective
            (by simpa only [RuntimeValue.ofCore] using decisionSame)
          cases actualBool
          rw [middleSame] at right
          obtain ⟨value, finalStore, same, finalSame, oldRight⟩ := rightIH right
          exact ⟨value, finalStore, same, finalSame, .orFalse oldLeft oldRight⟩
      | creation shape => cases shape
      | strictWordBinary _ _ meaning => cases meaning

private theorem embed {source : Syntax.Expr} (fragment : ClosedSourceDataExpression source)
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store} {value : Core.Value}
    (evaluated : LocalExpressionEvaluates names environment initialStore source value finalStore) :
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) source (RuntimeValue.ofCore value)
      (finalStore.map RuntimeValue.ofCore) := by
  induction fragment generalizing initialStore finalStore value with
  | reference =>
      cases evaluated with
      | identifier named found => exact .reference named (lookup_embed found)
  | literal =>
      cases evaluated with
      | wordLiteral meaning => simp only [RuntimeValue.ofCore]; exact .wordLiteral meaning
  | unit => cases evaluated; simp only [RuntimeValue.ofCore]; exact .unit
  | group _ ih =>
      cases evaluated with
      | group child => exact .group (ih child)
  | pair _ _ leftIH rightIH =>
      cases evaluated with
      | pair left right => simp only [RuntimeValue.ofCore]; exact .pair (leftIH left) (rightIH right)
  | many _ _ headIH tailIH =>
      cases evaluated with
      | many head tail => simp only [RuntimeValue.ofCore]; exact .many (headIH head) (tailIH tail)
  | conditional _ _ _ conditionIH thenIH elseIH =>
      cases evaluated with
      | ifTrue condition branch =>
          exact .conditionalTrue (by simpa only [RuntimeValue.ofCore] using conditionIH condition)
            (thenIH branch)
      | ifFalse condition branch =>
          exact .conditionalFalse (by simpa only [RuntimeValue.ofCore] using conditionIH condition)
            (elseIH branch)

  | logicalNot _ ih =>
      cases evaluated with
      | logicalNot child =>
          simp only [RuntimeValue.ofCore]
          exact .logicalNot (by simpa only [RuntimeValue.ofCore] using ih child)
  | bitNot _ ih =>
      cases evaluated with
      | bitNot child =>
          simp only [RuntimeValue.ofCore]
          exact .bitNot (by simpa only [RuntimeValue.ofCore] using ih child)

  | logicalAnd _ _ leftIH rightIH =>
      cases evaluated with
      | andTrue left right =>
          exact .andTrue (by simpa only [RuntimeValue.ofCore] using leftIH left) (rightIH right)
      | andFalse left =>
          simp only [RuntimeValue.ofCore]
          exact .andFalse (by simpa only [RuntimeValue.ofCore] using leftIH left)
  | logicalOr _ _ leftIH rightIH =>
      cases evaluated with
      | orTrue left =>
          simp only [RuntimeValue.ofCore]
          exact .orTrue (by simpa only [RuntimeValue.ofCore] using leftIH left)
      | orFalse left right =>
          exact .orFalse (by simpa only [RuntimeValue.ofCore] using leftIH left) (rightIH right)

/-- Every actual mixed result and whole final store is exactly an old local result's image. -/
theorem ClosedSourceDataExpression.local_evaluates_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {source : Syntax.Expr} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataExpression source) :
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      LocalExpressionEvaluates names environment initialStore source value finalStore := by
  constructor
  · exact reflect fragment
  · rintro ⟨value, finalStore, rfl, rfl, evaluated⟩
    exact embed fragment evaluated

/-- Whole resolution and the exact runtime identity order compose the independent raw bridge. -/
theorem ClosedSourceDataExpression.core_evaluates_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {source : Syntax.Expr} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataExpression source)
    {resolved : Resolved.Expr} {core : Core.Expr}
    (resolution : ResolvesLocalExpression names source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core) :
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
  rw [fragment.local_evaluates_iff]
  constructor
  · rintro ⟨value, finalStore, same, finalSame, evaluated⟩
    exact ⟨value, finalStore, same, finalSame, (resolution.core_evaluates_iff lowered).mp evaluated⟩
  · rintro ⟨value, finalStore, same, finalSame, evaluated⟩
    exact ⟨value, finalStore, same, finalSame, (resolution.core_evaluates_iff lowered).mpr evaluated⟩

end Solcore.Frontend
