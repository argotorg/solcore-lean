import Solcore.Frontend.ClosedSourceEvaluationCompatibility
import Solcore.Frontend.StrictWordBinaryProperties
import Solcore.Frontend.SourceLambdaEvaluationProperties
import Solcore.Frontend.SourceComputationBodyEvaluationProperties
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Resolved.LocalScopeProperties

/- One joint induction closes expression determinism without opaque callback
laws. Body determinism is subsequently derived through exact compatibility. -/
set_option autoImplicit false
namespace Solcore.Frontend

set_option doc.verso true in
/-- Two successful source-expression evaluations with the same owner, names,
captured values, initial store, and expression agree on the result and final
store. No external child law, typing premise, or termination assumption is
needed. Expression and body cases are handled together.
-/
theorem ClosedSourceExpressionEvaluates.deterministic
    {owner names captured initialStore source left right leftStore rightStore}
    (first : ClosedSourceExpressionEvaluates owner names captured initialStore source left leftStore)
    (second : ClosedSourceExpressionEvaluates owner names captured initialStore source right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction first using ClosedSourceExpressionEvaluates.rec
    (motive_2 := fun owner names captured store source value finalStore _ =>
      ∀ {right rightStore}, ClosedSourceBodyEvaluates owner names captured store source right rightStore →
        value = right ∧ finalStore = rightStore) generalizing right rightStore with
  | reference named found =>
      cases second with
      | reference otherNamed otherFound =>
          cases named.id_unique otherNamed
          exact ⟨found.value_unique otherFound, rfl⟩
      | creation shape => cases shape
  | unit =>
      cases second with
      | unit => exact ⟨rfl, rfl⟩
      | creation shape => cases shape
  | wordLiteral meaning =>
      cases second with
      | wordLiteral otherMeaning =>
          cases meaning.value_unique otherMeaning
          exact ⟨rfl, rfl⟩
      | creation shape => cases shape
  | group _ ih =>
      cases second with
      | group child => exact ih child
      | creation shape => cases shape
  | pair _ _ leftIH rightIH =>
      cases second with
      | pair otherLeft otherRight =>
          obtain ⟨rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, rfl⟩ := rightIH otherRight
          exact ⟨rfl, rfl⟩
      | creation shape => cases shape
  | many _ _ headIH tailIH =>
      cases second with
      | many otherHead otherTail =>
          obtain ⟨rfl, rfl⟩ := headIH otherHead
          obtain ⟨rfl, rfl⟩ := tailIH otherTail
          exact ⟨rfl, rfl⟩
      | creation shape => cases shape
  | creation shape =>
      cases shape <;> cases second with
      | creation _ => exact ⟨rfl, rfl⟩
  | call shape _ _ _ calleeIH argumentIH bodyIH =>
      cases second with
      | creation shape => cases shape
      | call otherShape otherCallee otherArgument otherBody =>
          obtain ⟨sameCallee, sameStore⟩ := calleeIH otherCallee
          cases sameCallee
          cases sameStore
          obtain ⟨rfl, rfl⟩ := argumentIH otherArgument
          have sameShape := Prod.mk.inj (Option.some.inj
            ((sourceUnaryLambdaShape?_iff.mpr shape).symm.trans
              (sourceUnaryLambdaShape?_iff.mpr otherShape)))
          obtain ⟨rfl, rfl⟩ := sameShape
          exact bodyIH otherBody
  | conditionalTrue _ _ conditionIH branchIH =>
      cases second with
      | creation shape => cases shape
      | conditionalTrue otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := conditionIH otherCondition
          exact branchIH otherBranch
      | conditionalFalse otherCondition _ => cases (conditionIH otherCondition).1
  | conditionalFalse _ _ conditionIH branchIH =>
      cases second with
      | creation shape => cases shape
      | conditionalTrue otherCondition _ => cases (conditionIH otherCondition).1
      | conditionalFalse otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := conditionIH otherCondition
          exact branchIH otherBranch
  | logicalNot _ ih =>
      cases second with
      | creation shape => cases shape
      | logicalNot child =>
          obtain ⟨same, sameStore⟩ := ih child
          cases RuntimeValue.bool.inj same
          cases sameStore
          exact ⟨rfl, rfl⟩
  | bitNot _ ih =>
      cases second with
      | creation shape => cases shape
      | bitNot child =>
          obtain ⟨same, sameStore⟩ := ih child
          cases RuntimeValue.word.inj same
          cases sameStore
          exact ⟨rfl, rfl⟩
  | andTrue _ _ leftIH rightIH =>
      cases second with
      | creation shape => cases shape
      | andTrue otherLeft otherRight =>
          obtain ⟨_, rfl⟩ := leftIH otherLeft
          exact rightIH otherRight
      | andFalse otherLeft => cases (leftIH otherLeft).1
      | strictWordBinary otherLeft _ _ => cases (leftIH otherLeft).1
  | andFalse _ leftIH =>
      cases second with
      | creation shape => cases shape
      | andTrue otherLeft _ => cases (leftIH otherLeft).1
      | andFalse otherLeft => exact leftIH otherLeft
      | strictWordBinary otherLeft _ _ => cases (leftIH otherLeft).1
  | orTrue _ leftIH =>
      cases second with
      | creation shape => cases shape
      | orTrue otherLeft => exact leftIH otherLeft
      | orFalse otherLeft _ => cases (leftIH otherLeft).1
      | strictWordBinary otherLeft _ _ => cases (leftIH otherLeft).1
  | orFalse _ _ leftIH rightIH =>
      cases second with
      | creation shape => cases shape
      | orTrue otherLeft => cases (leftIH otherLeft).1
      | orFalse otherLeft otherRight =>
          obtain ⟨_, rfl⟩ := leftIH otherLeft
          exact rightIH otherRight
      | strictWordBinary otherLeft _ _ => cases (leftIH otherLeft).1
  | strictWordBinary _ _ meaning leftIH rightIH =>
      cases second with
      | creation shape => cases shape
      | andTrue otherLeft _ => cases (leftIH otherLeft).1
      | andFalse otherLeft => cases (leftIH otherLeft).1
      | orTrue otherLeft => cases (leftIH otherLeft).1
      | orFalse otherLeft _ => cases (leftIH otherLeft).1
      | strictWordBinary otherLeft otherRight otherMeaning =>
          obtain ⟨sameLeft, rfl⟩ := leftIH otherLeft
          cases RuntimeValue.word.inj sameLeft
          obtain ⟨sameRight, rfl⟩ := rightIH otherRight
          cases RuntimeValue.word.inj sameRight
          cases meaning.value_unique otherMeaning
          exact ⟨rfl, rfl⟩
  | bare =>
      rename_i right rightStore other
      cases other
      exact ⟨rfl, rfl⟩
  | expression _ ih =>
      rename_i right rightStore other
      cases other with
      | expression otherChild => exact ih otherChild
  | block _ ih =>
      rename_i right rightStore other
      cases other with
      | block otherBody => exact ih otherBody
  | binding _ _ initializerIH tailIH =>
      rename_i right rightStore other
      cases other with
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := initializerIH otherInitializer
          exact tailIH otherTail
  | inferred _ _ initializerIH tailIH =>
      rename_i right rightStore other
      cases other with
      | inferred otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := initializerIH otherInitializer
          exact tailIH otherTail
  | discard _ _ expressionIH tailIH =>
      rename_i right rightStore other
      cases other with
      | discard otherExpression otherTail =>
          obtain ⟨_, rfl⟩ := expressionIH otherExpression
          exact tailIH otherTail
  | ifTrue _ _ conditionIH branchIH =>
      rename_i right rightStore other
      cases other with
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := conditionIH otherCondition
          exact branchIH otherBranch
      | ifFalse otherCondition _ => cases (conditionIH otherCondition).1
  | ifFalse _ _ conditionIH branchIH =>
      rename_i right rightStore other
      cases other with
      | ifTrue otherCondition _ => cases (conditionIH otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := conditionIH otherCondition
          exact branchIH otherBranch
  | wordMatch _ choice _ scrutineeIH branchIH =>
      rename_i right rightStore other
      cases other with
      | wordMatch otherScrutinee otherChoice otherBranch =>
          obtain ⟨rfl, rfl⟩ := scrutineeIH otherScrutinee
          obtain ⟨rfl, rfl⟩ := choice.deterministic otherChoice
          exact branchIH otherBranch

/-- Body uniqueness derived from exact compatibility and closed child determinism. -/
theorem ClosedSourceBodyEvaluates.deterministic
    {owner names captured initialStore source left right leftStore rightStore}
    (first : ClosedSourceBodyEvaluates owner names captured initialStore source left leftStore)
    (second : ClosedSourceBodyEvaluates owner names captured initialStore source right rightStore) :
    left = right ∧ leftStore = rightStore :=
  SourceComputationBodyEvaluates.deterministic ClosedSourceExpressionEvaluates.deterministic
    (closedSourceBodyEvaluates_iff.mp first) (closedSourceBodyEvaluates_iff.mp second)

end Solcore.Frontend
