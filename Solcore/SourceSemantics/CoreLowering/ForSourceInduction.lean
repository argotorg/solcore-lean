import Solcore.SourceSemantics.Dynamic

/-! A focused induction principle derived from the independent, mutually
inductive source semantics. The source judgments and their constructors are
unchanged; unrelated expression/call premises receive the trivial motive. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements

open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

/-- Induction on finite source for derivations, retaining the successful
body derivations and the induction hypothesis for each next iteration. -/
theorem for_induction {program : Program}
    (motive : Context → EvidenceEnvironment → TypedSource → Environment → Heap →
      ExpressionId → List ForItemForm → List StatementId → Context → ControlOutcome → Heap → Prop)
    (done : ∀ {context evidence source environment before after condition post body},
      ExpressionEvaluates program context evidence source environment before condition (.bool false) after →
      motive context evidence source environment before condition post body context (.fallthrough environment) after)
    (nextFallthrough : ∀ {context evidence source environment before conditionHeap bodyHeap postHeap after
        condition post body bodyFinalContext postFinalContext bodyEnvironment postEnvironment outcome},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.fallthrough bodyEnvironment) bodyHeap →
      ForItemsExecute program context evidence source environment bodyHeap post postFinalContext postEnvironment postHeap →
      ForLoopExecutes program context evidence source environment postHeap condition post body context outcome after →
      motive context evidence source environment postHeap condition post body context outcome after →
      motive context evidence source environment before condition post body context outcome after)
    (nextContinue : ∀ {context evidence source environment before conditionHeap bodyHeap postHeap after
        condition post body bodyFinalContext postFinalContext bodyEnvironment postEnvironment outcome},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.continuing bodyEnvironment) bodyHeap →
      ForItemsExecute program context evidence source environment bodyHeap post postFinalContext postEnvironment postHeap →
      ForLoopExecutes program context evidence source environment postHeap condition post body context outcome after →
      motive context evidence source environment postHeap condition post body context outcome after →
      motive context evidence source environment before condition post body context outcome after)
    (breaks : ∀ {context evidence source environment before conditionHeap after condition post body bodyFinalContext bodyEnvironment},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.breaking bodyEnvironment) after →
      motive context evidence source environment before condition post body context (.fallthrough environment) after)
    (returns : ∀ {context evidence source environment before conditionHeap after condition post body bodyFinalContext result},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext (.returned result) after →
      motive context evidence source environment before condition post body context (.returned result) after)
    {context evidence source environment before condition post body finalContext outcome after}
    (execution : ForLoopExecutes program context evidence source environment before condition post body finalContext outcome after) :
    motive context evidence source environment before condition post body finalContext outcome after := by
  apply ForLoopExecutes.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_17 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_18 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_19 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_20 := fun context evidence source environment before condition post body finalContext outcome after _ =>
      motive context evidence source environment before condition post body finalContext outcome after)
    (t := execution)
  all_goals intros
  all_goals first
    | exact True.intro
    | solve | apply done; assumption
    | solve | apply nextFallthrough <;> assumption
    | solve | apply nextContinue <;> assumption
    | solve | apply breaks <;> assumption
    | solve | apply returns <;> assumption

/-- Fault induction retains successful prefixes and follows only the first
faulting iteration. -/
theorem for_fault_induction {program : Program}
    (motive : Context → EvidenceEnvironment → TypedSource → Environment → Heap →
      ExpressionId → List ForItemForm → List StatementId → SemanticFault → Heap → Prop)
    (conditionFault : ∀ {context evidence source environment before after condition post body reason},
      ExpressionFaults program context evidence source environment before condition reason after →
      motive context evidence source environment before condition post body reason after)
    (conditionType : ∀ {context evidence source environment before after condition post body value actual},
      ExpressionEvaluates program context evidence source environment before condition value after →
      (¬ BooleanValue value) → ValueRuntimeType value actual →
      motive context evidence source environment before condition post body (.typeMismatch .bool actual) after)
    (bodyFault : ∀ {context evidence source environment before conditionHeap after condition post body finalContext reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsFault program context evidence source environment conditionHeap body finalContext reason after →
      motive context evidence source environment before condition post body reason after)
    (postFallthrough : ∀ {context evidence source environment before conditionHeap bodyHeap after
        condition post body bodyFinalContext bodyEnvironment finalContext reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.fallthrough bodyEnvironment) bodyHeap →
      ForItemsFault program context evidence source environment bodyHeap post finalContext reason after →
      motive context evidence source environment before condition post body reason after)
    (postContinue : ∀ {context evidence source environment before conditionHeap bodyHeap after
        condition post body bodyFinalContext bodyEnvironment finalContext reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.continuing bodyEnvironment) bodyHeap →
      ForItemsFault program context evidence source environment bodyHeap post finalContext reason after →
      motive context evidence source environment before condition post body reason after)
    (nextFallthrough : ∀ {context evidence source environment before conditionHeap bodyHeap postHeap after
        condition post body bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.fallthrough bodyEnvironment) bodyHeap →
      ForItemsExecute program context evidence source environment bodyHeap post postFinalContext postEnvironment postHeap →
      ForLoopFaults program context evidence source environment postHeap condition post body reason after →
      motive context evidence source environment postHeap condition post body reason after →
      motive context evidence source environment before condition post body reason after)
    (nextContinue : ∀ {context evidence source environment before conditionHeap bodyHeap postHeap after
        condition post body bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason},
      ExpressionEvaluates program context evidence source environment before condition (.bool true) conditionHeap →
      StatementsExecute program context evidence source environment conditionHeap body bodyFinalContext
        (.continuing bodyEnvironment) bodyHeap →
      ForItemsExecute program context evidence source environment bodyHeap post postFinalContext postEnvironment postHeap →
      ForLoopFaults program context evidence source environment postHeap condition post body reason after →
      motive context evidence source environment postHeap condition post body reason after →
      motive context evidence source environment before condition post body reason after)
    {context evidence source environment before condition post body reason after}
    (execution : ForLoopFaults program context evidence source environment before condition post body reason after) :
    motive context evidence source environment before condition post body reason after := by
  apply ForLoopFaults.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_17 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_18 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_19 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_20 := fun context evidence source environment before condition post body reason after _ =>
      motive context evidence source environment before condition post body reason after)
    (t := execution)
  all_goals intros
  all_goals first
    | exact True.intro
    | solve | apply conditionFault; assumption
    | solve | apply conditionType <;> assumption
    | solve | apply bodyFault <;> assumption
    | solve | apply postFallthrough <;> assumption
    | solve | apply postContinue <;> assumption
    | solve | apply nextFallthrough <;> assumption
    | solve | apply nextContinue <;> assumption

end Solcore.SourceSemantics.CoreLowering.LoopStatements
