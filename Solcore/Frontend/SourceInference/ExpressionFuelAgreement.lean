import Solcore.Frontend.SourceInference.PatternFuelAgreement

/-! Successful structural inference keeps the complete result when its
recursion budget increases. All original state and metadata remain exact. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
namespace Solcore.Frontend.SourceInference.Detail
open TypeSystem

private def Stable {α : Type} (action : Nat → Except Error α) (fuel : Nat) : Prop :=
  ∀ extra result, action fuel = .ok result → action (fuel + extra) = .ok result

private theorem inference_stable :
    (∀ fuel context expression expected state, Stable (fun budget => inferExprFuel budget context expression expected state) fuel) ∧
    (∀ fuel context source id instantiation arguments expected state, Stable (fun budget => inferConstructorApplicationFuel budget context source id instantiation arguments expected state) fuel) ∧
    (∀ fuel context sources expected state, Stable (fun budget => inferConstructorArgumentsFuel budget context sources expected state) fuel) ∧
    (∀ fuel context statements expectedReturn state, Stable (fun budget => inferStatementsFuel budget context statements expectedReturn state) fuel) ∧
    (∀ fuel context statement expectedReturn state, Stable (fun budget => inferStatementFuel budget context statement expectedReturn state) fuel) ∧
    (∀ fuel context items state, Stable (fun budget => inferForItemsFuel budget context items state) fuel) ∧
    (∀ fuel context item state, Stable (fun budget => inferForItemFuel budget context item state) fuel) ∧
    (∀ fuel context target state, Stable (fun budget => inferPlaceFuel budget context target state) fuel) ∧
    (∀ fuel context target operator value state, Stable (fun budget => inferAssignedValueFuel budget context target operator value state) fuel) ∧
    (∀ fuel context expressions state, Stable (fun budget => inferExprsFuel budget context expressions state) fuel) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state, Stable (fun budget => inferMatchCasesFuel budget context scrutineeType expectedReturn outerScope cases state) fuel) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      Stable (fun budget => inferExprFuel budget context expression expected state) fuel)
    (motive2 := fun fuel context source id instantiation arguments expected state =>
      Stable (fun budget => inferConstructorApplicationFuel budget context source id instantiation arguments expected state) fuel)
    (motive3 := fun fuel context sources expected state =>
      Stable (fun budget => inferConstructorArgumentsFuel budget context sources expected state) fuel)
    (motive4 := fun fuel context statements expectedReturn state =>
      Stable (fun budget => inferStatementsFuel budget context statements expectedReturn state) fuel)
    (motive5 := fun fuel context statement expectedReturn state =>
      Stable (fun budget => inferStatementFuel budget context statement expectedReturn state) fuel)
    (motive6 := fun fuel context items state =>
      Stable (fun budget => inferForItemsFuel budget context items state) fuel)
    (motive7 := fun fuel context item state =>
      Stable (fun budget => inferForItemFuel budget context item state) fuel)
    (motive8 := fun fuel context target state =>
      Stable (fun budget => inferPlaceFuel budget context target state) fuel)
    (motive9 := fun fuel context target operator value state =>
      Stable (fun budget => inferAssignedValueFuel budget context target operator value state) fuel)
    (motive10 := fun fuel context expressions state =>
      Stable (fun budget => inferExprsFuel budget context expressions state) fuel)
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope cases state =>
      Stable (fun budget => inferMatchCasesFuel budget context scrutineeType expectedReturn outerScope cases state) fuel)
  case case23 =>
    intro fuel context source id instantiation arguments expected state arity children
    unfold Stable at *
    intro extra result accepted
    unfold inferConstructorApplicationFuel at accepted ⊢
    simp only [arity, ↓reduceIte] at accepted ⊢
    simp_all [bind, Except.bind, pure, Except.pure]
    repeat' first | split at accepted
    all_goals try contradiction
    all_goals grind
  case case44 =>
    intro context statement expectedReturn state fuel id allocated allocation
      scrutinees arms form sources many casesInduction defaultInduction expressionsInduction
    have casesByType := fun type state =>
      casesInduction ⟨state.allocateExpressionId.fst, type⟩ state
    clear casesInduction
    unfold Stable at *
    intro extra result accepted
    simp only [Nat.succ_add] at *
    unfold inferStatementFuel at accepted ⊢
    simp_all [bind, Except.bind, pure, Except.pure]
    repeat' first | split at accepted
    all_goals try cases accepted
    all_goals try simp_all
    all_goals grind
  case case70 =>
    intro fuel context target operator value state placeInduction valueInduction
    unfold Stable at *
    intro extra result accepted
    unfold inferAssignedValueFuel at accepted ⊢
    cases found : inferPlaceFuel fuel context target state with
    | error error => simp [found, bind, Except.bind] at accepted
    | ok output =>
        have larger := placeInduction extra output found
        have valueAtTarget := valueInduction output.1
        clear valueInduction
        simp only [found, larger, bind, Except.bind] at accepted ⊢
        cases operator <;> simp_all [pure, Except.pure]
        all_goals repeat' first | split at accepted
        all_goals try cases accepted
        all_goals grind
  all_goals
    intros
    unfold Stable at *
    intro extra result accepted
    simp only [Nat.succ_add] at *
    first
      | unfold inferExprFuel at accepted ⊢
      | unfold inferConstructorApplicationFuel at accepted ⊢
      | unfold inferConstructorArgumentsFuel at accepted ⊢
      | unfold inferStatementsFuel at accepted ⊢
      | unfold inferStatementFuel at accepted ⊢
      | unfold inferForItemsFuel at accepted ⊢
      | unfold inferForItemFuel at accepted ⊢
      | unfold inferPlaceFuel at accepted ⊢
      | unfold inferAssignedValueFuel at accepted ⊢
      | unfold inferExprsFuel at accepted ⊢
      | unfold inferMatchCasesFuel at accepted ⊢
    simp_all [bind, Except.bind, pure, Except.pure]
    repeat' first | split at accepted
    all_goals try cases accepted
    all_goals try simp_all
    all_goals grind [inferMatchPatternFuel_success_mono]

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferExprFuel_success_mono
    {fuel : Nat} {context : Context}
    {expression : Syntax.Expr}
    {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (accepted : inferExprFuel fuel context expression expected state = .ok result)
    (extra : Nat) :
    inferExprFuel (fuel + extra) context expression expected state = .ok result :=
  inference_stable.1 fuel context expression expected state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferConstructorApplicationFuel_success_mono
    {fuel : Nat} {context : Context}
    {source : Syntax.Expr}
    {id : ExpressionId}
    {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr}
    {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (accepted : inferConstructorApplicationFuel fuel context source id instantiation arguments expected state = .ok result)
    (extra : Nat) :
    inferConstructorApplicationFuel (fuel + extra) context source id instantiation arguments expected state = .ok result :=
  inference_stable.2.1 fuel context source id instantiation arguments expected state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferConstructorArgumentsFuel_success_mono
    {fuel : Nat} {context : Context}
    {sources : List Syntax.Expr}
    {expected : List Ty}
    {state : State} {result : List InferredExpression × State}
    (accepted : inferConstructorArgumentsFuel fuel context sources expected state = .ok result)
    (extra : Nat) :
    inferConstructorArgumentsFuel (fuel + extra) context sources expected state = .ok result :=
  inference_stable.2.2.1 fuel context sources expected state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferStatementsFuel_success_mono
    {fuel : Nat} {context : Context}
    {statements : List Syntax.Statement}
    {expectedReturn : Ty}
    {state : State} {result : BlockResult}
    (accepted : inferStatementsFuel fuel context statements expectedReturn state = .ok result)
    (extra : Nat) :
    inferStatementsFuel (fuel + extra) context statements expectedReturn state = .ok result :=
  inference_stable.2.2.2.1 fuel context statements expectedReturn state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferStatementFuel_success_mono
    {fuel : Nat} {context : Context}
    {statement : Syntax.Statement}
    {expectedReturn : Ty}
    {state : State} {result : StatementResult}
    (accepted : inferStatementFuel fuel context statement expectedReturn state = .ok result)
    (extra : Nat) :
    inferStatementFuel (fuel + extra) context statement expectedReturn state = .ok result :=
  inference_stable.2.2.2.2.1 fuel context statement expectedReturn state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferForItemsFuel_success_mono
    {fuel : Nat} {context : Context}
    {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context items state = .ok result)
    (extra : Nat) :
    inferForItemsFuel (fuel + extra) context items state = .ok result :=
  inference_stable.2.2.2.2.2.1 fuel context items state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferForItemFuel_success_mono
    {fuel : Nat} {context : Context}
    {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (accepted : inferForItemFuel fuel context item state = .ok result)
    (extra : Nat) :
    inferForItemFuel (fuel + extra) context item state = .ok result :=
  inference_stable.2.2.2.2.2.2.1 fuel context item state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferPlaceFuel_success_mono
    {fuel : Nat} {context : Context}
    {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (accepted : inferPlaceFuel fuel context target state = .ok result)
    (extra : Nat) :
    inferPlaceFuel (fuel + extra) context target state = .ok result :=
  inference_stable.2.2.2.2.2.2.2.1 fuel context target state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferAssignedValueFuel_success_mono
    {fuel : Nat} {context : Context}
    {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp}
    {value : Syntax.Expr}
    {state : State} {result : AssignmentResolution × InferredExpression × State}
    (accepted : inferAssignedValueFuel fuel context target operator value state = .ok result)
    (extra : Nat) :
    inferAssignedValueFuel (fuel + extra) context target operator value state = .ok result :=
  inference_stable.2.2.2.2.2.2.2.2.1 fuel context target operator value state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferExprsFuel_success_mono
    {fuel : Nat} {context : Context}
    {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (accepted : inferExprsFuel fuel context expressions state = .ok result)
    (extra : Nat) :
    inferExprsFuel (fuel + extra) context expressions state = .ok result :=
  inference_stable.2.2.2.2.2.2.2.2.2.1 fuel context expressions state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferMatchCasesFuel_success_mono
    {fuel : Nat} {context : Context}
    {scrutineeType : Ty}
    {expectedReturn : Ty}
    {outerScope : LexicalScope}
    {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (accepted : inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope cases state = .ok result)
    (extra : Nat) :
    inferMatchCasesFuel (fuel + extra) context scrutineeType expectedReturn outerScope cases state = .ok result :=
  inference_stable.2.2.2.2.2.2.2.2.2.2 fuel context scrutineeType expectedReturn outerScope cases state extra result accepted

/-- Two successful budgets retain exactly the same statement body and state. -/
theorem inferStatementsFuel_success_unique_fuel
    {firstFuel secondFuel : Nat} {context : Context}
    {statements : List Syntax.Statement} {expectedReturn : Ty} {state : State}
    {first second : BlockResult}
    (firstAccepted : inferStatementsFuel firstFuel context statements expectedReturn state = .ok first)
    (secondAccepted : inferStatementsFuel secondFuel context statements expectedReturn state = .ok second) :
    first = second := by
  have firstLarger := inferStatementsFuel_success_mono firstAccepted secondFuel
  have secondLarger := inferStatementsFuel_success_mono secondAccepted firstFuel
  rw [Nat.add_comm secondFuel firstFuel] at secondLarger
  exact Except.ok.inj (firstLarger.symm.trans secondLarger)

end Solcore.Frontend.SourceInference.Detail
