import Solcore.Surface.Multi.ExactTokenTypeAnchoring
import Solcore.Surface.Multi.ExactTokenExpression

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- A successful braced-body plan has mandatory brace endpoints. -/
theorem bracedBodyTokenPlan?_wellAnchored
    (body : Body) (plan : TokenPlan)
    (success : bodyTokenPlan? .braced body = some plan) :
    plan.WellAnchored := by
  rcases body with ⟨span, payload⟩
  rcases payload with ⟨origin, statements⟩
  cases origin with
  | matchArm arrow => simp [bodyTokenPlan?] at success
  | braced openBrace closeBrace =>
      rw [bodyTokenPlan?] at success
      cases plansEq : statementTokenPlans? statements with
      | none => simp [plansEq] at success
      | some plans =>
          simp [plansEq, bracedBodyPlanWith?] at success
          subst plan
          apply TokenPlan.WellAnchored.enclose
          simpa using TokenPlan.WellAnchored.concatExactBookended
            (.symbol .leftBrace) openBrace (.symbol .rightBrace) closeBrace
            [TokenPlan.concat plans]

/-- Prefix-operator plans consist of one mandatory source-exact token. -/
theorem prefixOperatorTokenPlan_wellAnchored (operator : Located PrefixOperator) :
    (prefixOperatorTokenPlan operator).WellAnchored := by
  cases operator with
  | mk span payload =>
      cases payload
      exact TokenPlan.WellAnchored.exact _ _

/-- Infix-operator plans consist of one mandatory source-exact token. -/
theorem infixOperatorTokenPlan_wellAnchored (operator : Located InfixOperator) :
    (infixOperatorTokenPlan operator).WellAnchored := by
  cases operator with
  | mk span payload =>
      cases payload <;> exact TokenPlan.WellAnchored.exact _ _

/-- Literal plans consist of one mandatory source-exact token. -/
theorem literalTokenPlan_wellAnchored (literal : Literal) :
    (literalTokenPlan literal).WellAnchored := by
  cases literal with
  | mk span payload =>
      cases payload <;> exact TokenPlan.WellAnchored.exact _ _

mutual

private def expressionAnchorSize : Expression → Nat
  | ⟨_, payload⟩ => 1 + expressionPayloadAnchorSize payload

private def expressionPayloadAnchorSize : ExpressionPayload → Nat
  | .annotation inner _ => expressionAnchorSize inner
  | .keywordConditional condition thenBranch elseBranch
  | .ternaryConditional condition thenBranch elseBranch =>
      expressionAnchorSize condition + expressionAnchorSize thenBranch +
        expressionAnchorSize elseBranch
  | .call callee _ => expressionAnchorSize callee
  | .select receiver _ => expressionAnchorSize receiver
  | .index receiver index =>
      expressionAnchorSize receiver + expressionAnchorSize index
  | .prefix _ operand => expressionAnchorSize operand
  | .infix _ left right =>
      expressionAnchorSize left + expressionAnchorSize right
  | _ => 0

end

private def expressionLevelAnchorRank : ExpressionTokenLevel → Nat
  | .annotation => 13
  | .conditional => 12
  | .logicalOr => 11
  | .logicalAnd => 10
  | .equality => 9
  | .relational => 8
  | .bitOr => 7
  | .bitXor => 6
  | .bitAnd => 5
  | .additive => 4
  | .multiplicative => 3
  | .prefix => 2
  | .postfix => 1
  | .atom => 0

private def expressionAnchorMeasure
    (level : ExpressionTokenLevel) (value : Expression) : Nat :=
  16 * expressionAnchorSize value + expressionLevelAnchorRank level

private theorem concat3_probe
    {first second third : TokenPlan}
    (firstAnchor : first.WellAnchored)
    (secondAnchor : second.WellAnchored)
    (thirdAnchor : third.WellAnchored) :
    (TokenPlan.concat [first, second, third]).WellAnchored := by
  apply TokenPlan.WellAnchored.concat
  intro plan member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact firstAnchor
  · exact secondAnchor
  · exact thirdAnchor

private theorem concat4_probe
    {first second third fourth : TokenPlan}
    (firstAnchor : first.WellAnchored)
    (secondAnchor : second.WellAnchored)
    (thirdAnchor : third.WellAnchored)
    (fourthAnchor : fourth.WellAnchored) :
    (TokenPlan.concat [first, second, third, fourth]).WellAnchored := by
  apply TokenPlan.WellAnchored.concat
  intro plan member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact firstAnchor
  · exact secondAnchor
  · exact thirdAnchor
  · exact fourthAnchor

private theorem concat6_probe
    {first second third fourth fifth sixth : TokenPlan}
    (firstAnchor : first.WellAnchored)
    (secondAnchor : second.WellAnchored)
    (thirdAnchor : third.WellAnchored)
    (fourthAnchor : fourth.WellAnchored)
    (fifthAnchor : fifth.WellAnchored)
    (sixthAnchor : sixth.WellAnchored) :
    (TokenPlan.concat [first, second, third, fourth, fifth, sixth]).WellAnchored := by
  apply TokenPlan.WellAnchored.concat
  intro plan member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact firstAnchor
  · exact secondAnchor
  · exact thirdAnchor
  · exact fourthAnchor
  · exact fifthAnchor
  · exact sixthAnchor

private theorem concat5_probe
    {first second third fourth fifth : TokenPlan}
    (firstAnchor : first.WellAnchored)
    (secondAnchor : second.WellAnchored)
    (thirdAnchor : third.WellAnchored)
    (fourthAnchor : fourth.WellAnchored)
    (fifthAnchor : fifth.WellAnchored) :
    (TokenPlan.concat [first, second, third, fourth, fifth]).WellAnchored := by
  apply TokenPlan.WellAnchored.concat
  intro plan member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact firstAnchor
  · exact secondAnchor
  · exact thirdAnchor
  · exact fourthAnchor
  · exact fifthAnchor

local macro "solve_expression_anchor_decrease" measureEquation:ident : tactic =>
  `(tactic|
    simp [expressionAnchorMeasure, expressionAnchorSize,
      expressionPayloadAnchorSize, expressionLevelAnchorRank]
      at $measureEquation ⊢ <;> omega)

/-- Every expression plan accepted at any precedence level has mandatory
physical endpoints. -/
theorem expressionTokenPlanAt?_wellAnchored
    (level : ExpressionTokenLevel) (value : Expression) (plan : TokenPlan)
    (success : expressionTokenPlanAt? level value = some plan) :
    plan.WellAnchored := by
  induction measureEq : expressionAnchorMeasure level value using Nat.strongRecOn
      generalizing level value plan with
  | ind measure smaller =>
      have recurse
          (nextLevel : ExpressionTokenLevel) (nextValue : Expression)
          (nextPlan : TokenPlan)
          (decrease : expressionAnchorMeasure nextLevel nextValue < measure)
          (nextSuccess : expressionTokenPlanAt? nextLevel nextValue =
            some nextPlan) :
          nextPlan.WellAnchored :=
        smaller _ decrease nextLevel nextValue nextPlan nextSuccess rfl
      cases level with
      | annotation =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .conditional _ plan (by
              simp [expressionAnchorMeasure, expressionAnchorSize,
                expressionPayloadAnchorSize, expressionLevelAnchorRank]
              at measureEq ⊢
              omega) success
          case annotation inner typeExpression =>
            cases innerEq : expressionTokenPlanAt? .conditional inner with
            | none => simp [innerEq] at success
            | some innerPlan =>
                cases typeEq : typeExprPlan? typeExpression with
                | none => simp [innerEq, typeEq] at success
                | some typePlan =>
                    simp [innerEq, typeEq] at success
                    subst plan
                    apply TokenPlan.WellAnchored.enclose
                    exact concat3_probe
                      (recurse .conditional inner innerPlan (by
                        simp [expressionAnchorMeasure, expressionAnchorSize,
                          expressionPayloadAnchorSize,
                          expressionLevelAnchorRank] at measureEq ⊢
                        omega) innerEq)
                      (TokenPlan.WellAnchored.plain _)
                      (typeExprPlanAt?_wellAnchored false typeExpression typePlan typeEq)
      | conditional =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .logicalOr _ plan (by
              solve_expression_anchor_decrease measureEq) success
          case keywordConditional condition thenBranch elseBranch =>
            cases conditionEq : expressionTokenPlanAt? .conditional condition with
            | none => simp [conditionEq] at success
            | some conditionPlan =>
                cases thenEq : expressionTokenPlanAt? .conditional thenBranch with
                | none => simp [conditionEq, thenEq] at success
                | some thenPlan =>
                    cases elseEq : expressionTokenPlanAt? .conditional elseBranch with
                    | none => simp [conditionEq, thenEq, elseEq] at success
                    | some elsePlan =>
                        simp [conditionEq, thenEq, elseEq] at success
                        subst plan
                        apply TokenPlan.WellAnchored.enclose
                        exact concat6_probe
                          (TokenPlan.WellAnchored.plain _)
                          (recurse .conditional condition conditionPlan (by
                            solve_expression_anchor_decrease measureEq) conditionEq)
                          (TokenPlan.WellAnchored.plain _)
                          (recurse .conditional thenBranch thenPlan (by
                            solve_expression_anchor_decrease measureEq) thenEq)
                          (TokenPlan.WellAnchored.plain _)
                          (recurse .conditional elseBranch elsePlan (by
                            solve_expression_anchor_decrease measureEq) elseEq)
          case ternaryConditional condition thenBranch elseBranch =>
            cases conditionEq : expressionTokenPlanAt? .logicalOr condition with
            | none => simp [conditionEq] at success
            | some conditionPlan =>
                cases thenEq : expressionTokenPlanAt? .conditional thenBranch with
                | none => simp [conditionEq, thenEq] at success
                | some thenPlan =>
                    cases elseEq : expressionTokenPlanAt? .conditional elseBranch with
                    | none => simp [conditionEq, thenEq, elseEq] at success
                    | some elsePlan =>
                        simp [conditionEq, thenEq, elseEq] at success
                        subst plan
                        apply TokenPlan.WellAnchored.enclose
                        exact concat5_probe
                          (recurse .logicalOr condition conditionPlan (by
                            solve_expression_anchor_decrease measureEq) conditionEq)
                          (TokenPlan.WellAnchored.plain _)
                          (recurse .conditional thenBranch thenPlan (by
                            solve_expression_anchor_decrease measureEq) thenEq)
                          (TokenPlan.WellAnchored.plain _)
                          (recurse .conditional elseBranch elsePlan (by
                            solve_expression_anchor_decrease measureEq) elseEq)
      | logicalOr =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .logicalAnd _ plan (by
              solve_expression_anchor_decrease measureEq) success
          case «infix» operator left right =>
            rcases operator with ⟨operatorSpan, operatorPayload⟩
            cases operatorPayload
            all_goals try
              exact recurse .logicalAnd _ plan (by
                solve_expression_anchor_decrease measureEq) success
            case logicalOr =>
              cases leftEq : expressionTokenPlanAt? .logicalOr left with
              | none => simp [leftEq] at success
              | some leftPlan =>
                  cases rightEq : expressionTokenPlanAt? .logicalAnd right with
                  | none => simp [leftEq, rightEq] at success
                  | some rightPlan =>
                      simp [leftEq, rightEq] at success
                      subst plan
                      apply TokenPlan.WellAnchored.enclose
                      exact concat3_probe
                        (recurse .logicalOr left leftPlan (by
                          solve_expression_anchor_decrease measureEq) leftEq)
                        (infixOperatorTokenPlan_wellAnchored ⟨operatorSpan, .logicalOr⟩)
                        (recurse .logicalAnd right rightPlan (by
                          solve_expression_anchor_decrease measureEq) rightEq)
      | logicalAnd =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .equality _ plan (by
              solve_expression_anchor_decrease measureEq) success
          case «infix» operator left right =>
            rcases operator with ⟨operatorSpan, operatorPayload⟩
            cases operatorPayload
            all_goals try
              exact recurse .equality _ plan (by
                solve_expression_anchor_decrease measureEq) success
            case logicalAnd =>
              cases leftEq : expressionTokenPlanAt? .logicalAnd left with
              | none => simp [leftEq] at success
              | some leftPlan =>
                  cases rightEq : expressionTokenPlanAt? .equality right with
                  | none => simp [leftEq, rightEq] at success
                  | some rightPlan =>
                      simp [leftEq, rightEq] at success
                      subst plan
                      apply TokenPlan.WellAnchored.enclose
                      exact concat3_probe
                        (recurse .logicalAnd left leftPlan (by
                          solve_expression_anchor_decrease measureEq) leftEq)
                        (infixOperatorTokenPlan_wellAnchored ⟨operatorSpan, .logicalAnd⟩)
                        (recurse .equality right rightPlan (by
                          solve_expression_anchor_decrease measureEq) rightEq)
      | equality =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .relational _ plan (by
              solve_expression_anchor_decrease measureEq) success
          case «infix» operator left right =>
            rcases operator with ⟨operatorSpan, operatorPayload⟩
            cases operatorPayload
            all_goals try
              exact recurse .relational _ plan (by
                solve_expression_anchor_decrease measureEq) success
            all_goals
              cases leftEq : expressionTokenPlanAt? .relational left with
              | none => simp [leftEq] at success
              | some leftPlan =>
                  cases rightEq : expressionTokenPlanAt? .relational right with
                  | none => simp [leftEq, rightEq] at success
                  | some rightPlan =>
                      simp [leftEq, rightEq] at success
                      subst plan
                      apply TokenPlan.WellAnchored.enclose
                      exact concat3_probe
                        (recurse .relational left leftPlan (by
                          solve_expression_anchor_decrease measureEq) leftEq)
                        (infixOperatorTokenPlan_wellAnchored _)
                        (recurse .relational right rightPlan (by
                          solve_expression_anchor_decrease measureEq) rightEq)
      | relational =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .bitOr _ plan (by
              solve_expression_anchor_decrease measureEq) success
          case «infix» operator left right =>
            rcases operator with ⟨operatorSpan, operatorPayload⟩
            cases operatorPayload
            all_goals try
              exact recurse .bitOr _ plan (by
                solve_expression_anchor_decrease measureEq) success
            all_goals
              cases leftEq : expressionTokenPlanAt? .bitOr left with
              | none => simp [leftEq] at success
              | some leftPlan =>
                  cases rightEq : expressionTokenPlanAt? .bitOr right with
                  | none => simp [leftEq, rightEq] at success
                  | some rightPlan =>
                      simp [leftEq, rightEq] at success
                      subst plan
                      apply TokenPlan.WellAnchored.enclose
                      exact concat3_probe
                        (recurse .bitOr left leftPlan (by
                          solve_expression_anchor_decrease measureEq) leftEq)
                        (infixOperatorTokenPlan_wellAnchored _)
                        (recurse .bitOr right rightPlan (by
                          solve_expression_anchor_decrease measureEq) rightEq)
      | bitOr =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .bitXor _ plan (by
              solve_expression_anchor_decrease measureEq) success
          case «infix» operator left right =>
            rcases operator with ⟨operatorSpan, operatorPayload⟩
            cases operatorPayload
            all_goals try
              exact recurse .bitXor _ plan (by
                solve_expression_anchor_decrease measureEq) success
            case bitOr =>
              cases leftEq : expressionTokenPlanAt? .bitOr left with
              | none => simp [leftEq] at success
              | some leftPlan =>
                  cases rightEq : expressionTokenPlanAt? .bitXor right with
                  | none => simp [leftEq, rightEq] at success
                  | some rightPlan =>
                      simp [leftEq, rightEq] at success
                      subst plan
                      apply TokenPlan.WellAnchored.enclose
                      exact concat3_probe
                        (recurse .bitOr left leftPlan (by
                          solve_expression_anchor_decrease measureEq) leftEq)
                        (infixOperatorTokenPlan_wellAnchored ⟨operatorSpan, .bitOr⟩)
                        (recurse .bitXor right rightPlan (by
                          solve_expression_anchor_decrease measureEq) rightEq)
      | bitXor =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .bitAnd _ plan (by
              solve_expression_anchor_decrease measureEq) success
          case «infix» operator left right =>
            rcases operator with ⟨operatorSpan, operatorPayload⟩
            cases operatorPayload
            all_goals try
              exact recurse .bitAnd _ plan (by
                solve_expression_anchor_decrease measureEq) success
            case bitXor =>
              cases leftEq : expressionTokenPlanAt? .bitXor left with
              | none => simp [leftEq] at success
              | some leftPlan =>
                  cases rightEq : expressionTokenPlanAt? .bitAnd right with
                  | none => simp [leftEq, rightEq] at success
                  | some rightPlan =>
                      simp [leftEq, rightEq] at success
                      subst plan
                      apply TokenPlan.WellAnchored.enclose
                      exact concat3_probe
                        (recurse .bitXor left leftPlan (by
                          solve_expression_anchor_decrease measureEq) leftEq)
                        (infixOperatorTokenPlan_wellAnchored ⟨operatorSpan, .bitXor⟩)
                        (recurse .bitAnd right rightPlan (by
                          solve_expression_anchor_decrease measureEq) rightEq)
      | bitAnd =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .additive _ plan (by
              solve_expression_anchor_decrease measureEq) success
          case «infix» operator left right =>
            rcases operator with ⟨operatorSpan, operatorPayload⟩
            cases operatorPayload
            all_goals try
              exact recurse .additive _ plan (by
                solve_expression_anchor_decrease measureEq) success
            case bitAnd =>
              cases leftEq : expressionTokenPlanAt? .bitAnd left with
              | none => simp [leftEq] at success
              | some leftPlan =>
                  cases rightEq : expressionTokenPlanAt? .additive right with
                  | none => simp [leftEq, rightEq] at success
                  | some rightPlan =>
                      simp [leftEq, rightEq] at success
                      subst plan
                      apply TokenPlan.WellAnchored.enclose
                      exact concat3_probe
                        (recurse .bitAnd left leftPlan (by
                          solve_expression_anchor_decrease measureEq) leftEq)
                        (infixOperatorTokenPlan_wellAnchored ⟨operatorSpan, .bitAnd⟩)
                        (recurse .additive right rightPlan (by
                          solve_expression_anchor_decrease measureEq) rightEq)
      | additive =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .multiplicative _ plan (by
              solve_expression_anchor_decrease measureEq) success
          case «infix» operator left right =>
            rcases operator with ⟨operatorSpan, operatorPayload⟩
            cases operatorPayload
            all_goals try
              exact recurse .multiplicative _ plan (by
                solve_expression_anchor_decrease measureEq) success
            all_goals
              cases leftEq : expressionTokenPlanAt? .additive left with
              | none => simp [leftEq] at success
              | some leftPlan =>
                  cases rightEq : expressionTokenPlanAt? .multiplicative right with
                  | none => simp [leftEq, rightEq] at success
                  | some rightPlan =>
                      simp [leftEq, rightEq] at success
                      subst plan
                      apply TokenPlan.WellAnchored.enclose
                      exact concat3_probe
                        (recurse .additive left leftPlan (by
                          solve_expression_anchor_decrease measureEq) leftEq)
                        (infixOperatorTokenPlan_wellAnchored _)
                        (recurse .multiplicative right rightPlan (by
                          solve_expression_anchor_decrease measureEq) rightEq)
      | multiplicative =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .prefix _ plan (by
              solve_expression_anchor_decrease measureEq) success
          case «infix» operator left right =>
            rcases operator with ⟨operatorSpan, operatorPayload⟩
            cases operatorPayload
            all_goals try
              exact recurse .prefix _ plan (by
                solve_expression_anchor_decrease measureEq) success
            all_goals
              cases leftEq : expressionTokenPlanAt? .multiplicative left with
              | none => simp [leftEq] at success
              | some leftPlan =>
                  cases rightEq : expressionTokenPlanAt? .prefix right with
                  | none => simp [leftEq, rightEq] at success
                  | some rightPlan =>
                      simp [leftEq, rightEq] at success
                      subst plan
                      apply TokenPlan.WellAnchored.enclose
                      exact concat3_probe
                        (recurse .multiplicative left leftPlan (by
                          solve_expression_anchor_decrease measureEq) leftEq)
                        (infixOperatorTokenPlan_wellAnchored _)
                        (recurse .prefix right rightPlan (by
                          solve_expression_anchor_decrease measureEq) rightEq)
      | «prefix» =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .postfix _ plan (by
              solve_expression_anchor_decrease measureEq) success
          case «prefix» operator operand =>
            cases operandEq : expressionTokenPlanAt? .prefix operand with
            | none => simp [operandEq] at success
            | some operandPlan =>
                simp [operandEq] at success
                subst plan
                apply TokenPlan.WellAnchored.enclose
                exact TokenPlan.WellAnchored.append
                  (prefixOperatorTokenPlan_wellAnchored operator)
                  (recurse .prefix operand operandPlan (by
                    solve_expression_anchor_decrease measureEq) operandEq)
      | «postfix» =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          all_goals try
            exact recurse .atom _ plan (by
              solve_expression_anchor_decrease measureEq) success
          case call callee arguments =>
            cases calleeEq : expressionTokenPlanAt? .postfix callee with
            | none =>
                simp only [calleeEq] at success
                split at success <;> simp_all
            | some calleePlan =>
                cases argumentsEq : expressionTokenPlans? arguments with
                | none =>
                    simp only [calleeEq, argumentsEq] at success
                    split at success <;> simp_all
                | some argumentPlans =>
                    simp only [calleeEq, argumentsEq] at success
                    split at success <;> simp_all
                    subst plan
                    apply TokenPlan.WellAnchored.enclose
                    exact TokenPlan.WellAnchored.append
                      (recurse .postfix callee calleePlan (by
                        solve_expression_anchor_decrease measureEq) calleeEq)
                      (TokenPlan.WellAnchored.parens _)
          case select receiver field =>
            cases receiverEq : expressionTokenPlanAt? .postfix receiver with
            | none => simp [receiverEq] at success
            | some receiverPlan =>
                simp [receiverEq] at success
                subst plan
                apply TokenPlan.WellAnchored.enclose
                exact concat3_probe
                  (recurse .postfix receiver receiverPlan (by
                    solve_expression_anchor_decrease measureEq) receiverEq)
                  (TokenPlan.WellAnchored.plain _)
                  (TokenPlan.WellAnchored.exact _ _)
          case index receiver index =>
            cases receiverEq : expressionTokenPlanAt? .postfix receiver with
            | none => simp [receiverEq] at success
            | some receiverPlan =>
                cases indexEq : expressionTokenPlanAt? .annotation index with
                | none => simp [receiverEq, indexEq] at success
                | some indexPlan =>
                    simp [receiverEq, indexEq] at success
                    subst plan
                    apply TokenPlan.WellAnchored.enclose
                    exact concat4_probe
                      (recurse .postfix receiver receiverPlan (by
                        solve_expression_anchor_decrease measureEq) receiverEq)
                      (TokenPlan.WellAnchored.plain _)
                      (recurse .annotation index indexPlan (by
                        solve_expression_anchor_decrease measureEq) indexEq)
                      (TokenPlan.WellAnchored.plain _)
      | atom =>
          rcases value with ⟨span, payload⟩
          cases payload <;> unfold expressionTokenPlanAt? at success
          case name name =>
            injection success with planEq
            subst plan
            exact TokenPlan.WellAnchored.enclose
              (TokenPlan.WellAnchored.exact _ _) span
          case call => simp at success
          case select => simp at success
          case dotConstructor marker name arguments =>
            cases arguments with
            | none =>
                injection success with planEq
                subst plan
                apply TokenPlan.WellAnchored.enclose
                have nameAnchor : (identifierPlan name).WellAnchored := by
                  exact TokenPlan.WellAnchored.exact _ _
                simpa [TokenPlan.concat, TokenPlan.append] using
                  TokenPlan.WellAnchored.append
                    (TokenPlan.WellAnchored.exact _ _)
                    nameAnchor
            | some arguments =>
                rcases Option.bind_eq_some_iff.mp success with
                  ⟨argumentPlans, _argumentsEq, resultEq⟩
                injection resultEq with planEq
                subst plan
                apply TokenPlan.WellAnchored.enclose
                exact concat3_probe
                  (TokenPlan.WellAnchored.exact _ _)
                  (TokenPlan.WellAnchored.exact _ _)
                  (TokenPlan.WellAnchored.parens _)
          case proxy marker typeExpression =>
            rcases Option.bind_eq_some_iff.mp success with
              ⟨typePlan, typeEq, resultEq⟩
            injection resultEq with planEq
            subst plan
            apply TokenPlan.WellAnchored.enclose
            exact TokenPlan.WellAnchored.append
              (TokenPlan.WellAnchored.exact _ _)
              (typeExprPlanAt?_wellAnchored true typeExpression typePlan typeEq)
          case literal literal =>
            injection success with planEq
            subst plan
            exact TokenPlan.WellAnchored.enclose (literalTokenPlan_wellAnchored literal) span
          case lambda parameters returnType body =>
            rcases Option.bind_eq_some_iff.mp success with
              ⟨parameterPlans, _parameterPlansEq, success⟩
            cases returnType with
            | none =>
                rcases Option.bind_eq_some_iff.mp success with
                  ⟨returnPlan, returnEq, success⟩
                injection returnEq with returnPlanEq
                subst returnPlan
                rcases Option.bind_eq_some_iff.mp success with
                  ⟨bodyPlan, bodyEq, resultEq⟩
                injection resultEq with planEq
                subst plan
                apply TokenPlan.WellAnchored.enclose
                exact concat4_probe
                  (TokenPlan.WellAnchored.plain _)
                  (TokenPlan.WellAnchored.parens _)
                  TokenPlan.WellAnchored.empty
                  (bracedBodyTokenPlan?_wellAnchored body bodyPlan bodyEq)
            | some typeExpression =>
                simp only at success
                rcases Option.bind_eq_some_iff.mp success with
                  ⟨typePlan, typeEq, success⟩
                rcases Option.bind_eq_some_iff.mp success with
                  ⟨returnPlan, returnEq, success⟩
                injection returnEq with returnPlanEq
                subst returnPlan
                rcases Option.bind_eq_some_iff.mp success with
                  ⟨bodyPlan, bodyEq, resultEq⟩
                injection resultEq with planEq
                subst plan
                apply TokenPlan.WellAnchored.enclose
                exact concat4_probe
                  (TokenPlan.WellAnchored.plain _)
                  (TokenPlan.WellAnchored.parens _)
                  (TokenPlan.WellAnchored.append
                    (TokenPlan.WellAnchored.plain _)
                    (typeExprPlanAt?_wellAnchored false typeExpression typePlan typeEq))
                  (bracedBodyTokenPlan?_wellAnchored body bodyPlan bodyEq)
          case annotation => simp at success
          case keywordConditional => simp at success
          case ternaryConditional => simp at success
          case index => simp at success
          case «prefix» => simp at success
          case «infix» => simp at success
          case tuple elements =>
            cases elements with
            | nil =>
                injection success with planEq
                subst plan
                exact TokenPlan.WellAnchored.enclose
                  (TokenPlan.WellAnchored.parens _) span
            | cons first rest =>
                cases rest with
                | nil => simp at success
                | cons second rest =>
                    rcases Option.bind_eq_some_iff.mp success with
                      ⟨elementPlans, _elementPlansEq, resultEq⟩
                    injection resultEq with planEq
                    subst plan
                    exact TokenPlan.WellAnchored.enclose
                      (TokenPlan.WellAnchored.parens _) span
          case group inner =>
            rcases Option.bind_eq_some_iff.mp success with
              ⟨innerPlan, _innerEq, resultEq⟩
            injection resultEq with planEq
            subst plan
            exact TokenPlan.WellAnchored.enclose
              (TokenPlan.WellAnchored.parens innerPlan) span

/-- Every plan accepted by the public expression visitor has mandatory
physical endpoints. -/
theorem expressionTokenPlan?_wellAnchored
    (expression : Expression) (plan : TokenPlan)
    (success : expressionTokenPlan? expression = some plan) :
    plan.WellAnchored :=
  expressionTokenPlanAt?_wellAnchored .annotation expression plan success

private def parameterTypeCandidate? : Option TypeExpr → Option TokenPlan
  | none => some .empty
  | some typeExpression => do
      let innerPlan ← typeExprPlan? typeExpression
      pure (.append (.plain (.symbol .colon)) innerPlan)

/-- Every accepted parameter plan has the parameter name as a mandatory
interior anchor, with any surrounding components anchored as well. -/
theorem parameterTokenPlan?_wellAnchored
    (parameter : Parameter) (plan : TokenPlan)
    (success : parameterTokenPlan? parameter = some plan) :
    plan.WellAnchored := by
  rcases parameter with ⟨span, payload⟩
  rcases payload with ⟨comptime, name, typeExpression⟩
  have finish
      (comptimeCandidate : Option TokenPlan)
      (candidateAnchor : ∀ candidatePlan,
        comptimeCandidate = some candidatePlan →
          candidatePlan.WellAnchored)
      (equation :
        (do
          let comptimePlan ← comptimeCandidate
          let typePlan ← parameterTypeCandidate? typeExpression
          pure (.enclose span (.concat [
            comptimePlan,
            identifierPlan name,
            typePlan]))) = some plan) :
      plan.WellAnchored := by
    rcases Option.bind_eq_some_iff.mp equation with
      ⟨comptimePlan, comptimeEq, success⟩
    rcases Option.bind_eq_some_iff.mp success with
      ⟨typePlan, typeEq, resultEq⟩
    injection resultEq with planEq
    subst plan
    have comptimeAnchor := candidateAnchor comptimePlan comptimeEq
    have typeAnchor : typePlan.WellAnchored := by
      cases typeExpression with
      | none =>
          simp [parameterTypeCandidate?] at typeEq
          subst typePlan
          exact TokenPlan.WellAnchored.empty
      | some typeExpression =>
          simp only [parameterTypeCandidate?] at typeEq
          rcases Option.bind_eq_some_iff.mp typeEq with
            ⟨innerPlan, innerEq, resultEq⟩
          injection resultEq with typePlanEq
          subst typePlan
          exact TokenPlan.WellAnchored.append
            (TokenPlan.WellAnchored.plain _)
            (typeExprPlan?_wellAnchored typeExpression innerPlan innerEq)
    apply TokenPlan.WellAnchored.enclose
    exact concat3_probe comptimeAnchor
      (identifierPlan_wellAnchored name) typeAnchor
  simp only [parameterTokenPlan?] at success
  cases comptime with
  | none =>
      apply finish (some .empty)
      · intro candidatePlan candidateEq
        injection candidateEq with candidatePlanEq
        subst candidatePlan
        exact TokenPlan.WellAnchored.empty
      · cases typeExpression <;>
          simpa [parameterTypeCandidate?, Option.bind_assoc] using success
  | some marker =>
      by_cases accepted : marker.payload = .comptimeModifier
      · apply finish (some (.exact
          (.identifier ContextualKeyword.comptimeKw.spelling) marker.span))
        · intro candidatePlan candidateEq
          injection candidateEq with candidatePlanEq
          subst candidatePlan
          exact TokenPlan.WellAnchored.exact _ _
        · cases typeExpression <;>
            simpa [accepted, parameterTypeCandidate?, Option.bind_assoc] using success
      · simp [accepted] at success

/-- Every accepted pattern plan has mandatory physical endpoints. -/
theorem patternTokenPlan?_wellAnchored
    (pattern : Pattern) (plan : TokenPlan)
    (success : patternTokenPlan? pattern = some plan) :
    plan.WellAnchored := by
  rcases pattern with ⟨span, payload⟩
  cases payload <;> unfold patternTokenPlan? at success
  case named name arguments =>
    cases arguments with
    | none =>
        injection success with planEq
        subst plan
        exact TokenPlan.WellAnchored.enclose
          (qualifiedNamePlan_wellAnchored name) span
    | some arguments =>
        rcases Option.bind_eq_some_iff.mp success with
          ⟨argumentPlans, _argumentsEq, resultEq⟩
        injection resultEq with planEq
        subst plan
        apply TokenPlan.WellAnchored.enclose
        exact TokenPlan.WellAnchored.append
          (qualifiedNamePlan_wellAnchored name)
          (TokenPlan.WellAnchored.parens _)
  case dotConstructor marker name arguments =>
    cases arguments with
    | none =>
        injection success with planEq
        subst plan
        apply TokenPlan.WellAnchored.enclose
        simpa [TokenPlan.concat, TokenPlan.append] using
          TokenPlan.WellAnchored.append
            (TokenPlan.WellAnchored.exact _ _)
            (identifierPlan_wellAnchored name)
    | some arguments =>
        rcases Option.bind_eq_some_iff.mp success with
          ⟨argumentPlans, _argumentsEq, resultEq⟩
        injection resultEq with planEq
        subst plan
        apply TokenPlan.WellAnchored.enclose
        exact concat3_probe
          (TokenPlan.WellAnchored.exact _ _)
          (identifierPlan_wellAnchored name)
          (TokenPlan.WellAnchored.parens _)
  case wildcard marker =>
    by_cases accepted : marker.payload = .wildcard
    · simp [accepted] at success
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (TokenPlan.WellAnchored.exact _ _) span
    · simp [accepted] at success
  case literal literal =>
    injection success with planEq
    subst plan
    exact TokenPlan.WellAnchored.enclose
      (literalTokenPlan_wellAnchored literal) span
  case comptime marker expression =>
    by_cases accepted : marker.payload = .comptimeModifier
    · simp only [accepted, ↓reduceIte] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨expressionPlan, expressionEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      exact TokenPlan.WellAnchored.append
        (TokenPlan.WellAnchored.exact _ _)
        (expressionTokenPlanAt?_wellAnchored .annotation expression
          expressionPlan expressionEq)
    · simp [accepted] at success
  case tuple elements =>
    cases elements with
    | nil =>
        injection success with planEq
        subst plan
        exact TokenPlan.WellAnchored.enclose
          (TokenPlan.WellAnchored.parens _) span
    | cons first rest =>
        cases rest with
        | nil => simp at success
        | cons second rest =>
            rcases Option.bind_eq_some_iff.mp success with
              ⟨elementPlans, _elementPlansEq, resultEq⟩
            injection resultEq with planEq
            subst plan
            exact TokenPlan.WellAnchored.enclose
              (TokenPlan.WellAnchored.parens _) span
  case group inner =>
    rcases Option.bind_eq_some_iff.mp success with
      ⟨innerPlan, _innerEq, resultEq⟩
    injection resultEq with planEq
    subst plan
    exact TokenPlan.WellAnchored.enclose
      (TokenPlan.WellAnchored.parens innerPlan) span

end Solcore.Surface.Multi
