import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private def TokensHaveSource
    (source : SourceId) (tokens : List Token) : Prop :=
  ∀ token ∈ tokens, token.span.source = source

private theorem physicalTokens_haveSource
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (owned : TokensOwnedBy file tokens) :
    TokensHaveSource file.id (PhysicalTokens tokens origin finish) := by
  intro token member
  apply (owned token ?_).1
  unfold PhysicalTokens at member
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

private theorem TokensHaveSource.of_append_left
    {source : SourceId} {left right : List Token}
    (all : TokensHaveSource source (left ++ right)) :
    TokensHaveSource source left := by
  intro token member
  exact all token (List.mem_append_left right member)

private theorem TokensHaveSource.of_append_right
    {source : SourceId} {left right : List Token}
    (all : TokensHaveSource source (left ++ right)) :
    TokensHaveSource source right := by
  intro token member
  exact all token (List.mem_append_right left member)

private theorem MatchedTerminal.physicalTokenPlan_symbol
    {file : WorkspaceFile} {tokens : List Token}
    (symbol : Symbol)
    (matched : MatchedTerminal file tokens (.symbol symbol)) :
    matched.physicalTokenPlan =
      TokenPlan.exact (.symbol symbol) matched.span := by
  rcases matched with
    ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases terminalAt with
  | retained token inRange lookup valid =>
      simp [MatchedTerminal.physicalTokenPlan, TerminalMatches]
        at matchedEvidence ⊢
      rw [matchedEvidence]
  | endOfFile atEnd =>
      simp [TerminalMatches] at matchedEvidence

private def addConstraintView
    (constraint : TokenSpanConstraint) : TokenSlot → TokenSlot
  | .required expected => .required {
      expected with constraints := constraint :: expected.constraints }
  | .optional expected => .optional {
      expected with constraints := constraint :: expected.constraints }

private def addFirstView
    (constraint : TokenSpanConstraint) : List TokenSlot → List TokenSlot
  | [] => []
  | first :: rest => addConstraintView constraint first :: rest

private def addLastView (constraint : TokenSpanConstraint)
    (slots : List TokenSlot) : List TokenSlot :=
  (addFirstView constraint slots.reverse).reverse

private theorem enclose_eq_view (span : SourceSpan)
    (slots : List TokenSlot) :
    TokenSlot.enclose span slots =
      addLastView (.ends span) (addFirstView (.starts span) slots) := by
  rfl

private theorem addFirstView_append_of_ne_nil
    (constraint : TokenSpanConstraint) (left right : List TokenSlot)
    (nonempty : left ≠ []) :
    addFirstView constraint (left ++ right) =
      addFirstView constraint left ++ right := by
  cases left with
  | nil => contradiction
  | cons head tail => rfl

private theorem addLastView_cons_nonempty
    (constraint : TokenSpanConstraint) (first second : TokenSlot)
    (rest : List TokenSlot) :
    addLastView constraint (first :: second :: rest) =
      first :: addLastView constraint (second :: rest) := by
  unfold addLastView
  rw [List.reverse_cons]
  rw [addFirstView_append_of_ne_nil]
  · simp [List.reverse_append]
  · simp

@[simp] private theorem addFirstView_length
    (constraint : TokenSpanConstraint) (slots : List TokenSlot) :
    (addFirstView constraint slots).length = slots.length := by
  cases slots <;> rfl

@[simp] private theorem addLastView_length
    (constraint : TokenSpanConstraint) (slots : List TokenSlot) :
    (addLastView constraint slots).length = slots.length := by
  simp [addLastView]

@[simp] private theorem enclose_slots_length
    (span : SourceSpan) (plan : TokenPlan) :
    (plan.enclose span).slots.length = plan.slots.length := by
  simp [TokenPlan.enclose, enclose_eq_view]

private def StartsRequiredView : List TokenSlot → Prop
  | [] => False
  | .required _ :: _ => True
  | .optional _ :: _ => False

private def EndsRequiredView (slots : List TokenSlot) : Prop :=
  StartsRequiredView slots.reverse

private theorem StartsRequiredView.append
    {left : List TokenSlot} (right : List TokenSlot)
    (required : StartsRequiredView left) :
    StartsRequiredView (left ++ right) := by
  cases left with
  | nil => contradiction
  | cons first rest =>
      cases first <;> simpa [StartsRequiredView] using required

private def lastRequiredShape : Bool → List Bool → Bool
  | last, [] => last
  | _, next :: rest => lastRequiredShape next rest

private def slotsWellAnchored : List TokenSlot → Bool
  | [] => true
  | first :: rest =>
      first.isRequired &&
        lastRequiredShape first.isRequired (rest.map TokenSlot.isRequired)

private def requiredSentinel : TokenSlot :=
  .required (.plain (.symbol .comma))

private theorem exposedLastRequired_eq
    (first : TokenSlot) (rest : List TokenSlot) :
    ({ slots := requiredSentinel :: first :: rest } : TokenPlan).wellAnchored =
      lastRequiredShape first.isRequired
        (rest.map TokenSlot.isRequired) := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest induction =>
      exact induction next

private theorem wellAnchored_eq_slotsWellAnchored (plan : TokenPlan) :
    plan.wellAnchored = slotsWellAnchored plan.slots := by
  cases plan with
  | mk slots =>
      cases slots with
      | nil => rfl
      | cons first rest =>
          change (first.isRequired &&
              ({ slots := requiredSentinel :: first :: rest } :
                TokenPlan).wellAnchored) =
            (first.isRequired && lastRequiredShape first.isRequired
              (rest.map TokenSlot.isRequired))
          rw [exposedLastRequired_eq]

private theorem lastRequiredShape_ends
    (first : TokenSlot) (rest : List TokenSlot)
    (required :
      lastRequiredShape first.isRequired
        (rest.map TokenSlot.isRequired) = true) :
    EndsRequiredView (first :: rest) := by
  induction rest generalizing first with
  | nil =>
      cases first <;>
        simp_all [lastRequiredShape, EndsRequiredView,
          StartsRequiredView, TokenSlot.isRequired]
  | cons next rest induction =>
      have tailRequired : EndsRequiredView (next :: rest) :=
        induction next (by simpa [lastRequiredShape] using required)
      unfold EndsRequiredView at tailRequired ⊢
      rw [List.reverse_cons]
      exact tailRequired.append [first]

private theorem wellAnchored_nonempty_shapes
    {plan : TokenPlan} (anchored : plan.WellAnchored)
    (nonempty : plan.slots ≠ []) :
    StartsRequiredView plan.slots ∧ EndsRequiredView plan.slots := by
  rcases plan with ⟨slots⟩
  cases slots with
  | nil => contradiction
  | cons first rest =>
      unfold TokenPlan.WellAnchored at anchored
      rw [wellAnchored_eq_slotsWellAnchored] at anchored
      simp only [slotsWellAnchored, Bool.and_eq_true] at anchored
      constructor
      · cases first <;>
          simp_all [StartsRequiredView, TokenSlot.isRequired]
      · exact lastRequiredShape_ends first rest anchored.2

private def FirstCarries
    (constraint : TokenSpanConstraint) : List TokenSlot → Prop
  | .required expected :: _ => constraint ∈ expected.constraints
  | _ => False

private def LastCarries
    (constraint : TokenSpanConstraint) (slots : List TokenSlot) : Prop :=
  FirstCarries constraint slots.reverse

private theorem addFirstView_carries
    (constraint : TokenSpanConstraint) (slots : List TokenSlot)
    (required : StartsRequiredView slots) :
    FirstCarries constraint (addFirstView constraint slots) := by
  cases slots with
  | nil => contradiction
  | cons first rest =>
      cases first <;>
        simp_all [StartsRequiredView, FirstCarries, addFirstView,
          addConstraintView]

private theorem addLastView_preserves_firstCarries
    (added carried : TokenSpanConstraint) (slots : List TokenSlot)
    (carries : FirstCarries carried slots) :
    FirstCarries carried (addLastView added slots) := by
  cases slots with
  | nil => contradiction
  | cons first rest =>
      cases rest with
      | nil =>
          cases first <;>
            simp_all [FirstCarries, addLastView, addFirstView,
              addConstraintView]
      | cons second rest =>
          rw [addLastView_cons_nonempty]
          cases first <;> simpa [FirstCarries] using carries

private theorem addFirstView_carries_of_result_required
    (constraint : TokenSpanConstraint) (slots : List TokenSlot)
    (required : StartsRequiredView (addFirstView constraint slots)) :
    FirstCarries constraint (addFirstView constraint slots) := by
  cases slots with
  | nil => contradiction
  | cons first rest =>
      cases first <;>
        simp_all [StartsRequiredView, FirstCarries, addFirstView,
          addConstraintView]

private theorem addLastView_carries_of_result_required
    (constraint : TokenSpanConstraint) (slots : List TokenSlot)
    (required : EndsRequiredView (addLastView constraint slots)) :
    LastCarries constraint (addLastView constraint slots) := by
  unfold EndsRequiredView at required
  unfold LastCarries addLastView
  simp only [List.reverse_reverse]
  exact addFirstView_carries_of_result_required constraint slots.reverse
    (by simpa [addLastView] using required)

private theorem firstSatisfies_of_carries
    {constraint : TokenSpanConstraint} {slots : List TokenSlot}
    {actual : List Token}
    (carries : FirstCarries constraint slots)
    (relation : TokenSlot.ListMatches slots actual) :
    TokenSlot.FirstSatisfies constraint actual := by
  cases slots with
  | nil => contradiction
  | cons first rest =>
      cases first with
      | optional expected => contradiction
      | required expected =>
          cases relation with
          | required head tail =>
              exact head.2 constraint carries

private theorem lastSatisfies_of_carries
    {constraint : TokenSpanConstraint} {slots : List TokenSlot}
    {actual : List Token}
    (carries : LastCarries constraint slots)
    (relation : TokenSlot.ListMatches slots actual) :
    TokenSlot.LastSatisfies constraint actual := by
  have matchesAppend
      {leftSlots rightSlots : List TokenSlot}
      {leftActual rightActual : List Token}
      (left : TokenSlot.ListMatches leftSlots leftActual)
      (right : TokenSlot.ListMatches rightSlots rightActual) :
      TokenSlot.ListMatches (leftSlots ++ rightSlots)
        (leftActual ++ rightActual) :=
    left.append right
  have matchesReverse
      {sourceSlots : List TokenSlot} {sourceActual : List Token}
      (sourceRelation :
        TokenSlot.ListMatches sourceSlots sourceActual) :
      TokenSlot.ListMatches sourceSlots.reverse sourceActual.reverse := by
    induction sourceRelation with
    | nil => exact .nil
    | @required expected actual slots actualTail head tail induction =>
        simpa using matchesAppend induction
          (TokenSlot.ListMatches.required head .nil)
    | @optionalAbsent expected slots actual tail induction =>
        simpa using matchesAppend induction
          (TokenSlot.ListMatches.optionalAbsent
            (expected := expected) TokenSlot.ListMatches.nil)
    | @optionalPresent expected actual slots actualTail head tail induction =>
        simpa using matchesAppend induction
          (TokenSlot.ListMatches.optionalPresent head .nil)
  have firstOnReverse :
      TokenSlot.FirstSatisfies constraint actual.reverse :=
    firstSatisfies_of_carries carries (matchesReverse relation)
  have firstReverse_iff_last
      (values : List Token) :
      TokenSlot.FirstSatisfies constraint values.reverse ↔
        TokenSlot.LastSatisfies constraint values := by
    induction values with
    | nil => rfl
    | cons head tail induction =>
        cases tail with
        | nil => rfl
        | cons next rest =>
            rw [List.reverse_cons]
            have nonempty : (next :: rest).reverse ≠ [] := by simp
            have firstAppend :
                TokenSlot.FirstSatisfies constraint
                    ((next :: rest).reverse ++ [head]) ↔
                  TokenSlot.FirstSatisfies constraint
                    (next :: rest).reverse := by
              cases reversed : (next :: rest).reverse with
              | nil => contradiction
              | cons last before => rfl
            rw [firstAppend]
            exact induction
  exact (firstReverse_iff_last actual).mp firstOnReverse

/-- A nonempty, well-anchored enclosed plan forces its first and last matched
tokens to satisfy the enclosing source span's endpoint constraints. -/
theorem listMatches_enclose_endpoints
    {span : SourceSpan} {inner : TokenPlan} {actual : List Token}
    (anchored : (inner.enclose span).WellAnchored)
    (nonempty : (inner.enclose span).slots ≠ [])
    (relation : TokenSlot.ListMatches
      (inner.enclose span).slots actual) :
    TokenSlot.FirstSatisfies (.starts span) actual ∧
      TokenSlot.LastSatisfies (.ends span) actual := by
  have shapes := wellAnchored_nonempty_shapes anchored nonempty
  rw [TokenPlan.enclose, enclose_eq_view] at relation
  constructor
  · apply firstSatisfies_of_carries
      (relation := relation)
    have resultStarts : StartsRequiredView
        (addLastView (.ends span)
          (addFirstView (.starts span) inner.slots)) := by
      simpa [TokenPlan.enclose, enclose_eq_view] using shapes.1
    cases slotsEq : inner.slots with
    | nil =>
        rw [slotsEq] at resultStarts
        simp [addFirstView, addLastView, StartsRequiredView] at resultStarts
    | cons first rest =>
        rw [slotsEq] at resultStarts
        have initialStarts : StartsRequiredView (first :: rest) := by
          cases first with
          | required expected => trivial
          | optional expected =>
              cases rest with
              | nil =>
                  simp [addFirstView, addLastView, addConstraintView,
                    StartsRequiredView] at resultStarts
              | cons second rest =>
                  simp only [addFirstView, addConstraintView] at resultStarts
                  rw [addLastView_cons_nonempty] at resultStarts
                  simp [StartsRequiredView] at resultStarts
        exact addLastView_preserves_firstCarries _ _ _
          (addFirstView_carries _ _ initialStarts)
  · apply lastSatisfies_of_carries
      (relation := relation)
    apply addLastView_carries_of_result_required
    simpa [TokenPlan.enclose, enclose_eq_view] using shapes.2

/-- A successful expression plan has a nonempty core enclosed by the exact
source span retained on that expression. -/
def EnclosesExpressionSpan
    (expression : Expression) (plan : TokenPlan) : Prop :=
  ∃ inner : TokenPlan,
    plan = inner.enclose expression.span ∧ inner.slots ≠ []

private theorem encloses_result
    {span : SourceSpan} {inner plan : TokenPlan}
    (result : Option.some (inner.enclose span) = Option.some plan)
    (nonempty : inner.slots ≠ []) :
    ∃ core : TokenPlan,
      plan = core.enclose span ∧ core.slots ≠ [] := by
  injection result with equality
  subst plan
  exact ⟨inner, rfl, nonempty⟩

private theorem atomExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : atomExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [atomExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  case name name =>
      exact encloses_result success (by simp [identifierPlan, TokenPlan.exact])
  case call => simp at success
  case select => simp at success
  case dotConstructor marker name arguments =>
      cases arguments with
      | none =>
          exact encloses_result success (by
            simp [TokenPlan.concat, TokenPlan.exact, identifierPlan])
      | some arguments =>
          rcases Option.bind_eq_some_iff.mp success with
            ⟨argumentPlans, argumentPlansEq, result⟩
          exact encloses_result result (by
            simp [TokenPlan.concat, TokenPlan.exact, identifierPlan])
  case proxy marker typeExpression =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨typePlan, typePlanEq, result⟩
      exact encloses_result result (by
        simp [TokenPlan.append, TokenPlan.exact])
  case literal literal =>
      exact encloses_result success (by
        rcases literal with ⟨literalSpan, literalPayload⟩
        cases literalPayload <;>
          simp [literalTokenPlan, TokenPlan.exact])
  case lambda parameters returnType body =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨parameterPlans, parameterPlansEq, success⟩
      cases returnType with
      | none =>
          rcases Option.bind_eq_some_iff.mp success with
            ⟨returnPlan, returnPlanEq, success⟩
          injection returnPlanEq with returnPlanIdentity
          subst returnPlan
          rcases Option.bind_eq_some_iff.mp success with
            ⟨bodyPlan, bodyPlanEq, result⟩
          exact encloses_result result (by
            simp [TokenPlan.concat, TokenPlan.plain])
      | some typeExpression =>
          rcases Option.bind_eq_some_iff.mp success with
            ⟨typePlan, typePlanEq, success⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨returnPlan, returnPlanEq, success⟩
          injection returnPlanEq with returnPlanIdentity
          subst returnPlan
          rcases Option.bind_eq_some_iff.mp success with
            ⟨bodyPlan, bodyPlanEq, result⟩
          exact encloses_result result (by
            simp [TokenPlan.concat, TokenPlan.plain])
  case annotation => simp at success
  case keywordConditional => simp at success
  case ternaryConditional => simp at success
  case index => simp at success
  case «prefix» => simp at success
  case «infix» => simp at success
  case tuple elements =>
      cases elements with
      | nil =>
          exact encloses_result success (by
            simp [TokenPlan.parens, TokenPlan.concat, TokenPlan.plain])
      | cons first rest =>
          cases rest with
          | nil => simp at success
          | cons second rest =>
              rcases Option.bind_eq_some_iff.mp success with
                ⟨elementPlans, elementPlansEq, result⟩
              exact encloses_result result (by
                simp [TokenPlan.parens, TokenPlan.concat, TokenPlan.plain])
  case group inner =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨innerPlan, innerPlanEq, result⟩
      exact encloses_result result (by
        simp [TokenPlan.parens, TokenPlan.concat, TokenPlan.plain])

private theorem postfixExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : postfixExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [postfixExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case call callee arguments =>
      split at success
      · simp at success
      · rcases Option.bind_eq_some_iff.mp success with
          ⟨calleePlan, calleePlanEq, success⟩
        rcases Option.bind_eq_some_iff.mp success with
          ⟨argumentPlans, argumentPlansEq, result⟩
        exact encloses_result result (by
          simp [TokenPlan.append, TokenPlan.parens,
            TokenPlan.concat, TokenPlan.plain])
  case select receiver field =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨receiverPlan, receiverPlanEq, result⟩
      exact encloses_result result (by
        simp [TokenPlan.concat, TokenPlan.plain,
          identifierPlan, TokenPlan.exact])
  case index receiver index =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨receiverPlan, receiverPlanEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨indexPlan, indexPlanEq, result⟩
      exact encloses_result result (by
        simp [TokenPlan.concat, TokenPlan.plain])
  all_goals
    simpa [EnclosesExpressionSpan] using
      atomExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

private theorem prefix_candidate_encloses
    (span : SourceSpan) (operator : Located PrefixOperator)
    (operandCandidate : Option TokenPlan) (plan : TokenPlan)
    (success :
      (do
        let operandPlan ← operandCandidate
        pure (.enclose span (.append
          (prefixOperatorTokenPlan operator) operandPlan))) = some plan) :
    ∃ inner : TokenPlan,
      plan = inner.enclose span ∧ inner.slots ≠ [] := by
  rcases Option.bind_eq_some_iff.mp success with
    ⟨operandPlan, operandPlanEq, result⟩
  exact encloses_result result (by
    rcases operator with ⟨operatorSpan, operatorPayload⟩
    cases operatorPayload
    simp [prefixOperatorTokenPlan, TokenPlan.append, TokenPlan.exact])

private theorem infix_candidate_encloses
    (span : SourceSpan) (operator : Located InfixOperator)
    (leftCandidate rightCandidate : Option TokenPlan) (plan : TokenPlan)
    (success :
      (do
        let leftPlan ← leftCandidate
        let rightPlan ← rightCandidate
        pure (.enclose span (.concat [
          leftPlan, infixOperatorTokenPlan operator, rightPlan]))) =
        some plan) :
    ∃ inner : TokenPlan,
      plan = inner.enclose span ∧ inner.slots ≠ [] := by
  rcases Option.bind_eq_some_iff.mp success with
    ⟨leftPlan, leftPlanEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨rightPlan, rightPlanEq, result⟩
  exact encloses_result result (by
    rcases operator with ⟨operatorSpan, operatorPayload⟩
    cases operatorPayload <;>
      simp [infixOperatorTokenPlan, TokenPlan.concat, TokenPlan.exact])

private theorem prefixExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : prefixExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [prefixExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case «prefix» operator operand =>
      exact prefix_candidate_encloses span operator
        (expressionTokenPlanAt? .prefix operand) plan success
  all_goals
    simpa [EnclosesExpressionSpan] using
      postfixExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

private theorem multiplicativeExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : multiplicativeExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [multiplicativeExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case «infix» operator left right =>
      rcases operator with ⟨operatorSpan, operatorPayload⟩
      cases operatorPayload
      all_goals try
        exact infix_candidate_encloses span ⟨operatorSpan, _⟩
          (expressionTokenPlanAt? .multiplicative left)
          (expressionTokenPlanAt? .prefix right) plan success
      all_goals
        simpa [EnclosesExpressionSpan] using
          prefixExpressionTokenPlan?_encloses
            (show Expression from
              ⟨span, .infix ⟨operatorSpan, _⟩ left right⟩)
            plan success
  all_goals
    simpa [EnclosesExpressionSpan] using
      prefixExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

private theorem additiveExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : additiveExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [additiveExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case «infix» operator left right =>
      rcases operator with ⟨operatorSpan, operatorPayload⟩
      cases operatorPayload
      all_goals try
        exact infix_candidate_encloses span ⟨operatorSpan, _⟩
          (expressionTokenPlanAt? .additive left)
          (expressionTokenPlanAt? .multiplicative right) plan success
      all_goals
        simpa [EnclosesExpressionSpan] using
          multiplicativeExpressionTokenPlan?_encloses
            (show Expression from
              ⟨span, .infix ⟨operatorSpan, _⟩ left right⟩)
            plan success
  all_goals
    simpa [EnclosesExpressionSpan] using
      multiplicativeExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

private theorem bitAndExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : bitAndExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [bitAndExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case «infix» operator left right =>
      rcases operator with ⟨operatorSpan, operatorPayload⟩
      cases operatorPayload
      all_goals try
        exact infix_candidate_encloses span ⟨operatorSpan, _⟩
          (expressionTokenPlanAt? .bitAnd left)
          (expressionTokenPlanAt? .additive right) plan success
      all_goals
        simpa [EnclosesExpressionSpan] using
          additiveExpressionTokenPlan?_encloses
            (show Expression from
              ⟨span, .infix ⟨operatorSpan, _⟩ left right⟩)
            plan success
  all_goals
    simpa [EnclosesExpressionSpan] using
      additiveExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

private theorem bitXorExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : bitXorExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [bitXorExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case «infix» operator left right =>
      rcases operator with ⟨operatorSpan, operatorPayload⟩
      cases operatorPayload
      all_goals try
        exact infix_candidate_encloses span ⟨operatorSpan, _⟩
          (expressionTokenPlanAt? .bitXor left)
          (expressionTokenPlanAt? .bitAnd right) plan success
      all_goals
        simpa [EnclosesExpressionSpan] using
          bitAndExpressionTokenPlan?_encloses
            (show Expression from
              ⟨span, .infix ⟨operatorSpan, _⟩ left right⟩)
            plan success
  all_goals
    simpa [EnclosesExpressionSpan] using
      bitAndExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

private theorem bitOrExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : bitOrExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [bitOrExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case «infix» operator left right =>
      rcases operator with ⟨operatorSpan, operatorPayload⟩
      cases operatorPayload
      all_goals try
        exact infix_candidate_encloses span ⟨operatorSpan, _⟩
          (expressionTokenPlanAt? .bitOr left)
          (expressionTokenPlanAt? .bitXor right) plan success
      all_goals
        simpa [EnclosesExpressionSpan] using
          bitXorExpressionTokenPlan?_encloses
            (show Expression from
              ⟨span, .infix ⟨operatorSpan, _⟩ left right⟩)
            plan success
  all_goals
    simpa [EnclosesExpressionSpan] using
      bitXorExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

private theorem relationalExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : relationalExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [relationalExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case «infix» operator left right =>
      rcases operator with ⟨operatorSpan, operatorPayload⟩
      cases operatorPayload
      all_goals try
        exact infix_candidate_encloses span ⟨operatorSpan, _⟩
          (expressionTokenPlanAt? .bitOr left)
          (expressionTokenPlanAt? .bitOr right) plan success
      all_goals
        simpa [EnclosesExpressionSpan] using
          bitOrExpressionTokenPlan?_encloses
            (show Expression from
              ⟨span, .infix ⟨operatorSpan, _⟩ left right⟩)
            plan success
  all_goals
    simpa [EnclosesExpressionSpan] using
      bitOrExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

private theorem equalityExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : equalityExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [equalityExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case «infix» operator left right =>
      rcases operator with ⟨operatorSpan, operatorPayload⟩
      cases operatorPayload
      all_goals try
        exact infix_candidate_encloses span ⟨operatorSpan, _⟩
          (expressionTokenPlanAt? .relational left)
          (expressionTokenPlanAt? .relational right) plan success
      all_goals
        simpa [EnclosesExpressionSpan] using
          relationalExpressionTokenPlan?_encloses
            (show Expression from
              ⟨span, .infix ⟨operatorSpan, _⟩ left right⟩)
            plan success
  all_goals
    simpa [EnclosesExpressionSpan] using
      relationalExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

private theorem logicalAndExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : logicalAndExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [logicalAndExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case «infix» operator left right =>
      rcases operator with ⟨operatorSpan, operatorPayload⟩
      cases operatorPayload
      all_goals try
        exact infix_candidate_encloses span ⟨operatorSpan, _⟩
          (expressionTokenPlanAt? .logicalAnd left)
          (expressionTokenPlanAt? .equality right) plan success
      all_goals
        simpa [EnclosesExpressionSpan] using
          equalityExpressionTokenPlan?_encloses
            (show Expression from
              ⟨span, .infix ⟨operatorSpan, _⟩ left right⟩)
            plan success
  all_goals
    simpa [EnclosesExpressionSpan] using
      equalityExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

private theorem logicalOrExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : logicalOrExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [logicalOrExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case «infix» operator left right =>
      rcases operator with ⟨operatorSpan, operatorPayload⟩
      cases operatorPayload
      all_goals try
        exact infix_candidate_encloses span ⟨operatorSpan, _⟩
          (expressionTokenPlanAt? .logicalOr left)
          (expressionTokenPlanAt? .logicalAnd right) plan success
      all_goals
        simpa [EnclosesExpressionSpan] using
          logicalAndExpressionTokenPlan?_encloses
            (show Expression from
              ⟨span, .infix ⟨operatorSpan, _⟩ left right⟩)
            plan success
  all_goals
    simpa [EnclosesExpressionSpan] using
      logicalAndExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

private theorem conditionalExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : conditionalExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [conditionalExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case keywordConditional condition thenBranch elseBranch =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨conditionPlan, conditionPlanEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨thenPlan, thenPlanEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨elsePlan, elsePlanEq, result⟩
      exact encloses_result result (by
        simp [TokenPlan.concat, TokenPlan.plain])
  case ternaryConditional condition thenBranch elseBranch =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨conditionPlan, conditionPlanEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨thenPlan, thenPlanEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨elsePlan, elsePlanEq, result⟩
      exact encloses_result result (by
        simp [TokenPlan.concat, TokenPlan.plain])
  all_goals
    simpa [EnclosesExpressionSpan] using
      logicalOrExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

private theorem annotationExpressionTokenPlan?_encloses
    (expression : Expression) (plan : TokenPlan)
    (success : annotationExpressionTokenPlan? expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  rcases expression with ⟨span, payload⟩
  unfold EnclosesExpressionSpan
  cases payload <;> simp only [annotationExpressionTokenPlan?] at success
  all_goals unfold expressionTokenPlanAt? at success
  all_goals simp only at success
  case annotation inner typeExpression =>
      rcases Option.bind_eq_some_iff.mp success with
        ⟨innerPlan, innerPlanEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨typePlan, typePlanEq, result⟩
      exact encloses_result result (by
        simp [TokenPlan.concat, TokenPlan.plain])
  all_goals
    simpa [EnclosesExpressionSpan] using
      conditionalExpressionTokenPlan?_encloses
        (show Expression from ⟨span, _⟩) plan success

/-- Every successful expression plan at every precedence level encloses a
nonempty core by the expression's exact retained source span. -/
theorem expressionTokenPlanAt?_encloses
    (level : ExpressionTokenLevel) (expression : Expression)
    (plan : TokenPlan)
    (success : expressionTokenPlanAt? level expression = some plan) :
    EnclosesExpressionSpan expression plan := by
  cases level with
  | annotation =>
      exact annotationExpressionTokenPlan?_encloses expression plan success
  | conditional =>
      exact conditionalExpressionTokenPlan?_encloses expression plan success
  | logicalOr =>
      exact logicalOrExpressionTokenPlan?_encloses expression plan success
  | logicalAnd =>
      exact logicalAndExpressionTokenPlan?_encloses expression plan success
  | equality =>
      exact equalityExpressionTokenPlan?_encloses expression plan success
  | relational =>
      exact relationalExpressionTokenPlan?_encloses expression plan success
  | bitOr =>
      exact bitOrExpressionTokenPlan?_encloses expression plan success
  | bitXor =>
      exact bitXorExpressionTokenPlan?_encloses expression plan success
  | bitAnd =>
      exact bitAndExpressionTokenPlan?_encloses expression plan success
  | additive =>
      exact additiveExpressionTokenPlan?_encloses expression plan success
  | multiplicative =>
      exact multiplicativeExpressionTokenPlan?_encloses expression plan
        success
  | «prefix» =>
      exact prefixExpressionTokenPlan?_encloses expression plan success
  | «postfix» =>
      exact postfixExpressionTokenPlan?_encloses expression plan success
  | atom =>
      exact atomExpressionTokenPlan?_encloses expression plan success

/-- Matching a successful expression plan fixes the first and last physical
tokens at the expression's retained source-span endpoints. -/
theorem expressionPlan_matches_endpoints
    (level : ExpressionTokenLevel) (expression : Expression)
    (plan : TokenPlan)
    (success : expressionTokenPlanAt? level expression = some plan)
    (encloses : EnclosesExpressionSpan expression plan)
    {actual : List Token}
    (relation : TokenSlot.ListMatches plan.slots actual) :
    TokenSlot.FirstSatisfies (.starts expression.span) actual ∧
      TokenSlot.LastSatisfies (.ends expression.span) actual := by
  rcases encloses with ⟨inner, planEq, nonempty⟩
  subst plan
  apply listMatches_enclose_endpoints
  · exact expressionTokenPlanAt?_wellAnchored level expression
      (inner.enclose expression.span) success
  · intro empty
    have := congrArg List.length empty
    simp at this
    exact nonempty this
  · exact relation

private theorem TokenSlot.FirstSatisfies.append
    {constraint : TokenSpanConstraint} {left right : List Token}
    (satisfies : TokenSlot.FirstSatisfies constraint left) :
    TokenSlot.FirstSatisfies constraint (left ++ right) := by
  cases left with
  | nil => contradiction
  | cons head tail => exact satisfies

private theorem TokenSlot.LastSatisfies.prepend
    {constraint : TokenSpanConstraint} {left right : List Token}
    (satisfies : TokenSlot.LastSatisfies constraint right) :
    TokenSlot.LastSatisfies constraint (left ++ right) := by
  induction left with
  | nil => exact satisfies
  | cons head tail induction =>
      cases right with
      | nil => contradiction
      | cons next rest =>
          cases tail with
          | nil => exact satisfies
          | cons second remaining => exact induction

private theorem firstSatisfies_between
    {file : WorkspaceFile} {leftSpan rightSpan : SourceSpan}
    {actual : List Token}
    (sources : TokensHaveSource file.id actual)
    (starts : TokenSlot.FirstSatisfies (.starts leftSpan) actual) :
    TokenSlot.FirstSatisfies
      (.starts (RuleReduction.between file leftSpan rightSpan ()).span)
      actual := by
  cases actual with
  | nil => contradiction
  | cons first rest =>
      exact ⟨sources first (by simp), starts.2⟩

private theorem lastSatisfies_between
    {file : WorkspaceFile} {leftSpan rightSpan : SourceSpan}
    {actual : List Token}
    (sources : TokensHaveSource file.id actual)
    (ends : TokenSlot.LastSatisfies (.ends rightSpan) actual) :
    TokenSlot.LastSatisfies
      (.ends (RuleReduction.between file leftSpan rightSpan ()).span)
      actual := by
  induction actual with
  | nil => contradiction
  | cons first rest induction =>
      cases rest with
      | nil => exact ⟨sources first (by simp), ends.2⟩
      | cons next rest =>
          exact induction
            (by
              intro token member
              exact sources token (by simp [member]))
            ends

private def infixPartPlan?
    (rightCandidate : Expression → Option TokenPlan)
    (part : Located InfixOperator × Expression) : Option TokenPlan := do
  let rightPlan ← rightCandidate part.2
  pure ((infixOperatorTokenPlan part.1).append rightPlan)

private theorem logicalOrSourceParts_mapM
    {file : WorkspaceFile} {tokens : List Token}
    (values : List (MatchedTerminal file tokens (.symbol .logicalOr) ×
      Expression)) :
    (values.map fun value =>
      EbnfValue.group
        (.sequence [.atom (.terminal (.symbol .logicalOr)),
          .atom (.nonterminal .logicalAnd)])
        (EbnfValue.sequence
          [.atom (.terminal (.symbol .logicalOr)),
            .atom (.nonterminal .logicalAnd)]
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .logicalOr) value.1)
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .logicalAnd value.2)
              EbnfValues.nil)))).mapM
        (fun value => value.tokenPlan? { plan? := ruleTokenPlan? }) =
      (values.map fun value =>
        (RuleReduction.infixOperator value.1 (.logicalOr value.1),
          value.2)).mapM
        (infixPartPlan? logicalAndExpressionTokenPlan?) := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      simp [infixPartPlan?, sourceRuleTokenPlanLayout, ruleTokenPlan?,
        RuleReduction.infixOperator, RuleReduction.terminalLoc,
        MatchedTerminal.physicalTokenPlan_symbol,
        infixOperatorTokenPlan, induction]

private theorem logicalAndSourceParts_mapM
    {file : WorkspaceFile} {tokens : List Token}
    (values : List (MatchedTerminal file tokens (.symbol .logicalAnd) ×
      Expression)) :
    (values.map fun value =>
      EbnfValue.group
        (.sequence [.atom (.terminal (.symbol .logicalAnd)),
          .atom (.nonterminal .equality)])
        (EbnfValue.sequence
          [.atom (.terminal (.symbol .logicalAnd)),
            .atom (.nonterminal .equality)]
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .logicalAnd) value.1)
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .equality value.2)
              EbnfValues.nil)))).mapM
        (fun value => value.tokenPlan? { plan? := ruleTokenPlan? }) =
      (values.map fun value =>
        (RuleReduction.infixOperator value.1 (.logicalAnd value.1),
          value.2)).mapM
        (infixPartPlan? equalityExpressionTokenPlan?) := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      simp [infixPartPlan?, sourceRuleTokenPlanLayout, ruleTokenPlan?,
        RuleReduction.infixOperator, RuleReduction.terminalLoc,
        MatchedTerminal.physicalTokenPlan_symbol,
        infixOperatorTokenPlan, induction]

private theorem bitOrSourceParts_mapM
    {file : WorkspaceFile} {tokens : List Token}
    (values : List (MatchedTerminal file tokens (.symbol .pipe) ×
      Expression)) :
    (values.map fun value =>
      EbnfValue.group
        (.sequence [.atom (.terminal (.symbol .pipe)),
          .atom (.nonterminal .bitXor)])
        (EbnfValue.sequence
          [.atom (.terminal (.symbol .pipe)),
            .atom (.nonterminal .bitXor)]
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .pipe) value.1)
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .bitXor value.2)
              EbnfValues.nil)))).mapM
        (fun value => value.tokenPlan? { plan? := ruleTokenPlan? }) =
      (values.map fun value =>
        (RuleReduction.infixOperator value.1 (.bitOr value.1),
          value.2)).mapM
        (infixPartPlan? bitXorExpressionTokenPlan?) := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      simp [infixPartPlan?, sourceRuleTokenPlanLayout, ruleTokenPlan?,
        RuleReduction.infixOperator, RuleReduction.terminalLoc,
        MatchedTerminal.physicalTokenPlan_symbol,
        infixOperatorTokenPlan, induction]

private theorem bitXorSourceParts_mapM
    {file : WorkspaceFile} {tokens : List Token}
    (values : List (MatchedTerminal file tokens (.symbol .caret) ×
      Expression)) :
    (values.map fun value =>
      EbnfValue.group
        (.sequence [.atom (.terminal (.symbol .caret)),
          .atom (.nonterminal .bitAnd)])
        (EbnfValue.sequence
          [.atom (.terminal (.symbol .caret)),
            .atom (.nonterminal .bitAnd)]
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .caret) value.1)
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .bitAnd value.2)
              EbnfValues.nil)))).mapM
        (fun value => value.tokenPlan? { plan? := ruleTokenPlan? }) =
      (values.map fun value =>
        (RuleReduction.infixOperator value.1 (.bitXor value.1),
          value.2)).mapM
        (infixPartPlan? bitAndExpressionTokenPlan?) := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      simp [infixPartPlan?, sourceRuleTokenPlanLayout, ruleTokenPlan?,
        RuleReduction.infixOperator, RuleReduction.terminalLoc,
        MatchedTerminal.physicalTokenPlan_symbol,
        infixOperatorTokenPlan, induction]

private theorem bitAndSourceParts_mapM
    {file : WorkspaceFile} {tokens : List Token}
    (values : List (MatchedTerminal file tokens (.symbol .amp) ×
      Expression)) :
    (values.map fun value =>
      EbnfValue.group
        (.sequence [.atom (.terminal (.symbol .amp)),
          .atom (.nonterminal .additive)])
        (EbnfValue.sequence
          [.atom (.terminal (.symbol .amp)),
            .atom (.nonterminal .additive)]
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .amp) value.1)
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .additive value.2)
              EbnfValues.nil)))).mapM
        (fun value => value.tokenPlan? { plan? := ruleTokenPlan? }) =
      (values.map fun value =>
        (RuleReduction.infixOperator value.1 (.bitAnd value.1),
          value.2)).mapM
        (infixPartPlan? additiveExpressionTokenPlan?) := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      simp [infixPartPlan?, sourceRuleTokenPlanLayout, ruleTokenPlan?,
        RuleReduction.infixOperator, RuleReduction.terminalLoc,
        MatchedTerminal.physicalTokenPlan_symbol,
        infixOperatorTokenPlan, induction]

private theorem additiveSourceParts_mapM
    {file : WorkspaceFile} {tokens : List Token}
    (values : List
      (Sum
        (MatchedTerminal file tokens (.symbol .plus))
        (MatchedTerminal file tokens (.symbol .minus)) × Expression)) :
    (values.map fun value =>
      EbnfValue.group
        (.sequence [
          .group (.choice [
            .atom (.terminal (.symbol .plus)),
            .atom (.terminal (.symbol .minus))]),
          .atom (.nonterminal .multiplicative)])
        (EbnfValue.sequence _
          (EbnfValues.cons _ _
            (EbnfValue.group _
              (match value.1 with
              | .inl plus =>
                  EbnfValue.choice _
                    ⟨⟨0, by decide⟩,
                      EbnfValue.terminalAtom (.symbol .plus) plus⟩
              | .inr minus =>
                  EbnfValue.choice _
                    ⟨⟨1, by decide⟩,
                      EbnfValue.terminalAtom (.symbol .minus) minus⟩))
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .multiplicative value.2)
              EbnfValues.nil)))).mapM
        (fun value => value.tokenPlan? { plan? := ruleTokenPlan? }) =
      (values.map fun value =>
        (match value.1 with
        | .inl plus =>
            RuleReduction.infixOperator plus (.add plus)
        | .inr minus =>
            RuleReduction.infixOperator minus (.subtract minus),
          value.2)).mapM
        (infixPartPlan? multiplicativeExpressionTokenPlan?) := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      rw [List.map_cons, List.mapM_cons, List.map_cons, List.mapM_cons]
      rw [induction]
      rcases value with ⟨operator, right⟩
      cases operator with
      | inl plus =>
          simp [infixPartPlan?, sourceRuleTokenPlanLayout, ruleTokenPlan?,
            RuleReduction.infixOperator, RuleReduction.terminalLoc,
            MatchedTerminal.physicalTokenPlan_symbol,
            infixOperatorTokenPlan]
      | inr minus =>
          simp [infixPartPlan?, sourceRuleTokenPlanLayout, ruleTokenPlan?,
            RuleReduction.infixOperator, RuleReduction.terminalLoc,
            MatchedTerminal.physicalTokenPlan_symbol,
            infixOperatorTokenPlan]

private theorem multiplicativeSourceParts_mapM
    {file : WorkspaceFile} {tokens : List Token}
    (values : List
      (Sum
        (MatchedTerminal file tokens (.symbol .star))
        (Sum
          (MatchedTerminal file tokens (.symbol .slash))
          (MatchedTerminal file tokens (.symbol .percent))) × Expression)) :
    (values.map fun value =>
      EbnfValue.group
        (.sequence [
          .group (.choice [
            .atom (.terminal (.symbol .star)),
            .atom (.terminal (.symbol .slash)),
            .atom (.terminal (.symbol .percent))]),
          .atom (.nonterminal .prefix)])
        (EbnfValue.sequence _
          (EbnfValues.cons _ _
            (EbnfValue.group _
              (match value.1 with
              | .inl star =>
                  EbnfValue.choice _
                    ⟨⟨0, by decide⟩,
                      EbnfValue.terminalAtom (.symbol .star) star⟩
              | .inr (.inl slash) =>
                  EbnfValue.choice _
                    ⟨⟨1, by decide⟩,
                      EbnfValue.terminalAtom (.symbol .slash) slash⟩
              | .inr (.inr percent) =>
                  EbnfValue.choice _
                    ⟨⟨2, by decide⟩,
                      EbnfValue.terminalAtom (.symbol .percent) percent⟩))
            (EbnfValues.cons _ _
              (EbnfValue.ruleAtom .prefix value.2)
              EbnfValues.nil)))).mapM
        (fun value => value.tokenPlan? { plan? := ruleTokenPlan? }) =
      (values.map fun value =>
        (match value.1 with
        | .inl star =>
            RuleReduction.infixOperator star (.multiply star)
        | .inr (.inl slash) =>
            RuleReduction.infixOperator slash (.divide slash)
        | .inr (.inr percent) =>
            RuleReduction.infixOperator percent (.modulo percent),
          value.2)).mapM
        (infixPartPlan? prefixExpressionTokenPlan?) := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      rw [List.map_cons, List.mapM_cons, List.map_cons, List.mapM_cons]
      rw [induction]
      rcases value with ⟨operator, right⟩
      rcases operator with star | remainder
      · simp [infixPartPlan?, sourceRuleTokenPlanLayout, ruleTokenPlan?,
          RuleReduction.infixOperator, RuleReduction.terminalLoc,
          MatchedTerminal.physicalTokenPlan_symbol,
          infixOperatorTokenPlan]
      · rcases remainder with slash | percent
        · simp [infixPartPlan?, sourceRuleTokenPlanLayout, ruleTokenPlan?,
            RuleReduction.infixOperator, RuleReduction.terminalLoc,
            MatchedTerminal.physicalTokenPlan_symbol,
            infixOperatorTokenPlan]
        · simp [infixPartPlan?, sourceRuleTokenPlanLayout, ruleTokenPlan?,
            RuleReduction.infixOperator, RuleReduction.terminalLoc,
            MatchedTerminal.physicalTokenPlan_symbol,
            infixOperatorTokenPlan]

private def infixFoldInputPlan?
    (targetCandidate rightCandidate : Expression → Option TokenPlan)
    (left : Expression)
    (parts : List (Located InfixOperator × Expression)) :
    Option TokenPlan := do
  let leftPlan ← targetCandidate left
  let partPlans ← parts.mapM (infixPartPlan? rightCandidate)
  pure (leftPlan.append (.concat partPlans))

private theorem nestedInfixFoldInput_eq
    (targetCandidate rightCandidate : Expression → Option TokenPlan)
    (left : Expression)
    (parts : List (Located InfixOperator × Expression)) :
    ((targetCandidate left).bind fun leftPlan =>
      ((parts.mapM (infixPartPlan? rightCandidate)).bind fun plans =>
        some (.concat plans)).bind fun tailPlan =>
          some (leftPlan.append tailPlan)) =
      infixFoldInputPlan? targetCandidate rightCandidate left parts := by
  unfold infixFoldInputPlan?
  cases targetCandidate left <;> simp
  cases parts.mapM (infixPartPlan? rightCandidate) <;> rfl

private theorem TokenPlanEvidence.mapSuccessfulCandidate
    {candidate replacement : Option TokenPlan} {actual : List Token}
    (evidence : TokenPlanEvidence candidate actual)
    (preserves : ∀ plan, candidate = Option.some plan →
      replacement = Option.some plan) :
    TokenPlanEvidence replacement actual := by
  rcases evidence with ⟨plan, success, relation⟩
  exact ⟨plan, preserves plan success, relation⟩

private theorem TokenPlanEvidence.sourceSequence
    {file : WorkspaceFile} {tokens : List Token}
    (children : List EbnfExpr)
    (values : EbnfValues file tokens children) {actual : List Token}
    (evidence : TokenPlanEvidence
      ((EbnfValue.sequence children values).tokenPlan?
        sourceRuleTokenPlanLayout) actual) :
    TokenPlanEvidence
      (values.tokenPlan? sourceRuleTokenPlanLayout) actual := by
  exact evidence.candidate_eq
    (EbnfValue.tokenPlan?_sequence
      sourceRuleTokenPlanLayout children values)

private theorem infixFoldInputPlan?_promoteLeft
    (lower target rightCandidate : Expression → Option TokenPlan)
    (promotes : ∀ expression plan,
      lower expression = some plan → target expression = some plan)
    (left : Expression) (parts : List (Located InfixOperator × Expression))
    (plan : TokenPlan)
    (success : infixFoldInputPlan? lower rightCandidate left parts =
      some plan) :
    infixFoldInputPlan? target rightCandidate left parts = some plan := by
  rcases Option.bind_eq_some_iff.mp success with
    ⟨leftPlan, leftPlanEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨partPlans, partPlansEq, result⟩
  injection result with planEq
  subst plan
  simp [infixFoldInputPlan?, promotes left leftPlan leftPlanEq,
    partPlansEq]

private theorem logicalAndExpressionTokenPlan?_promotesLogicalOr
    {expression : Expression} {plan : TokenPlan}
    (success : logicalAndExpressionTokenPlan? expression = some plan) :
    logicalOrExpressionTokenPlan? expression = some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;> try
    simpa [logicalOrExpressionTokenPlan?,
      logicalAndExpressionTokenPlan?, expressionTokenPlanAt?] using success
  case «infix» operator left right =>
    rcases operator with ⟨operatorSpan, operatorPayload⟩
    cases operatorPayload <;>
      simpa [logicalOrExpressionTokenPlan?,
        logicalAndExpressionTokenPlan?, expressionTokenPlanAt?] using success

private theorem equalityExpressionTokenPlan?_promotesLogicalAnd
    {expression : Expression} {plan : TokenPlan}
    (success : equalityExpressionTokenPlan? expression = some plan) :
    logicalAndExpressionTokenPlan? expression = some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;> try
    simpa [logicalAndExpressionTokenPlan?,
      equalityExpressionTokenPlan?, expressionTokenPlanAt?] using success
  case «infix» operator left right =>
    rcases operator with ⟨operatorSpan, operatorPayload⟩
    cases operatorPayload <;>
      simpa [logicalAndExpressionTokenPlan?,
        equalityExpressionTokenPlan?, expressionTokenPlanAt?] using success

private theorem bitXorExpressionTokenPlan?_promotesBitOr
    {expression : Expression} {plan : TokenPlan}
    (success : bitXorExpressionTokenPlan? expression = some plan) :
    bitOrExpressionTokenPlan? expression = some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;> try
    simpa [bitOrExpressionTokenPlan?,
      bitXorExpressionTokenPlan?, expressionTokenPlanAt?] using success
  case «infix» operator left right =>
    rcases operator with ⟨operatorSpan, operatorPayload⟩
    cases operatorPayload <;>
      simpa [bitOrExpressionTokenPlan?,
        bitXorExpressionTokenPlan?, expressionTokenPlanAt?] using success

private theorem bitAndExpressionTokenPlan?_promotesBitXor
    {expression : Expression} {plan : TokenPlan}
    (success : bitAndExpressionTokenPlan? expression = some plan) :
    bitXorExpressionTokenPlan? expression = some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;> try
    simpa [bitXorExpressionTokenPlan?,
      bitAndExpressionTokenPlan?, expressionTokenPlanAt?] using success
  case «infix» operator left right =>
    rcases operator with ⟨operatorSpan, operatorPayload⟩
    cases operatorPayload <;>
      simpa [bitXorExpressionTokenPlan?,
        bitAndExpressionTokenPlan?, expressionTokenPlanAt?] using success

private theorem additiveExpressionTokenPlan?_promotesBitAnd
    {expression : Expression} {plan : TokenPlan}
    (success : additiveExpressionTokenPlan? expression = some plan) :
    bitAndExpressionTokenPlan? expression = some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;> try
    simpa [bitAndExpressionTokenPlan?,
      additiveExpressionTokenPlan?, expressionTokenPlanAt?] using success
  case «infix» operator left right =>
    rcases operator with ⟨operatorSpan, operatorPayload⟩
    cases operatorPayload <;>
      simpa [bitAndExpressionTokenPlan?,
        additiveExpressionTokenPlan?, expressionTokenPlanAt?] using success

private theorem multiplicativeExpressionTokenPlan?_promotesAdditive
    {expression : Expression} {plan : TokenPlan}
    (success : multiplicativeExpressionTokenPlan? expression = some plan) :
    additiveExpressionTokenPlan? expression = some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;> try
    simpa [additiveExpressionTokenPlan?,
      multiplicativeExpressionTokenPlan?, expressionTokenPlanAt?] using success
  case «infix» operator left right =>
    rcases operator with ⟨operatorSpan, operatorPayload⟩
    cases operatorPayload <;>
      simpa [additiveExpressionTokenPlan?,
        multiplicativeExpressionTokenPlan?, expressionTokenPlanAt?] using success

private theorem prefixExpressionTokenPlan?_promotesMultiplicative
    {expression : Expression} {plan : TokenPlan}
    (success : prefixExpressionTokenPlan? expression = some plan) :
    multiplicativeExpressionTokenPlan? expression = some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;>
    simpa [multiplicativeExpressionTokenPlan?,
      prefixExpressionTokenPlan?, expressionTokenPlanAt?] using success

private theorem atomExpressionTokenPlan?_promotesPostfix
    {expression : Expression} {plan : TokenPlan}
    (success : atomExpressionTokenPlan? expression = some plan) :
    postfixExpressionTokenPlan? expression = some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;>
    simpa [postfixExpressionTokenPlan?,
      atomExpressionTokenPlan?, expressionTokenPlanAt?] using success

private theorem infixFoldInputPlan?_evidence
    {file : WorkspaceFile}
    (targetLevel rightLevel : ExpressionTokenLevel)
    (targetCandidate rightCandidate : Expression → Option TokenPlan)
    (Accepts : Located InfixOperator → Prop)
    (targetEq : targetCandidate = expressionTokenPlanAt? targetLevel)
    (rightEq : rightCandidate = expressionTokenPlanAt? rightLevel)
    (targetEncloses : ∀ expression plan,
      targetCandidate expression = some plan →
        EnclosesExpressionSpan expression plan)
    (rightEncloses : ∀ expression plan,
      rightCandidate expression = some plan →
        EnclosesExpressionSpan expression plan)
    (stepCandidate : ∀ left operator right leftPlan rightPlan,
      Accepts operator →
      targetCandidate left = some leftPlan →
      rightCandidate right = some rightPlan →
      targetCandidate
          (RuleReduction.between file left.span right.span
            (.infix operator left right)) =
        some (.enclose
          (RuleReduction.between file left.span right.span ()).span
          (.concat [leftPlan, infixOperatorTokenPlan operator,
            rightPlan])))
    (left : Expression)
    (parts : List (Located InfixOperator × Expression))
    (acceptedParts : ∀ part ∈ parts, Accepts part.1)
    {actual : List Token}
    (sources : TokensHaveSource file.id actual)
    (evidence : TokenPlanEvidence
      (infixFoldInputPlan? targetCandidate rightCandidate left parts)
      actual) :
    TokenPlanEvidence
      (targetCandidate (RuleReduction.foldInfixLeft file left parts))
      actual := by
  induction parts generalizing left actual with
  | nil =>
      simpa [infixFoldInputPlan?, RuleReduction.foldInfixLeft] using evidence
  | cons part rest induction =>
      rcases part with ⟨operator, right⟩
      have operatorAccepted : Accepts operator :=
        acceptedParts (operator, right) (by simp)
      have restAccepted : ∀ part ∈ rest, Accepts part.1 := by
        intro candidate member
        exact acceptedParts candidate (by simp [member])
      rcases evidence with ⟨wholePlan, candidateEq, relation⟩
      cases leftEq : targetCandidate left with
      | none =>
          simp [infixFoldInputPlan?, leftEq] at candidateEq
      | some leftPlan =>
          cases rightPlanEq : rightCandidate right with
          | none =>
              simp [infixFoldInputPlan?, infixPartPlan?, leftEq,
                rightPlanEq] at candidateEq
          | some rightPlan =>
              cases restPlansEq :
                  rest.mapM (infixPartPlan? rightCandidate) with
              | none =>
                  simp [infixFoldInputPlan?, infixPartPlan?, leftEq,
                    rightPlanEq, restPlansEq] at candidateEq
              | some restPlans =>
                  simp [infixFoldInputPlan?, infixPartPlan?, leftEq,
                    rightPlanEq, restPlansEq] at candidateEq
                  subst wholePlan
                  rw [← TokenPlan.append_assoc] at relation
                  rcases TokenSlot.ListMatches.split_append relation with
                    ⟨prefixActual, restActual, actualEq,
                      prefixRelation, restRelation⟩
                  have splitSources : TokensHaveSource file.id
                      (prefixActual ++ restActual) := by
                    intro token member
                    exact sources token (by rw [actualEq]; exact member)
                  have prefixSources : TokensHaveSource file.id prefixActual :=
                    splitSources.of_append_left
                  have restSources : TokensHaveSource file.id restActual :=
                    splitSources.of_append_right
                  rcases TokenSlot.ListMatches.split_append prefixRelation with
                    ⟨leftActual, partActual, prefixEq,
                      leftRelation, partRelation⟩
                  rcases TokenSlot.ListMatches.split_append partRelation with
                    ⟨operatorActual, rightActual, partEq,
                      operatorRelation, rightRelation⟩
                  have prefixSourceParts :
                      TokensHaveSource file.id
                        (leftActual ++ operatorActual ++ rightActual) := by
                    intro token member
                    apply prefixSources token
                    rw [prefixEq, partEq]
                    simpa [List.append_assoc] using member
                  have leftEndpoints := expressionPlan_matches_endpoints
                    targetLevel left leftPlan (by simpa [targetEq] using leftEq)
                    (targetEncloses left leftPlan leftEq) leftRelation
                  have rightEndpoints := expressionPlan_matches_endpoints
                    rightLevel right rightPlan
                    (by simpa [rightEq] using rightPlanEq)
                    (rightEncloses right rightPlan rightPlanEq) rightRelation
                  have combinedRelation : TokenSlot.ListMatches
                      (TokenPlan.concat [leftPlan,
                        infixOperatorTokenPlan operator,
                        rightPlan]).slots
                      (leftActual ++ operatorActual ++ rightActual) := by
                    simpa [TokenPlan.concat, List.append_assoc] using
                      leftRelation.append
                        (operatorRelation.append rightRelation)
                  have combinedAnchored :
                      (TokenPlan.concat [leftPlan,
                        infixOperatorTokenPlan operator,
                        rightPlan]).WellAnchored := by
                    apply TokenPlan.WellAnchored.concat
                    intro candidate member
                    simp only [List.mem_cons, List.not_mem_nil,
                      or_false] at member
                    rcases member with first | second | third
                    · subst candidate
                      exact expressionTokenPlanAt?_wellAnchored
                        targetLevel left _
                          (by simpa [targetEq] using leftEq)
                    · subst candidate
                      exact infixOperatorTokenPlan_wellAnchored operator
                    · subst candidate
                      exact expressionTokenPlanAt?_wellAnchored
                        rightLevel right _
                          (by simpa [rightEq] using rightPlanEq)
                  let next := RuleReduction.between file left.span right.span
                    (ExpressionPayload.infix operator left right)
                  let nextPlan := TokenPlan.enclose next.span
                    (TokenPlan.concat [leftPlan,
                      infixOperatorTokenPlan operator, rightPlan])
                  have nextRelation : TokenSlot.ListMatches nextPlan.slots
                      (leftActual ++ operatorActual ++ rightActual) := by
                    apply TokenSlot.ListMatches.enclose
                      combinedRelation combinedAnchored
                    · apply firstSatisfies_between prefixSourceParts
                      simpa [List.append_assoc] using
                        (TokenSlot.FirstSatisfies.append
                          (right := operatorActual ++ rightActual)
                          leftEndpoints.1)
                    · apply lastSatisfies_between prefixSourceParts
                      simpa [List.append_assoc] using
                        (TokenSlot.LastSatisfies.prepend
                          (left := leftActual ++ operatorActual)
                          rightEndpoints.2)
                  have nextEq : targetCandidate next = some nextPlan := by
                    exact stepCandidate left operator right leftPlan rightPlan
                      operatorAccepted leftEq rightPlanEq
                  have recursiveEvidence : TokenPlanEvidence
                      (infixFoldInputPlan? targetCandidate rightCandidate
                        next rest)
                      ((leftActual ++ operatorActual ++ rightActual) ++
                        restActual) := by
                    refine ⟨nextPlan.append (.concat restPlans), ?_, ?_⟩
                    · simp [infixFoldInputPlan?, nextEq, restPlansEq]
                    · exact nextRelation.append restRelation
                  have recursiveSources : TokensHaveSource file.id
                      ((leftActual ++ operatorActual ++ rightActual) ++
                        restActual) := by
                    intro token member
                    apply splitSources token
                    rw [prefixEq, partEq]
                    simpa [List.append_assoc] using member
                  have result := induction next restAccepted recursiveSources
                    recursiveEvidence
                  simpa [RuleReduction.foldInfixLeft, next,
                    List.append_assoc, actualEq, prefixEq, partEq] using result

private def AcceptsLogicalOr (operator : Located InfixOperator) : Prop :=
  operator.payload = .logicalOr

/-- The logical-or left fold preserves every retained token while rebuilding
the nested source spans of its left-associated AST. -/
theorem grammarRuleTokenPlanSound_logicalOr :
    GrammarRuleTokenPlanSound .logicalOr := by
  intro file tokens origin finish input output owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | logicalOr origin finish left rest =>
      let parts : List (Located InfixOperator × Expression) :=
        rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.logicalOr value.1),
            value.2)
      have sourceEvidence : TokenPlanEvidence
          (infixFoldInputPlan? logicalAndExpressionTokenPlan?
            logicalAndExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) := by
        simp only [EbnfExpr.children] at inputEvidence
        have sequenceEvidence := TokenPlanEvidence.sourceSequence
          _ _ inputEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_ruleAtom] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_star] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_nil] at sequenceEvidence
        simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?] at sequenceEvidence
        rw [logicalOrSourceParts_mapM rest] at sequenceEvidence
        apply sequenceEvidence.candidate_eq
        simpa [parts] using nestedInfixFoldInput_eq
          logicalAndExpressionTokenPlan?
          logicalAndExpressionTokenPlan? left parts
      have promotedEvidence : TokenPlanEvidence
          (infixFoldInputPlan? logicalOrExpressionTokenPlan?
            logicalAndExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) :=
        sourceEvidence.mapSuccessfulCandidate fun plan success =>
          infixFoldInputPlan?_promoteLeft
            logicalAndExpressionTokenPlan?
            logicalOrExpressionTokenPlan?
            logicalAndExpressionTokenPlan?
            (fun _ _ lowerSuccess =>
              logicalAndExpressionTokenPlan?_promotesLogicalOr lowerSuccess)
            left parts plan success
      change TokenPlanEvidence
        (logicalOrExpressionTokenPlan?
          (RuleReduction.foldInfixLeft file left parts))
        (PhysicalTokens tokens origin finish)
      apply infixFoldInputPlan?_evidence
        .logicalOr .logicalAnd
        logicalOrExpressionTokenPlan? logicalAndExpressionTokenPlan?
        AcceptsLogicalOr rfl rfl
        logicalOrExpressionTokenPlan?_encloses
        logicalAndExpressionTokenPlan?_encloses
      · intro foldLeft operator right leftPlan rightPlan accepted
          leftPlanEq rightPlanEq
        rcases operator with ⟨operatorSpan, operatorPayload⟩
        simp only [AcceptsLogicalOr] at accepted
        subst operatorPayload
        change expressionTokenPlanAt? .logicalOr foldLeft =
          some leftPlan at leftPlanEq
        change expressionTokenPlanAt? .logicalAnd right =
          some rightPlan at rightPlanEq
        simp [logicalOrExpressionTokenPlan?, expressionTokenPlanAt?,
          RuleReduction.between, leftPlanEq, rightPlanEq,
          infixOperatorTokenPlan]
      · intro part member
        rcases part with ⟨operator, right⟩
        simp only [parts, List.mem_map] at member
        rcases member with ⟨source, sourceMember, pairEq⟩
        injection pairEq with operatorEq rightEq
        subst operator
        simp [AcceptsLogicalOr, RuleReduction.infixOperator,
          RuleReduction.terminalLoc]
      · exact physicalTokens_haveSource owned
      · exact promotedEvidence

private def AcceptsLogicalAnd (operator : Located InfixOperator) : Prop :=
  operator.payload = .logicalAnd

/-- The logical-and fold preserves its complete physical token interval. -/
theorem grammarRuleTokenPlanSound_logicalAnd :
    GrammarRuleTokenPlanSound .logicalAnd := by
  intro file tokens origin finish input output owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | logicalAnd origin finish left rest =>
      let parts : List (Located InfixOperator × Expression) :=
        rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.logicalAnd value.1),
            value.2)
      have sourceEvidence : TokenPlanEvidence
          (infixFoldInputPlan? equalityExpressionTokenPlan?
            equalityExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) := by
        simp only [EbnfExpr.children] at inputEvidence
        have sequenceEvidence := TokenPlanEvidence.sourceSequence
          _ _ inputEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_ruleAtom] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_star] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_nil] at sequenceEvidence
        simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?] at sequenceEvidence
        rw [logicalAndSourceParts_mapM rest] at sequenceEvidence
        apply sequenceEvidence.candidate_eq
        simpa [parts] using nestedInfixFoldInput_eq
          equalityExpressionTokenPlan?
          equalityExpressionTokenPlan? left parts
      have promotedEvidence : TokenPlanEvidence
          (infixFoldInputPlan? logicalAndExpressionTokenPlan?
            equalityExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) :=
        sourceEvidence.mapSuccessfulCandidate fun plan success =>
          infixFoldInputPlan?_promoteLeft
            equalityExpressionTokenPlan?
            logicalAndExpressionTokenPlan?
            equalityExpressionTokenPlan?
            (fun _ _ lowerSuccess =>
              equalityExpressionTokenPlan?_promotesLogicalAnd lowerSuccess)
            left parts plan success
      change TokenPlanEvidence
        (logicalAndExpressionTokenPlan?
          (RuleReduction.foldInfixLeft file left parts))
        (PhysicalTokens tokens origin finish)
      apply infixFoldInputPlan?_evidence
        .logicalAnd .equality
        logicalAndExpressionTokenPlan? equalityExpressionTokenPlan?
        AcceptsLogicalAnd rfl rfl
        logicalAndExpressionTokenPlan?_encloses
        equalityExpressionTokenPlan?_encloses
      · intro foldLeft operator right leftPlan rightPlan accepted
          leftPlanEq rightPlanEq
        rcases operator with ⟨operatorSpan, operatorPayload⟩
        simp only [AcceptsLogicalAnd] at accepted
        subst operatorPayload
        change expressionTokenPlanAt? .logicalAnd foldLeft =
          some leftPlan at leftPlanEq
        change expressionTokenPlanAt? .equality right =
          some rightPlan at rightPlanEq
        simp [logicalAndExpressionTokenPlan?, expressionTokenPlanAt?,
          RuleReduction.between, leftPlanEq, rightPlanEq,
          infixOperatorTokenPlan]
      · intro part member
        rcases part with ⟨operator, right⟩
        simp only [parts, List.mem_map] at member
        rcases member with ⟨source, sourceMember, pairEq⟩
        injection pairEq with operatorEq rightEq
        subst operator
        simp [AcceptsLogicalAnd, RuleReduction.infixOperator,
          RuleReduction.terminalLoc]
      · exact physicalTokens_haveSource owned
      · exact promotedEvidence

private def AcceptsBitOr (operator : Located InfixOperator) : Prop :=
  operator.payload = .bitOr

/-- The bitwise-or fold preserves its complete physical token interval. -/
theorem grammarRuleTokenPlanSound_bitOr :
    GrammarRuleTokenPlanSound .bitOr := by
  intro file tokens origin finish input output owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | bitOr origin finish left rest =>
      let parts : List (Located InfixOperator × Expression) :=
        rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.bitOr value.1), value.2)
      have sourceEvidence : TokenPlanEvidence
          (infixFoldInputPlan? bitXorExpressionTokenPlan?
            bitXorExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) := by
        simp only [EbnfExpr.children] at inputEvidence
        have sequenceEvidence := TokenPlanEvidence.sourceSequence
          _ _ inputEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_ruleAtom] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_star] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_nil] at sequenceEvidence
        simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?] at sequenceEvidence
        rw [bitOrSourceParts_mapM rest] at sequenceEvidence
        apply sequenceEvidence.candidate_eq
        simpa [parts] using nestedInfixFoldInput_eq
          bitXorExpressionTokenPlan?
          bitXorExpressionTokenPlan? left parts
      have promotedEvidence : TokenPlanEvidence
          (infixFoldInputPlan? bitOrExpressionTokenPlan?
            bitXorExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) :=
        sourceEvidence.mapSuccessfulCandidate fun plan success =>
          infixFoldInputPlan?_promoteLeft
            bitXorExpressionTokenPlan?
            bitOrExpressionTokenPlan?
            bitXorExpressionTokenPlan?
            (fun _ _ lowerSuccess =>
              bitXorExpressionTokenPlan?_promotesBitOr lowerSuccess)
            left parts plan success
      change TokenPlanEvidence
        (bitOrExpressionTokenPlan?
          (RuleReduction.foldInfixLeft file left parts))
        (PhysicalTokens tokens origin finish)
      apply infixFoldInputPlan?_evidence
        .bitOr .bitXor
        bitOrExpressionTokenPlan? bitXorExpressionTokenPlan?
        AcceptsBitOr rfl rfl
        bitOrExpressionTokenPlan?_encloses
        bitXorExpressionTokenPlan?_encloses
      · intro foldLeft operator right leftPlan rightPlan accepted
          leftPlanEq rightPlanEq
        rcases operator with ⟨operatorSpan, operatorPayload⟩
        simp only [AcceptsBitOr] at accepted
        subst operatorPayload
        change expressionTokenPlanAt? .bitOr foldLeft =
          some leftPlan at leftPlanEq
        change expressionTokenPlanAt? .bitXor right =
          some rightPlan at rightPlanEq
        simp [bitOrExpressionTokenPlan?, expressionTokenPlanAt?,
          RuleReduction.between, leftPlanEq, rightPlanEq,
          infixOperatorTokenPlan]
      · intro part member
        rcases part with ⟨operator, right⟩
        simp only [parts, List.mem_map] at member
        rcases member with ⟨source, sourceMember, pairEq⟩
        injection pairEq with operatorEq rightEq
        subst operator
        simp [AcceptsBitOr, RuleReduction.infixOperator,
          RuleReduction.terminalLoc]
      · exact physicalTokens_haveSource owned
      · exact promotedEvidence

private def AcceptsBitXor (operator : Located InfixOperator) : Prop :=
  operator.payload = .bitXor

/-- The bitwise-xor fold preserves its complete physical token interval. -/
theorem grammarRuleTokenPlanSound_bitXor :
    GrammarRuleTokenPlanSound .bitXor := by
  intro file tokens origin finish input output owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | bitXor origin finish left rest =>
      let parts : List (Located InfixOperator × Expression) :=
        rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.bitXor value.1), value.2)
      have sourceEvidence : TokenPlanEvidence
          (infixFoldInputPlan? bitAndExpressionTokenPlan?
            bitAndExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) := by
        simp only [EbnfExpr.children] at inputEvidence
        have sequenceEvidence := TokenPlanEvidence.sourceSequence
          _ _ inputEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_ruleAtom] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_star] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_nil] at sequenceEvidence
        simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?] at sequenceEvidence
        rw [bitXorSourceParts_mapM rest] at sequenceEvidence
        apply sequenceEvidence.candidate_eq
        simpa [parts] using nestedInfixFoldInput_eq
          bitAndExpressionTokenPlan?
          bitAndExpressionTokenPlan? left parts
      have promotedEvidence : TokenPlanEvidence
          (infixFoldInputPlan? bitXorExpressionTokenPlan?
            bitAndExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) :=
        sourceEvidence.mapSuccessfulCandidate fun plan success =>
          infixFoldInputPlan?_promoteLeft
            bitAndExpressionTokenPlan?
            bitXorExpressionTokenPlan?
            bitAndExpressionTokenPlan?
            (fun _ _ lowerSuccess =>
              bitAndExpressionTokenPlan?_promotesBitXor lowerSuccess)
            left parts plan success
      change TokenPlanEvidence
        (bitXorExpressionTokenPlan?
          (RuleReduction.foldInfixLeft file left parts))
        (PhysicalTokens tokens origin finish)
      apply infixFoldInputPlan?_evidence
        .bitXor .bitAnd
        bitXorExpressionTokenPlan? bitAndExpressionTokenPlan?
        AcceptsBitXor rfl rfl
        bitXorExpressionTokenPlan?_encloses
        bitAndExpressionTokenPlan?_encloses
      · intro foldLeft operator right leftPlan rightPlan accepted
          leftPlanEq rightPlanEq
        rcases operator with ⟨operatorSpan, operatorPayload⟩
        simp only [AcceptsBitXor] at accepted
        subst operatorPayload
        change expressionTokenPlanAt? .bitXor foldLeft =
          some leftPlan at leftPlanEq
        change expressionTokenPlanAt? .bitAnd right =
          some rightPlan at rightPlanEq
        simp [bitXorExpressionTokenPlan?, expressionTokenPlanAt?,
          RuleReduction.between, leftPlanEq, rightPlanEq,
          infixOperatorTokenPlan]
      · intro part member
        rcases part with ⟨operator, right⟩
        simp only [parts, List.mem_map] at member
        rcases member with ⟨source, sourceMember, pairEq⟩
        injection pairEq with operatorEq rightEq
        subst operator
        simp [AcceptsBitXor, RuleReduction.infixOperator,
          RuleReduction.terminalLoc]
      · exact physicalTokens_haveSource owned
      · exact promotedEvidence

private def AcceptsBitAnd (operator : Located InfixOperator) : Prop :=
  operator.payload = .bitAnd

/-- The bitwise-and fold preserves its complete physical token interval. -/
theorem grammarRuleTokenPlanSound_bitAnd :
    GrammarRuleTokenPlanSound .bitAnd := by
  intro file tokens origin finish input output owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | bitAnd origin finish left rest =>
      let parts : List (Located InfixOperator × Expression) :=
        rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.bitAnd value.1), value.2)
      have sourceEvidence : TokenPlanEvidence
          (infixFoldInputPlan? additiveExpressionTokenPlan?
            additiveExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) := by
        simp only [EbnfExpr.children] at inputEvidence
        have sequenceEvidence := TokenPlanEvidence.sourceSequence
          _ _ inputEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_ruleAtom] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_star] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_nil] at sequenceEvidence
        simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?] at sequenceEvidence
        rw [bitAndSourceParts_mapM rest] at sequenceEvidence
        apply sequenceEvidence.candidate_eq
        simpa [parts] using nestedInfixFoldInput_eq
          additiveExpressionTokenPlan?
          additiveExpressionTokenPlan? left parts
      have promotedEvidence : TokenPlanEvidence
          (infixFoldInputPlan? bitAndExpressionTokenPlan?
            additiveExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) :=
        sourceEvidence.mapSuccessfulCandidate fun plan success =>
          infixFoldInputPlan?_promoteLeft
            additiveExpressionTokenPlan?
            bitAndExpressionTokenPlan?
            additiveExpressionTokenPlan?
            (fun _ _ lowerSuccess =>
              additiveExpressionTokenPlan?_promotesBitAnd lowerSuccess)
            left parts plan success
      change TokenPlanEvidence
        (bitAndExpressionTokenPlan?
          (RuleReduction.foldInfixLeft file left parts))
        (PhysicalTokens tokens origin finish)
      apply infixFoldInputPlan?_evidence
        .bitAnd .additive
        bitAndExpressionTokenPlan? additiveExpressionTokenPlan?
        AcceptsBitAnd rfl rfl
        bitAndExpressionTokenPlan?_encloses
        additiveExpressionTokenPlan?_encloses
      · intro foldLeft operator right leftPlan rightPlan accepted
          leftPlanEq rightPlanEq
        rcases operator with ⟨operatorSpan, operatorPayload⟩
        simp only [AcceptsBitAnd] at accepted
        subst operatorPayload
        change expressionTokenPlanAt? .bitAnd foldLeft =
          some leftPlan at leftPlanEq
        change expressionTokenPlanAt? .additive right =
          some rightPlan at rightPlanEq
        simp [bitAndExpressionTokenPlan?, expressionTokenPlanAt?,
          RuleReduction.between, leftPlanEq, rightPlanEq,
          infixOperatorTokenPlan]
      · intro part member
        rcases part with ⟨operator, right⟩
        simp only [parts, List.mem_map] at member
        rcases member with ⟨source, sourceMember, pairEq⟩
        injection pairEq with operatorEq rightEq
        subst operator
        simp [AcceptsBitAnd, RuleReduction.infixOperator,
          RuleReduction.terminalLoc]
      · exact physicalTokens_haveSource owned
      · exact promotedEvidence

private def AcceptsAdditive (operator : Located InfixOperator) : Prop :=
  operator.payload = .add ∨ operator.payload = .subtract

/-- The additive fold preserves plus and minus tokens at their exact spans. -/
theorem grammarRuleTokenPlanSound_additive :
    GrammarRuleTokenPlanSound .additive := by
  intro file tokens origin finish input output owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | additive origin finish left rest =>
      let parts : List (Located InfixOperator × Expression) :=
        rest.map fun value =>
          (match value.1 with
          | .inl plus =>
              RuleReduction.infixOperator plus (.add plus)
          | .inr minus =>
              RuleReduction.infixOperator minus (.subtract minus),
            value.2)
      have sourceEvidence : TokenPlanEvidence
          (infixFoldInputPlan? multiplicativeExpressionTokenPlan?
            multiplicativeExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) := by
        simp only [EbnfExpr.children] at inputEvidence
        have sequenceEvidence := TokenPlanEvidence.sourceSequence
          _ _ inputEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_ruleAtom] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_star] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_nil] at sequenceEvidence
        simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?] at sequenceEvidence
        erw [additiveSourceParts_mapM rest] at sequenceEvidence
        apply sequenceEvidence.candidate_eq
        simpa [parts] using nestedInfixFoldInput_eq
          multiplicativeExpressionTokenPlan?
          multiplicativeExpressionTokenPlan? left parts
      have promotedEvidence : TokenPlanEvidence
          (infixFoldInputPlan? additiveExpressionTokenPlan?
            multiplicativeExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) :=
        sourceEvidence.mapSuccessfulCandidate fun plan success =>
          infixFoldInputPlan?_promoteLeft
            multiplicativeExpressionTokenPlan?
            additiveExpressionTokenPlan?
            multiplicativeExpressionTokenPlan?
            (fun _ _ lowerSuccess =>
              multiplicativeExpressionTokenPlan?_promotesAdditive
                lowerSuccess)
            left parts plan success
      change TokenPlanEvidence
        (additiveExpressionTokenPlan?
          (RuleReduction.foldInfixLeft file left parts))
        (PhysicalTokens tokens origin finish)
      apply infixFoldInputPlan?_evidence
        .additive .multiplicative
        additiveExpressionTokenPlan? multiplicativeExpressionTokenPlan?
        AcceptsAdditive rfl rfl
        additiveExpressionTokenPlan?_encloses
        multiplicativeExpressionTokenPlan?_encloses
      · intro foldLeft operator right leftPlan rightPlan accepted
          leftPlanEq rightPlanEq
        rcases operator with ⟨operatorSpan, operatorPayload⟩
        simp only [AcceptsAdditive] at accepted
        rcases accepted with addEq | subtractEq
        · subst operatorPayload
          change expressionTokenPlanAt? .additive foldLeft =
            some leftPlan at leftPlanEq
          change expressionTokenPlanAt? .multiplicative right =
            some rightPlan at rightPlanEq
          simp [additiveExpressionTokenPlan?, expressionTokenPlanAt?,
            RuleReduction.between, leftPlanEq, rightPlanEq,
            infixOperatorTokenPlan]
        · subst operatorPayload
          change expressionTokenPlanAt? .additive foldLeft =
            some leftPlan at leftPlanEq
          change expressionTokenPlanAt? .multiplicative right =
            some rightPlan at rightPlanEq
          simp [additiveExpressionTokenPlan?, expressionTokenPlanAt?,
            RuleReduction.between, leftPlanEq, rightPlanEq,
            infixOperatorTokenPlan]
      · intro part member
        rcases part with ⟨operator, right⟩
        simp only [parts, List.mem_map] at member
        rcases member with ⟨source, sourceMember, pairEq⟩
        rcases source with ⟨sourceOperator, sourceRight⟩
        cases sourceOperator with
        | inl plus =>
            injection pairEq with operatorEq rightEq
            subst operator
            simp [AcceptsAdditive, RuleReduction.infixOperator,
              RuleReduction.terminalLoc]
        | inr minus =>
            injection pairEq with operatorEq rightEq
            subst operator
            simp [AcceptsAdditive, RuleReduction.infixOperator,
              RuleReduction.terminalLoc]
      · exact physicalTokens_haveSource owned
      · exact promotedEvidence

private def AcceptsMultiplicative
    (operator : Located InfixOperator) : Prop :=
  operator.payload = .multiply ∨ operator.payload = .divide ∨
    operator.payload = .modulo

/-- The multiplicative fold preserves all three operator tokens exactly. -/
theorem grammarRuleTokenPlanSound_multiplicative :
    GrammarRuleTokenPlanSound .multiplicative := by
  intro file tokens origin finish input output owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | multiplicative origin finish left rest =>
      let parts : List (Located InfixOperator × Expression) :=
        rest.map fun value =>
          (match value.1 with
          | .inl star =>
              RuleReduction.infixOperator star (.multiply star)
          | .inr (.inl slash) =>
              RuleReduction.infixOperator slash (.divide slash)
          | .inr (.inr percent) =>
              RuleReduction.infixOperator percent (.modulo percent),
            value.2)
      have sourceEvidence : TokenPlanEvidence
          (infixFoldInputPlan? prefixExpressionTokenPlan?
            prefixExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) := by
        simp only [EbnfExpr.children] at inputEvidence
        have sequenceEvidence := TokenPlanEvidence.sourceSequence
          _ _ inputEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_ruleAtom] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_cons] at sequenceEvidence
        rw [EbnfValue.tokenPlan?_star] at sequenceEvidence
        rw [EbnfValues.tokenPlan?_nil] at sequenceEvidence
        simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?] at sequenceEvidence
        erw [multiplicativeSourceParts_mapM rest] at sequenceEvidence
        apply sequenceEvidence.candidate_eq
        simpa [parts] using nestedInfixFoldInput_eq
          prefixExpressionTokenPlan?
          prefixExpressionTokenPlan? left parts
      have promotedEvidence : TokenPlanEvidence
          (infixFoldInputPlan? multiplicativeExpressionTokenPlan?
            prefixExpressionTokenPlan? left parts)
          (PhysicalTokens tokens origin finish) :=
        sourceEvidence.mapSuccessfulCandidate fun plan success =>
          infixFoldInputPlan?_promoteLeft
            prefixExpressionTokenPlan?
            multiplicativeExpressionTokenPlan?
            prefixExpressionTokenPlan?
            (fun _ _ lowerSuccess =>
              prefixExpressionTokenPlan?_promotesMultiplicative
                lowerSuccess)
            left parts plan success
      change TokenPlanEvidence
        (multiplicativeExpressionTokenPlan?
          (RuleReduction.foldInfixLeft file left parts))
        (PhysicalTokens tokens origin finish)
      apply infixFoldInputPlan?_evidence
        .multiplicative .prefix
        multiplicativeExpressionTokenPlan? prefixExpressionTokenPlan?
        AcceptsMultiplicative rfl rfl
        multiplicativeExpressionTokenPlan?_encloses
        prefixExpressionTokenPlan?_encloses
      · intro foldLeft operator right leftPlan rightPlan accepted
          leftPlanEq rightPlanEq
        rcases operator with ⟨operatorSpan, operatorPayload⟩
        simp only [AcceptsMultiplicative] at accepted
        rcases accepted with multiplyEq | divideEq | moduloEq
        · subst operatorPayload
          change expressionTokenPlanAt? .multiplicative foldLeft =
            some leftPlan at leftPlanEq
          change expressionTokenPlanAt? .prefix right =
            some rightPlan at rightPlanEq
          simp [multiplicativeExpressionTokenPlan?, expressionTokenPlanAt?,
            RuleReduction.between, leftPlanEq, rightPlanEq,
            infixOperatorTokenPlan]
        · subst operatorPayload
          change expressionTokenPlanAt? .multiplicative foldLeft =
            some leftPlan at leftPlanEq
          change expressionTokenPlanAt? .prefix right =
            some rightPlan at rightPlanEq
          simp [multiplicativeExpressionTokenPlan?, expressionTokenPlanAt?,
            RuleReduction.between, leftPlanEq, rightPlanEq,
            infixOperatorTokenPlan]
        · subst operatorPayload
          change expressionTokenPlanAt? .multiplicative foldLeft =
            some leftPlan at leftPlanEq
          change expressionTokenPlanAt? .prefix right =
            some rightPlan at rightPlanEq
          simp [multiplicativeExpressionTokenPlan?, expressionTokenPlanAt?,
            RuleReduction.between, leftPlanEq, rightPlanEq,
            infixOperatorTokenPlan]
      · intro part member
        rcases part with ⟨operator, right⟩
        simp only [parts, List.mem_map] at member
        rcases member with ⟨source, sourceMember, pairEq⟩
        rcases source with ⟨sourceOperator, sourceRight⟩
        rcases sourceOperator with star | remainder
        · injection pairEq with operatorEq rightEq
          subst operator
          simp [AcceptsMultiplicative, RuleReduction.infixOperator,
            RuleReduction.terminalLoc]
        · rcases remainder with slash | percent
          · injection pairEq with operatorEq rightEq
            subst operator
            simp [AcceptsMultiplicative, RuleReduction.infixOperator,
              RuleReduction.terminalLoc]
          · injection pairEq with operatorEq rightEq
            subst operator
            simp [AcceptsMultiplicative, RuleReduction.infixOperator,
              RuleReduction.terminalLoc]
      · exact physicalTokens_haveSource owned
      · exact promotedEvidence

/-- The token plan contributed by one postfix suffix after the source-exact
delimiter spans have been consumed into the enclosing expression span. -/
private def postfixPartPlainTokenPlan? :
    PostfixPartValue → Option TokenPlan
  | .call _ arguments _ => do
      let argumentPlans ← expressionTokenPlans? arguments
      pure (.parens (.commaSeparated argumentPlans))
  | .select _ field =>
      some (.append (.plain (.symbol .dot)) (identifierPlan field))
  | .index _ index _ => do
      let indexPlan ← expressionTokenPlan? index
      pure (.concat [
        .plain (.symbol .leftBracket), indexPlan,
        .plain (.symbol .rightBracket)])

/-- The physical right endpoint contributed by one postfix suffix. -/
private def postfixPartEndSpan : PostfixPartValue → SourceSpan
  | .call _ _ closeParen => closeParen
  | .select _ field => field.span
  | .index _ _ closeBracket => closeBracket

private theorem TokenSlot.ListMatches.twoExactToPlainAndEnds
    {firstKind secondKind : TokenKind}
    {firstSpan secondSpan : SourceSpan}
    {middle : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.concat [
        .exact firstKind firstSpan, middle,
        .exact secondKind secondSpan]).slots actual) :
    TokenSlot.ListMatches
        (TokenPlan.concat [
          .plain firstKind, middle,
          .plain secondKind]).slots actual ∧
      TokenSlot.LastSatisfies (.ends secondSpan) actual := by
  simp only [TokenPlan.concat, List.flatMap_cons, List.flatMap_nil,
    TokenPlan.exact, TokenPlan.plain, List.append_nil,
    List.singleton_append] at relation ⊢
  cases relation with
  | required firstMatch afterFirst =>
      rcases afterFirst.split_append with
        ⟨middleActual, afterMiddleActual, rfl,
          middleRelation, afterMiddleRelation⟩
      cases afterMiddleRelation with
      | required secondMatch afterSecond =>
          cases afterSecond
          rename_i firstToken secondToken
          constructor
          · exact .required firstMatch.toPlain <|
              middleRelation.append <|
                .required secondMatch.toPlain .nil
          · have exactSpan :=
                secondMatch.2 (.exact secondSpan)
                  (List.mem_cons_self ..)
            change secondToken.span = secondSpan at exactSpan
            have singletonEnd : TokenSlot.LastSatisfies
                (.ends secondSpan) [secondToken] := by
              change TokenSpanConstraint.Holds (.ends secondSpan) secondToken
              simpa [TokenSpanConstraint.Holds, exactSpan]
            have prefixed := TokenSlot.LastSatisfies.prepend
              (left := firstToken :: middleActual) singletonEnd
            simpa [List.append_assoc] using prefixed

private theorem TokenSlot.ListMatches.firstExactToPlainAndEnds
    {firstKind secondKind : TokenKind}
    {firstSpan secondSpan : SourceSpan}
    {actual : List Token}
    (relation : TokenSlot.ListMatches
      (TokenPlan.append
        (.exact firstKind firstSpan)
        (.exact secondKind secondSpan)).slots actual) :
    TokenSlot.ListMatches
        (TokenPlan.append
          (.plain firstKind)
          (.exact secondKind secondSpan)).slots actual ∧
      TokenSlot.LastSatisfies (.ends secondSpan) actual := by
  simp only [TokenPlan.append, TokenPlan.exact, TokenPlan.plain,
    List.singleton_append] at relation ⊢
  cases relation with
  | required firstMatch afterFirst =>
      cases afterFirst with
      | required secondMatch afterSecond =>
          cases afterSecond
          rename_i firstToken secondToken
          constructor
          · exact .required firstMatch.toPlain <|
              .required secondMatch .nil
          · change TokenSpanConstraint.Holds (.ends secondSpan) _
            have exactSpan := secondMatch.2 (.exact secondSpan)
              (List.mem_cons_self ..)
            change secondToken.span = secondSpan at exactSpan
            simpa [TokenSpanConstraint.Holds, exactSpan]

/-- Source suffix evidence can forget only its delimiter locations while
retaining the endpoint needed to locate the folded expression. -/
private theorem postfixPart_relation_plainAndEnds
    (part : PostfixPartValue) (sourcePlan : TokenPlan)
    (sourceSuccess : postfixPartTokenPlan? part = some sourcePlan)
    {actual : List Token}
    (relation : TokenSlot.ListMatches sourcePlan.slots actual) :
    ∃ plainPlan,
      postfixPartPlainTokenPlan? part = some plainPlan ∧
        TokenSlot.ListMatches plainPlan.slots actual ∧
        TokenSlot.LastSatisfies
          (.ends (postfixPartEndSpan part)) actual := by
  cases part with
  | call openParen arguments closeParen =>
      cases plansEq : expressionTokenPlans? arguments with
      | none => simp [postfixPartTokenPlan?, plansEq] at sourceSuccess
      | some plans =>
          simp [postfixPartTokenPlan?, plansEq] at sourceSuccess
          subst sourcePlan
          refine ⟨.parens (.commaSeparated plans), ?_, ?_⟩
          · simp [postfixPartPlainTokenPlan?, plansEq]
          · simpa [TokenPlan.parens, postfixPartEndSpan] using
              TokenSlot.ListMatches.twoExactToPlainAndEnds relation
  | select dot field =>
      simp [postfixPartTokenPlan?] at sourceSuccess
      subst sourcePlan
      refine ⟨.append (.plain (.symbol .dot)) (identifierPlan field),
        rfl, ?_⟩
      simpa [postfixPartPlainTokenPlan?, postfixPartEndSpan,
        identifierPlan] using
          (TokenSlot.ListMatches.firstExactToPlainAndEnds relation)
  | index openBracket index closeBracket =>
      cases planEq : expressionTokenPlan? index with
      | none => simp [postfixPartTokenPlan?, planEq] at sourceSuccess
      | some indexPlan =>
          simp [postfixPartTokenPlan?, planEq] at sourceSuccess
          subst sourcePlan
          refine ⟨.concat [
              .plain (.symbol .leftBracket), indexPlan,
              .plain (.symbol .rightBracket)], ?_, ?_⟩
          · simp [postfixPartPlainTokenPlan?, planEq]
          · exact TokenSlot.ListMatches.twoExactToPlainAndEnds relation

private theorem postfixPartPlainTokenPlan?_wellAnchored
    (part : PostfixPartValue) (plan : TokenPlan)
    (success : postfixPartPlainTokenPlan? part = some plan) :
    plan.WellAnchored := by
  cases part with
  | call openParen arguments closeParen =>
      cases plansEq : expressionTokenPlans? arguments with
      | none => simp [postfixPartPlainTokenPlan?, plansEq] at success
      | some plans =>
          simp [postfixPartPlainTokenPlan?, plansEq] at success
          subst plan
          exact TokenPlan.WellAnchored.parens _
  | select dot field =>
      simp [postfixPartPlainTokenPlan?] at success
      subst plan
      exact TokenPlan.WellAnchored.append
        (TokenPlan.WellAnchored.plain _)
        (identifierPlan_wellAnchored field)
  | index openBracket index closeBracket =>
      cases planEq : expressionTokenPlan? index with
      | none => simp [postfixPartPlainTokenPlan?, planEq] at success
      | some indexPlan =>
          simp [postfixPartPlainTokenPlan?, planEq] at success
          subst plan
          exact TokenPlan.WellAnchored.append
            (TokenPlan.WellAnchored.plain _)
            (TokenPlan.WellAnchored.append
              (expressionTokenPlan?_wellAnchored index indexPlan planEq)
              (TokenPlan.WellAnchored.plain _))

/-- The sole AST-shape side condition of postfix folding: a leading-dot
constructor without arguments cannot be reinterpreted as the callee of a
following call suffix. -/
def PostfixFoldAdmissible
    (receiver : Expression) : List PostfixPartValue → Prop
  | .call .. :: _ =>
      match receiver.payload with
      | .dotConstructor _ _ none => False
      | _ => True
  | _ => True

private def postfixStep
    (file : WorkspaceFile) (receiver : Expression) :
    PostfixPartValue → Expression
  | .call _ arguments closeParen =>
      RuleReduction.between file receiver.span closeParen
        (.call receiver arguments)
  | .select _ field =>
      RuleReduction.between file receiver.span field.span
        (.select receiver field)
  | .index _ index closeBracket =>
      RuleReduction.between file receiver.span closeBracket
        (.index receiver index)

private theorem foldPostfix_cons
    (file : WorkspaceFile) (receiver : Expression)
    (part : PostfixPartValue) (rest : List PostfixPartValue) :
    RuleReduction.foldPostfix file receiver (part :: rest) =
      RuleReduction.foldPostfix file
        (postfixStep file receiver part) rest := by
  cases part <;> rfl

/-- The exact source candidate before postfix suffixes are folded into the
left-associated expression AST. -/
def postfixFoldSourceTokenPlan?
    (receiver : Expression) (parts : List PostfixPartValue) :
    Option TokenPlan := do
  let receiverPlan ← atomExpressionTokenPlan? receiver
  let partPlans ← parts.mapM postfixPartTokenPlan?
  pure (receiverPlan.append (.concat partPlans))

private def postfixFoldWorkingTokenPlan?
    (receiver : Expression) (parts : List PostfixPartValue) :
    Option TokenPlan := do
  let receiverPlan ← postfixExpressionTokenPlan? receiver
  let partPlans ← parts.mapM postfixPartTokenPlan?
  pure (receiverPlan.append (.concat partPlans))

private theorem postfixFoldSourceTokenPlan?_promotes
    (receiver : Expression) (parts : List PostfixPartValue)
    (plan : TokenPlan)
    (success : postfixFoldSourceTokenPlan? receiver parts = some plan) :
    postfixFoldWorkingTokenPlan? receiver parts = some plan := by
  rcases Option.bind_eq_some_iff.mp success with
    ⟨receiverPlan, receiverEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨partPlans, partPlansEq, result⟩
  injection result with planEq
  subst plan
  simp [postfixFoldWorkingTokenPlan?,
    atomExpressionTokenPlan?_promotesPostfix receiverEq, partPlansEq]

private theorem PostfixFoldAdmissible.afterStep
    (file : WorkspaceFile) (receiver : Expression)
    (part : PostfixPartValue) (rest : List PostfixPartValue) :
    PostfixFoldAdmissible (postfixStep file receiver part) rest := by
  cases part <;> cases rest with
  | nil => trivial
  | cons head tail => cases head <;> trivial

private theorem postfixStep_span
    (file : WorkspaceFile) (receiver : Expression)
    (part : PostfixPartValue) :
    (postfixStep file receiver part).span =
      (RuleReduction.between file receiver.span
        (postfixPartEndSpan part) ()).span := by
  cases part <;> rfl

private theorem postfixStep_tokenPlan
    (file : WorkspaceFile) (receiver : Expression)
    (part : PostfixPartValue)
    (receiverPlan plainPartPlan : TokenPlan)
    (admissible : PostfixFoldAdmissible receiver (part :: []))
    (receiverEq : postfixExpressionTokenPlan? receiver = some receiverPlan)
    (plainPartEq :
      postfixPartPlainTokenPlan? part = some plainPartPlan) :
    postfixExpressionTokenPlan? (postfixStep file receiver part) =
      some ((receiverPlan.append plainPartPlan).enclose
        (postfixStep file receiver part).span) := by
  change expressionTokenPlanAt? .postfix receiver =
    some receiverPlan at receiverEq
  cases part with
  | call openParen arguments closeParen =>
      cases plansEq : expressionTokenPlans? arguments with
      | none =>
          simp [postfixPartPlainTokenPlan?, plansEq] at plainPartEq
      | some plans =>
          simp [postfixPartPlainTokenPlan?, plansEq] at plainPartEq
          subst plainPartPlan
          rcases receiver with ⟨receiverSpan, receiverPayload⟩
          cases receiverPayload <;>
            simp_all [PostfixFoldAdmissible, postfixStep,
              postfixExpressionTokenPlan?, expressionTokenPlanAt?,
              RuleReduction.between, plansEq]
          case dotConstructor constructorArguments =>
            cases constructorArguments <;>
              simp_all [PostfixFoldAdmissible, postfixStep,
                postfixExpressionTokenPlan?, expressionTokenPlanAt?,
                RuleReduction.between, plansEq]
  | select dot field =>
      simp [postfixPartPlainTokenPlan?] at plainPartEq
      subst plainPartPlan
      simp [postfixStep, postfixExpressionTokenPlan?,
        expressionTokenPlanAt?, RuleReduction.between, receiverEq]
  | index openBracket index closeBracket =>
      cases indexEq : expressionTokenPlan? index with
      | none =>
          have directEq : expressionTokenPlanAt? .annotation index = none :=
            indexEq
          change ((expressionTokenPlanAt? .annotation index).bind fun plan =>
            some (.concat [
              .plain (.symbol .leftBracket), plan,
              .plain (.symbol .rightBracket)])) =
            some plainPartPlan at plainPartEq
          simp [postfixPartPlainTokenPlan?, directEq] at plainPartEq
      | some indexPlan =>
          have directEq : expressionTokenPlanAt? .annotation index =
              some indexPlan := indexEq
          change ((expressionTokenPlanAt? .annotation index).bind fun plan =>
            some (.concat [
              .plain (.symbol .leftBracket), plan,
              .plain (.symbol .rightBracket)])) =
            some plainPartPlan at plainPartEq
          simp [postfixPartPlainTokenPlan?, directEq] at plainPartEq
          subst plainPartPlan
          simp [postfixStep, postfixExpressionTokenPlan?,
            expressionTokenPlanAt?, RuleReduction.between,
            receiverEq, directEq]

private theorem postfixFoldWorkingTokenPlan?_evidence
    {file : WorkspaceFile}
    (receiver : Expression) (parts : List PostfixPartValue)
    (admissible : PostfixFoldAdmissible receiver parts)
    {actual : List Token}
    (sources : TokensHaveSource file.id actual)
    (evidence : TokenPlanEvidence
      (postfixFoldWorkingTokenPlan? receiver parts) actual) :
    TokenPlanEvidence
      (postfixExpressionTokenPlan?
        (RuleReduction.foldPostfix file receiver parts)) actual := by
  induction parts generalizing receiver actual with
  | nil =>
      simpa [postfixFoldWorkingTokenPlan?,
        RuleReduction.foldPostfix] using evidence
  | cons part rest induction =>
      rcases evidence with ⟨wholePlan, candidateEq, relation⟩
      cases receiverEq : postfixExpressionTokenPlan? receiver with
      | none =>
          simp [postfixFoldWorkingTokenPlan?, receiverEq] at candidateEq
      | some receiverPlan =>
          cases partEq : postfixPartTokenPlan? part with
          | none =>
              simp [postfixFoldWorkingTokenPlan?, receiverEq,
                List.mapM_cons, partEq] at candidateEq
          | some partPlan =>
              cases restPlansEq : rest.mapM postfixPartTokenPlan? with
              | none =>
                  simp [postfixFoldWorkingTokenPlan?, receiverEq,
                    List.mapM_cons, partEq, restPlansEq] at candidateEq
              | some restPlans =>
                  simp [postfixFoldWorkingTokenPlan?, receiverEq,
                    List.mapM_cons, partEq, restPlansEq] at candidateEq
                  subst wholePlan
                  rw [← TokenPlan.append_assoc] at relation
                  rcases TokenSlot.ListMatches.split_append relation with
                    ⟨prefixActual, restActual, actualEq,
                      prefixRelation, restRelation⟩
                  rcases TokenSlot.ListMatches.split_append prefixRelation with
                    ⟨receiverActual, partActual, prefixEq,
                      receiverRelation, partRelation⟩
                  have splitSources : TokensHaveSource file.id
                      (prefixActual ++ restActual) := by
                    intro token member
                    exact sources token (by rw [actualEq]; exact member)
                  have prefixSources : TokensHaveSource file.id prefixActual :=
                    splitSources.of_append_left
                  have receiverSources : TokensHaveSource file.id
                      receiverActual := by
                    intro token member
                    apply prefixSources token
                    rw [prefixEq]
                    exact List.mem_append_left _ member
                  rcases postfixPart_relation_plainAndEnds
                      part partPlan partEq partRelation with
                    ⟨plainPartPlan, plainPartEq, plainPartRelation,
                      partEnds⟩
                  have receiverEndpoints := expressionPlan_matches_endpoints
                    .postfix receiver receiverPlan receiverEq
                    (postfixExpressionTokenPlan?_encloses
                      receiver receiverPlan receiverEq)
                    receiverRelation
                  let next : Expression := postfixStep file receiver part
                  let nextInner := receiverPlan.append plainPartPlan
                  let nextPlan := nextInner.enclose next.span
                  have nextInnerRelation : TokenSlot.ListMatches
                      nextInner.slots (receiverActual ++ partActual) :=
                    receiverRelation.append plainPartRelation
                  have nextInnerAnchored : nextInner.WellAnchored :=
                    TokenPlan.WellAnchored.append
                      (expressionTokenPlanAt?_wellAnchored
                        .postfix receiver receiverPlan receiverEq)
                      (postfixPartPlainTokenPlan?_wellAnchored
                        part plainPartPlan plainPartEq)
                  have prefixSourceParts : TokensHaveSource file.id
                      (receiverActual ++ partActual) := by
                    intro token member
                    apply prefixSources token
                    simpa [prefixEq] using member
                  have nextRelation : TokenSlot.ListMatches nextPlan.slots
                      (receiverActual ++ partActual) := by
                    apply TokenSlot.ListMatches.enclose
                      nextInnerRelation nextInnerAnchored
                    · simp only [next]
                      rw [postfixStep_span]
                      apply firstSatisfies_between prefixSourceParts
                      exact TokenSlot.FirstSatisfies.append
                        receiverEndpoints.1
                    · simp only [next]
                      rw [postfixStep_span]
                      apply lastSatisfies_between prefixSourceParts
                      exact TokenSlot.LastSatisfies.prepend partEnds
                  have nextEq :
                      postfixExpressionTokenPlan? next = some nextPlan := by
                    have headAdmissible :
                        PostfixFoldAdmissible receiver (part :: []) := by
                      cases part <;> simpa [PostfixFoldAdmissible] using
                        admissible
                    simpa [next, nextPlan, nextInner] using
                      postfixStep_tokenPlan file receiver part
                        receiverPlan plainPartPlan headAdmissible
                        receiverEq plainPartEq
                  have recursiveEvidence : TokenPlanEvidence
                      (postfixFoldWorkingTokenPlan? next rest)
                      ((receiverActual ++ partActual) ++ restActual) := by
                    refine ⟨nextPlan.append (.concat restPlans), ?_, ?_⟩
                    · simp [postfixFoldWorkingTokenPlan?, nextEq,
                        restPlansEq]
                    · exact nextRelation.append restRelation
                  have recursiveSources : TokensHaveSource file.id
                      ((receiverActual ++ partActual) ++ restActual) := by
                    intro token member
                    apply splitSources token
                    rw [prefixEq]
                    simpa [List.append_assoc] using member
                  have result := induction next
                    (PostfixFoldAdmissible.afterStep
                      file receiver part rest)
                    recursiveSources recursiveEvidence
                  have resultAtActual := result.actual_eq (show
                      (receiverActual ++ partActual) ++ restActual =
                        actual from by
                        rw [← prefixEq, ← actualEq])
                  rw [foldPostfix_cons]
                  exact resultAtActual

/-- Exact source token evidence survives admissible postfix folding. -/
theorem postfixFold_tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (receiver : Expression) (parts : List PostfixPartValue)
    (admissible : PostfixFoldAdmissible receiver parts)
    (owned : TokensOwnedBy file tokens)
    (evidence : TokenPlanEvidence
      (postfixFoldSourceTokenPlan? receiver parts)
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence
      (postfixExpressionTokenPlan?
        (RuleReduction.foldPostfix file receiver parts))
      (PhysicalTokens tokens origin finish) := by
  have promoted : TokenPlanEvidence
      (postfixFoldWorkingTokenPlan? receiver parts)
      (PhysicalTokens tokens origin finish) :=
    evidence.mapSuccessfulCandidate fun plan success =>
      postfixFoldSourceTokenPlan?_promotes receiver parts plan success
  exact postfixFoldWorkingTokenPlan?_evidence receiver parts admissible
    (physicalTokens_haveSource owned) promoted

end Solcore.Surface.Multi
