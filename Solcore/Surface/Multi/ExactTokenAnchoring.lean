import Solcore.Surface.Multi.ExactTokenDeclaration
import Solcore.Surface.Multi.ExactTokenProperties

set_option autoImplicit false

namespace Solcore.Surface.Multi

/-!
This module proves that every successful declaration-level exact-token visitor
produces a plan whose physical endpoints are mandatory.  Most declarations
have fixed opening and closing tokens, so their interior expression, type, and
statement plans cannot weaken this property.  Functions are the one asymmetric
case: optional modifiers precede the required `function` token, while a braced
body supplies the required final token.  The local one-sided endpoint predicates
compose those two facts without assuming anything false about the intervening
plans.

The final theorem follows the public empty/cons equations of
`declarationModulePlan?`, preserving the source order of top-level plans.
-/

namespace TokenPlan.WellAnchored

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

private theorem lastRequiredShape_append_nonempty
    (first : Bool) (rest : List Bool) (next : Bool) (tail : List Bool) :
    lastRequiredShape first (rest ++ next :: tail) =
      lastRequiredShape next tail := by
  induction rest generalizing first with
  | nil => rfl
  | cons head rest induction =>
      exact induction head

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

@[simp] private theorem isRequired_addConstraintView
    (constraint : TokenSpanConstraint) (slot : TokenSlot) :
    (addConstraintView constraint slot).isRequired = slot.isRequired := by
  cases slot <;> rfl

@[simp] private theorem requiredShape_addFirstView
    (constraint : TokenSpanConstraint) (slots : List TokenSlot) :
    (addFirstView constraint slots).map TokenSlot.isRequired =
      slots.map TokenSlot.isRequired := by
  cases slots with
  | nil => rfl
  | cons first rest => simp [addFirstView]

@[simp] private theorem requiredShape_addLastView
    (constraint : TokenSpanConstraint) (slots : List TokenSlot) :
    (addLastView constraint slots).map TokenSlot.isRequired =
      slots.map TokenSlot.isRequired := by
  simp [addLastView, List.map_reverse]

private theorem requiredShape_enclose (span : SourceSpan)
    (slots : List TokenSlot) :
    (TokenSlot.enclose span slots).map TokenSlot.isRequired =
      slots.map TokenSlot.isRequired := by
  rw [enclose_eq_view]
  simp

/-- The generated plan has a mandatory physical first token. -/
def StartsRequired (plan : TokenPlan) : Prop :=
  ∃ rest, plan.slots.map TokenSlot.isRequired = true :: rest

/-- The generated plan has a mandatory physical last token. -/
def EndsRequired (plan : TokenPlan) : Prop :=
  ∃ initial, plan.slots.map TokenSlot.isRequired = initial ++ [true]

namespace StartsRequired

theorem enclose {plan : TokenPlan} (starts : StartsRequired plan)
    (span : SourceSpan) : StartsRequired (plan.enclose span) := by
  rcases starts with ⟨rest, shape⟩
  exact ⟨rest, by simpa [TokenPlan.enclose, requiredShape_enclose]
    using shape⟩

theorem concat_plain_first (kind : TokenKind) (rest : List TokenPlan) :
    StartsRequired (TokenPlan.concat (TokenPlan.plain kind :: rest)) := by
  exact ⟨rest.flatMap (fun plan => plan.slots) |>.map
      TokenSlot.isRequired, by
    simp [TokenPlan.concat, TokenPlan.plain, TokenSlot.isRequired]⟩

theorem prepend_anchored {left right : TokenPlan}
    (leftAnchored : left.WellAnchored) (rightStarts : StartsRequired right) :
    StartsRequired (left.append right) := by
  cases left with
  | mk slots =>
      cases slots with
      | nil =>
          rcases rightStarts with ⟨rest, shape⟩
          exact ⟨rest, by simpa [TokenPlan.append] using shape⟩
      | cons first rest =>
          have firstRequired : first.isRequired = true := by
            unfold TokenPlan.WellAnchored at leftAnchored
            rw [wellAnchored_eq_slotsWellAnchored] at leftAnchored
            simp only [slotsWellAnchored, Bool.and_eq_true] at leftAnchored
            exact leftAnchored.1
          cases first with
          | required expected =>
              exact ⟨(rest ++ right.slots).map TokenSlot.isRequired, by
                simp [TokenPlan.append, TokenSlot.isRequired]⟩
          | optional expected =>
              simp [TokenSlot.isRequired] at firstRequired

end StartsRequired

namespace EndsRequired

theorem enclose {plan : TokenPlan} (ends : EndsRequired plan)
    (span : SourceSpan) : EndsRequired (plan.enclose span) := by
  rcases ends with ⟨initial, shape⟩
  exact ⟨initial, by simpa [TokenPlan.enclose, requiredShape_enclose]
    using shape⟩

theorem append_plain_last (initial : TokenPlan) (kind : TokenKind) :
    EndsRequired (initial.append (.plain kind)) := by
  exact ⟨initial.slots.map TokenSlot.isRequired, by
    simp [TokenPlan.append, TokenPlan.plain, TokenSlot.isRequired]⟩

theorem concat_exact_last (initial : List TokenPlan)
    (kind : TokenKind) (span : SourceSpan) :
    EndsRequired (TokenPlan.concat
      (initial ++ [TokenPlan.exact kind span])) := by
  exact ⟨(initial.flatMap (fun plan => plan.slots)).map
      TokenSlot.isRequired, by
    simp [TokenPlan.concat, TokenPlan.exact, List.flatMap_append,
      TokenSlot.isRequired]⟩

theorem concat_exact_last_two (first second : TokenPlan)
    (kind : TokenKind) (span : SourceSpan) :
    EndsRequired (TokenPlan.concat
      [first, second, TokenPlan.exact kind span]) := by
  simpa using concat_exact_last [first, second] kind span

end EndsRequired

private theorem wellAnchored_of_required_shape
    (plan : TokenPlan) (middle : List Bool)
    (shape : plan.slots.map TokenSlot.isRequired =
      true :: middle ++ [true]) :
    plan.WellAnchored := by
  cases plan with
  | mk slots =>
      cases slots with
      | nil => simp at shape
      | cons first rest =>
          cases first with
          | required expected =>
              have restShape : rest.map TokenSlot.isRequired =
                  middle ++ [true] := by
                simpa [TokenSlot.isRequired] using
                  congrArg List.tail shape
              unfold TokenPlan.WellAnchored
              rw [wellAnchored_eq_slotsWellAnchored]
              simp only [slotsWellAnchored, TokenSlot.isRequired,
                Bool.true_and]
              rw [restShape, lastRequiredShape_append_nonempty]
              rfl
          | optional expected =>
              simp [TokenSlot.isRequired] at shape

theorem of_starts_ends_append
    {left right : TokenPlan}
    (starts : StartsRequired left) (ends : EndsRequired right) :
    (left.append right).WellAnchored := by
  rcases starts with ⟨leftRest, leftShape⟩
  rcases ends with ⟨rightInitial, rightShape⟩
  apply wellAnchored_of_required_shape _ (leftRest ++ rightInitial)
  simp only [TokenPlan.append, List.map_append]
  rw [leftShape, rightShape]
  simp

theorem concat_plain_bookended_one
    (first last : TokenKind) (one : TokenPlan) :
    (TokenPlan.concat [TokenPlan.plain first, one,
      TokenPlan.plain last]).WellAnchored := by
  simpa using TokenPlan.WellAnchored.concatPlainBookended
    first last [one]

theorem concat_plain_bookended_two
    (first last : TokenKind) (one two : TokenPlan) :
    (TokenPlan.concat [TokenPlan.plain first, one, two,
      TokenPlan.plain last]).WellAnchored := by
  simpa using TokenPlan.WellAnchored.concatPlainBookended
    first last [one, two]

theorem concat_plain_bookended_three
    (first last : TokenKind) (one two three : TokenPlan) :
    (TokenPlan.concat [TokenPlan.plain first, one, two, three,
      TokenPlan.plain last]).WellAnchored := by
  simpa using TokenPlan.WellAnchored.concatPlainBookended
    first last [one, two, three]

theorem concat_plain_bookended_four
    (first last : TokenKind) (one two three four : TokenPlan) :
    (TokenPlan.concat [TokenPlan.plain first, one, two, three, four,
      TokenPlan.plain last]).WellAnchored := by
  simpa using TokenPlan.WellAnchored.concatPlainBookended
    first last [one, two, three, four]

theorem concat_plain_bookended_six
    (first last : TokenKind) (one two three four five six : TokenPlan) :
    (TokenPlan.concat [TokenPlan.plain first, one, two, three, four,
      five, six, TokenPlan.plain last]).WellAnchored := by
  simpa using TokenPlan.WellAnchored.concatPlainBookended first last
    [one, two, three, four, five, six]

end TokenPlan.WellAnchored

theorem hidingClausePlan?_wellAnchored
    (clause : HidingClause) (plan : TokenPlan)
    (success : hidingClausePlan? clause = some plan) :
    plan.WellAnchored := by
  unfold hidingClausePlan? at success
  injection success with planEq
  subst plan
  apply TokenPlan.WellAnchored.enclose
  change (TokenPlan.concat [
    .plain (.hardKeyword .hidingKw),
    .plain (.symbol .leftBrace),
    .commaSeparated (clause.payload.names.map identifierPlan),
    .plain (.symbol .rightBrace)]).WellAnchored
  simpa using TokenPlan.WellAnchored.concatPlainBookended
    (.hardKeyword .hidingKw) (.symbol .rightBrace)
    [.plain (.symbol .leftBrace),
      .commaSeparated (clause.payload.names.map identifierPlan)]

theorem importSelectionPlan?_wellAnchored
    (selection : ImportSelection) (plan : TokenPlan)
    (success : importSelectionPlan? selection = some plan) :
    plan.WellAnchored := by
  unfold importSelectionPlan? at success
  have decomposed := Option.bind_eq_some_iff.mp success
  rcases decomposed with ⟨entryPlans, _entriesEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  apply TokenPlan.WellAnchored.enclose
  simpa using TokenPlan.WellAnchored.concatPlainBookended
    (.symbol .leftBrace) (.symbol .rightBrace)
    [.commaSeparated entryPlans]

theorem forallClausePlan?_wellAnchored
    (clause : ForallClause) (plan : TokenPlan)
    (success : forallClausePlan? clause = some plan) :
    plan.WellAnchored := by
  unfold forallClausePlan? at success
  have firstResult := Option.bind_eq_some_iff.mp success
  rcases firstResult with ⟨first, _firstEq, success⟩
  have restResult := Option.bind_eq_some_iff.mp success
  rcases restResult with ⟨rest, _restEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  apply TokenPlan.WellAnchored.enclose
  apply TokenPlan.WellAnchored.concat_plain_bookended_two

private theorem forallClausePlan?_startsRequired
    (clause : ForallClause) (plan : TokenPlan)
    (success : forallClausePlan? clause = some plan) :
    TokenPlan.WellAnchored.StartsRequired plan := by
  unfold forallClausePlan? at success
  have firstResult := Option.bind_eq_some_iff.mp success
  rcases firstResult with ⟨first, _firstEq, success⟩
  have restResult := Option.bind_eq_some_iff.mp success
  rcases restResult with ⟨rest, _restEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  apply TokenPlan.WellAnchored.StartsRequired.enclose
  apply TokenPlan.WellAnchored.StartsRequired.concat_plain_first

theorem genericPrefixPlan?_wellAnchored
    (generic : GenericPrefix) (plan : TokenPlan)
    (success : genericPrefixPlan? generic = some plan) :
    plan.WellAnchored := by
  unfold genericPrefixPlan? at success
  have forallResult := Option.bind_eq_some_iff.mp success
  rcases forallResult with ⟨forallPlan, forallEq, success⟩
  cases contextEq : generic.payload.context with
  | none =>
      simp [contextEq] at success
      subst plan
      apply TokenPlan.WellAnchored.enclose
      simpa [TokenPlan.append] using TokenPlan.WellAnchored.append
        (forallClausePlan?_wellAnchored _ _ forallEq)
        TokenPlan.WellAnchored.empty
  | some predicates =>
      rw [contextEq] at success
      have predicatesResult := Option.bind_eq_some_iff.mp success
      rcases predicatesResult with
        ⟨predicatesPlan, _predicatesEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      exact TokenPlan.WellAnchored.of_starts_ends_append
        (forallClausePlan?_startsRequired _ _ forallEq)
        (TokenPlan.WellAnchored.EndsRequired.append_plain_last
          predicatesPlan (.symbol .fatArrow))

private theorem functionSignaturePlan?_startsRequired
    (signature : FunctionSignature) (plan : TokenPlan)
    (success : functionSignaturePlan? signature = some plan) :
    TokenPlan.WellAnchored.StartsRequired plan := by
  unfold functionSignaturePlan? at success
  have genericResult := Option.bind_eq_some_iff.mp success
  rcases genericResult with ⟨generic, genericEq, success⟩
  have publicResult := Option.bind_eq_some_iff.mp success
  rcases publicResult with ⟨publicModifier, publicEq, success⟩
  have payableResult := Option.bind_eq_some_iff.mp success
  rcases payableResult with ⟨payableModifier, payableEq, success⟩
  have parametersResult := Option.bind_eq_some_iff.mp success
  rcases parametersResult with ⟨parameters, _parametersEq, success⟩
  have returnResult := Option.bind_eq_some_iff.mp success
  rcases returnResult with ⟨returnType, _returnEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  have genericAnchored : generic.WellAnchored := by
    cases genericOptionEq : signature.payload.genericPrefix with
    | none =>
        rw [genericOptionEq] at genericEq
        change some TokenPlan.empty = some generic at genericEq
        injection genericEq with equality
        subst generic
        exact TokenPlan.WellAnchored.empty
    | some genericValue =>
        rw [genericOptionEq] at genericEq
        change genericPrefixPlan? genericValue = some generic at genericEq
        exact genericPrefixPlan?_wellAnchored _ _ genericEq
  have publicAnchored : publicModifier.WellAnchored := by
    cases publicOptionEq : signature.payload.public with
    | none =>
        rw [publicOptionEq] at publicEq
        change some TokenPlan.empty = some publicModifier at publicEq
        injection publicEq with equality
        subst publicModifier
        exact TokenPlan.WellAnchored.empty
    | some marker =>
        rw [publicOptionEq] at publicEq
        change (if marker.payload = .publicModifier then
            some (.exact (.hardKeyword .publicKw) marker.span)
          else none) = some publicModifier at publicEq
        by_cases markerRole : marker.payload = .publicModifier
        · simp [markerRole] at publicEq
          subst publicModifier
          exact TokenPlan.WellAnchored.exact _ _
        · simp [markerRole] at publicEq
  have payableAnchored : payableModifier.WellAnchored := by
    cases payableOptionEq : signature.payload.payable with
    | none =>
        rw [payableOptionEq] at payableEq
        change some TokenPlan.empty = some payableModifier at payableEq
        injection payableEq with equality
        subst payableModifier
        exact TokenPlan.WellAnchored.empty
    | some marker =>
        rw [payableOptionEq] at payableEq
        change (if marker.payload = .payableModifier then
            some (.exact (.hardKeyword .payableKw) marker.span)
          else none) = some payableModifier at payableEq
        by_cases markerRole : marker.payload = .payableModifier
        · simp [markerRole] at payableEq
          subst payableModifier
          exact TokenPlan.WellAnchored.exact _ _
        · simp [markerRole] at payableEq
  have suffixStarts :=
    TokenPlan.WellAnchored.StartsRequired.concat_plain_first
      (.hardKeyword .functionKw)
      [identifierPlan signature.payload.name,
        .parens (.commaSeparated parameters), returnType]
  apply TokenPlan.WellAnchored.StartsRequired.enclose
  simpa [TokenPlan.concat, TokenPlan.append] using
    TokenPlan.WellAnchored.StartsRequired.prepend_anchored genericAnchored
      (TokenPlan.WellAnchored.StartsRequired.prepend_anchored publicAnchored
        (TokenPlan.WellAnchored.StartsRequired.prepend_anchored
          payableAnchored suffixStarts))

private theorem bracedBodyPlan?_endsRequired
    (body : Body) (plan : TokenPlan)
    (success : bodyTokenPlan? .braced body = some plan) :
    TokenPlan.WellAnchored.EndsRequired plan := by
  rcases body with ⟨bodySpan, origin, statements⟩
  cases origin with
  | braced openBrace closeBrace =>
      unfold bodyTokenPlan? at success
      have statementsResult := Option.bind_eq_some_iff.mp success
      rcases statementsResult with
        ⟨statementPlans, _statementPlansEq, resultEq⟩
      unfold bracedBodyPlanWith? at resultEq
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.EndsRequired.enclose
      apply TokenPlan.WellAnchored.EndsRequired.concat_exact_last_two
  | matchArm fatArrow =>
      simp [bodyTokenPlan?] at success

theorem functionDeclPlan?_wellAnchored
    (declaration : FunctionDecl) (plan : TokenPlan)
    (success : functionDeclPlan? declaration = some plan) :
    plan.WellAnchored := by
  unfold functionDeclPlan? at success
  have signatureResult := Option.bind_eq_some_iff.mp success
  rcases signatureResult with ⟨signature, signatureEq, success⟩
  have bodyResult := Option.bind_eq_some_iff.mp success
  rcases bodyResult with ⟨body, bodyEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  apply TokenPlan.WellAnchored.enclose
  exact TokenPlan.WellAnchored.of_starts_ends_append
    (functionSignaturePlan?_startsRequired _ _ signatureEq)
    (bracedBodyPlan?_endsRequired _ _ bodyEq)

theorem importDeclPlan?_wellAnchored
    (declaration : ImportDecl) (plan : TokenPlan)
    (success : importDeclPlan? declaration = some plan) :
    plan.WellAnchored := by
  unfold importDeclPlan? at success
  have referenceResult := Option.bind_eq_some_iff.mp success
  rcases referenceResult with ⟨reference, _referenceEq, success⟩
  cases modeEq : declaration.payload.mode with
  | module alias =>
      simp [modeEq] at success
      subst plan
      apply TokenPlan.WellAnchored.enclose
      apply TokenPlan.WellAnchored.concat_plain_bookended_two
  | items selection hidden =>
      rw [modeEq] at success
      have selectionResult := Option.bind_eq_some_iff.mp success
      rcases selectionResult with
        ⟨selectionPlan, _selectionEq, success⟩
      have hidingResult := Option.bind_eq_some_iff.mp success
      rcases hidingResult with ⟨hidingPlan, _hidingEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      apply TokenPlan.WellAnchored.concat_plain_bookended_two

theorem exportDeclPlan?_wellAnchored
    (declaration : ExportDecl) (plan : TokenPlan)
    (success : exportDeclPlan? declaration = some plan) :
    plan.WellAnchored := by
  unfold exportDeclPlan? at success
  cases modeEq : declaration.payload with
  | «local» selection =>
      rw [modeEq] at success
      have modeResult := Option.bind_eq_some_iff.mp success
      rcases modeResult with ⟨mode, _modeEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      apply TokenPlan.WellAnchored.concat_plain_bookended_one
  | module moduleRef alias =>
      rw [modeEq] at success
      have referenceResult := Option.bind_eq_some_iff.mp success
      rcases referenceResult with ⟨reference, _referenceEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      apply TokenPlan.WellAnchored.concat_plain_bookended_one
  | «from» moduleRef selection =>
      rw [modeEq] at success
      have referenceResult := Option.bind_eq_some_iff.mp success
      rcases referenceResult with ⟨reference, _referenceEq, success⟩
      have selectionResult := Option.bind_eq_some_iff.mp success
      rcases selectionResult with
        ⟨selectionPlan, _selectionEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      apply TokenPlan.WellAnchored.concat_plain_bookended_one

theorem pragmaDeclPlan?_wellAnchored
    (declaration : PragmaDecl) (plan : TokenPlan)
    (success : pragmaDeclPlan? declaration = some plan) :
    plan.WellAnchored := by
  unfold pragmaDeclPlan? at success
  injection success with planEq
  subst plan
  apply TokenPlan.WellAnchored.enclose
  apply TokenPlan.WellAnchored.concat_plain_bookended_two

theorem dataDeclPlan?_wellAnchored
    (declaration : DataDecl) (plan : TokenPlan)
    (success : dataDeclPlan? declaration = some plan) :
    plan.WellAnchored := by
  unfold dataDeclPlan? at success
  cases constructorsEq : declaration.payload.constructors with
  | none =>
      simp [constructorsEq] at success
      subst plan
      apply TokenPlan.WellAnchored.enclose
      apply TokenPlan.WellAnchored.concat_plain_bookended_three
  | some constructorsValue =>
      rw [constructorsEq] at success
      have plansResult := Option.bind_eq_some_iff.mp success
      rcases plansResult with ⟨plans, _plansEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      apply TokenPlan.WellAnchored.concat_plain_bookended_three

theorem typeAliasDeclPlan?_wellAnchored
    (declaration : TypeAliasDecl) (plan : TokenPlan)
    (success : typeAliasDeclPlan? declaration = some plan) :
    plan.WellAnchored := by
  unfold typeAliasDeclPlan? at success
  have bodyResult := Option.bind_eq_some_iff.mp success
  rcases bodyResult with ⟨body, _bodyEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  apply TokenPlan.WellAnchored.enclose
  apply TokenPlan.WellAnchored.concat_plain_bookended_four

theorem classDeclPlan?_wellAnchored
    (declaration : ClassDecl) (plan : TokenPlan)
    (success : classDeclPlan? declaration = some plan) :
    plan.WellAnchored := by
  unfold classDeclPlan? at success
  have genericResult := Option.bind_eq_some_iff.mp success
  rcases genericResult with ⟨generic, _genericEq, success⟩
  have mainResult := Option.bind_eq_some_iff.mp success
  rcases mainResult with ⟨main, _mainEq, success⟩
  have parametersResult := Option.bind_eq_some_iff.mp success
  rcases parametersResult with ⟨parameters, _parametersEq, success⟩
  have methodsResult := Option.bind_eq_some_iff.mp success
  rcases methodsResult with ⟨methods, _methodsEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  apply TokenPlan.WellAnchored.enclose
  have genericAnchored : generic.WellAnchored := by
    cases genericOptionEq : declaration.payload.genericPrefix with
    | none =>
        rw [genericOptionEq] at _genericEq
        change some TokenPlan.empty = some generic at _genericEq
        injection _genericEq with genericEq
        subst generic
        exact TokenPlan.WellAnchored.empty
    | some genericValue =>
        rw [genericOptionEq] at _genericEq
        change genericPrefixPlan? genericValue = some generic at _genericEq
        exact genericPrefixPlan?_wellAnchored _ _ _genericEq
  have suffixAnchored := TokenPlan.WellAnchored.concat_plain_bookended_six
    (.hardKeyword .classKw) (.symbol .rightBrace)
    main (.plain (.symbol .colon))
    (identifierPlan declaration.payload.className)
    parameters (.plain (.symbol .leftBrace)) (.concat methods)
  simpa [TokenPlan.concat, TokenPlan.append] using
    TokenPlan.WellAnchored.append genericAnchored suffixAnchored

theorem instanceDeclPlan?_wellAnchored
    (declaration : InstanceDecl) (plan : TokenPlan)
    (success : instanceDeclPlan? declaration = some plan) :
    plan.WellAnchored := by
  unfold instanceDeclPlan? at success
  have genericResult := Option.bind_eq_some_iff.mp success
  rcases genericResult with ⟨generic, _genericEq, success⟩
  have defaultResult := Option.bind_eq_some_iff.mp success
  rcases defaultResult with ⟨defaultModifier, _defaultEq, success⟩
  have mainResult := Option.bind_eq_some_iff.mp success
  rcases mainResult with ⟨main, _mainEq, success⟩
  have parametersResult := Option.bind_eq_some_iff.mp success
  rcases parametersResult with ⟨parameters, _parametersEq, success⟩
  have methodsResult := Option.bind_eq_some_iff.mp success
  rcases methodsResult with ⟨methods, _methodsEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  apply TokenPlan.WellAnchored.enclose
  have genericAnchored : generic.WellAnchored := by
    cases genericOptionEq : declaration.payload.genericPrefix with
    | none =>
        rw [genericOptionEq] at _genericEq
        change some TokenPlan.empty = some generic at _genericEq
        injection _genericEq with genericEq
        subst generic
        exact TokenPlan.WellAnchored.empty
    | some genericValue =>
        rw [genericOptionEq] at _genericEq
        change genericPrefixPlan? genericValue = some generic at _genericEq
        exact genericPrefixPlan?_wellAnchored _ _ _genericEq
  have defaultAnchored : defaultModifier.WellAnchored := by
    cases defaultOptionEq : declaration.payload.default with
    | none =>
        rw [defaultOptionEq] at _defaultEq
        change some TokenPlan.empty = some defaultModifier at _defaultEq
        injection _defaultEq with defaultEq
        subst defaultModifier
        exact TokenPlan.WellAnchored.empty
    | some marker =>
        rw [defaultOptionEq] at _defaultEq
        change (if marker.payload = .defaultModifier then
            some (.exact (.hardKeyword .defaultKw) marker.span)
          else none) = some defaultModifier at _defaultEq
        by_cases markerRole : marker.payload = .defaultModifier
        · simp [markerRole] at _defaultEq
          subst defaultModifier
          exact TokenPlan.WellAnchored.exact _ _
        · simp [markerRole] at _defaultEq
  have suffixAnchored := TokenPlan.WellAnchored.concat_plain_bookended_six
    (.hardKeyword .instanceKw) (.symbol .rightBrace)
    main (.plain (.symbol .colon))
    (qualifiedNamePlan declaration.payload.className)
    parameters (.plain (.symbol .leftBrace)) (.concat methods)
  simpa [TokenPlan.concat, TokenPlan.append] using
    TokenPlan.WellAnchored.append genericAnchored
      (TokenPlan.WellAnchored.append defaultAnchored suffixAnchored)

theorem contractDeclPlan?_wellAnchored
    (declaration : ContractDecl) (plan : TokenPlan)
    (success : contractDeclPlan? declaration = some plan) :
    plan.WellAnchored := by
  unfold contractDeclPlan? at success
  have membersResult := Option.bind_eq_some_iff.mp success
  rcases membersResult with ⟨members, _membersEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  apply TokenPlan.WellAnchored.enclose
  apply TokenPlan.WellAnchored.concat_plain_bookended_four

theorem topItemPlan?_wellAnchored
    (item : TopItem) (plan : TokenPlan)
    (success : topItemPlan? item = some plan) :
    plan.WellAnchored := by
  rcases item with ⟨span, payload⟩
  cases payload with
  | importDecl declaration =>
      unfold topItemPlan? at success
      have innerResult := Option.bind_eq_some_iff.mp success
      rcases innerResult with ⟨inner, innerEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (importDeclPlan?_wellAnchored _ _ innerEq) span
  | exportDecl declaration =>
      unfold topItemPlan? at success
      have innerResult := Option.bind_eq_some_iff.mp success
      rcases innerResult with ⟨inner, innerEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (exportDeclPlan?_wellAnchored _ _ innerEq) span
  | pragmaDecl declaration =>
      unfold topItemPlan? at success
      have innerResult := Option.bind_eq_some_iff.mp success
      rcases innerResult with ⟨inner, innerEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (pragmaDeclPlan?_wellAnchored _ _ innerEq) span
  | dataDecl declaration =>
      unfold topItemPlan? at success
      have innerResult := Option.bind_eq_some_iff.mp success
      rcases innerResult with ⟨inner, innerEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (dataDeclPlan?_wellAnchored _ _ innerEq) span
  | typeAliasDecl declaration =>
      unfold topItemPlan? at success
      have innerResult := Option.bind_eq_some_iff.mp success
      rcases innerResult with ⟨inner, innerEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (typeAliasDeclPlan?_wellAnchored _ _ innerEq) span
  | classDecl declaration =>
      unfold topItemPlan? at success
      have innerResult := Option.bind_eq_some_iff.mp success
      rcases innerResult with ⟨inner, innerEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (classDeclPlan?_wellAnchored _ _ innerEq) span
  | instanceDecl declaration =>
      unfold topItemPlan? at success
      have innerResult := Option.bind_eq_some_iff.mp success
      rcases innerResult with ⟨inner, innerEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (instanceDeclPlan?_wellAnchored _ _ innerEq) span
  | contractDecl declaration =>
      unfold topItemPlan? at success
      have innerResult := Option.bind_eq_some_iff.mp success
      rcases innerResult with ⟨inner, innerEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (contractDeclPlan?_wellAnchored _ _ innerEq) span
  | functionDecl declaration =>
      unfold topItemPlan? at success
      have innerResult := Option.bind_eq_some_iff.mp success
      rcases innerResult with ⟨inner, innerEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (functionDeclPlan?_wellAnchored _ _ innerEq) span

/-- Successful declaration-module token plans always have mandatory physical
endpoints (or are empty when the module has no declarations). -/
theorem declarationModulePlan?_wellAnchored
    (module : ParsedModuleV1) (plan : TokenPlan)
    (success : declarationModulePlan? module = some plan) :
    plan.WellAnchored := by
  rcases module with ⟨moduleSpan, source, items⟩
  induction items generalizing plan with
  | nil =>
      rw [declarationModulePlan?_nil] at success
      injection success with planEq
      subst plan
      exact TokenPlan.WellAnchored.empty
  | cons item rest induction =>
      rw [declarationModulePlan?_cons] at success
      have itemResult := Option.bind_eq_some_iff.mp success
      rcases itemResult with ⟨itemPlan, itemEq, success⟩
      have restResult := Option.bind_eq_some_iff.mp success
      rcases restResult with ⟨restPlan, restEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      have itemAnchored := topItemPlan?_wellAnchored item itemPlan itemEq
      have restAnchored := induction restPlan restEq
      exact TokenPlan.WellAnchored.append itemAnchored restAnchored

end Solcore.Surface.Multi
