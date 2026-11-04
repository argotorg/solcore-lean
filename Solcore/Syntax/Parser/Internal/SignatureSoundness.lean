import Solcore.Syntax.Internal.SignatureOutcomes
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.ParameterSoundness
import Solcore.Syntax.Internal.TypeExactness
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Internal.SignatureExactness
import Solcore.Syntax.Parser.Internal.ParameterBasics
import Solcore.Syntax.Grammar.Signatures
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Parser.Internal.ParameterTotality
import Solcore.Syntax.Parser.Internal.OutcomeCompleteness
import Solcore.Syntax.Parser.Internal.PublicTermTotality
import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Syntax.Parser.Internal.ExportSoundness

/-!
Soundness of the parsers of function signatures and predicates: each success and each
rejection has its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for canonical generic parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem lessPresent_of_isSymbol_eq_true {input : State}
    (present : isSymbol input .less = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .less } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .less .parameter present with
    ⟨opening, parsed⟩
  exact ⟨opening.span,
    (symbol_success_exactTokenParses .less .parameter parsed).1⟩

/-- Every executable generic-parameter rejection is the exact rejection of
its required nonempty, allow-trailing delimited list. -/
theorem genericParameters_reject_sound
    {input rejected : State} {failure : Failure}
    (result : genericParameters input = .reject failure rejected) :
    DeclarativeGrammar.GenericParametersRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold genericParameters at result
  cases valuesResult : delimited .less .greater false
      (identifier .parameter) .parameter .topLevel input with
  | invariant error => simp [bind, valuesResult] at result
  | reject valuesFailure valuesRejected =>
      simp only [bind, valuesResult] at result
      cases result
      exact delimited_reject_sound .less .greater false
        (identifier .parameter) DeclarativeGrammar.IdentifierParses
        DeclarativeGrammar.IdentifierRejects .parameter .topLevel
        (identifier_success_sound .parameter)
        (identifier_reject_sound .parameter) valuesResult
  | ok values afterValues =>
      simp only [bind, valuesResult] at result
      unfold requireGenericParameters at result
      cases elements : values.elements with
      | nil => simp [elements] at result
      | cons head tail => simp [elements, pure] at result

/-- Package executable generic-parameter success and exact rejection. -/
theorem genericParameters_ordinaryOutcome_sound :
    (∀ {input next : State} {parameters : GenericParameters},
      genericParameters input = .ok parameters next →
        DeclarativeGrammar.GenericParametersParses
          input.declarativeRemainder parameters next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      genericParameters input = .reject failure rejected →
        DeclarativeGrammar.GenericParametersRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨genericParameters_success_sound, genericParameters_reject_sound⟩

/-- Every optional-generic rejection is the selected generic rejection from
the original positively guarded input. -/
theorem optionalGenericParameters_reject_sound
    {input rejected : State} {failure : Failure}
    (result : optionalGenericParameters input = .reject failure rejected) :
    DeclarativeGrammar.OptionalGenericParametersRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold optionalGenericParameters getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .less
  · simp only [present, if_true] at result
    cases parametersResult : genericParameters input with
    | invariant error => simp [parametersResult] at result
    | ok parameters afterParameters =>
        simp [parametersResult, pure] at result
    | reject parametersFailure parametersRejected =>
        simp only [parametersResult] at result
        cases result
        exact .present (lessPresent_of_isSymbol_eq_true present)
          (genericParameters_reject_sound parametersResult)
  · have absent : isSymbol input .less = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package executable optional-generic success and exact rejection. -/
theorem optionalGenericParameters_ordinaryOutcome_sound :
    (∀ {input next : State} {parameters : Option GenericParameters},
      optionalGenericParameters input = .ok parameters next →
        DeclarativeGrammar.OptionalGenericParametersParses
          input.declarativeRemainder parameters next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      optionalGenericParameters input = .reject failure rejected →
        DeclarativeGrammar.OptionalGenericParametersRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨optionalGenericParameters_success_sound,
    optionalGenericParameters_reject_sound⟩

/-- Re-export exact required generic-parameter outcomes. -/
theorem genericParameters_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.GenericParametersParses
      DeclarativeGrammar.GenericParametersRejects :=
  DeclarativeGrammar.genericParametersExactOutcomeSpec

/-- Two successful required generic lists have the same AST and remainder. -/
theorem genericParameters_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : GenericParameters}
    (leftResult : genericParameters input = .ok left leftOutput)
    (rightResult : genericParameters input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.GenericParametersParses.result_unique
    (genericParameters_success_sound leftResult)
    (genericParameters_success_sound rightResult)

/-- Two required-generic rejections have the same declarative endpoint. -/
theorem genericParameters_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : genericParameters input = .reject leftFailure leftOutput)
    (rightResult : genericParameters input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.GenericParametersRejects.output_unique
    (genericParameters_reject_sound leftResult)
    (genericParameters_reject_sound rightResult)

/-- Re-export exact optional generic-parameter outcomes. -/
theorem optionalGenericParameters_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.OptionalGenericParametersParses
      DeclarativeGrammar.OptionalGenericParametersRejects :=
  DeclarativeGrammar.optionalGenericParametersExactOutcomeSpec

/-- Two successful optional generic lists have the same value and remainder. -/
theorem optionalGenericParameters_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : Option GenericParameters}
    (leftResult : optionalGenericParameters input = .ok left leftOutput)
    (rightResult : optionalGenericParameters input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalGenericParametersParses.result_unique
    (optionalGenericParameters_success_sound leftResult)
    (optionalGenericParameters_success_sound rightResult)

/-- Two optional-generic rejections have the same declarative endpoint. -/
theorem optionalGenericParameters_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : optionalGenericParameters input =
      .reject leftFailure leftOutput)
    (rightResult : optionalGenericParameters input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalGenericParametersRejects.output_unique
    (optionalGenericParameters_reject_sound leftResult)
    (optionalGenericParameters_reject_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
/-! Aggregate ordinary-success and exact-rejection soundness for Core types. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Fuel zero is the invariant boundary and cannot report ordinary rejection. -/
theorem typeExprWithFuel_zero_ne_reject {input rejected : State}
    {failure : Failure} :
    typeExprWithFuel 0 input ≠ .reject failure rejected := by
  simp [typeExprWithFuel]

/-- Every fuel-bounded executable rejection follows the exact prioritized
parser-independent relation at the same fuel. -/
theorem typeExprWithFuel_reject_sound :
    ∀ fuel {input rejected : State} {failure : Failure},
      typeExprWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.TypeExprRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro input rejected failure result
      simp [typeExprWithFuel] at result
  | succ fuel inductionHypothesis =>
      intro input rejected failure result
      simp only [typeExprWithFuel] at result
      split at result
      next functionPresent =>
        exact .function (parseFunctionType_reject_type_sound
          (typeExprWithFuel fuel)
          (DeclarativeGrammar.TypeExprRejectsWithFuel fuel)
          (typeExprWithFuel_success_sound fuel) inductionHypothesis
          (typeExprWithFuel_preservesTokenWindow fuel) functionPresent result)
      next functionAbsent =>
        have functionAbsentAt := keywordAbsentAt_of_isKeyword_eq_false
          .functionKw (Bool.eq_false_iff.mpr functionAbsent)
        split at result
        next comptimePresent =>
          have composite : (isContextual input .comptime &&
              (input.peekOffsetKind? 1 == some (.symbol .less))) = true := by
            change (isContextual input .comptime &&
              (input.peekOffsetKind? 1 == some (.symbol .less))) = true at comptimePresent
            exact comptimePresent
          have parts := Bool.and_eq_true_iff.mp composite
          exact .comptime functionAbsentAt
            (parseComptimeType_reject_type_sound (typeExprWithFuel fuel)
              (DeclarativeGrammar.TypeExprRejectsWithFuel fuel)
              (typeExprWithFuel_success_sound fuel) inductionHypothesis parts.1
              parts.2 result)
        next comptimeAbsent =>
          have comptimeFalse : (isContextual input .comptime &&
              (input.peekOffsetKind? 1 == some (.symbol .less))) = false := by
            apply Bool.eq_false_iff.mpr
            change ¬ (isContextual input .comptime &&
              (input.peekOffsetKind? 1 == some (.symbol .less))) = true at comptimeAbsent
            exact comptimeAbsent
          have comptimeAbsentAt :=
            contextualSymbolPairAbsentAt_of_guard_eq_false .comptime .less
              comptimeFalse
          split at result
          next mappingPresent =>
            have composite : (isContextual input .mapping &&
                (input.peekOffsetKind? 1 ==
                  some (.symbol .leftParen))) = true := by
              change (isContextual input .mapping &&
                (input.peekOffsetKind? 1 ==
                  some (.symbol .leftParen))) = true at mappingPresent
              exact mappingPresent
            have parts := Bool.and_eq_true_iff.mp composite
            exact .mapping functionAbsentAt comptimeAbsentAt
              (parseMappingType_reject_type_sound (typeExprWithFuel fuel)
                (DeclarativeGrammar.TypeExprRejectsWithFuel fuel)
                (typeExprWithFuel_success_sound fuel) inductionHypothesis parts.1
                parts.2 result)
          next mappingAbsent =>
            have mappingFalse : (isContextual input .mapping &&
                (input.peekOffsetKind? 1 ==
                  some (.symbol .leftParen))) = false := by
              apply Bool.eq_false_iff.mpr
              change ¬ (isContextual input .mapping &&
                (input.peekOffsetKind? 1 ==
                  some (.symbol .leftParen))) = true at mappingAbsent
              exact mappingAbsent
            have mappingAbsentAt :=
              contextualSymbolPairAbsentAt_of_guard_eq_false .mapping
                .leftParen mappingFalse
            split at result
            next proxyPresent =>
              exact .proxy functionAbsentAt comptimeAbsentAt mappingAbsentAt
                (parseProxyType_reject_type_sound (typeExprWithFuel fuel)
                  (DeclarativeGrammar.TypeExprRejectsWithFuel fuel)
                  inductionHypothesis proxyPresent result)
            next proxyAbsent =>
              have atAbsent := symbolAbsentAt_of_isSymbol_eq_false .at
                (Bool.eq_false_iff.mpr proxyAbsent)
              split at result
              next tuplePresent =>
                exact .tuple functionAbsentAt comptimeAbsentAt mappingAbsentAt
                  atAbsent
                  (parseTupleType_reject_type_sound (typeExprWithFuel fuel)
                    (DeclarativeGrammar.TypeExprRejectsWithFuel fuel)
                    (typeExprWithFuel_success_sound fuel) inductionHypothesis
                    tuplePresent result)
              next tupleAbsent =>
                have leftParenAbsent :=
                  symbolAbsentAt_of_isSymbol_eq_false .leftParen
                    (Bool.eq_false_iff.mpr tupleAbsent)
                split at result
                next namedPresent =>
                  have identifierPresent :=
                    identifierPresentAt_of_isIdentifier_eq_true namedPresent
                  exact .named functionAbsentAt comptimeAbsentAt
                    mappingAbsentAt atAbsent leftParenAbsent identifierPresent
                    (parseNamedType_reject_type_sound (typeExprWithFuel fuel)
                      (DeclarativeGrammar.TypeExprRejectsWithFuel fuel)
                      (typeExprWithFuel_success_sound fuel)
                      inductionHypothesis result)
                next namedAbsent =>
                  have identifierAbsent :=
                    identifierAbsentAt_of_isIdentifier_eq_false
                      (Bool.eq_false_iff.mpr namedAbsent)
                  unfold rejectAt at result
                  cases result
                  exact .final functionAbsentAt comptimeAbsentAt
                    mappingAbsentAt atAbsent leftParenAbsent identifierAbsent

/-- Fuel-bounded executable ordinary replies jointly reflect established
recursive successes and exact same-fuel rejections. -/
theorem typeExprWithFuel_ordinaryOutcome_sound (fuel : Nat) :
    (∀ {input next : State} {value : TypeExpr},
      typeExprWithFuel fuel input = .ok value next →
        DeclarativeGrammar.TypeExprOrdinaryParses
          input.declarativeRemainder value next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      typeExprWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.TypeExprRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨typeExprWithFuel_success_sound fuel, typeExprWithFuel_reject_sound fuel⟩

/-- Re-export the exact outcome contract at one executable recursion fuel. -/
theorem typeExprWithFuel_exactOutcomeSpec (fuel : Nat) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeExprOrdinaryParses
      (DeclarativeGrammar.TypeExprRejectsWithFuel fuel) :=
  DeclarativeGrammar.typeExprExactOutcomeSpecWithFuel fuel

/-- Two successful same-fuel executable reflections have the same type AST and
final declarative remainder. -/
theorem typeExprWithFuel_success_result_unique
    (fuel : Nat) {input leftOutput rightOutput : State}
    {left right : TypeExpr}
    (leftResult : typeExprWithFuel fuel input = .ok left leftOutput)
    (rightResult : typeExprWithFuel fuel input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeExprParses.result_unique
    (typeExprWithFuel_success_sound fuel leftResult)
    (typeExprWithFuel_success_sound fuel rightResult)

/-- Two rejected same-fuel executable reflections have the same exact
declarative endpoint. -/
theorem typeExprWithFuel_reject_output_unique
    (fuel : Nat) {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : typeExprWithFuel fuel input =
      .reject leftFailure leftOutput)
    (rightResult : typeExprWithFuel fuel input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (typeExprWithFuel_exactOutcomeSpec fuel).rejectOutputUnique
    (typeExprWithFuel_reject_sound fuel leftResult)
    (typeExprWithFuel_reject_sound fuel rightResult)

/-- Every public executable rejection uses the same remainder-derived fuel as
the public parser-independent rejection relation. -/
theorem typeExpr_reject_sound {input rejected : State} {failure : Failure}
    (result : typeExpr input = .reject failure rejected) :
    DeclarativeGrammar.TypeExprRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold typeExpr at result
  have reflected := typeExprWithFuel_reject_sound
    (input.remainingCount + 1) result
  simpa [DeclarativeGrammar.TypeExprRejects,
    DeclarativeGrammar.typeExprPublicFuel, State.remainingCount,
    State.declarativeRemainder] using reflected

/-- Public executable ordinary replies jointly reflect the established
recursive success grammar and exact public rejection relation. -/
theorem typeExpr_ordinaryOutcome_sound :
    (∀ {input next : State} {value : TypeExpr},
      typeExpr input = .ok value next →
        DeclarativeGrammar.TypeExprOrdinaryParses
          input.declarativeRemainder value next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected →
        DeclarativeGrammar.TypeExprRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨typeExpr_success_sound, typeExpr_reject_sound⟩

/-- Re-export full public Core type value and rejection-endpoint
functionality. -/
theorem typeExpr_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects :=
  DeclarativeGrammar.typeExprExactOutcomeSpec

/-- Two successful public executable reflections have the same type AST and
final declarative remainder. -/
theorem typeExpr_success_result_unique
    {input leftOutput rightOutput : State} {left right : TypeExpr}
    (leftResult : typeExpr input = .ok left leftOutput)
    (rightResult : typeExpr input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeExprParses.result_unique
    (typeExpr_success_sound leftResult) (typeExpr_success_sound rightResult)

/-- Two rejected public executable reflections have the same exact
declarative endpoint. -/
theorem typeExpr_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : typeExpr input = .reject leftFailure leftOutput)
    (rightResult : typeExpr input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeExprRejects.output_unique
    (typeExpr_reject_sound leftResult) (typeExpr_reject_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaParameterOrdinaryOutcomeSoundnessProperties
/-!
Complete executable ordinary outcomes at the public lambda-parameter rewind,
boundary, diagnostic emission, and recovery layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem rewound_declarativeRemainder_eq
    (input failed : State)
    (shape : failed.tokens = input.tokens ∧ failed.window = input.window) :
    ({ failed with cursor := input.cursor } : State).declarativeRemainder =
      input.declarativeRemainder := by
  unfold State.declarativeRemainder
  simp only
  rw [shape.1, shape.2]

private theorem emitted_rewound_declarativeRemainder_eq
    (input failed : State) (diagnostic : ParseDiagnostic)
    (shape : failed.tokens = input.tokens ∧ failed.window = input.window) :
    State.declarativeRemainder
        (({ failed with cursor := input.cursor } : State).emit diagnostic) =
      input.declarativeRemainder := by
  unfold State.emit State.declarativeRemainder
  simp only
  rw [shape.1, shape.2]

private theorem coreRejectsWithPreservedWindow_of_result
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input failed : State} {failure : Failure}
    (result : LambdaParameterInternals.lambdaParameterCore input =
      .reject failure failed) :
    DeclarativeGrammar.LambdaParameterCoreRejectsWithPreservedWindow
      typeRejects input.declarativeRemainder := by
  have resultShape :=
    LambdaParameterInternals.lambdaParameterCore_preservesTokenWindow input
  rw [result] at resultShape
  have shape : failed.tokens = input.tokens ∧ failed.window = input.window := by
    simpa only [Reply.PreservesTokenWindow] using resultShape
  exact ⟨failed.declarativeRemainder,
    LambdaParameterInternals.lambdaParameterCore_reject_ordinary_sound
      typeRejects typeRejectSound result,
    shape.1, congrArg TokenWindow.endIndex shape.2⟩

/-- Every public success is direct Core success or exact rewound recovery. -/
theorem lambdaParameter_success_ordinaryOutcome_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input output : State} {parameter : LambdaParameter}
    (result : lambdaParameter input = .ok parameter output) :
    DeclarativeGrammar.LambdaParameterOrdinaryParses typeOrdinary typeRejects
      input.declarativeRemainder parameter output.declarativeRemainder := by
  unfold lambdaParameter at result
  cases coreResult : LambdaParameterInternals.lambdaParameterCore input with
  | ok coreParameter afterCore =>
      simp only [coreResult] at result
      cases result
      exact .core
        (LambdaParameterInternals.lambdaParameterCore_success_ordinary_sound
          typeOrdinary typeSuccessSound coreResult)
  | invariant error => simp [coreResult] at result
  | reject failure failed =>
      simp only [coreResult] at result
      have resultShape :=
        LambdaParameterInternals.lambdaParameterCore_preservesTokenWindow input
      rw [coreResult] at resultShape
      have shape : failed.tokens = input.tokens ∧
          failed.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using resultShape
      let rewound : State := { failed with cursor := input.cursor }
      have rewoundEq : rewound.declarativeRemainder =
          input.declarativeRemainder := by
        simpa only [rewound] using
          rewound_declarativeRemainder_eq input failed shape
      have emittedEq :
          (rewound.emit failure.toDiagnostic).declarativeRemainder =
            input.declarativeRemainder := by
        simpa only [rewound] using
          emitted_rewound_declarativeRemainder_eq input failed
            failure.toDiagnostic shape
      have coreRejected := coreRejectsWithPreservedWindow_of_result
        typeRejects typeRejectSound coreResult
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject failure rewound
        else LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit failure.toDiagnostic)) = .ok parameter output at result
      by_cases boundary : (rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen) = true
      · simp [boundary] at result
      · have boundaryFalse : (rewound.atEnd || isSymbol rewound .comma ||
            isSymbol rewound .rightParen) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues := no_lambdaParameterBoundaryStops_of_guard_eq_false
          rewound boundaryFalse
        rw [rewoundEq] at continues
        have recovered :=
          LambdaParameterInternals.recoverLambdaParameter_success_ordinary_sound
            result
        rw [emittedEq] at recovered
        exact .recovered coreRejected continues recovered

/-- Every public rejection is the exact rewound boundary or recovery reject. -/
theorem lambdaParameter_reject_ordinaryOutcome_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : lambdaParameter input = .reject failure rejected) :
    DeclarativeGrammar.LambdaParameterRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold lambdaParameter at result
  cases coreResult : LambdaParameterInternals.lambdaParameterCore input with
  | ok parameter output => simp [coreResult] at result
  | invariant error => simp [coreResult] at result
  | reject coreFailure failed =>
      simp only [coreResult] at result
      have resultShape :=
        LambdaParameterInternals.lambdaParameterCore_preservesTokenWindow input
      rw [coreResult] at resultShape
      have shape : failed.tokens = input.tokens ∧
          failed.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using resultShape
      let rewound : State := { failed with cursor := input.cursor }
      have rewoundEq : rewound.declarativeRemainder =
          input.declarativeRemainder := by
        simpa only [rewound] using
          rewound_declarativeRemainder_eq input failed shape
      have emittedEq :
          (rewound.emit coreFailure.toDiagnostic).declarativeRemainder =
            input.declarativeRemainder := by
        simpa only [rewound] using
          emitted_rewound_declarativeRemainder_eq input failed
            coreFailure.toDiagnostic shape
      have coreRejected := coreRejectsWithPreservedWindow_of_result
        typeRejects typeRejectSound coreResult
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject coreFailure rewound
        else LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit coreFailure.toDiagnostic)) =
            .reject failure rejected at result
      by_cases boundary : (rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen) = true
      · simp only [boundary, if_true] at result
        have rejectedEq : rewound = rejected := by injection result
        subst rejected
        have stops := lambdaParameterBoundaryStops_of_guard_eq_true rewound
          boundary
        rw [rewoundEq] at stops
        simpa only [rewoundEq] using
          DeclarativeGrammar.LambdaParameterRejects.boundary coreRejected stops
      · have boundaryFalse : (rewound.atEnd || isSymbol rewound .comma ||
            isSymbol rewound .rightParen) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues := no_lambdaParameterBoundaryStops_of_guard_eq_false
          rewound boundaryFalse
        rw [rewoundEq] at continues
        have recoveryRejected :=
          LambdaParameterInternals.recoverLambdaParameter_reject_ordinary_sound
            result
        rw [emittedEq] at recoveryRejected
        exact .recovery coreRejected continues recoveryRejected

/-- Package both public executable ordinary outcomes. -/
theorem lambdaParameter_ordinaryOutcome_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {parameter : LambdaParameter},
      lambdaParameter input = .ok parameter output →
        DeclarativeGrammar.LambdaParameterOrdinaryParses typeOrdinary
          typeRejects input.declarativeRemainder parameter
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      lambdaParameter input = .reject failure rejected →
        DeclarativeGrammar.LambdaParameterRejects typeRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨lambdaParameter_success_ordinaryOutcome_sound typeOrdinary typeRejects
      typeSuccessSound typeRejectSound,
    lambdaParameter_reject_ordinaryOutcome_sound typeRejects typeRejectSound⟩

/-- Lift deterministic supplied type outcomes through the executable API. -/
theorem lambdaParameter_ordinaryOutcomeSpec
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LambdaParameterOrdinaryParses typeOrdinary
        typeRejects)
      (DeclarativeGrammar.LambdaParameterRejects typeRejects) :=
  DeclarativeGrammar.lambdaParameterDeterministicOutcomeSpec typeOutcomes

/-- Concrete public Core types discharge every lambda-parameter exactness premise. -/
theorem lambdaParameter_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.LambdaParameterOrdinaryParses
        DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects)
      (DeclarativeGrammar.LambdaParameterRejects DeclarativeGrammar.TypeExprRejects) :=
  DeclarativeGrammar.lambdaParameterPublicExactOutcomeSpec

/-- Public executable parameter successes agree on their complete AST and remainder. -/
theorem lambdaParameter_success_result_unique
    {input leftOutput rightOutput : State} {left right : LambdaParameter}
    (leftResult : lambdaParameter input = .ok left leftOutput)
    (rightResult : lambdaParameter input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  lambdaParameter_exactOutcomeSpec.successResultUnique
    (lambdaParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects
      typeExpr_success_sound typeExpr_reject_sound leftResult)
    (lambdaParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects
      typeExpr_success_sound typeExpr_reject_sound rightResult)

/-- Public executable parameter rejections agree on the complete rewound endpoint. -/
theorem lambdaParameter_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : lambdaParameter input = .reject leftFailure leftOutput)
    (rightResult : lambdaParameter input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  lambdaParameter_exactOutcomeSpec.rejectOutputUnique
    (lambdaParameter_reject_ordinaryOutcome_sound DeclarativeGrammar.TypeExprRejects
      typeExpr_reject_sound leftResult)
    (lambdaParameter_reject_ordinaryOutcome_sound DeclarativeGrammar.TypeExprRejects
      typeExpr_reject_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionParameterOrdinaryOutcomeSoundnessProperties
/-!
Complete executable ordinary outcomes at the public named-parameter rewind,
boundary, diagnostic emission, and recovery layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem coreRejectsWithPreservedWindow_of_result_variant
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input failed : State} {failure : Failure}
    (result : FunctionParameterInternals.namedParameterCore input =
      .reject failure failed) :
    DeclarativeGrammar.FunctionParameterCoreRejectsWithPreservedWindow
      typeRejects input.declarativeRemainder := by
  have resultShape :=
    FunctionParameterInternals.namedParameterCore_preservesTokenWindow input
  rw [result] at resultShape
  have shape : failed.tokens = input.tokens ∧ failed.window = input.window := by
    simpa only [Reply.PreservesTokenWindow] using resultShape
  exact ⟨failed.declarativeRemainder,
    FunctionParameterInternals.namedParameterCore_reject_ordinary_sound
      typeRejects typeRejectSound result,
    shape.1, congrArg TokenWindow.endIndex shape.2⟩

/-- Every public success is direct Core success or exact rewound recovery. -/
theorem namedParameter_success_ordinaryOutcome_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input output : State} {parameter : FunctionParameter}
    (result : namedParameter input = .ok parameter output) :
    DeclarativeGrammar.FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input.declarativeRemainder parameter output.declarativeRemainder := by
  unfold namedParameter at result
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | ok coreParameter afterCore =>
      simp only [coreResult] at result
      cases result
      exact .core
        (FunctionParameterInternals.namedParameterCore_success_ordinary_sound
          typeOrdinary typeSuccessSound coreResult)
  | invariant error => simp [coreResult] at result
  | reject failure failed =>
      simp only [coreResult] at result
      have resultShape :=
        FunctionParameterInternals.namedParameterCore_preservesTokenWindow input
      rw [coreResult] at resultShape
      have shape : failed.tokens = input.tokens ∧
          failed.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using resultShape
      let rewound : State := { failed with cursor := input.cursor }
      have rewoundEq : rewound.declarativeRemainder =
          input.declarativeRemainder := by
        simpa only [rewound] using
          rewound_declarativeRemainder_eq input failed shape
      have emittedEq :
          (rewound.emit failure.toDiagnostic).declarativeRemainder =
            input.declarativeRemainder := by
        simpa only [rewound] using
          emitted_rewound_declarativeRemainder_eq input failed
            failure.toDiagnostic shape
      have coreRejected := coreRejectsWithPreservedWindow_of_result_variant
        typeRejects typeRejectSound coreResult
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject failure rewound
        else FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)) = .ok parameter output at result
      by_cases boundary : (rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen) = true
      · simp [boundary] at result
      · have boundaryFalse : (rewound.atEnd || isSymbol rewound .comma ||
            isSymbol rewound .rightParen) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues := no_functionParameterBoundaryStops_of_guard_eq_false
          rewound boundaryFalse
        rw [rewoundEq] at continues
        have recovered :=
          FunctionParameterInternals.recoverParameter_success_ordinary_sound
            result
        rw [emittedEq] at recovered
        exact .recovered coreRejected continues recovered

/-- Every public rejection is the exact rewound boundary or recovery reject. -/
theorem namedParameter_reject_ordinaryOutcome_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : namedParameter input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParameterRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold namedParameter at result
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | ok parameter output => simp [coreResult] at result
  | invariant error => simp [coreResult] at result
  | reject coreFailure failed =>
      simp only [coreResult] at result
      have resultShape :=
        FunctionParameterInternals.namedParameterCore_preservesTokenWindow input
      rw [coreResult] at resultShape
      have shape : failed.tokens = input.tokens ∧
          failed.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using resultShape
      let rewound : State := { failed with cursor := input.cursor }
      have rewoundEq : rewound.declarativeRemainder =
          input.declarativeRemainder := by
        simpa only [rewound] using
          rewound_declarativeRemainder_eq input failed shape
      have emittedEq :
          (rewound.emit coreFailure.toDiagnostic).declarativeRemainder =
            input.declarativeRemainder := by
        simpa only [rewound] using
          emitted_rewound_declarativeRemainder_eq input failed
            coreFailure.toDiagnostic shape
      have coreRejected := coreRejectsWithPreservedWindow_of_result_variant
        typeRejects typeRejectSound coreResult
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject coreFailure rewound
        else FunctionParameterInternals.recoverParameter
          (rewound.emit coreFailure.toDiagnostic)) =
            .reject failure rejected at result
      by_cases boundary : (rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen) = true
      · simp only [boundary, if_true] at result
        have rejectedEq : rewound = rejected := by injection result
        subst rejected
        have stops := functionParameterBoundaryStops_of_guard_eq_true rewound
          boundary
        rw [rewoundEq] at stops
        simpa only [rewoundEq] using
          DeclarativeGrammar.FunctionParameterRejects.boundary coreRejected stops
      · have boundaryFalse : (rewound.atEnd || isSymbol rewound .comma ||
            isSymbol rewound .rightParen) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues := no_functionParameterBoundaryStops_of_guard_eq_false
          rewound boundaryFalse
        rw [rewoundEq] at continues
        have recoveryRejected :=
          FunctionParameterInternals.recoverParameter_reject_ordinary_sound
            result
        rw [emittedEq] at recoveryRejected
        exact .recovery coreRejected continues recoveryRejected

/-- Package both public executable ordinary outcomes. -/
theorem namedParameter_ordinaryOutcome_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {parameter : FunctionParameter},
      namedParameter input = .ok parameter output →
        DeclarativeGrammar.FunctionParameterOrdinaryParses typeOrdinary
          typeRejects input.declarativeRemainder parameter
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      namedParameter input = .reject failure rejected →
        DeclarativeGrammar.FunctionParameterRejects typeRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨namedParameter_success_ordinaryOutcome_sound typeOrdinary typeRejects
      typeSuccessSound typeRejectSound,
    namedParameter_reject_ordinaryOutcome_sound typeRejects typeRejectSound⟩

/-- Lift deterministic supplied type outcomes through the executable API. -/
theorem namedParameter_ordinaryOutcomeSpec
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.FunctionParameterOrdinaryParses typeOrdinary
        typeRejects)
      (DeclarativeGrammar.FunctionParameterRejects typeRejects) :=
  DeclarativeGrammar.functionParameterDeterministicOutcomeSpec typeOutcomes

/-- Re-export exact named-parameter outcomes for the executable Core type
grammar. -/
theorem namedParameter_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.FunctionParameterOrdinaryParses
        DeclarativeGrammar.TypeExprOrdinaryParses
        DeclarativeGrammar.TypeExprRejects)
      (DeclarativeGrammar.FunctionParameterRejects
        DeclarativeGrammar.TypeExprRejects) :=
  DeclarativeGrammar.functionParameterExactOutcomeSpec
    DeclarativeGrammar.typeExprExactOutcomeSpec

/-- Two successful executable reflections have the same parameter AST and
final declarative remainder. -/
theorem namedParameter_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : FunctionParameter}
    (leftResult : namedParameter input = .ok left leftOutput)
    (rightResult : namedParameter input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FunctionParameterOrdinaryParses.result_unique
    DeclarativeGrammar.typeExprExactOutcomeSpec
    (namedParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects typeExpr_ordinaryOutcome_sound.1
      typeExpr_ordinaryOutcome_sound.2 leftResult)
    (namedParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects typeExpr_ordinaryOutcome_sound.1
      typeExpr_ordinaryOutcome_sound.2 rightResult)

/-- Two rejected executable reflections have the same declarative endpoint. -/
theorem namedParameter_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : namedParameter input = .reject leftFailure leftOutput)
    (rightResult : namedParameter input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FunctionParameterRejects.output_unique
    (namedParameter_reject_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprRejects typeExpr_ordinaryOutcome_sound.2
      leftResult)
    (namedParameter_reject_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprRejects typeExpr_ordinaryOutcome_sound.2
      rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionParametersOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for recovery-aware function parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful parameter list retains exact delimiters, order, recovery
outcomes, and final remainder. -/
theorem functionParameters_success_ordinaryOutcome_sound
    {input output : State}
    {parameters : DelimitedList FunctionParameter}
    (result : functionParameters input = .ok parameters output) :
    DeclarativeGrammar.FunctionParametersOrdinaryParses
      input.declarativeRemainder parameters output.declarativeRemainder := by
  unfold functionParameters at result
  unfold DeclarativeGrammar.FunctionParametersOrdinaryParses
  exact delimited_allowEmpty_trailing_success_sound .leftParen .rightParen
    namedParameter
    (DeclarativeGrammar.FunctionParameterOrdinaryParses
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects)
    .parameter .topLevel
    (namedParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects typeExpr_ordinaryOutcome_sound.1
      typeExpr_ordinaryOutcome_sound.2)
    namedParameter_preservesTokenWindow result

/-- Every rejected parameter list records its exact delimiter or nested
named-parameter rejection endpoint. -/
theorem functionParameters_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : functionParameters input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParametersRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold functionParameters at result
  exact delimited_reject_sound .leftParen .rightParen true namedParameter
    (DeclarativeGrammar.FunctionParameterOrdinaryParses
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects)
    (DeclarativeGrammar.FunctionParameterRejects
      DeclarativeGrammar.TypeExprRejects)
    .parameter .topLevel
    (namedParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects typeExpr_ordinaryOutcome_sound.1
      typeExpr_ordinaryOutcome_sound.2)
    (namedParameter_reject_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprRejects typeExpr_ordinaryOutcome_sound.2)
    result

/-- Package executable function-parameter-list success and rejection. -/
theorem functionParameters_ordinaryOutcome_sound :
    (∀ {input output : State}
      {parameters : DelimitedList FunctionParameter},
      functionParameters input = .ok parameters output →
        DeclarativeGrammar.FunctionParametersOrdinaryParses
          input.declarativeRemainder parameters output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      functionParameters input = .reject failure rejected →
        DeclarativeGrammar.FunctionParametersRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨functionParameters_success_ordinaryOutcome_sound,
    functionParameters_reject_ordinaryOutcome_sound⟩

/-- Re-export the deterministic parser-independent list outcome contract. -/
theorem functionParameters_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.FunctionParametersOrdinaryParses
      DeclarativeGrammar.FunctionParametersRejects :=
  DeclarativeGrammar.functionParametersDeterministicOutcomeSpec

/-- Re-export full function-parameter-list AST and rejection-endpoint
functionality. -/
theorem functionParameters_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FunctionParametersOrdinaryParses
      DeclarativeGrammar.FunctionParametersRejects :=
  DeclarativeGrammar.functionParametersExactOutcomeSpec

/-- Two successful executable reflections have the same parameter-list AST
and final declarative remainder. -/
theorem functionParameters_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : DelimitedList FunctionParameter}
    (leftResult : functionParameters input = .ok left leftOutput)
    (rightResult : functionParameters input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FunctionParametersOrdinaryParses.result_unique
    (functionParameters_success_ordinaryOutcome_sound leftResult)
    (functionParameters_success_ordinaryOutcome_sound rightResult)

/-- Two rejected executable reflections have the same first failing
declarative endpoint. -/
theorem functionParameters_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : functionParameters input = .reject leftFailure leftOutput)
    (rightResult : functionParameters input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FunctionParametersRejects.output_unique
    (functionParameters_reject_ordinaryOutcome_sound leftResult)
    (functionParameters_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ReturnClauseOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for optional canonical `returns`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable optional-`returns` rejection is the committed return-type
list rejection after its positively guarded marker. -/
theorem returnClause_reject_sound
    {input rejected : State} {failure : Failure}
    (result : returnClause input = .reject failure rejected) :
    DeclarativeGrammar.OptionalReturnClauseRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold returnClause getState at result
  simp only [bind] at result
  by_cases present : isContextual input .returns
  · rcases contextual_eq_ok_of_isContextual_eq_true .returns .typeExpr
        present with ⟨marker, markerResult⟩
    simp only [present, if_true, markerResult] at result
    cases typesResult : delimited .leftParen .rightParen true typeExpr
        .typeExpr .typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typesResult] at result
    | ok types afterTypes => simp [typesResult, pure] at result
    | reject typesFailure typesRejected =>
        simp only [typesResult] at result
        cases result
        exact .typesRejected marker.span
          (contextual_success_exactTokenParses .returns .typeExpr markerResult)
          (delimited_reject_sound .leftParen .rightParen true typeExpr
            DeclarativeGrammar.TypeExprOrdinaryParses
            DeclarativeGrammar.TypeExprRejects .typeExpr .typeExpr
            typeExpr_success_sound typeExpr_reject_sound typesResult)
  · have absent : isContextual input .returns = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package executable optional-`returns` success and exact rejection. -/
theorem returnClause_ordinaryOutcome_sound :
    (∀ {input next : State} {clause : Option ReturnClause},
      returnClause input = .ok clause next →
        DeclarativeGrammar.OptionalReturnClauseParses
          input.declarativeRemainder clause next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      returnClause input = .reject failure rejected →
        DeclarativeGrammar.OptionalReturnClauseRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨returnClause_success_sound, returnClause_reject_sound⟩

/-- Re-export exact optional return-clause outcomes. -/
theorem returnClause_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.OptionalReturnClauseParses
      DeclarativeGrammar.OptionalReturnClauseRejects :=
  DeclarativeGrammar.optionalReturnClauseExactOutcomeSpec

/-- Two successful optional return clauses have the same AST and remainder. -/
theorem returnClause_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : Option ReturnClause}
    (leftResult : returnClause input = .ok left leftOutput)
    (rightResult : returnClause input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalReturnClauseParses.result_unique
    (returnClause_success_sound leftResult)
    (returnClause_success_sound rightResult)

/-- Two return-clause rejections have the same declarative endpoint. -/
theorem returnClause_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : returnClause input = .reject leftFailure leftOutput)
    (rightResult : returnClause input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalReturnClauseRejects.output_unique
    (returnClause_reject_sound leftResult)
    (returnClause_reject_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PredicateOrdinaryRejectionSoundnessProperties
/-! Exact executable ordinary-rejection reflection for one trait predicate. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable predicate rejection records its exact first rejected
stage after all successful prefixes. -/
theorem predicate_reject_sound {input rejected : State} {failure : Failure}
    (result : predicate input = .reject failure rejected) :
    DeclarativeGrammar.PredicateRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold predicate at result
  cases subjectResult : typeExpr input with
  | invariant error => simp [bind, subjectResult] at result
  | reject subjectFailure subjectRejected =>
      simp only [bind, subjectResult] at result
      cases result
      exact .subjectRejected (typeExpr_reject_sound subjectResult)
  | ok subject afterSubject =>
      simp only [bind, subjectResult] at result
      have subjectParsed := typeExpr_success_sound subjectResult
      cases colonResult : symbol .colon .typeExpr afterSubject with
      | invariant error => simp [colonResult] at result
      | reject colonFailure colonRejected =>
          have rejectedEq := symbol_reject_state_eq .colon .typeExpr
            colonResult
          subst colonRejected
          simp only [colonResult] at result
          cases result
          exact .colonMissing subjectParsed
            (symbol_reject_tokenKindAbsentAt .colon .typeExpr colonResult)
      | ok colon afterColon =>
          simp only [colonResult] at result
          have colonParsed := symbol_success_exactTokenParses .colon .typeExpr
            colonResult
          cases nameResult : identifier .typeExpr afterColon with
          | invariant error => simp [nameResult] at result
          | reject nameFailure nameRejected =>
              simp only [nameResult] at result
              cases result
              exact .nameRejected colon.span subjectParsed colonParsed
                (identifier_reject_sound .typeExpr nameResult)
          | ok traitName afterName =>
              simp only [nameResult] at result
              have nameParsed := identifier_success_sound .typeExpr nameResult
              cases argumentsResult : parseNamedTypeArguments typeExpr
                  afterName with
              | invariant error => simp [argumentsResult] at result
              | reject argumentsFailure argumentsRejected =>
                  simp only [argumentsResult] at result
                  cases result
                  exact .argumentsRejected colon.span subjectParsed
                    colonParsed nameParsed
                    (parseNamedTypeArguments_reject_type_sound typeExpr
                      DeclarativeGrammar.TypeExprRejects typeExpr_success_sound
                        typeExpr_reject_sound argumentsResult)
              | ok arguments afterArguments =>
                  simp [argumentsResult, pure] at result

/-- Package executable predicate success and exact ordinary rejection. -/
theorem predicate_ordinaryOutcome_sound :
    (∀ {input next : State} {value : Predicate},
      predicate input = .ok value next →
        DeclarativeGrammar.PredicateParses input.declarativeRemainder value
          next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      predicate input = .reject failure rejected →
        DeclarativeGrammar.PredicateRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨predicate_success_sound, predicate_reject_sound⟩

/-- Re-export exact single-predicate outcomes. -/
theorem predicate_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.PredicateParses DeclarativeGrammar.PredicateRejects :=
  DeclarativeGrammar.predicateExactOutcomeSpec

/-- Two successful predicates have the same AST and declarative remainder. -/
theorem predicate_success_result_unique
    {input leftOutput rightOutput : State} {left right : Predicate}
    (leftResult : predicate input = .ok left leftOutput)
    (rightResult : predicate input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.PredicateParses.result_unique
    (predicate_success_sound leftResult) (predicate_success_sound rightResult)

/-- Two predicate rejections have the same declarative endpoint. -/
theorem predicate_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : predicate input = .reject leftFailure leftOutput)
    (rightResult : predicate input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.PredicateRejects.output_unique
    (predicate_reject_sound leftResult) (predicate_reject_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.GroupedPredicateSequenceOrdinaryRejectionSoundnessProperties
/-! Exact executable ordinary rejection for grouped predicate sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

/-- Every grouped-predicate rejection is the exact rejection of its required
nonempty, allow-trailing parenthesized predicate list. -/
theorem groupedPredicates_reject_sound
    {input rejected : State} {failure : Failure}
    (result : groupedPredicates input = .reject failure rejected) :
    DeclarativeGrammar.GroupedPredicateSequenceRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold groupedPredicates at result
  cases parsedResult : delimited .leftParen .rightParen false predicate
      .typeExpr .topLevel input with
  | invariant error => simp [bind, parsedResult] at result
  | reject parsedFailure parsedRejected =>
      simp only [bind, parsedResult] at result
      cases result
      exact delimited_reject_sound .leftParen .rightParen false predicate
        DeclarativeGrammar.PredicateParses
        DeclarativeGrammar.PredicateRejects .typeExpr .topLevel
        predicate_success_sound predicate_reject_sound parsedResult
  | ok parsed afterParsed =>
      simp only [bind, parsedResult] at result
      cases elements : parsed.elements <;> simp [elements, pure] at result

/-- Package executable grouped-predicate success and exact ordinary
rejection. -/
theorem groupedPredicates_ordinaryOutcome_sound :
    (∀ {input next : State} {values : PredicateSequence},
      groupedPredicates input = .ok values next →
        DeclarativeGrammar.GroupedPredicateSequenceParses
          input.declarativeRemainder values next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      groupedPredicates input = .reject failure rejected →
        DeclarativeGrammar.GroupedPredicateSequenceRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨groupedPredicates_success_sound, groupedPredicates_reject_sound⟩

/-- Re-export exact grouped-predicate outcomes. -/
theorem groupedPredicates_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.GroupedPredicateSequenceParses
      DeclarativeGrammar.GroupedPredicateSequenceRejects :=
  DeclarativeGrammar.groupedPredicateSequenceExactOutcomeSpec

/-- Two grouped-predicate successes have the same AST and remainder. -/
theorem groupedPredicates_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : PredicateSequence}
    (leftResult : groupedPredicates input = .ok left leftOutput)
    (rightResult : groupedPredicates input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.GroupedPredicateSequenceParses.result_unique
    (groupedPredicates_success_sound leftResult)
    (groupedPredicates_success_sound rightResult)

/-- Two grouped-predicate rejections have the same declarative endpoint. -/
theorem groupedPredicates_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : groupedPredicates input = .reject leftFailure leftOutput)
    (rightResult : groupedPredicates input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.GroupedPredicateSequenceRejects.output_unique
    (groupedPredicates_reject_sound leftResult)
    (groupedPredicates_reject_sound rightResult)

end Solcore.Syntax.Parser.PredicateInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PredicateSequenceSoundnessProperties
/-! Success soundness for predicate-sequence branch selection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

private theorem groupedUnavailable_of_opening_absent {input : State}
    (openingAbsent : isSymbol input .leftParen = false) :
    DeclarativeGrammar.GroupedPredicateSequenceUnavailable
      input.declarativeRemainder := by
  rintro ⟨values, output, grouped⟩
  unfold DeclarativeGrammar.GroupedPredicateSequenceParses at grouped
  rcases grouped with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact symbolAbsentAt_of_isSymbol_eq_false .leftParen openingAbsent
    ⟨openingSpan, openingToken⟩

/-- Every successful sequence records exact grouped-first branch priority. -/
theorem predicateSequence_success_sound {input next : State}
    {values : PredicateSequence}
    (result : predicateSequence input = .ok values next) :
    DeclarativeGrammar.PredicateSequenceParses
      input.declarativeRemainder values next.declarativeRemainder := by
  unfold predicateSequence at result
  split at result
  · unfold orElse at result
    cases groupedResult : groupedPredicates input with
    | ok grouped afterGrouped =>
        simp only [groupedResult] at result
        cases result
        exact .grouped (groupedPredicates_success_sound groupedResult)
    | reject failure rejected =>
        simp only [groupedResult] at result
        exact .bare
          (groupedPredicates_reject_sound groupedResult).no_parse
          (barePredicates_success_sound result)
    | invariant error =>
        simp [groupedResult] at result
  · rename_i openingAbsent
    exact .bare
      (groupedUnavailable_of_opening_absent
        (Bool.eq_false_iff.mpr openingAbsent))
      (barePredicates_success_sound result)

/-- Sequence-union soundness composes with source validity. -/
theorem predicateSequence_success_sound_and_validFor {input next : State}
    {values : PredicateSequence} (inputValid : input.ValidFor)
    (result : predicateSequence input = .ok values next) :
    DeclarativeGrammar.PredicateSequenceParses
        input.declarativeRemainder values next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor Predicate.ValidFor input.file values := by
  refine ⟨predicateSequence_success_sound result, ?_⟩
  have valid := predicateSequence_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.PredicateInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.WhereClauseSoundnessProperties
/-! Success soundness for optional canonical `where` clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful optional `where` follows its marker-prioritized grammar. -/
theorem whereClause_success_sound {input next : State}
    {clause : Option WhereClause}
    (result : whereClause input = .ok clause next) :
    DeclarativeGrammar.OptionalWhereClauseParses
      input.declarativeRemainder clause next.declarativeRemainder := by
  unfold whereClause getState at result
  simp only [bind] at result
  by_cases present : isContextual input .where
  · simp only [present, if_true] at result
    rcases predicateBind_ok_components result with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases predicateBind_ok_components rest with
      ⟨predicates, afterPredicates, predicatesResult, finished⟩
    cases finished
    exact .present marker.span
      (contextual_success_exactTokenParses .where .typeExpr markerResult)
      (PredicateInternals.predicateSequence_success_sound predicatesResult)
  · have absent : isContextual input .where = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (contextualAbsentAt_of_isContextual_eq_false .where absent)

/-- Optional-where grammar soundness composes with source validity. -/
theorem whereClause_success_sound_and_validFor {input next : State}
    {clause : Option WhereClause} (inputValid : input.ValidFor)
    (result : whereClause input = .ok clause next) :
    DeclarativeGrammar.OptionalWhereClauseParses
        input.declarativeRemainder clause next.declarativeRemainder ∧
      Option.ValidFor WhereClause.ValidFor input.file clause := by
  refine ⟨whereClause_success_sound result, ?_⟩
  have valid := whereClause_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionSignatureSoundnessProperties
/-! Diagnostic-free success soundness for complete function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

private theorem signatureEnd_eq
    (parameters : DelimitedList FunctionParameter)
    (modifiers : FunctionModifiers) (returnsClause : Option ReturnClause)
    (whereClause : Option WhereClause) :
    SignatureInternals.signatureEnd parameters modifiers returnsClause
        whereClause =
      DeclarativeGrammar.functionSignatureEnd parameters modifiers
        returnsClause whereClause := by
  rfl

/-- Every diagnostic-free complete signature follows its location policy and
strict parser-independent grammar. -/
theorem functionSignature_success_sound (location : FunctionLocation)
    {input next : State} {signature : FunctionSignature}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionSignature location input = .ok signature next) :
    DeclarativeGrammar.FunctionSignatureParses
      (match location with
      | .module => DeclarativeGrammar.ModuleFunctionModifiersAllowed
      | .contract => DeclarativeGrammar.ContractFunctionModifiersAllowed)
      input.declarativeRemainder signature next.declarativeRemainder := by
  unfold functionSignature at result
  rcases bind_ok_components result with
    ⟨functionToken, afterKeyword, keywordResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases bind_ok_components rest with
    ⟨modifiers, afterModifiers, modifiersResult, rest⟩
  rcases bind_ok_components rest with
    ⟨returnsClause, afterReturns, returnsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨whereClause, afterWhere, whereResult, finished⟩
  cases finished
  have afterReturnsFree := whereClause_reflectsDiagnosticFreeOnSuccess
    afterReturns whereClause next whereResult diagnosticFree
  have afterModifiersFree := returnClause_reflectsDiagnosticFreeOnSuccess
    afterModifiers returnsClause afterReturns returnsResult afterReturnsFree
  have afterParametersFree :=
    functionModifiers_reflectsDiagnosticFreeOnSuccess location afterParameters
      modifiers afterModifiers modifiersResult afterModifiersFree
  have keywordGrammar := keyword_success_exactTokenParses .functionKw
    .topItem keywordResult
  have nameGrammar := identifier_success_sound .topItem nameResult
  have genericsGrammar := optionalGenericParameters_success_sound
    genericsResult
  have parametersGrammar := functionParameters_success_sound
    afterParametersFree parametersResult
  have modifiersGrammar := functionModifiers_success_sound location
    modifiersResult
  have returnsGrammar := returnClause_success_sound returnsResult
  have whereGrammar := whereClause_success_sound whereResult
  cases location with
  | module =>
      have policy := functionModifiers_module_success_allowed
        afterModifiersFree modifiersResult
      simpa only [signatureEnd_eq] using
        (DeclarativeGrammar.FunctionSignatureParses.parsed functionToken.span
          keywordGrammar nameGrammar genericsGrammar parametersGrammar
          modifiersGrammar returnsGrammar whereGrammar policy)
  | contract =>
      have policy := functionModifiers_contract_success_allowed modifiersResult
      simpa only [signatureEnd_eq] using
        (DeclarativeGrammar.FunctionSignatureParses.parsed functionToken.span
          keywordGrammar nameGrammar genericsGrammar parametersGrammar
          modifiersGrammar returnsGrammar whereGrammar policy)

/-- Signature grammar soundness composes with retained-source validity. -/
theorem functionSignature_success_sound_and_validFor
    (location : FunctionLocation) {input next : State}
    {signature : FunctionSignature} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionSignature location input = .ok signature next) :
    DeclarativeGrammar.FunctionSignatureParses
        (match location with
        | .module => DeclarativeGrammar.ModuleFunctionModifiersAllowed
        | .contract => DeclarativeGrammar.ContractFunctionModifiersAllowed)
        input.declarativeRemainder signature next.declarativeRemainder ∧
      FunctionSignature.ValidFor input.file signature := by
  refine ⟨functionSignature_success_sound location diagnosticFree result, ?_⟩
  have valid := functionSignature_validFor location input inputValid
  rw [result] at valid
  exact valid.1

/-- Module signature success specializes the generic location policy. -/
theorem functionSignature_module_success_sound {input next : State}
    {signature : FunctionSignature} (diagnosticFree : next.diagnosticsRev = [])
    (result : functionSignature .module input = .ok signature next) :
    DeclarativeGrammar.FunctionSignatureParses
      DeclarativeGrammar.ModuleFunctionModifiersAllowed
      input.declarativeRemainder signature next.declarativeRemainder :=
  functionSignature_success_sound .module diagnosticFree result

/-- Contract signature success specializes the generic location policy. -/
theorem functionSignature_contract_success_sound {input next : State}
    {signature : FunctionSignature} (diagnosticFree : next.diagnosticsRev = [])
    (result : functionSignature .contract input = .ok signature next) :
    DeclarativeGrammar.FunctionSignatureParses
      DeclarativeGrammar.ContractFunctionModifiersAllowed
      input.declarativeRemainder signature next.declarativeRemainder :=
  functionSignature_success_sound .contract diagnosticFree result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.BarePredicateSequenceOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for bare predicate sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

private theorem barePredicatesTail_reject_sound
    (first : Predicate) : ∀ fuel last tailRev input failure rejected,
      barePredicatesTail first fuel last tailRev input =
          .reject failure rejected →
        DeclarativeGrammar.BarePredicateTailRejects
          input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input failure rejected result
      simp [barePredicatesTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input failure rejected result
      unfold barePredicatesTail at result
      split at result
      · rename_i commaPresent
        cases commaResult : symbol .comma .typeExpr input with
        | invariant error => simp [commaResult] at result
        | reject commaFailure commaRejected =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .comma .typeExpr
              commaPresent with ⟨comma, parsed⟩
            rw [parsed] at commaResult
            contradiction
        | ok comma afterComma =>
            simp only [commaResult] at result
            have commaParsed := symbol_success_exactTokenParses .comma
              .typeExpr commaResult
            split at result
            · rename_i typePresent
              have nextStarts :=
                typeExprStartsAt_of_startsTypeExpr_eq_true typePresent
              cases predicateResult : predicate afterComma with
              | invariant error => simp [predicateResult] at result
              | reject predicateFailure predicateRejected =>
                  simp only [predicateResult] at result
                  cases result
                  exact .predicateRejected comma.span commaParsed nextStarts
                    (predicate_reject_sound predicateResult)
              | ok value afterPredicate =>
                  simp only [predicateResult] at result
                  exact .next comma.span commaParsed nextStarts
                    (predicate_success_sound predicateResult)
                    (inductionHypothesis value (value :: tailRev)
                      afterPredicate failure rejected result)
            · simp at result
      · simp at result

/-- Every rejected bare sequence records its exact first rejected stage. -/
theorem barePredicates_reject_sound
    {input rejected : State} {failure : Failure}
    (result : barePredicates input = .reject failure rejected) :
    DeclarativeGrammar.BarePredicateSequenceRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold barePredicates at result
  cases firstResult : predicate input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure firstRejected =>
      simp only [firstResult] at result
      cases result
      exact .firstRejected (predicate_reject_sound firstResult)
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact .tailRejected (predicate_success_sound firstResult)
        (barePredicatesTail_reject_sound first
          (afterFirst.remainingCount + 1) first [] afterFirst failure
            rejected result)

/-- Package executable bare-sequence success and exact rejection. -/
theorem barePredicates_ordinaryOutcome_sound :
    (∀ {input next : State} {values : PredicateSequence},
      barePredicates input = .ok values next →
        DeclarativeGrammar.BarePredicateSequenceParses
          input.declarativeRemainder values next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      barePredicates input = .reject failure rejected →
        DeclarativeGrammar.BarePredicateSequenceRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨barePredicates_success_sound, barePredicates_reject_sound⟩

/-- Re-export exact bare-predicate-sequence outcomes. -/
theorem barePredicates_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.BarePredicateSequenceParses
      DeclarativeGrammar.BarePredicateSequenceRejects :=
  DeclarativeGrammar.barePredicateSequenceExactOutcomeSpec

/-- Two bare-predicate successes have the same AST and remainder. -/
theorem barePredicates_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : PredicateSequence}
    (leftResult : barePredicates input = .ok left leftOutput)
    (rightResult : barePredicates input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.barePredicateSequenceExactOutcomeSpec.successResultUnique
    (barePredicates_success_sound leftResult)
    (barePredicates_success_sound rightResult)

/-- Two bare-predicate rejections have the same declarative endpoint. -/
theorem barePredicates_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : barePredicates input = .reject leftFailure leftOutput)
    (rightResult : barePredicates input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.BarePredicateSequenceRejects.output_unique
    (barePredicates_reject_sound leftResult)
    (barePredicates_reject_sound rightResult)

end Solcore.Syntax.Parser.PredicateInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PredicateSequenceOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for grouped-first predicate choice. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

private theorem openingPresent_of_isSymbol_eq_true {input : State}
    (present : isSymbol input .leftParen = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .leftParen } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeExpr present with
    ⟨opening, parsed⟩
  exact ⟨opening.span,
    (symbol_success_exactTokenParses .leftParen .typeExpr parsed).1⟩

/-- Every rejected predicate sequence retains exact grouped-first dispatch and
the final bare rejection remainder. -/
theorem predicateSequence_reject_sound
    {input rejected : State} {failure : Failure}
    (result : predicateSequence input = .reject failure rejected) :
    DeclarativeGrammar.PredicateSequenceRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold predicateSequence at result
  split at result
  · rename_i openingPresent
    unfold orElse at result
    cases groupedResult : groupedPredicates input with
    | ok grouped afterGrouped => simp [groupedResult] at result
    | invariant error => simp [groupedResult] at result
    | reject groupedFailure groupedRejected =>
        simp only [groupedResult] at result
        exact .fallback
          (openingPresent_of_isSymbol_eq_true openingPresent)
          (groupedPredicates_reject_sound groupedResult)
          (barePredicates_reject_sound result)
  · rename_i openingAbsent
    exact .direct
      (symbolAbsentAt_of_isSymbol_eq_false .leftParen
        (Bool.eq_false_iff.mpr openingAbsent))
      (barePredicates_reject_sound result)

/-- Package executable predicate-sequence success and exact rejection. -/
theorem predicateSequence_ordinaryOutcome_sound :
    (∀ {input next : State} {values : PredicateSequence},
      predicateSequence input = .ok values next →
        DeclarativeGrammar.PredicateSequenceParses
          input.declarativeRemainder values next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      predicateSequence input = .reject failure rejected →
        DeclarativeGrammar.PredicateSequenceRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨predicateSequence_success_sound, predicateSequence_reject_sound⟩

/-- Re-export exact prioritized predicate-sequence outcomes. -/
theorem predicateSequence_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.PredicateSequenceParses
      DeclarativeGrammar.PredicateSequenceRejects :=
  DeclarativeGrammar.predicateSequenceExactOutcomeSpec

/-- Two prioritized predicate-sequence successes have the same AST and
remainder. -/
theorem predicateSequence_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : PredicateSequence}
    (leftResult : predicateSequence input = .ok left leftOutput)
    (rightResult : predicateSequence input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.PredicateSequenceParses.result_unique
    (predicateSequence_success_sound leftResult)
    (predicateSequence_success_sound rightResult)

/-- Two prioritized predicate-sequence rejections have the same endpoint. -/
theorem predicateSequence_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : predicateSequence input = .reject leftFailure leftOutput)
    (rightResult : predicateSequence input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.PredicateSequenceRejects.output_unique
    (predicateSequence_reject_sound leftResult)
    (predicateSequence_reject_sound rightResult)

end Solcore.Syntax.Parser.PredicateInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.WhereClauseOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for optional canonical `where`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable optional-`where` rejection is the committed predicate
sequence rejection after its positively guarded marker. -/
theorem whereClause_reject_sound
    {input rejected : State} {failure : Failure}
    (result : whereClause input = .reject failure rejected) :
    DeclarativeGrammar.OptionalWhereClauseRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold whereClause getState at result
  simp only [bind] at result
  by_cases present : isContextual input .where
  · rcases contextual_eq_ok_of_isContextual_eq_true .where .typeExpr
        present with ⟨marker, markerResult⟩
    simp only [present, if_true, markerResult] at result
    cases predicatesResult : PredicateInternals.predicateSequence
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [predicatesResult] at result
    | ok predicates afterPredicates =>
        simp [predicatesResult, pure] at result
    | reject predicatesFailure predicatesRejected =>
        simp only [predicatesResult] at result
        cases result
        exact .predicatesRejected marker.span
          (contextual_success_exactTokenParses .where .typeExpr markerResult)
          (PredicateInternals.predicateSequence_reject_sound predicatesResult)
  · have absent : isContextual input .where = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package executable optional-`where` success and exact rejection. -/
theorem whereClause_ordinaryOutcome_sound :
    (∀ {input next : State} {clause : Option WhereClause},
      whereClause input = .ok clause next →
        DeclarativeGrammar.OptionalWhereClauseParses
          input.declarativeRemainder clause next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      whereClause input = .reject failure rejected →
        DeclarativeGrammar.OptionalWhereClauseRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨whereClause_success_sound, whereClause_reject_sound⟩

/-- Re-export exact optional `where` outcomes. -/
theorem whereClause_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.OptionalWhereClauseParses
      DeclarativeGrammar.OptionalWhereClauseRejects :=
  DeclarativeGrammar.optionalWhereClauseExactOutcomeSpec

/-- Two successful optional `where` clauses have the same AST and remainder. -/
theorem whereClause_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : Option WhereClause}
    (leftResult : whereClause input = .ok left leftOutput)
    (rightResult : whereClause input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalWhereClauseParses.result_unique
    (whereClause_success_sound leftResult) (whereClause_success_sound rightResult)

/-- Two `where` rejections have the same declarative endpoint. -/
theorem whereClause_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : whereClause input = .reject leftFailure leftOutput)
    (rightResult : whereClause input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalWhereClauseRejects.output_unique
    (whereClause_reject_sound leftResult) (whereClause_reject_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionSignatureOrdinarySuccessSoundnessProperties
/-! Ordinary success soundness for complete named-function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful complete signature follows the recovery-aware ordinary
grammar, independently of its executable location policy. -/
theorem functionSignature_success_ordinaryOutcome_sound
    (location : FunctionLocation) {input output : State}
    {signature : FunctionSignature}
    (result : functionSignature location input = .ok signature output) :
    DeclarativeGrammar.FunctionSignatureOrdinaryParses
      input.declarativeRemainder signature output.declarativeRemainder := by
  unfold functionSignature at result
  rcases bind_ok_components result with
    ⟨functionToken, afterKeyword, keywordResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases bind_ok_components rest with
    ⟨modifiers, afterModifiers, modifiersResult, rest⟩
  rcases bind_ok_components rest with
    ⟨returnsClause, afterReturns, returnsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨whereClause, afterWhere, whereResult, finished⟩
  cases finished
  have keywordGrammar := keyword_success_exactTokenParses .functionKw
    .topItem keywordResult
  have nameGrammar := identifier_success_sound .topItem nameResult
  have genericsGrammar := optionalGenericParameters_ordinaryOutcome_sound.1
    genericsResult
  have parametersGrammar := functionParameters_success_ordinaryOutcome_sound
    parametersResult
  have modifiersGrammar := functionModifiers_success_sound location
    modifiersResult
  have returnsGrammar := returnClause_ordinaryOutcome_sound.1 returnsResult
  have whereGrammar := whereClause_ordinaryOutcome_sound.1 whereResult
  simpa only [signatureEnd_eq] using
    (DeclarativeGrammar.FunctionSignatureOrdinaryParses.parsed
      functionToken.span keywordGrammar nameGrammar genericsGrammar
      parametersGrammar modifiersGrammar returnsGrammar whereGrammar)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionSignatureOrdinaryRejectionSoundnessProperties
/-! Exact first-stage rejection of executable function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem optionalFunctionModifier_ne_reject
    (keywordValue : HardKeyword) {input rejected : State} {failure : Failure}
    (result : optionalFunctionModifier keywordValue input =
      .reject failure rejected) : False := by
  unfold optionalFunctionModifier getState at result
  simp only [bind] at result
  by_cases present : isKeyword input keywordValue
  · rcases keyword_eq_ok_of_isKeyword_eq_true keywordValue .parameter
        present with ⟨marker, markerResult⟩
    simp [present, markerResult, pure] at result
  · have absent : isKeyword input keywordValue = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

private theorem functionModifiers_ne_reject
    (location : FunctionLocation) {input rejected : State}
    {failure : Failure}
    (result : functionModifiers location input = .reject failure rejected) :
    False := by
  unfold functionModifiers at result
  cases publicResult : optionalFunctionModifier .publicKw input with
  | invariant error => simp [bind, publicResult] at result
  | reject publicFailure publicRejected =>
      exact optionalFunctionModifier_ne_reject .publicKw publicResult
  | ok publicMarker afterPublic =>
      simp only [bind, publicResult] at result
      cases payableResult : optionalFunctionModifier .payableKw afterPublic with
      | invariant error => simp [payableResult] at result
      | reject payableFailure payableRejected =>
          exact optionalFunctionModifier_ne_reject .payableKw payableResult
      | ok payableMarker afterPayable =>
          simp only [payableResult] at result
          exact finishFunctionModifiers_ne_reject location publicMarker
            payableMarker afterPayable rejected failure result

/-- Every executable signature rejection records the exact first rejecting
structural stage; modifier parsing itself cannot reject. -/
theorem functionSignature_reject_ordinaryOutcome_sound
    (location : FunctionLocation) {input rejected : State}
    {failure : Failure}
    (result : functionSignature location input = .reject failure rejected) :
    DeclarativeGrammar.FunctionSignatureRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold functionSignature at result
  cases keywordResult : keyword .functionKw .topItem input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      have rejectedEq := keyword_reject_state_eq .functionKw .topItem
        keywordResult
      subst keywordRejected
      simp only [bind, keywordResult] at result
      cases result
      exact .keywordMissing
        (keyword_reject_tokenKindAbsentAt .functionKw .topItem keywordResult)
  | ok functionToken afterKeyword =>
      simp only [bind, keywordResult] at result
      have keywordParsed := keyword_success_exactTokenParses .functionKw
        .topItem keywordResult
      cases nameResult : identifier .topItem afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected functionToken.span keywordParsed
            (identifier_reject_sound .topItem nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := identifier_success_sound .topItem nameResult
          cases genericsResult : optionalGenericParameters afterName with
          | invariant error => simp [genericsResult] at result
          | reject genericsFailure genericsRejected =>
              simp only [genericsResult] at result
              cases result
              exact .genericsRejected functionToken.span keywordParsed
                nameParsed
                (optionalGenericParameters_reject_sound genericsResult)
          | ok genericParameters afterGenerics =>
              simp only [genericsResult] at result
              have genericsParsed :=
                optionalGenericParameters_ordinaryOutcome_sound.1
                  genericsResult
              cases parametersResult : functionParameters afterGenerics with
              | invariant error => simp [parametersResult] at result
              | reject parametersFailure parametersRejected =>
                  simp only [parametersResult] at result
                  cases result
                  exact .parametersRejected functionToken.span keywordParsed
                    nameParsed genericsParsed
                    (functionParameters_reject_ordinaryOutcome_sound
                      parametersResult)
              | ok parameters afterParameters =>
                  simp only [parametersResult] at result
                  have parametersParsed :=
                    functionParameters_success_ordinaryOutcome_sound
                      parametersResult
                  cases modifiersResult : functionModifiers location
                      afterParameters with
                  | invariant error => simp [modifiersResult] at result
                  | reject modifiersFailure modifiersRejected =>
                      exact False.elim
                        (functionModifiers_ne_reject location modifiersResult)
                  | ok modifiers afterModifiers =>
                      simp only [modifiersResult] at result
                      have modifiersParsed := functionModifiers_success_sound
                        location modifiersResult
                      cases returnsResult : returnClause afterModifiers with
                      | invariant error => simp [returnsResult] at result
                      | reject returnsFailure returnsRejected =>
                          simp only [returnsResult] at result
                          cases result
                          exact .returnsRejected functionToken.span
                            keywordParsed nameParsed genericsParsed
                            parametersParsed modifiersParsed
                            (returnClause_reject_sound returnsResult)
                      | ok returnsClause afterReturns =>
                          simp only [returnsResult] at result
                          have returnsParsed :=
                            returnClause_ordinaryOutcome_sound.1 returnsResult
                          cases whereResult : whereClause afterReturns with
                          | invariant error => simp [whereResult] at result
                          | ok whereClause afterWhere =>
                              simp [whereResult, pure] at result
                          | reject whereFailure whereRejected =>
                              simp only [whereResult] at result
                              cases result
                              exact .whereRejected functionToken.span
                                keywordParsed nameParsed genericsParsed
                                parametersParsed modifiersParsed returnsParsed
                                (whereClause_reject_sound whereResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionSignatureOrdinaryOutcomeSoundnessProperties
/-! Complete executable ordinary outcomes for named-function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package exact executable signature success and rejection at one location. -/
theorem functionSignature_ordinaryOutcome_sound
    (location : FunctionLocation) :
    (∀ {input output : State} {signature : FunctionSignature},
      functionSignature location input = .ok signature output →
        DeclarativeGrammar.FunctionSignatureOrdinaryParses
          input.declarativeRemainder signature output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      functionSignature location input = .reject failure rejected →
        DeclarativeGrammar.FunctionSignatureRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨functionSignature_success_ordinaryOutcome_sound location,
    functionSignature_reject_ordinaryOutcome_sound location⟩

/-- Re-export the location-independent deterministic signature contract. -/
theorem functionSignature_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.FunctionSignatureOrdinaryParses
      DeclarativeGrammar.FunctionSignatureRejects :=
  DeclarativeGrammar.functionSignatureDeterministicOutcomeSpec

/-- Re-export complete location-independent signature exactness. -/
theorem functionSignature_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.FunctionSignatureOrdinaryParses
      DeclarativeGrammar.FunctionSignatureRejects :=
  DeclarativeGrammar.functionSignatureExactOutcomeSpec

/-- At any executable location, two successful signatures have the same AST
and final declarative remainder. -/
theorem functionSignature_success_result_unique
    (location : FunctionLocation)
    {input leftOutput rightOutput : State}
    {left right : FunctionSignature}
    (leftResult : functionSignature location input = .ok left leftOutput)
    (rightResult : functionSignature location input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FunctionSignatureOrdinaryParses.result_unique
    (functionSignature_success_ordinaryOutcome_sound location leftResult)
    (functionSignature_success_ordinaryOutcome_sound location rightResult)

/-- At any executable location, two signature rejections have the same
declarative endpoint. -/
theorem functionSignature_reject_output_unique
    (location : FunctionLocation)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : functionSignature location input =
      .reject leftFailure leftOutput)
    (rightResult : functionSignature location input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.FunctionSignatureRejects.output_unique
    (functionSignature_reject_ordinaryOutcome_sound location leftResult)
    (functionSignature_reject_ordinaryOutcome_sound location rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaParameterCompletenessProperties
/-! Complete public lambda-parameter correspondence, including ordinary
recovery and the existing rewound rejection endpoint. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public lambda-parameter grammar success is exactly execution with the
same parameter AST and declarative remainder on a valid input. -/
theorem lambdaParameter_ordinary_success_iff
    {input : State} (inputValid : input.ValidFor)
    {value : LambdaParameter} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.LambdaParameterOrdinaryParses
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects
        input.declarativeRemainder value remainder ↔
      ∃ output, lambdaParameter input = .ok value output ∧
        output.declarativeRemainder = remainder :=
  ordinary_success_iff_exists_ok lambdaParameter lambdaParameter_exactOutcomeSpec
    (lambdaParameter_invariantFreeOnValid.ne_invariant input inputValid)
    (lambdaParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects
      typeExpr_success_sound typeExpr_reject_sound)
    (lambdaParameter_reject_ordinaryOutcome_sound DeclarativeGrammar.TypeExprRejects
      typeExpr_reject_sound)

/-- Public lambda-parameter grammar rejection is exactly execution at its
declarative endpoint, without identifying emitted diagnostics. -/
theorem lambdaParameter_ordinary_reject_iff
    {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.LambdaParameterRejects DeclarativeGrammar.TypeExprRejects
      input.declarativeRemainder rejected ↔
      ∃ failure output, lambdaParameter input = .reject failure output ∧
        output.declarativeRemainder = rejected :=
  ordinary_reject_iff_exists_reject lambdaParameter lambdaParameter_exactOutcomeSpec
    (lambdaParameter_invariantFreeOnValid.ne_invariant input inputValid)
    (lambdaParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects
      typeExpr_success_sound typeExpr_reject_sound)
    (lambdaParameter_reject_ordinaryOutcome_sound DeclarativeGrammar.TypeExprRejects
      typeExpr_reject_sound)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionSignatureLeafTotalityProperties
/-! Totality for reusable function-signature leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem functionParameters_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ values next, functionParameters input = .ok values next) ∨
      (∃ failure next,
        functionParameters input = .reject failure next) := by
  simpa only [functionParameters] using
    delimited_ordinary .leftParen .rightParen true namedParameter
      .parameter .topLevel namedParameter_elementTotalityContract
      input inputValid

theorem functionParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid functionParameters :=
  functionParameters_ordinary

theorem functionParameters_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    functionParameters input ≠ .invariant error :=
  functionParameters_invariantFreeOnValid.ne_invariant
    input inputValid error

/-- Optional modifier selection is total whether its keyword is present or not. -/
theorem optionalFunctionModifier_ordinary
    (keywordValue : HardKeyword)
    (input : State) (_inputValid : input.ValidFor) :
    (∃ value next,
      optionalFunctionModifier keywordValue input = .ok value next) ∨
      (∃ failure next,
        optionalFunctionModifier keywordValue input = .reject failure next) := by
  by_cases present : isKeyword input keywordValue
  · rcases (keyword_ordinary keywordValue .parameter) input with
      ⟨marker, next, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · exact Or.inl ⟨some marker.span, next, by
        simp only [optionalFunctionModifier, getState, bind, present,
          ↓reduceIte, markerResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalFunctionModifier, getState, bind, present,
          ↓reduceIte, markerResult]⟩
  · have absent : isKeyword input keywordValue = false := by
      cases found : isKeyword input keywordValue with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalFunctionModifier, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem optionalFunctionModifier_invariantFreeOnValid
    (keywordValue : HardKeyword) :
    Parser.InvariantFreeOnValid (optionalFunctionModifier keywordValue) :=
  optionalFunctionModifier_ordinary keywordValue

theorem optionalFunctionModifier_ne_invariant
    (keywordValue : HardKeyword)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    optionalFunctionModifier keywordValue input ≠ .invariant error :=
  (optionalFunctionModifier_invariantFreeOnValid keywordValue).ne_invariant
    input inputValid error

/-- Both optional markers and their policy diagnostics are total. -/
theorem functionModifiers_ordinary
    (location : FunctionLocation)
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, functionModifiers location input = .ok value next) ∨
      (∃ failure next,
        functionModifiers location input = .reject failure next) := by
  rcases optionalFunctionModifier_ordinary .publicKw input inputValid with
    ⟨publicMarker, afterPublic, publicResult⟩ |
    ⟨failure, rejected, publicResult⟩
  · have publicReply := optionalFunctionModifier_validFor .publicKw
      input inputValid
    rw [publicResult] at publicReply
    rcases optionalFunctionModifier_ordinary .payableKw afterPublic
        publicReply.2.1 with
      ⟨payableMarker, afterPayable, payableResult⟩ |
      ⟨failure, rejected, payableResult⟩
    · cases location <;> cases publicMarker <;> cases payableMarker <;>
        exact Or.inl ⟨_, _, by
          simp only [functionModifiers, bind, publicResult, payableResult]
          rfl⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [functionModifiers, bind, publicResult, payableResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [functionModifiers, bind, publicResult]⟩

theorem functionModifiers_invariantFreeOnValid
    (location : FunctionLocation) :
    Parser.InvariantFreeOnValid (functionModifiers location) :=
  functionModifiers_ordinary location

theorem functionModifiers_ne_invariant
    (location : FunctionLocation)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    functionModifiers location input ≠ .invariant error :=
  (functionModifiers_invariantFreeOnValid location).ne_invariant
    input inputValid error

/-- A present return clause reuses total public type parsing. -/
theorem returnClause_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, returnClause input = .ok value next) ∨
      (∃ failure next, returnClause input = .reject failure next) := by
  by_cases present : isContextual input .returns
  · rcases (contextual_ordinary .returns .typeExpr) input with
      ⟨marker, afterMarker, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · have markerReply := contextual_validFor .returns .typeExpr
        input inputValid
      rw [markerResult] at markerReply
      rcases delimited_ordinary .leftParen .rightParen true typeExpr
          .typeExpr .typeExpr typeExpr_elementTotalityContract afterMarker
          markerReply.2.1 with
        ⟨types, final, typesResult⟩ |
        ⟨failure, rejected, typesResult⟩
      · exact Or.inl ⟨some {
            span := SourceSpan.cover marker.span types.span
            types
          }, final, by
            simp only [returnClause, getState, bind, present, ↓reduceIte,
              markerResult, typesResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [returnClause, getState, bind, present, ↓reduceIte,
            markerResult, typesResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [returnClause, getState, bind, present, ↓reduceIte,
          markerResult]⟩
  · have absent : isContextual input .returns = false := by
      cases found : isContextual input .returns with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [returnClause, getState, bind, absent, Bool.false_eq_true,
        ↓reduceIte, pure]⟩

theorem returnClause_invariantFreeOnValid :
    Parser.InvariantFreeOnValid returnClause :=
  returnClause_ordinary

theorem returnClause_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    returnClause input ≠ .invariant error :=
  returnClause_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.GenericParametersTotalityProperties
/-! Valid-input totality for canonical generic parameter lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Nonempty delimiter syntax discharges the defensive refinement invariant. -/
theorem genericParameters_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ values next, genericParameters input = .ok values next) ∨
      (∃ failure next,
        genericParameters input = .reject failure next) := by
  rcases delimited_ordinary .less .greater false (identifier .parameter)
      .parameter .topLevel (identifier_elementTotalityContract .parameter)
      input inputValid with
    ⟨values, afterValues, valuesResult⟩ |
    ⟨failure, rejected, valuesResult⟩
  · rcases values with ⟨span, elements⟩
    have nonempty := delimited_false_elements_ne_nil_onSuccess .less .greater
      (identifier .parameter) .parameter .topLevel valuesResult
    cases elements with
    | nil => exact False.elim (nonempty rfl)
    | cons head tail =>
        exact Or.inl ⟨{
          span
          elements := { head, tail }
        }, afterValues, by
          simp only [genericParameters, bind, valuesResult]
          rfl⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [genericParameters, bind, valuesResult]⟩

theorem genericParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid genericParameters :=
  genericParameters_ordinary

theorem genericParameters_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    genericParameters input ≠ .invariant error :=
  genericParameters_invariantFreeOnValid.ne_invariant input inputValid error

/-- Optional generic parameters are total in both selected and absent paths. -/
theorem optionalGenericParameters_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ values next, optionalGenericParameters input = .ok values next) ∨
      (∃ failure next,
        optionalGenericParameters input = .reject failure next) := by
  by_cases present : isSymbol input .less
  · rcases genericParameters_ordinary input inputValid with
      ⟨values, next, valuesResult⟩ |
      ⟨failure, rejected, valuesResult⟩
    · exact Or.inl ⟨some values, next, by
        simp only [optionalGenericParameters, getState, bind, present,
          ↓reduceIte, valuesResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalGenericParameters, getState, bind, present,
          ↓reduceIte, valuesResult]⟩
  · have absent : isSymbol input .less = false := by
      cases found : isSymbol input .less with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalGenericParameters, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem optionalGenericParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid optionalGenericParameters :=
  optionalGenericParameters_ordinary

theorem optionalGenericParameters_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    optionalGenericParameters input ≠ .invariant error :=
  optionalGenericParameters_invariantFreeOnValid.ne_invariant
    input inputValid error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionSignatureTotalityProperties
/-! Valid-input totality for complete canonical function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem functionSignature_invariantFreeOnValid
    (location : FunctionLocation) :
    Parser.InvariantFreeOnValid (functionSignature location) := by
  unfold functionSignature
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .functionKw .topItem)
    (keyword_ordinary .functionKw .topItem).invariantFreeOnValid
  intro functionToken
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .topItem)
    (identifier_ordinary .topItem).invariantFreeOnValid
  intro name
  apply Parser.bind_invariantFreeOnValid
    optionalGenericParameters_validFor
    optionalGenericParameters_invariantFreeOnValid
  intro genericParameters
  apply Parser.bind_invariantFreeOnValid functionParameters_validFor
    functionParameters_invariantFreeOnValid
  intro parameters
  apply Parser.bind_invariantFreeOnValid (functionModifiers_validFor location)
    (functionModifiers_invariantFreeOnValid location)
  intro modifiers
  apply Parser.bind_invariantFreeOnValid returnClause_validFor
    returnClause_invariantFreeOnValid
  intro returnsClause
  apply Parser.bind_invariantFreeOnValid whereClause_validFor
    whereClause_invariantFreeOnValid
  intro parsedWhereClause
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover functionToken.span
      (SignatureInternals.signatureEnd parameters modifiers returnsClause
        parsedWhereClause)
    name
    genericParameters
    parameters
    modifiers
    returnsClause
    whereClause := parsedWhereClause
  } : FunctionSignature)

theorem functionSignature_ordinary
    (location : FunctionLocation)
    (input : State) (inputValid : input.ValidFor) :
    (∃ signature next,
      functionSignature location input = .ok signature next) ∨
      (∃ failure next,
        functionSignature location input = .reject failure next) :=
  functionSignature_invariantFreeOnValid location input inputValid

theorem functionSignature_ne_invariant
    (location : FunctionLocation)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    functionSignature location input ≠ .invariant error :=
  (functionSignature_invariantFreeOnValid location).ne_invariant
    input inputValid error

/-- A complete signature is a strict reusable parser element. -/
theorem functionSignature_elementTotalityContract
    (location : FunctionLocation) :
    ElementTotalityContract (functionSignature location) := {
  validFor := (functionSignature_validFor location).mono
    (fun _ _ _ => trivial)
  preservesTokenWindow := functionSignature_preservesTokenWindow location
  cursorLtOnSuccess :=
    FunctionInternals.functionSignature_cursor_lt_onSuccess location
  invariantFree := functionSignature_ne_invariant location
}

end Solcore.Syntax.Parser
end
