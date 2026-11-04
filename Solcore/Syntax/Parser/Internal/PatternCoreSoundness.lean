import Solcore.Syntax.Parser.Internal.PatternSoundness
import Solcore.Syntax.Parser.Internal.ImportProofs
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Internal.ExpressionTotality
import Solcore.Syntax.Parser.Internal.PatternProofs

/-!
Soundness of the parsers of core patterns: each success and each rejection has its
declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternConstructorSoundnessProperties
/-!
Diagnostic reflection and exact parser-independent soundness for leading-dot
and qualified constructor patterns.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

private theorem bindOkComponents {alpha beta : Type} {first : Parser alpha}
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

private theorem qualifiedNameTail_diagnosticFreeHyphens
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input path next,
      QualifiedNameInternals.qualifiedNameTail context phase first fuel last
          tailRev input = .ok path next →
      next.diagnosticsRev = [] →
      input.diagnosticsRev = [] ∧
        ((first.value.toList.contains '-' = false ∧
          ∀ component ∈ tailRev,
            component.value.toList.contains '-' = false) →
          ∀ component ∈ path.value.components.toList,
            component.value.toList.contains '-' = false) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input path next result diagnosticFree
      simp [QualifiedNameInternals.qualifiedNameTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input path next result diagnosticFree
      unfold QualifiedNameInternals.qualifiedNameTail at result
      split at result
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                rcases inductionHypothesis component (component :: tailRev)
                    afterComponent path next result diagnosticFree with
                  ⟨afterComponentFree, assembled⟩
                have componentGood :=
                  identifier_hyphenAbsent_of_diagnosticFree context
                    afterComponentFree componentResult
                have afterDotFree := identifier_reflectsDiagnosticFreeOnSuccess
                  context afterDot component afterComponent componentResult
                    afterComponentFree
                have inputFree := symbol_reflectsDiagnosticFreeOnSuccess .dot
                  context input dot afterDot dotResult afterDotFree
                refine ⟨inputFree, ?_⟩
                rintro ⟨firstGood, tailGood⟩
                apply assembled
                refine ⟨firstGood, ?_⟩
                intro item member
                rcases List.mem_cons.mp member with rfl | member
                · exact componentGood
                · exact tailGood item member
      · unfold QualifiedNameInternals.finishQualifiedName at result
        cases result
        refine ⟨diagnosticFree, ?_⟩
        rintro ⟨firstGood, tailGood⟩ component member
        simp only [NonemptyList.toList, List.mem_cons,
          List.mem_reverse] at member
        rcases member with rfl | member
        · exact firstGood
        · exact tailGood component member

/-- Diagnostic-free qualified paths exclude hyphens in every component. -/
theorem patternQualifiedName_success_sound
    {input next : State} {path : QualifiedName}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : qualifiedName .pattern .pattern input = .ok path next) :
    DeclarativeGrammar.PatternQualifiedNameParses input.declarativeRemainder
      path next.declarativeRemainder := by
  unfold qualifiedName at result
  cases firstResult : identifier .pattern input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      rcases qualifiedNameTail_diagnosticFreeHyphens .pattern .pattern first
          (afterFirst.remainingCount + 1) first [] afterFirst path next result
            diagnosticFree with
        ⟨afterFirstFree, componentsGood⟩
      refine ⟨qualifiedName_success_sound .pattern .pattern (by
        unfold qualifiedName
        simp only [firstResult]
        exact result), ?_⟩
      exact componentsGood ⟨
        identifier_hyphenAbsent_of_diagnosticFree .pattern afterFirstFree
          firstResult,
        by simp⟩

/-- Leading-dot constructors reflect through marker, name, and arguments. -/
theorem dotConstructorPattern_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (dotConstructorPattern nested) := by
  unfold dotConstructorPattern
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .dot .pattern)
  intro dot
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    patternName_reflectsDiagnosticFreeOnSuccess
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalConstructorArguments_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects)
  intro arguments
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Qualified constructors reflect through their maximal path and arguments. -/
theorem qualifiedPattern_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (qualifiedPattern nested) := by
  intro input pattern next result diagnosticFree
  unfold qualifiedPattern at result
  rcases bindOkComponents result with
    ⟨path, afterPath, pathResult, rest⟩
  rcases bindOkComponents rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases componentsEq : path.value.components.toList.reverse with
  | nil => simp [componentsEq] at finished
  | cons name qualifiersRev =>
      simp only [componentsEq] at finished
      split at finished <;> cases finished
      all_goals
        have afterPathFree :=
          optionalConstructorArguments_reflectsDiagnosticFreeOnSuccess nested
            nestedReflects afterPath arguments next argumentsResult
              diagnosticFree
        exact qualifiedName_reflectsDiagnosticFreeOnSuccess .pattern .pattern
          input path afterPath pathResult afterPathFree

/--
Every diagnostic-free leading-dot success retains its marker, Boolean-first
name, transactional arguments, empty qualifier list, span, and final cursor.
-/
theorem dotConstructorPattern_success_sound
    (nested : Parser Pattern)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.ConstructorArgumentsFallbackSpec nestedParses)
    (argumentsRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      constructorArguments nested input = .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {pattern : Pattern}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : dotConstructorPattern nested input = .ok pattern next) :
    DeclarativeGrammar.DotConstructorPatternParses nestedParses fallback
      input.declarativeRemainder pattern next.declarativeRemainder := by
  unfold dotConstructorPattern at result
  rcases bindOkComponents result with
    ⟨dot, afterDot, dotResult, rest⟩
  rcases bindOkComponents rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases bindOkComponents rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases finished
  have afterNameFree :=
    optionalConstructorArguments_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects afterName arguments next argumentsResult diagnosticFree
  exact .parsed dot.span
    (symbol_success_exactTokenParses .dot .pattern dotResult)
    (patternName_success_sound afterNameFree nameResult)
    (optionalConstructorArguments_success_sound nested nestedParses
      fallback argumentsRejectionSound nestedReflects nestedSound nestedShape
        diagnosticFree argumentsResult)

/--
Every diagnostic-free qualified success fixes maximal components, their
reverse split into final name and forward qualifiers, lowercase binder choice,
arguments, outer span, AST branch, and final remainder.
-/
theorem qualifiedPattern_success_sound
    (nested : Parser Pattern)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.ConstructorArgumentsFallbackSpec nestedParses)
    (argumentsRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      constructorArguments nested input = .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {pattern : Pattern}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : qualifiedPattern nested input = .ok pattern next) :
    DeclarativeGrammar.QualifiedPatternParses nestedParses fallback
      input.declarativeRemainder pattern next.declarativeRemainder := by
  unfold qualifiedPattern at result
  rcases bindOkComponents result with
    ⟨path, afterPath, pathResult, rest⟩
  rcases bindOkComponents rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases componentsEq : path.value.components.toList.reverse with
  | nil => simp [componentsEq] at finished
  | cons name qualifiersRev =>
      simp only [componentsEq] at finished
      split at finished
      · rename_i binderChoice
        change DeclarativeGrammar.qualifiedPatternIsBinder qualifiersRev
          arguments name = true at binderChoice
        cases finished
        have afterPathFree :=
          optionalConstructorArguments_reflectsDiagnosticFreeOnSuccess nested
            nestedReflects afterPath arguments next argumentsResult
              diagnosticFree
        have pathGrammar := patternQualifiedName_success_sound afterPathFree
          pathResult
        have argumentsGrammar := optionalConstructorArguments_success_sound
          nested nestedParses fallback argumentsRejectionSound nestedReflects
            nestedSound nestedShape diagnosticFree argumentsResult
        have qualifiersEmpty : qualifiersRev = [] := by
          have parts : (qualifiersRev = [] ∧ arguments = none) ∧
              DeclarativeGrammar.patternIdentifierStartsWithLowercase name =
                true := by
            simpa [DeclarativeGrammar.qualifiedPatternIsBinder] using
              binderChoice
          exact parts.1.1
        subst qualifiersRev
        exact .binder pathGrammar argumentsGrammar componentsEq binderChoice
      · rename_i constructorChoice
        change DeclarativeGrammar.qualifiedPatternIsBinder qualifiersRev
          arguments name ≠ true at constructorChoice
        have constructorChoiceBool :
            DeclarativeGrammar.qualifiedPatternIsBinder qualifiersRev
              arguments name = false :=
          Bool.eq_false_iff.mpr constructorChoice
        cases finished
        have afterPathFree :=
          optionalConstructorArguments_reflectsDiagnosticFreeOnSuccess nested
            nestedReflects afterPath arguments next argumentsResult
              diagnosticFree
        have pathGrammar := patternQualifiedName_success_sound afterPathFree
          pathResult
        have argumentsGrammar := optionalConstructorArguments_success_sound
          nested nestedParses fallback argumentsRejectionSound nestedReflects
            nestedSound nestedShape diagnosticFree argumentsResult
        exact .constructor pathGrammar argumentsGrammar componentsEq
          constructorChoiceBool

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternCoreSoundnessProperties
/-!
Diagnostic reflection and exact ordered soundness for the non-recovering Core
pattern dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- The Core dispatcher reflects through whichever prioritized branch wins. -/
theorem patternCore_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (patternCore nested expression) := by
  intro input value next result diagnosticFree
  unfold patternCore at result
  split at result
  · exact wildcardPattern_reflectsDiagnosticFreeOnSuccess input value next
      result diagnosticFree
  · split at result
    · exact literalPattern_reflectsDiagnosticFreeOnSuccess input value next
        result diagnosticFree
    · split at result
      · exact booleanBinderPattern_reflectsDiagnosticFreeOnSuccess input
          value next result diagnosticFree
      · split at result
        · exact parenthesizedPattern_reflectsDiagnosticFreeOnSuccess nested
            nestedReflects input value next result diagnosticFree
        · split at result
          · exact dotConstructorPattern_reflectsDiagnosticFreeOnSuccess
              nested nestedReflects input value next result diagnosticFree
          · split at result
            · exact comptimePattern_reflectsDiagnosticFreeOnSuccess
                expression expressionReflects input value next result
                  diagnosticFree
            · split at result
              · exact qualifiedPattern_reflectsDiagnosticFreeOnSuccess
                  nested nestedReflects input value next result diagnosticFree
              · simp [rejectAt] at result

/--
Every diagnostic-free Core dispatcher success follows its exact independent
branch and carries evidence excluding every earlier executable guard.
-/
theorem patternCore_success_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.ConstructorArgumentsFallbackSpec nestedParses)
    (argumentsRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      constructorArguments nested input = .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Pattern}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : patternCore nested expression input = .ok value next) :
    DeclarativeGrammar.PatternCoreParses nestedParses expressionParses
      fallback input.declarativeRemainder value next.declarativeRemainder := by
  unfold patternCore at result
  split at result
  next underscorePresent =>
    exact .wildcard (wildcardPattern_success_sound result)
  next underscoreAbsent =>
    have noUnderscore := symbolAbsentAt_of_isSymbol_eq_false .underscore
      (Bool.eq_false_iff.mpr underscoreAbsent)
    split at result
    next literalPresent =>
      exact .literal noUnderscore (literalPattern_success_sound result)
    next literalAbsent =>
      have noLiteral :=
        ExpressionAtomInternals.not_coreLiteralStartsAt_of_isCoreLiteral_eq_false
          (Bool.eq_false_iff.mpr literalAbsent)
      split at result
      next booleanPresent =>
        exact .boolean noUnderscore noLiteral
          (booleanBinderPattern_success_sound result)
      next booleanAbsent =>
        have noBoolean :=
          not_booleanPatternStartsAt_of_isBooleanValue_eq_false
            (Bool.eq_false_iff.mpr booleanAbsent)
        split at result
        next leftParenPresent =>
          exact .parenthesized noUnderscore noLiteral noBoolean
            (parenthesizedPattern_success_sound nested nestedParses
              nestedReflects nestedSound diagnosticFree result)
        next leftParenAbsent =>
          have noLeftParen := symbolAbsentAt_of_isSymbol_eq_false .leftParen
            (Bool.eq_false_iff.mpr leftParenAbsent)
          split at result
          next dotPresent =>
            exact .dotConstructor noUnderscore noLiteral noBoolean noLeftParen
              (dotConstructorPattern_success_sound nested nestedParses
                fallback argumentsRejectionSound nestedReflects nestedSound
                  nestedShape diagnosticFree result)
          next dotAbsent =>
            have noDot := symbolAbsentAt_of_isSymbol_eq_false .dot
              (Bool.eq_false_iff.mpr dotAbsent)
            split at result
            next comptimePresent =>
              exact .comptime noUnderscore noLiteral noBoolean noLeftParen
                noDot (comptimePattern_success_sound expression
                  expressionParses expressionSound diagnosticFree result)
            next comptimeAbsent =>
              have noComptime := contextualAbsentAt_of_isContextual_eq_false
                .comptime (Bool.eq_false_iff.mpr comptimeAbsent)
              split at result
              next identifierPresent =>
                exact .qualified noUnderscore noLiteral noBoolean noLeftParen
                  noDot noComptime
                    (qualifiedPattern_success_sound nested nestedParses
                      fallback argumentsRejectionSound nestedReflects
                        nestedSound nestedShape diagnosticFree result)
              next identifierAbsent =>
                simp [rejectAt] at result

end Solcore.Syntax.Parser.PatternInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CorePatternSoundnessProperties
/-!
Public diagnostic reflection and exact diagnostic-free soundness for one Core
pattern recursion layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public pattern reflection follows from the two recursive components. -/
theorem patternLayer_reflectsDiagnosticFreeOnSuccess_of_components
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (patternLayer nested expression) :=
  patternLayer_reflectsDiagnosticFreeOnSuccess nested expression
    (PatternInternals.patternCore_reflectsDiagnosticFreeOnSuccess nested
      expression nestedReflects expressionReflects)

/--
Every diagnostic-free public pattern success is the unchanged Core success
and therefore follows the exact ordered independent grammar.
-/
theorem patternLayer_success_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (nestedParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (fallback :
      DeclarativeGrammar.ConstructorArgumentsFallbackSpec nestedParses)
    (argumentsRejectionSound : ∀ {input rejected : State}
      {failure : Failure},
      PatternInternals.constructorArguments nested input =
          .reject failure rejected →
        fallback.rejects input.declarativeRemainder)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Pattern}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : patternLayer nested expression input = .ok value next) :
    DeclarativeGrammar.PatternLayerParses nestedParses expressionParses
      fallback input.declarativeRemainder value next.declarativeRemainder :=
  PatternInternals.patternCore_success_sound nested expression nestedParses
    expressionParses fallback argumentsRejectionSound nestedReflects
      nestedSound nestedShape expressionSound diagnosticFree
        (patternCore_of_diagnosticFree_success nested expression result
          diagnosticFree)

end Solcore.Syntax.Parser
end
