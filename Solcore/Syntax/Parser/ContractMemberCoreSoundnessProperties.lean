import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.Parser.ContractFieldSoundnessProperties
import Solcore.Syntax.Parser.DeclarationLeafDiagnosticReflectionProperties
import Solcore.Syntax.Parser.Enum
import Solcore.Syntax.Parser.FunctionDeclSoundnessProperties
import Solcore.Syntax.Parser.TypeAlias

/-! Parametric strict soundness for attribute-free contract-member dispatch. -/

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

namespace ContractInternals

private theorem tokenKind_eq_colon_of_beq_true {actual : TokenKind}
    (accepted : (actual == .symbol .colon) = true) :
    actual = .symbol .colon := by
  change instBEqTokenKind.beq actual (.symbol .colon) = true at accepted
  cases actual <;> simp only [instBEqTokenKind.beq] at accepted
  all_goals try contradiction
  case symbol actual =>
    change instBEqSymbol.beq actual .colon = true at accepted
    unfold instBEqSymbol.beq at accepted
    cases actual <;> first | rfl | cases accepted

/-- Executable positive field lookahead is exactly the two-token grammar. -/
theorem contractFieldStartsAt_of_startsContractField_eq_true
    {input : State} (starts : startsContractField input = true) :
    DeclarativeGrammar.ContractFieldStartsAt input.declarativeRemainder := by
  unfold startsContractField at starts
  have parts := Bool.and_eq_true_iff.mp starts
  cases currentFound : input.peek? with
  | none =>
      simp [isIdentifier, State.peekKind?, currentFound] at parts
  | some current =>
      rcases current with ⟨nameSpan, currentKind⟩
      cases currentKind <;>
        simp [isIdentifier, State.peekKind?, currentFound] at parts
      case identifier spelling =>
        unfold State.peekOffsetKind? at parts
        cases followingFound : input.peekOffset? 1 with
        | none => simp [followingFound] at parts
        | some following =>
            rcases following with ⟨colonSpan, followingKind⟩
            simp only [followingFound, Option.map_some] at parts
            have followingKindEq := tokenKind_eq_colon_of_beq_true parts
            subst followingKind
            exact ⟨spelling, nameSpan, colonSpan,
              tokenAt_of_peek?_eq_some currentFound,
              State.cursor_add_lt_endIndex_of_peekOffset?_eq_some
                followingFound,
              State.getElem?_eq_some_of_peekOffset?_eq_some followingFound⟩

/-- The independent two-token field grammar makes executable lookahead true. -/
theorem startsContractField_eq_true_of_contractFieldStartsAt
    {input : State}
    (starts : DeclarativeGrammar.ContractFieldStartsAt
      input.declarativeRemainder) :
    startsContractField input = true := by
  rcases starts with ⟨spelling, nameSpan, colonSpan, nameToken, colonToken⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span := nameSpan, value := .identifier spelling }
    at nameToken
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    (input.cursor + 1) { span := colonSpan, value := .symbol .colon }
    at colonToken
  have namePresent : isIdentifier input = true := by
    unfold isIdentifier State.peekKind? State.peek?
    simp only [nameToken.1, ↓reduceIte, nameToken.2, Option.map_some]
  have colonPresent : input.peekOffsetKind? 1 =
      some (.symbol .colon) := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [colonToken.1, ↓reduceIte, colonToken.2, Option.map_some]
  unfold startsContractField
  rw [namePresent, colonPresent]
  decide

/-- Executable negative field lookahead excludes the exact field prefix. -/
theorem not_contractFieldStartsAt_of_startsContractField_eq_false
    {input : State} (stops : startsContractField input = false) :
    ¬ DeclarativeGrammar.ContractFieldStartsAt input.declarativeRemainder := by
  intro starts
  rw [startsContractField_eq_true_of_contractFieldStartsAt starts] at stops
  contradiction

private theorem mapMember_reflectsDiagnosticFreeOnSuccess {alpha : Type}
    (parser : Parser alpha) (wrap : alpha → ContractMember)
    (reflects : Parser.ReflectsDiagnosticFreeOnSuccess parser) :
    Parser.ReflectsDiagnosticFreeOnSuccess (mapMember parser wrap) := by
  unfold mapMember
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess reflects
  intro value
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Core dispatch cannot erase diagnostics when its abstract leaves cannot. -/
theorem contractMemberCore_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess contractMemberCore := by
  intro input member next result diagnosticFree
  unfold contractMemberCore contractMemberParser at result
  split at result
  · exact mapMember_reflectsDiagnosticFreeOnSuccess
      (contractField expression) wrapField
      (contractField_reflectsDiagnosticFreeOnSuccess expression
        expressionReflects) input member next result diagnosticFree
  split at result
  · exact mapMember_reflectsDiagnosticFreeOnSuccess
      (functionDecl .contract) wrapContractFunction
      (functionDecl_reflectsDiagnosticFreeOnSuccess .contract
        allowBodyReflects) input member next result diagnosticFree
  split at result
  · exact mapMember_reflectsDiagnosticFreeOnSuccess
      constructorDecl wrapConstructor
      (constructorDecl_reflectsDiagnosticFreeOnSuccess requiredBodyReflects)
        input member next result diagnosticFree
  split at result
  · exact mapMember_reflectsDiagnosticFreeOnSuccess
      fallbackDecl wrapFallback
      (fallbackDecl_reflectsDiagnosticFreeOnSuccess requiredBodyReflects)
        input member next result diagnosticFree
  split at result
  · exact mapMember_reflectsDiagnosticFreeOnSuccess
      typeAlias wrapContractTypeAlias
      typeAlias_reflectsDiagnosticFreeOnSuccess input member next result
        diagnosticFree
  split at result
  · exact mapMember_reflectsDiagnosticFreeOnSuccess
      (enumDecl none) wrapContractEnum
      (enumDecl_reflectsDiagnosticFreeOnSuccess none) input member next result
        diagnosticFree
  · simp [rejectedContractMember, rejectAt] at result

/-- Every diagnostic-free core success follows the exact six-way priority. -/
theorem contractMemberCore_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {member : ContractMember}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractMemberCore input = .ok member next) :
    DeclarativeGrammar.ContractMemberCoreParses expressionParses
      allowBodyParses requiredBodyParses input.declarativeRemainder member
        next.declarativeRemainder := by
  unfold contractMemberCore contractMemberParser at result
  split at result
  next startsField =>
    unfold mapMember at result
    rcases bind_ok_components result with
      ⟨declaration, afterDeclaration, declarationResult, finished⟩
    cases finished
    exact .field
      (contractFieldStartsAt_of_startsContractField_eq_true startsField)
      (contractField_success_sound expression expressionParses
        expressionSound diagnosticFree declarationResult)
  next fieldAbsent =>
    have fieldAbsentEq : startsContractField input = false :=
      Bool.eq_false_iff.mpr fieldAbsent
    split at result
    next startsFunction =>
      unfold mapMember at result
      rcases bind_ok_components result with
        ⟨declaration, afterDeclaration, declarationResult, finished⟩
      cases finished
      exact .function
        (not_contractFieldStartsAt_of_startsContractField_eq_false
          fieldAbsentEq)
        (functionDecl_success_sound .contract allowBodyParses
          allowBodyReflects allowBodySound diagnosticFree declarationResult)
    next functionAbsent =>
      have functionAbsentEq : isKeyword input .functionKw = false :=
        Bool.eq_false_iff.mpr functionAbsent
      split at result
      next startsConstructor =>
        unfold mapMember at result
        rcases bind_ok_components result with
          ⟨declaration, afterDeclaration, declarationResult, finished⟩
        cases finished
        exact .constructor
          (not_contractFieldStartsAt_of_startsContractField_eq_false
            fieldAbsentEq)
          (keywordAbsentAt_of_isKeyword_eq_false .functionKw
            functionAbsentEq)
          (constructorDecl_success_sound requiredBodyParses
            requiredBodyReflects requiredBodySound diagnosticFree
              declarationResult)
      next constructorAbsent =>
        have constructorAbsentEq : isKeyword input .constructorKw = false :=
          Bool.eq_false_iff.mpr constructorAbsent
        split at result
        next startsFallback =>
          unfold mapMember at result
          rcases bind_ok_components result with
            ⟨declaration, afterDeclaration, declarationResult, finished⟩
          cases finished
          exact .fallback
            (not_contractFieldStartsAt_of_startsContractField_eq_false
              fieldAbsentEq)
            (keywordAbsentAt_of_isKeyword_eq_false .functionKw
              functionAbsentEq)
            (keywordAbsentAt_of_isKeyword_eq_false .constructorKw
              constructorAbsentEq)
            (fallbackDecl_success_sound requiredBodyParses
              requiredBodyReflects requiredBodySound diagnosticFree
                declarationResult)
        next fallbackAbsent =>
          have fallbackAbsentEq : isKeyword input .fallbackKw = false :=
            Bool.eq_false_iff.mpr fallbackAbsent
          split at result
          next startsType =>
            unfold mapMember at result
            rcases bind_ok_components result with
              ⟨declaration, afterDeclaration, declarationResult, finished⟩
            cases finished
            exact .typeAlias
              (not_contractFieldStartsAt_of_startsContractField_eq_false
                fieldAbsentEq)
              (keywordAbsentAt_of_isKeyword_eq_false .functionKw
                functionAbsentEq)
              (keywordAbsentAt_of_isKeyword_eq_false .constructorKw
                constructorAbsentEq)
              (keywordAbsentAt_of_isKeyword_eq_false .fallbackKw
                fallbackAbsentEq)
              (typeAlias_success_sound diagnosticFree declarationResult)
          next typeAbsent =>
            have typeAbsentEq : isKeyword input .typeKw = false :=
              Bool.eq_false_iff.mpr typeAbsent
            split at result
            next startsEnum =>
              unfold mapMember at result
              rcases bind_ok_components result with
                ⟨declaration, afterDeclaration, declarationResult, finished⟩
              cases finished
              exact .enum
                (not_contractFieldStartsAt_of_startsContractField_eq_false
                  fieldAbsentEq)
                (keywordAbsentAt_of_isKeyword_eq_false .functionKw
                  functionAbsentEq)
                (keywordAbsentAt_of_isKeyword_eq_false .constructorKw
                  constructorAbsentEq)
                (keywordAbsentAt_of_isKeyword_eq_false .fallbackKw
                  fallbackAbsentEq)
                (keywordAbsentAt_of_isKeyword_eq_false .typeKw typeAbsentEq)
                (enumDecl_success_sound none declarationResult)
            next enumAbsent =>
              simp [rejectedContractMember, rejectAt] at result

end ContractInternals
end Solcore.Syntax.Parser
