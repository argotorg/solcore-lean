import Solcore.Syntax.Parser.ContractDeclSoundnessProperties
import Solcore.Syntax.Parser.Enum
import Solcore.Syntax.Parser.ExportDeclSoundnessProperties
import Solcore.Syntax.Parser.File
import Solcore.Syntax.Parser.FunctionDeclSoundnessProperties
import Solcore.Syntax.Parser.Impl
import Solcore.Syntax.Parser.ImportDeclSoundnessProperties
import Solcore.Syntax.Parser.PragmaSoundnessProperties
import Solcore.Syntax.Parser.Trait
import Solcore.Syntax.Parser.TypeAlias

/-! Parametric strict soundness for attribute-free top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem mapTopItem_ok_components {alpha : Type}
    {parser : Parser alpha} {wrap : alpha → TopItem}
    {input next : State} {item : TopItem}
    (result : mapTopItem parser wrap input = .ok item next) :
    ∃ value, parser input = .ok value next ∧ item = wrap value := by
  unfold mapTopItem at result
  cases parserResult : parser input with
  | ok value afterValue =>
      simp only [parserResult] at result
      cases result
      exact ⟨value, rfl, rfl⟩
  | reject failure rejected => simp [parserResult] at result
  | invariant error => simp [parserResult] at result

private theorem topItemKindsAbsentAt_nil (input : State) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder [] := by
  intro kind member
  contradiction

private theorem topItemKindsAbsentAt_cons (input : State) (kind : TokenKind)
    (kinds : List TokenKind)
    (headAbsent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor kind)
    (tailAbsent : DeclarativeGrammar.TopItemKindsAbsentAt
      input.declarativeRemainder kinds) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      (kind :: kinds) := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | member
  · simpa [State.declarativeRemainder] using headAbsent
  · exact tailAbsent candidate member

private theorem keywordKindsAbsentAt_cons (input : State)
    (keywordValue : HardKeyword) (kinds : List TokenKind)
    (absent : isKeyword input keywordValue = false)
    (tailAbsent : DeclarativeGrammar.TopItemKindsAbsentAt
      input.declarativeRemainder kinds) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      (.keyword keywordValue :: kinds) :=
  topItemKindsAbsentAt_cons input (.keyword keywordValue) kinds
    (keywordAbsentAt_of_isKeyword_eq_false keywordValue absent) tailAbsent

private theorem contextualKindsAbsentAt_cons (input : State)
    (contextualValue : ContextualKeyword) (kinds : List TokenKind)
    (absent : isContextual input contextualValue = false)
    (tailAbsent : DeclarativeGrammar.TopItemKindsAbsentAt
      input.declarativeRemainder kinds) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      (.identifier contextualValue.spelling :: kinds) :=
  topItemKindsAbsentAt_cons input
    (.identifier contextualValue.spelling) kinds
      (contextualAbsentAt_of_isContextual_eq_false contextualValue absent)
      tailAbsent

private theorem precedingThroughFunctionAbsent (input : State)
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder [
      .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
      .keyword .typeKw, .keyword .functionKw] :=
  keywordKindsAbsentAt_cons input .importKw _ importAbsent
    (keywordKindsAbsentAt_cons input .exportKw _ exportAbsent
      (keywordKindsAbsentAt_cons input .pragmaKw _ pragmaAbsent
        (keywordKindsAbsentAt_cons input .typeKw _ typeAbsent
          (keywordKindsAbsentAt_cons input .functionKw _ functionAbsent
            (topItemKindsAbsentAt_nil input)))))

private theorem precedingThroughEnumAbsent (input : State)
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder [
      .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
      .keyword .typeKw, .keyword .functionKw,
      .identifier ContextualKeyword.enum.spelling] :=
  keywordKindsAbsentAt_cons input .importKw _ importAbsent
    (keywordKindsAbsentAt_cons input .exportKw _ exportAbsent
      (keywordKindsAbsentAt_cons input .pragmaKw _ pragmaAbsent
        (keywordKindsAbsentAt_cons input .typeKw _ typeAbsent
          (keywordKindsAbsentAt_cons input .functionKw _ functionAbsent
            (contextualKindsAbsentAt_cons input .enum _ enumAbsent
              (topItemKindsAbsentAt_nil input))))))

private theorem precedingThroughTraitAbsent (input : State)
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false)
    (traitAbsent : isContextual input .trait = false) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder [
      .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
      .keyword .typeKw, .keyword .functionKw,
      .identifier ContextualKeyword.enum.spelling,
      .identifier ContextualKeyword.trait.spelling] :=
  keywordKindsAbsentAt_cons input .importKw _ importAbsent
    (keywordKindsAbsentAt_cons input .exportKw _ exportAbsent
      (keywordKindsAbsentAt_cons input .pragmaKw _ pragmaAbsent
        (keywordKindsAbsentAt_cons input .typeKw _ typeAbsent
          (keywordKindsAbsentAt_cons input .functionKw _ functionAbsent
            (contextualKindsAbsentAt_cons input .enum _ enumAbsent
              (contextualKindsAbsentAt_cons input .trait _ traitAbsent
                (topItemKindsAbsentAt_nil input)))))))

private theorem precedingThroughImplDefaultAbsent (input : State)
    (importAbsent : isKeyword input .importKw = false)
    (exportAbsent : isKeyword input .exportKw = false)
    (pragmaAbsent : isKeyword input .pragmaKw = false)
    (typeAbsent : isKeyword input .typeKw = false)
    (functionAbsent : isKeyword input .functionKw = false)
    (enumAbsent : isContextual input .enum = false)
    (traitAbsent : isContextual input .trait = false)
    (implAbsent : isContextual input .impl = false)
    (defaultAbsent : isKeyword input .defaultKw = false) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder [
      .keyword .importKw, .keyword .exportKw, .keyword .pragmaKw,
      .keyword .typeKw, .keyword .functionKw,
      .identifier ContextualKeyword.enum.spelling,
      .identifier ContextualKeyword.trait.spelling,
      .identifier ContextualKeyword.impl.spelling, .keyword .defaultKw] :=
  keywordKindsAbsentAt_cons input .importKw _ importAbsent
    (keywordKindsAbsentAt_cons input .exportKw _ exportAbsent
      (keywordKindsAbsentAt_cons input .pragmaKw _ pragmaAbsent
        (keywordKindsAbsentAt_cons input .typeKw _ typeAbsent
          (keywordKindsAbsentAt_cons input .functionKw _ functionAbsent
            (contextualKindsAbsentAt_cons input .enum _ enumAbsent
              (contextualKindsAbsentAt_cons input .trait _ traitAbsent
                (contextualKindsAbsentAt_cons input .impl _ implAbsent
                  (keywordKindsAbsentAt_cons input .defaultKw _ defaultAbsent
                    (topItemKindsAbsentAt_nil input)))))))))

/-- Diagnostic-free plain dispatch follows the exact executable priority. -/
theorem plainTopItem_success_sound
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      DeclarativeGrammar.Remainder → Block →
        DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
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
    {input next : State} {item : TopItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : plainTopItem input = .ok item next) :
    DeclarativeGrammar.PlainTopItemParses expressionParses allowBodyParses
      requiredBodyParses input.declarativeRemainder item
        next.declarativeRemainder := by
  unfold plainTopItem at result
  split at result
  next startsImport =>
    rcases mapTopItem_ok_components result with
      ⟨declaration, declarationResult, rfl⟩
    exact .importDecl (importDecl_success_sound diagnosticFree
      declarationResult)
  next importAbsent =>
    have importAbsentEq := Bool.eq_false_iff.mpr importAbsent
    split at result
    next startsExport =>
      rcases mapTopItem_ok_components result with
        ⟨declaration, declarationResult, rfl⟩
      exact .exportDecl
        (keywordKindsAbsentAt_cons input .importKw _ importAbsentEq
          (topItemKindsAbsentAt_nil input))
        (exportDecl_success_sound declarationResult)
    next exportAbsent =>
      have exportAbsentEq := Bool.eq_false_iff.mpr exportAbsent
      split at result
      next startsPragma =>
        rcases mapTopItem_ok_components result with
          ⟨declaration, declarationResult, rfl⟩
        exact .pragmaDecl
          (keywordKindsAbsentAt_cons input .importKw _ importAbsentEq
            (keywordKindsAbsentAt_cons input .exportKw _ exportAbsentEq
              (topItemKindsAbsentAt_nil input)))
          (pragmaDecl_success_sound declarationResult)
      next pragmaAbsent =>
        have pragmaAbsentEq := Bool.eq_false_iff.mpr pragmaAbsent
        split at result
        next startsType =>
          rcases mapTopItem_ok_components result with
            ⟨declaration, declarationResult, rfl⟩
          exact .typeAlias
            (keywordKindsAbsentAt_cons input .importKw _ importAbsentEq
              (keywordKindsAbsentAt_cons input .exportKw _ exportAbsentEq
                (keywordKindsAbsentAt_cons input .pragmaKw _ pragmaAbsentEq
                  (topItemKindsAbsentAt_nil input))))
            (typeAlias_success_sound diagnosticFree declarationResult)
        next typeAbsent =>
          have typeAbsentEq := Bool.eq_false_iff.mpr typeAbsent
          split at result
          next startsFunction =>
            rcases mapTopItem_ok_components result with
              ⟨declaration, declarationResult, rfl⟩
            exact .function
              (keywordKindsAbsentAt_cons input .importKw _ importAbsentEq
                (keywordKindsAbsentAt_cons input .exportKw _ exportAbsentEq
                  (keywordKindsAbsentAt_cons input .pragmaKw _ pragmaAbsentEq
                    (keywordKindsAbsentAt_cons input .typeKw _ typeAbsentEq
                      (topItemKindsAbsentAt_nil input)))))
              (functionDecl_success_sound .module allowBodyParses
                allowBodyReflects allowBodySound diagnosticFree
                  declarationResult)
          next functionAbsent =>
            have functionAbsentEq := Bool.eq_false_iff.mpr functionAbsent
            have throughFunction := precedingThroughFunctionAbsent input
              importAbsentEq exportAbsentEq pragmaAbsentEq typeAbsentEq
                functionAbsentEq
            split at result
            next startsEnum =>
              rcases mapTopItem_ok_components result with
                ⟨declaration, declarationResult, rfl⟩
              exact .enum throughFunction
                (enumDecl_success_sound none declarationResult)
            next enumAbsent =>
              have enumAbsentEq := Bool.eq_false_iff.mpr enumAbsent
              split at result
              next startsTrait =>
                rcases mapTopItem_ok_components result with
                  ⟨declaration, declarationResult, rfl⟩
                exact .trait
                  (precedingThroughEnumAbsent input importAbsentEq
                    exportAbsentEq pragmaAbsentEq typeAbsentEq functionAbsentEq
                      enumAbsentEq)
                  (traitDecl_success_sound diagnosticFree declarationResult)
              next traitAbsent =>
                have traitAbsentEq := Bool.eq_false_iff.mpr traitAbsent
                split at result
                next startsImpl =>
                  rcases mapTopItem_ok_components result with
                    ⟨declaration, declarationResult, rfl⟩
                  exact .impl
                    (precedingThroughTraitAbsent input importAbsentEq
                      exportAbsentEq pragmaAbsentEq typeAbsentEq
                        functionAbsentEq enumAbsentEq traitAbsentEq)
                    (implDecl_success_sound allowBodyParses allowBodyReflects
                      allowBodySound diagnosticFree declarationResult)
                next implAbsent =>
                  have implChoiceAbsent := Bool.eq_false_iff.mpr implAbsent
                  have implParts := Bool.or_eq_false_iff.mp implChoiceAbsent
                  split at result
                  next startsContract =>
                    rcases mapTopItem_ok_components result with
                      ⟨declaration, declarationResult, rfl⟩
                    exact .contract
                      (precedingThroughImplDefaultAbsent input importAbsentEq
                        exportAbsentEq pragmaAbsentEq typeAbsentEq
                          functionAbsentEq enumAbsentEq traitAbsentEq
                          implParts.1 implParts.2)
                      (ContractInternals.contractDecl_success_sound
                        expressionParses allowBodyParses requiredBodyParses
                        expressionReflects expressionSound allowBodyReflects
                        allowBodySound requiredBodyReflects requiredBodySound
                        diagnosticFree declarationResult)
                  next contractAbsent =>
                    simp [rejectAt] at result

end Solcore.Syntax.Parser.FileInternals
