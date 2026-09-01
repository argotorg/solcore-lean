import Solcore.Syntax.Parser.ContractDeriveAttachmentSoundnessProperties
import Solcore.Syntax.Parser.DeriveAttributeSoundnessProperties
import Solcore.Syntax.Parser.DeriveDiagnosticReflectionProperties
import Solcore.Syntax.Parser.PlainTopItemDiagnosticReflectionProperties
import Solcore.Syntax.Parser.PlainTopItemSoundnessProperties

/-! Parametric diagnostic-free soundness for derive-aware top-item dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Derive attachment cannot erase an incoming diagnostic. -/
theorem attachDeriveAttribute_reflectsDiagnosticFreeOnSuccess
    (derive : DeriveAttribute) (item : TopItem) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (attachDeriveAttribute derive item) := by
  intro input value next result diagnosticFree
  rcases item with ⟨itemSpan, leadingComments, itemValue⟩
  cases itemValue <;>
    simp only [attachDeriveAttribute, emitDiagnostic, modifyState, bind, pure]
      at result
  all_goals rcases result with ⟨rfl, rfl⟩
  case enum => exact diagnosticFree
  all_goals cases diagnosticFree

/-- A diagnostic-free attachment success is possible only for an enum item. -/
private theorem attachDeriveAttribute_success_requiresEnum
    {derive : DeriveAttribute} {item value : TopItem}
    {input next : State} (diagnosticFree : next.diagnosticsRev = [])
    (result : attachDeriveAttribute derive item input = .ok value next) :
    ∃ declaration, item.value = .enum declaration := by
  rcases item with ⟨itemSpan, leadingComments, itemValue⟩
  cases itemValue <;>
    simp only [attachDeriveAttribute, emitDiagnostic, modifyState, bind, pure]
      at result
  all_goals rcases result with ⟨rfl, rfl⟩
  case enum declaration => exact ⟨declaration, rfl⟩
  all_goals cases diagnosticFree

/-- Derive-aware dispatch reflects diagnostic freedom through every stage. -/
theorem topItem_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess topItem := by
  intro input item next result diagnosticFree
  unfold topItem at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact plainTopItem_reflectsDiagnosticFreeOnSuccess expressionReflects
        allowBodyReflects requiredBodyReflects input item next result
          diagnosticFree
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | reject failure rejected => simp [deriveResult] at result
      | invariant error => simp [deriveResult] at result
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases itemResult : plainTopItem afterDerive with
          | reject failure rejected => simp [itemResult] at result
          | invariant error => simp [itemResult] at result
          | ok plainItem afterItem =>
              simp only [itemResult] at result
              have afterItemFree :=
                attachDeriveAttribute_reflectsDiagnosticFreeOnSuccess
                  derive plainItem afterItem item next result diagnosticFree
              have afterDeriveFree :=
                plainTopItem_reflectsDiagnosticFreeOnSuccess expressionReflects
                  allowBodyReflects requiredBodyReflects afterDerive plainItem
                    afterItem itemResult afterItemFree
              exact deriveAttribute_reflectsDiagnosticFreeOnSuccess input
                derive afterDerive deriveResult afterDeriveFree

/-!
Every diagnostic-free top-item success follows exact leading-hash priority.
An attached derive attribute survives only when plain dispatch selected its
enum branch; its exact earlier-selector exclusions and final remainder are
retained.
-/
theorem topItem_success_sound
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
    (result : topItem input = .ok item next) :
    DeclarativeGrammar.TopItemParses expressionParses allowBodyParses
      requiredBodyParses input.declarativeRemainder item
        next.declarativeRemainder := by
  unfold topItem at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact .plain (symbolAbsentAt_of_isSymbol_eq_false .hash hashPresent)
        (plainTopItem_success_sound expressionParses allowBodyParses
          requiredBodyParses expressionReflects expressionSound
          allowBodyReflects allowBodySound requiredBodyReflects
          requiredBodySound diagnosticFree result)
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | reject failure rejected => simp [deriveResult] at result
      | invariant error => simp [deriveResult] at result
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases itemResult : plainTopItem afterDerive with
          | reject failure rejected => simp [itemResult] at result
          | invariant error => simp [itemResult] at result
          | ok plainItem afterItem =>
              simp only [itemResult] at result
              have afterItemFree :=
                attachDeriveAttribute_reflectsDiagnosticFreeOnSuccess
                  derive plainItem afterItem item next result diagnosticFree
              have afterDeriveFree :=
                plainTopItem_reflectsDiagnosticFreeOnSuccess expressionReflects
                  allowBodyReflects requiredBodyReflects afterDerive plainItem
                    afterItem itemResult afterItemFree
              have deriveParsed := deriveAttribute_success_sound
                afterDeriveFree deriveResult
              have attachedEnum :=
                attachDeriveAttribute_success_requiresEnum diagnosticFree
                  result
              have plainParsed := plainTopItem_success_sound expressionParses
                allowBodyParses requiredBodyParses expressionReflects
                expressionSound allowBodyReflects allowBodySound
                requiredBodyReflects requiredBodySound afterItemFree itemResult
              cases plainParsed with
              | importDecl importParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | exportDecl earlierAbsent exportParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | pragmaDecl earlierAbsent pragmaParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | typeAlias earlierAbsent aliasParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | function earlierAbsent functionParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | enum earlierAbsent enumParsed =>
                  simp only [attachDeriveAttribute, pure] at result
                  cases result
                  exact .derivedEnum deriveParsed earlierAbsent
                    (enumParsed.withDerive derive)
              | trait earlierAbsent traitParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | impl earlierAbsent implParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | contract earlierAbsent contractParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction

end Solcore.Syntax.Parser.FileInternals
