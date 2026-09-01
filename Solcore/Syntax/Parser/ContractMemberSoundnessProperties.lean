import Solcore.Syntax.Parser.ContractDeriveAttachmentSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberCoreSoundnessProperties
import Solcore.Syntax.Parser.DeriveAttributeSoundnessProperties
import Solcore.Syntax.Parser.DeriveDiagnosticReflectionProperties

/-! Parametric diagnostic-free soundness for attribute-aware contract members. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Derive attachment either stays pure for an enum or emits a diagnostic, so
it can never erase an incoming diagnostic. -/
theorem attachContractDerive_reflectsDiagnosticFreeOnSuccess
    (derive : DeriveAttribute) (member : ContractMember) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (attachContractDerive derive member) := by
  intro input value next result diagnosticFree
  rcases member with ⟨memberSpan, leadingComments, memberValue⟩
  cases memberValue <;>
    simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
      at result
  all_goals rcases result with ⟨rfl, rfl⟩
  case enum => exact diagnosticFree
  all_goals cases diagnosticFree

/-- A diagnostic-free attachment success is possible only for an enum member. -/
private theorem attachContractDerive_success_requiresEnum
    {derive : DeriveAttribute} {member value : ContractMember}
    {input next : State} (diagnosticFree : next.diagnosticsRev = [])
    (result : attachContractDerive derive member input = .ok value next) :
    ∃ declaration, member.value = .enum declaration := by
  rcases member with ⟨memberSpan, leadingComments, memberValue⟩
  cases memberValue <;>
    simp only [attachContractDerive, emitDiagnostic, modifyState, bind, pure]
      at result
  all_goals rcases result with ⟨rfl, rfl⟩
  case enum declaration => exact ⟨declaration, rfl⟩
  all_goals cases diagnosticFree

/-- Attribute-aware dispatch reflects diagnostic freedom through the derive
attribute, core member, and attachment stages. -/
theorem contractMemberWithAttribute_reflectsDiagnosticFreeOnSuccess
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess contractMemberWithAttribute := by
  intro input member next result diagnosticFree
  unfold contractMemberWithAttribute at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact contractMemberCore_reflectsDiagnosticFreeOnSuccess
        expressionReflects allowBodyReflects requiredBodyReflects input member
          next result diagnosticFree
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | reject failure rejected => simp [deriveResult] at result
      | invariant error => simp [deriveResult] at result
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases memberResult : contractMemberCore afterDerive with
          | reject failure rejected => simp [memberResult] at result
          | invariant error => simp [memberResult] at result
          | ok coreMember afterMember =>
              simp only [memberResult] at result
              have afterMemberFree :=
                attachContractDerive_reflectsDiagnosticFreeOnSuccess
                  derive coreMember afterMember member next result
                    diagnosticFree
              have afterDeriveFree :=
                contractMemberCore_reflectsDiagnosticFreeOnSuccess
                  expressionReflects allowBodyReflects requiredBodyReflects
                    afterDerive coreMember afterMember memberResult
                      afterMemberFree
              exact deriveAttribute_reflectsDiagnosticFreeOnSuccess input
                derive afterDerive deriveResult afterDeriveFree

/-!
Every diagnostic-free success follows exact hash priority.  A leading derive
attribute can survive attachment only when core dispatch selected its enum
branch; the enum's earlier field/function/constructor/fallback/type exclusions
are retained unchanged.
-/
theorem contractMemberWithAttribute_success_sound
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
    {input next : State} {member : ContractMember}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractMemberWithAttribute input = .ok member next) :
    DeclarativeGrammar.ContractMemberParses expressionParses allowBodyParses
      requiredBodyParses input.declarativeRemainder member
        next.declarativeRemainder := by
  unfold contractMemberWithAttribute at result
  cases hashPresent : isSymbol input .hash with
  | false =>
      simp only [hashPresent, Bool.false_eq_true, if_false] at result
      exact .plain (symbolAbsentAt_of_isSymbol_eq_false .hash hashPresent)
        (contractMemberCore_success_sound expressionParses allowBodyParses
          requiredBodyParses expressionSound allowBodyReflects allowBodySound
          requiredBodyReflects requiredBodySound diagnosticFree result)
  | true =>
      simp only [hashPresent, if_true] at result
      cases deriveResult : deriveAttribute input with
      | reject failure rejected => simp [deriveResult] at result
      | invariant error => simp [deriveResult] at result
      | ok derive afterDerive =>
          simp only [deriveResult] at result
          cases memberResult : contractMemberCore afterDerive with
          | reject failure rejected => simp [memberResult] at result
          | invariant error => simp [memberResult] at result
          | ok coreMember afterMember =>
              simp only [memberResult] at result
              have afterMemberFree :=
                attachContractDerive_reflectsDiagnosticFreeOnSuccess
                  derive coreMember afterMember member next result
                    diagnosticFree
              have afterDeriveFree :=
                contractMemberCore_reflectsDiagnosticFreeOnSuccess
                  expressionReflects allowBodyReflects requiredBodyReflects
                    afterDerive coreMember afterMember memberResult
                      afterMemberFree
              have deriveParsed := deriveAttribute_success_sound
                afterDeriveFree deriveResult
              have attachedEnum :=
                attachContractDerive_success_requiresEnum diagnosticFree
                  result
              have coreParsed := contractMemberCore_success_sound
                expressionParses allowBodyParses requiredBodyParses
                expressionSound allowBodyReflects allowBodySound
                requiredBodyReflects requiredBodySound afterMemberFree
                memberResult
              cases coreParsed with
              | field startsField fieldParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | function fieldAbsent functionParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | constructor fieldAbsent functionAbsent constructorParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | fallback fieldAbsent functionAbsent constructorAbsent
                  fallbackParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | typeAlias fieldAbsent functionAbsent constructorAbsent
                  fallbackAbsent aliasParsed =>
                  rcases attachedEnum with ⟨declaration, impossible⟩
                  contradiction
              | enum fieldAbsent functionAbsent constructorAbsent
                  fallbackAbsent typeAbsent enumParsed =>
                  simp only [attachContractDerive, pure] at result
                  cases result
                  exact .derivedEnum deriveParsed fieldAbsent functionAbsent
                    constructorAbsent fallbackAbsent typeAbsent
                    (enumParsed.withDerive derive)

end Solcore.Syntax.Parser.ContractInternals
