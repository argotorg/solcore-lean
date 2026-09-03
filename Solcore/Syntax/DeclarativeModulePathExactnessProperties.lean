import Solcore.Syntax.DeclarativeCoreTypeNameExactnessProperties
import Solcore.Syntax.DeclarativeModulePathOutcomeProperties

/-! Exact local and external-package module-path values and rejecting endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem at_conflicts_qualified {input output : Remainder}
    {markerSpan : SourceSpan} {name : Syntax.QualifiedName}
    (marker : TokenAt input.tokens input.endIndex input.cursor {
      span := markerSpan, value := .symbol .at })
    (parsed : QualifiedNameParses input name output) : False := by
  have tokenEq := marker.token_unique parsed.2.2.1
  have kindEq := congrArg (fun token : Token => token.value) tokenEq
  cases kindEq

/-- The selected local/external branch fixes every marker, name, and covering span. -/
theorem ModulePathOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.ModulePath}
    {afterLeft afterRight : Remainder}
    (leftParsed : ModulePathOrdinaryParses input left afterLeft)
    (rightParsed : ModulePathOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | «local» leftName =>
      cases rightParsed with
      | «local» rightName =>
          cases leftName.value_unique rightName
          rfl
      | externalPackage _ rightMarker _ =>
          exact False.elim (at_conflicts_qualified rightMarker leftName)
  | externalPackage leftSpan leftMarker leftName =>
      cases rightParsed with
      | «local» rightName =>
          exact False.elim (at_conflicts_qualified leftMarker rightName)
      | externalPackage rightSpan rightMarker rightName =>
          have spanEq := congrArg (fun token : Token => token.span)
            (leftMarker.token_unique rightMarker)
          subst spanEq
          cases leftName.value_unique rightName
          rfl

/-- An ordinary module path fixes its complete AST and final remainder. -/
theorem ModulePathOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.ModulePath}
    {afterLeft afterRight : Remainder}
    (leftParsed : ModulePathOrdinaryParses input left afterLeft)
    (rightParsed : ModulePathOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Local/external branch priority fixes the exact failing module-path endpoint. -/
theorem ModulePathRejects.output_unique {input left right : Remainder}
    (leftRejected : ModulePathRejects input left)
    (rightRejected : ModulePathRejects input right) : left = right := by
  cases leftRejected with
  | localRejected leftAbsent leftName =>
      cases rightRejected with
      | localRejected _ rightName => exact leftName.output_unique rightName
      | externalRejected _ rightMarker _ =>
          exact False.elim (leftAbsent ⟨_, rightMarker.1⟩)
  | externalRejected _ leftMarker leftName =>
      cases rightRejected with
      | localRejected rightAbsent _ =>
          exact False.elim (rightAbsent ⟨_, leftMarker.1⟩)
      | externalRejected _ rightMarker rightName =>
          have outputEq := leftMarker.output_unique rightMarker
          subst outputEq
          exact leftName.output_unique rightName

/-- Module paths have fully exact successful values and rejecting endpoints. -/
theorem modulePathExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ModulePathOrdinaryParses ModulePathRejects where
  toDeterministicOutcomeSpec := modulePathDeterministicOutcomeSpec
  successValueUnique := ModulePathOrdinaryParses.value_unique
  rejectOutputUnique := ModulePathRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
