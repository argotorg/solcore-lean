import Solcore.SourceSemantics.StaticValidation

/-! Focused executable tests for source-level type-formation validation. -/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsStaticValidation

open Frontend
open SourceSemantics
open TypeSystem

private def emptySignatures : ProgramSignatures := {
  functions := []
  implRules := []
  traits := []
  implementations := []
  dataTypes := []
  contracts := []
}

private def emptyContext : Context :=
  Context.ofSignatures emptySignatures

private def flexible : TypeVarId := ⟨0⟩

/-- Explicitly opened flexible variables are accepted. -/
example :
    validateTypeWellScoped emptyContext [flexible] (.variable flexible) =
      .ok () := by
  rfl

/-- Residual admission accepts a retained open occurrence type. -/
example :
    validateTypeAdmissible emptyContext.withResidualTypeVariables
        (.variable flexible) = .ok () := by
  rfl

private def testModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"source_semantics_static_validation", by decide⟩], by decide⟩⟩

private def contractOwner : Resolved.DeclarationId :=
  ⟨testModule, 0⟩

private def unknownOwner : Resolved.DeclarationId :=
  ⟨testModule, 1⟩

private def sourceId : Syntax.SourceId := {
  origin := .main
  path := "source_semantics_static_validation.sol"
}

private def sourceSpan : Syntax.SourceSpan := {
  source := sourceId
  startByte := 0
  endByte := 0
}

private def contractSyntax : Syntax.ContractDecl := {
  span := sourceSpan
  value := {
    name := ⟨sourceSpan, "Box"⟩
    genericParameters := some
      ⟨sourceSpan, ⟨⟨sourceSpan, "T"⟩, []⟩⟩
    bodySpan := sourceSpan
    members := []
  }
}

private def contractSignature : ProgramContractSignature := {
  id := contractOwner
  name := "Box"
  parameters := [{ owner := contractOwner, index := 0 }]
  source := contractSyntax
}

private def nominalSignatures : ProgramSignatures := {
  functions := []
  implRules := []
  traits := []
  implementations := []
  dataTypes := []
  contracts := [contractSignature]
}

private def nominalContext : Context :=
  Context.ofSignatures nominalSignatures

/-- A cataloged nominal at its declared arity is accepted. -/
example :
    validateTypeWellScoped nominalContext []
        (Ty.nominal contractOwner [.word]) = .ok () := by
  rfl

/-- A cataloged nominal at the wrong arity is rejected precisely. -/
example :
    validateTypeWellScoped nominalContext [] (Ty.nominal contractOwner []) =
      .error (.nominalArityMismatch contractOwner 1 0) := by
  rfl

/-- A declaration absent from both nominal catalogs is rejected. -/
example :
    validateTypeWellScoped nominalContext [] (Ty.nominal unknownOwner []) =
      .error (.unknownNominal unknownOwner) := by
  rfl

private def duplicateScheme : Scheme := {
  quantified := [flexible, flexible]
  body := .variable flexible
}

/-- Duplicate quantified variables are rejected before body validation. -/
example :
    validateSchemeWellFormed emptyContext duplicateScheme =
      .error .duplicateSchemeVariables := by
  rfl

private def underGeneralizedScheme : Scheme := {
  quantified := []
  body := .variable flexible
}

/-- Exact generalization rejects a scheme that omits a generalizable variable. -/
example :
    validateSchemeGeneralizes emptyContext underGeneralizedScheme =
      .error .schemeGeneralizationMismatch := by
  rfl

private def generalizedScheme : Scheme := {
  quantified := [flexible]
  body := .variable flexible
}

/-- Exact generalization accepts the stable free-variable order. -/
example :
    validateSchemeGeneralizes emptyContext generalizedScheme = .ok () := by
  rfl

end Solcore.Test.SourceSemanticsStaticValidation
