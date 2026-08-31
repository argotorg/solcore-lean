import Solcore.Syntax.ContractDeclarationValidity
import Solcore.Syntax.Parser.ContractEntryProperties

/-! External consumers for canonical contract declaration validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @ContractField.ValidFor
example := @ConstructorDecl.ValidFor
example := @FallbackDecl.ValidFor
example := @ContractMember.ValidFor
example := @ContractDecl.ValidFor

example := @namedParameter_preservesTokenWindow
example := @namedParameter_preservesTokensOnSuccess
example := @namedParameter_validFor
example := @FunctionParameterInternals.ordinaryNamedParameter_validFor
example := @FunctionParameterInternals.comptimeNamedParameter_validFor
example := @FunctionParameterInternals.namedParameterCore_validFor
example := @FunctionParameterInternals.finishRecoveredParameter_validFor
example := @FunctionParameterInternals.recoverParameterAux_validFor
example := @FunctionParameterInternals.recoverParameter_validFor
example := @FunctionParameterInternals.namedParameterTail_validFor
example := @ContractEntryInternals.entryParameters_validFor_of_namedParameter
example := @ContractEntryInternals.entryParameters_validFor
example := @ContractEntryInternals.entryParameters_preservesTokenWindow
example := @ContractEntryInternals.entryParameters_preservesTokensOnSuccess
example :=
  @ContractEntryInternals.entryParameters_cursorMonotoneOnSuccess
example :=
  @ContractEntryInternals.entryParameters_startsAtCurrentTokenOnSuccess
example := @ContractEntryInternals.optionalModifier_validFor
example := @ContractEntryInternals.optionalModifier_preservesTokenWindow
example := @ContractEntryInternals.optionalModifier_preservesTokensOnSuccess
example :=
  @ContractEntryInternals.optionalModifier_cursorMonotoneOnSuccess
example :=
  @ContractEntryInternals.optionalModifier_some_startsAtCurrentTokenOnSuccess
example := @ContractEntryInternals.implicitPublicModifiers_validFor
example :=
  @ContractEntryInternals.implicitPublicModifiers_preservesTokenWindow
example :=
  @ContractEntryInternals.implicitPublicModifiers_preservesTokensOnSuccess
example :=
  @ContractEntryInternals.implicitPublicModifiers_cursorMonotoneOnSuccess
example := @constructorDecl_preservesTokenWindow
example := @constructorDecl_preservesTokensOnSuccess
example := @constructorDecl_cursorMonotoneOnSuccess
example := @constructorDecl_startsAtCurrentTokenOnSuccess
example := @ContractEntryInternals.requiredBlock_startsAtCurrentTokenOnSuccess
example := @constructorDecl_span_validOnSuccess
example := @constructorDecl_validFor_of_span
example := @constructorDecl_validFor
example := @fallbackDecl_preservesTokenWindow
example := @fallbackDecl_preservesTokensOnSuccess
example := @fallbackDecl_cursorMonotoneOnSuccess
example := @fallbackDecl_startsAtCurrentTokenOnSuccess

example (statementValid : SourceFile → Statement → Prop)
    (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (declaration : ContractDecl)
    (valid : ContractDecl.ValidFor statementValid expressionValid
      file declaration)
    (member : ContractMember)
    (retained : member ∈ declaration.value.members) :
    declaration.value.bodySpan.ValidFor file ∧
      ContractMember.ValidFor statementValid expressionValid file member :=
  ⟨valid.2.2.2.2.1, valid.2.2.2.2.2 member retained⟩

end Tests
