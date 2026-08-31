import Solcore.Syntax.Parser.TypeAliasProperties
import Solcore.Syntax.Parser.EnumProperties

/-! External consumers for type and enum declaration validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @TypeAliasDecl.ValidFor
example := @TypeAliasInternals.finishRecoveredType_validFor
example := @TypeAliasInternals.recoverTypeAliasValueAux_validFor
example := @TypeAliasInternals.parseAliasValue_validFor
example := @TypeAliasInternals.parseAliasValue_preservesTokenWindow
example := @TypeAliasInternals.parseAliasValue_preservesTokensOnSuccess
example := @TypeAliasInternals.parseAliasValue_cursorMonotoneOnSuccess
example := @parseTypeAliasParameters_validFor
example := @typeAlias_validFor
example := @typeAlias_preservesTokenWindow
example := @typeAlias_preservesTokensOnSuccess
example := @typeAlias_cursorMonotoneOnSuccess
example := @typeAlias_startsAtCurrentTokenOnSuccess
example := @EnumConstructor.ValidFor
example := @EnumDecl.ValidFor
example := @EnumInternals.enumConstructorFields_validFor
example := @EnumInternals.enumConstructorFields_preservesTokenWindow
example := @EnumInternals.enumConstructorFields_cursorMonotoneOnSuccess
example := @EnumInternals.enumConstructor_validFor
example := @EnumInternals.enumConstructor_preservesTokenWindow
example := @EnumInternals.enumConstructor_preservesTokensOnSuccess
example := @EnumInternals.enumConstructor_cursorMonotoneOnSuccess
example := @EnumInternals.enumConstructor_startsAtCurrentTokenOnSuccess
example := @EnumInternals.closeEnumBody_validFor
example := @EnumInternals.closeEnumBody_preservesTokenWindow
example := @EnumInternals.closeEnumBody_cursorMonotoneOnSuccess
example := @EnumInternals.closeEnumBody_preservesOpeningStartOnSuccess
example := @EnumInternals.enumConstructors_validFor
example := @EnumInternals.enumConstructors_preservesTokenWindow
example := @EnumInternals.enumConstructors_cursorMonotoneOnSuccess
example := @EnumInternals.enumConstructors_preservesOpeningStartOnSuccess
example := @EnumInternals.enumBody_validFor
example := @EnumInternals.enumBody_preservesTokenWindow
example := @EnumInternals.enumBody_preservesTokensOnSuccess
example := @EnumInternals.enumBody_cursorMonotoneOnSuccess
example := @EnumInternals.enumBody_startsAtCurrentTokenOnSuccess

example (file : SourceFile) (declaration : TypeAliasDecl)
    (valid : TypeAliasDecl.ValidFor file declaration) :
    declaration.span.ValidFor file ∧
      declaration.value.name.span.ValidFor file ∧
      TypeExpr.ValidFor file declaration.value.value :=
  ⟨valid.1, valid.2.1, valid.2.2.2.2⟩

example (file : SourceFile) (declaration : EnumDecl)
    (valid : EnumDecl.ValidFor file declaration)
    (constructor : EnumConstructor)
    (member : constructor ∈ declaration.value.constructors) :
    declaration.value.bodySpan.ValidFor file ∧
      EnumConstructor.ValidFor file constructor :=
  ⟨valid.2.2.2.2.2.1, valid.2.2.2.2.2.2 constructor member⟩

end Tests
