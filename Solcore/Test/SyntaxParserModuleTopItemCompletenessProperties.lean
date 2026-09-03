import Solcore.Syntax.Parser.ModuleDeclarationCompletenessProperties
import Solcore.Syntax.Parser.TopItemCompletenessProperties

/-! External consumers of both directions of module and top-item completeness.
The pragma examples intentionally require no state-validity hypothesis. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserModuleTopItemCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example {input : State} (inputValid : input.ValidFor)
    {value : ImportDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ImportDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, importDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (importDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : ImportDecl} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : importDecl input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ImportDeclOrdinaryParses
      input.declarativeRemainder value remainder :=
  (importDecl_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ImportDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, importDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (importDecl_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : importDecl input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ImportDeclRejects input.declarativeRemainder rejected :=
  (importDecl_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : ExportDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExportDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, exportDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (exportDecl_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : ExportDecl} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : exportDecl input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.ExportDeclOrdinaryParses
      input.declarativeRemainder value remainder :=
  (exportDecl_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ExportDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, exportDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (exportDecl_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : exportDecl input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.ExportDeclRejects input.declarativeRemainder rejected :=
  (exportDecl_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example {input : State}
    {value : PragmaDecl} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.PragmaDeclOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, pragmaDecl input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (pragmaDecl_ordinary_success_iff).mp parsed

example {input : State}
    {value : PragmaDecl} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : pragmaDecl input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.PragmaDeclOrdinaryParses
      input.declarativeRemainder value remainder :=
  (pragmaDecl_ordinary_success_iff).mpr ⟨output, result, remainderEq⟩

example {input : State}
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.PragmaDeclRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, pragmaDecl input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (pragmaDecl_ordinary_reject_iff).mp rejection

example {input : State}
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : pragmaDecl input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.PragmaDeclRejects input.declarativeRemainder rejected :=
  (pragmaDecl_ordinary_reject_iff).mpr ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : TopItem} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.PlainTopItemOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, plainTopItem input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (plainTopItem_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : TopItem} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : plainTopItem input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.PlainTopItemOrdinaryParses
      input.declarativeRemainder value remainder :=
  (plainTopItem_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.PlainTopItemRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, plainTopItem input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (plainTopItem_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : plainTopItem input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.PlainTopItemRejects input.declarativeRemainder rejected :=
  (plainTopItem_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {value : TopItem} {remainder : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.TopItemOrdinaryParses
      input.declarativeRemainder value remainder) :
    ∃ output, topItem input = .ok value output ∧
      output.declarativeRemainder = remainder :=
  (topItem_ordinary_success_iff inputValid).mp parsed

example {input : State} (inputValid : input.ValidFor)
    {value : TopItem} {remainder : DeclarativeGrammar.Remainder}
    {output : State} (result : topItem input = .ok value output)
    (remainderEq : output.declarativeRemainder = remainder) :
    DeclarativeGrammar.TopItemOrdinaryParses
      input.declarativeRemainder value remainder :=
  (topItem_ordinary_success_iff inputValid).mpr ⟨output, result, remainderEq⟩

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.TopItemRejects
      input.declarativeRemainder rejected) :
    ∃ failure output, topItem input = .reject failure output ∧
      output.declarativeRemainder = rejected :=
  (topItem_ordinary_reject_iff inputValid).mp rejection

example {input : State} (inputValid : input.ValidFor)
    {rejected : DeclarativeGrammar.Remainder} {failure : Failure} {output : State}
    (result : topItem input = .reject failure output)
    (remainderEq : output.declarativeRemainder = rejected) :
    DeclarativeGrammar.TopItemRejects input.declarativeRemainder rejected :=
  (topItem_ordinary_reject_iff inputValid).mpr ⟨failure, output, result, remainderEq⟩

end Solcore.Test.SyntaxParserModuleTopItemCompletenessProperties
