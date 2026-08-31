import Solcore.Syntax.FileValidity

/-! External consumers for canonical file-validity contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @TopItem.ValidFor
example := @TopItem.ValidFor.importDecl
example := @TopItem.ValidFor.exportDecl
example := @TopItem.ValidFor.contract
example := @TopItem.ValidFor.error
example := @TopItem.ValidFor.span_valid
example := @TopItem.ValidFor.comments_valid
example := @ParsedFile.ValidFor

example {statementValid : SourceFile → Statement → Prop}
    {expressionValid : SourceFile → Expr → Prop}
    {file : SourceFile} {parsed : ParsedFile}
    (valid : ParsedFile.ValidFor statementValid expressionValid file parsed) :
    parsed.source = file.id := valid.1

end Tests
