import Solcore.Syntax.CoreTermValidity

/-! External consumers for canonical recursive Core source-validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @Expr.ValidFor.mono
example := @Pattern.ValidFor.mono
example := @ForItem.ValidFor.mono
example := @Statement.ValidFor.mono
example := @CoreStatement.ValidForAt
example := @CoreStatement.ValidFor
example := @CoreExpr.ValidFor
example := @CorePattern.ValidFor
example := @CoreStatement.ValidFor.ofStatement
example := @CoreStatement.ValidFor.span_valid

end Tests
