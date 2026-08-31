import Solcore.Syntax.Yul

/-! Recursive source-validity contract for canonical inline-Yul expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.YulExpr

/-- Every range recursively retained by an inline-Yul expression is valid. -/
inductive ValidFor (file : SourceFile) : YulExpr → Prop where
  | literal {span : SourceSpan} {literal : YulLiteral}
      (spanValid : span.ValidFor file)
      (literalValid : literal.span.ValidFor file) :
      ValidFor file { span, value := .literal literal }
  | identifier {span : SourceSpan} {name : YulIdentifier}
      (spanValid : span.ValidFor file) (nameValid : name.span.ValidFor file) :
      ValidFor file { span, value := .identifier name }
  | call {span : SourceSpan} {callee : YulIdentifier}
      {arguments : DelimitedList YulExpr}
      (spanValid : span.ValidFor file) (calleeValid : callee.span.ValidFor file)
      (argumentsSpanValid : arguments.span.ValidFor file)
      (argumentsValid : ∀ argument ∈ arguments.elements,
        ValidFor file argument) :
      ValidFor file { span, value := .call callee arguments }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      ValidFor file { span, value := .error }

end Solcore.Syntax.YulExpr
