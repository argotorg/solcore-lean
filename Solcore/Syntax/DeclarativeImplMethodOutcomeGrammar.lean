import Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeGrammar

/-!
Parser-independent ordinary success and exact rejection for one implementation
method wrapper.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An ordinary implementation method is exactly a module-position function
declaration wrapped with empty parser-time leading comments. -/
inductive ImplMethodOrdinaryParses :
    Remainder → Syntax.ImplMethod → Remainder → Prop where
  | parsed {input output : Remainder}
      {declaration : Syntax.FunctionDecl}
      (declarationParsed : FunctionDeclOrdinaryParses input declaration
        output) :
      ImplMethodOrdinaryParses input {
        span := declaration.span
        value := { leadingComments := [], declaration }
      } output

/-- Implementation-method rejection is exactly its nested function-declaration
rejection; the pure wrapper adds no rejecting stage. -/
inductive ImplMethodRejects : Remainder → Remainder → Prop where
  | declarationRejected {input rejected : Remainder}
      (declarationRejected : FunctionDeclRejects input rejected) :
      ImplMethodRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
