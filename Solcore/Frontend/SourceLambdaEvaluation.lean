import Solcore.Frontend.RuntimeValue
import Solcore.Resolved.FreshIdentity

/-!
Opt-in original source closure construction and unary call sequencing over mixed values.
Unmarked syntax does not establish canonical runtime staging: annotation meanings are
never inspected. These success rules do not close the supplied callbacks recursively
or classify failures, divergence, costs or effects of unsuccessful computations.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Unmarked unary syntax only; annotation meaning and canonical staging are not checked. -/
inductive SourceUnaryLambdaShape : Syntax.Expr → Syntax.Identifier → Syntax.Block → Prop where
  | inferred {span keyword parametersSpan parameterSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {body : Syntax.Block} :
      SourceUnaryLambdaShape
        ⟨span, .lambda keyword ⟨parametersSpan, [⟨parameterSpan, .inferred name⟩]⟩ annotation body⟩
        name body
  | typed {span keyword parametersSpan parameterSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {parameterAnnotation : Syntax.TypeExpr}
      {annotation : Option Syntax.TypeExpr} {body : Syntax.Block} :
      SourceUnaryLambdaShape
        ⟨span, .lambda keyword
          ⟨parametersSpan, [⟨parameterSpan, .typed none name parameterAnnotation⟩]⟩ annotation body⟩
        name body

/-- Decode only the original direct unary shape, retaining the name/body verbatim.
Unsupported syntax is absent from this profile, not classified as a runtime fault. -/
def sourceUnaryLambdaShape? (source : Syntax.Expr) : Option (Syntax.Identifier × Syntax.Block) :=
  match source.value with
  | .lambda _ ⟨_, [parameter]⟩ _ body =>
      match parameter.value with
      | .inferred name => some (name, body)
      | .typed none name _ => some (name, body)
      | _ => none
  | _ => none

/-- Creation captures every original row without running the body or taking a heap
snapshot. Calls sequence actual stores through caller callee/argument evaluation and
then the saved source body. Fresh IDs depend on saved name rows only. -/
inductive SourceLambdaEvaluates
    (ChildEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
      RuntimeValue → List RuntimeValue → Prop)
    (BodyEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Block →
      RuntimeValue → List RuntimeValue → Prop)
    (owner : Resolved.DeclarationId) (names : List (String × Resolved.LocalId))
    (captured : List (Resolved.LocalId × RuntimeValue)) :
    List RuntimeValue → Syntax.Expr → RuntimeValue → List RuntimeValue → Prop where
  | creation {store : List RuntimeValue} {source : Syntax.Expr}
      {name : Syntax.Identifier} {body : Syntax.Block}
      (shape : SourceUnaryLambdaShape source name body) :
      SourceLambdaEvaluates ChildEval BodyEval owner names captured store source
        (.sourceClosure source owner names captured) store
  | call {initialStore calleeStore argumentStore finalStore : List RuntimeValue}
      {span argumentsSpan : Syntax.SourceSpan} {callee argument source : Syntax.Expr}
      {savedOwner : Resolved.DeclarationId} {savedNames : List (String × Resolved.LocalId)}
      {savedCaptured : List (Resolved.LocalId × RuntimeValue)}
      {name : Syntax.Identifier} {body : Syntax.Block} {argumentValue result : RuntimeValue}
      (shape : SourceUnaryLambdaShape source name body)
      (calleeEvaluation : ChildEval owner names captured initialStore callee
        (.sourceClosure source savedOwner savedNames savedCaptured) calleeStore)
      (argumentEvaluation : ChildEval owner names captured calleeStore argument argumentValue argumentStore)
      (bodyEvaluation : BodyEval savedOwner
        ((name.value, Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)) :: savedNames)
        ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd), argumentValue) :: savedCaptured)
        argumentStore body result finalStore) :
      SourceLambdaEvaluates ChildEval BodyEval owner names captured initialStore
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore

end Solcore.Frontend
