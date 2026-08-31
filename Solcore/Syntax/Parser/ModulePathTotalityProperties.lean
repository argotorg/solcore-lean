import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.ModulePath
import Solcore.Syntax.Parser.QualifiedNameTotalityProperties

/-! Totality laws for module-path parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Module paths always produce an ordinary success or rejection reply. -/
theorem modulePath_ordinary (context : ParseContext) :
    Parser.Ordinary (modulePath context) := by
  intro input
  unfold modulePath
  split
  · cases markerResult : symbol .at context input with
    | invariant error =>
        exact False.elim
          (symbol_ne_invariant .at context input error markerResult)
    | reject failure rejected =>
        exact Or.inr ⟨failure, rejected, rfl⟩
    | ok marker afterMarker =>
        dsimp only
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error =>
            exact False.elim
              (qualifiedName_ne_invariant context .topLevel afterMarker error
                nameResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok name next =>
            exact Or.inl ⟨_, next, rfl⟩
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error =>
        exact False.elim
          (qualifiedName_ne_invariant context .topLevel input error nameResult)
    | reject failure rejected =>
        exact Or.inr ⟨failure, rejected, rfl⟩
    | ok name next =>
        exact Or.inl ⟨_, next, rfl⟩

/-- Module paths cannot expose an internal parser invariant. -/
theorem modulePath_ne_invariant (context : ParseContext) (input : State)
    (error : ParserInvariantError) :
    modulePath context input ≠ .invariant error :=
  (modulePath_ordinary context).ne_invariant input error

/-- Module paths are invariant-free on the canonical valid-input domain. -/
theorem modulePath_invariantFreeOnValid (context : ParseContext) :
    Parser.InvariantFreeOnValid (modulePath context) :=
  (modulePath_ordinary context).invariantFreeOnValid

/-- Module paths satisfy the generic strict element-parser contract. -/
theorem modulePath_elementTotalityContract (context : ParseContext) :
    ElementTotalityContract (modulePath context) := {
  validFor := (modulePath_validFor context).mono (fun _ _ _ => trivial)
  preservesTokenWindow := modulePath_preservesTokenWindow context
  cursorLtOnSuccess := modulePath_cursor_lt_onSuccess context
  invariantFree := fun input _ error =>
    modulePath_ne_invariant context input error
}

end Solcore.Syntax.Parser
