import Solcore.TypeSystem.Inference

set_option autoImplicit false

namespace Solcore.Test.TypeSystemInference

open TypeSystem

example : DecidableEq Ty := inferInstance
example : DecidableEq Inference.Error := inferInstance

private def identity : Expr :=
  .lambda "x" (.variable "x")

example : Inference.inferClosed identity =
    .ok (.function (.variable ⟨0⟩) (.variable ⟨0⟩)) := by
  rfl

private def polymorphicIdentityPair : Expr :=
  .letE "id" identity
    (.pair
      (.application (.variable "id") .unit)
      (.application (.variable "id") (.bool true)))

example : Inference.inferClosed polymorphicIdentityPair =
    .ok (.product .unit .bool) := by
  rfl

private def selfApplication : Expr :=
  .lambda "x" (.application (.variable "x") (.variable "x"))

example : Inference.inferClosed selfApplication =
    .error (.unification
      (.occursCheck ⟨0⟩ (.function (.variable ⟨0⟩) (.variable ⟨1⟩)))) := by
  rfl

example : Inference.inferClosed (.variable "missing") =
    .error (.unknownVariable "missing") := by
  rfl

private def variable0 : Ty := .variable ⟨0⟩
private def box (argument : Ty) : Ty :=
  .application (.constructor (.builtin .word)) argument

example : Unification.unifyTypes (box variable0) (box .bool) =
    .ok [(⟨0⟩, .bool)] := by
  rfl

private def rigidOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"rigid", by decide⟩], by decide⟩⟩, 0⟩

example : Unification.unifyTypes
    (.parameter { owner := rigidOwner, index := 0 })
    (.parameter { owner := rigidOwner, index := 1 }) =
    .error (.mismatch
      (.parameter { owner := rigidOwner, index := 0 })
      (.parameter { owner := rigidOwner, index := 1 })) := by
  rfl

private def rigidParameter : TypeParameterId :=
  { owner := rigidOwner, index := 0 }

example :
    let scheme : DeclarationScheme :=
      { parameters := [rigidParameter]
        body := .function (.parameter rigidParameter) (.parameter rigidParameter) }
    scheme.instantiate 20 =
      (.function (.variable ⟨20⟩) (.variable ⟨20⟩), 21) := by
  rfl

example :
    let scheme : Scheme :=
      { quantified := [⟨7⟩], body := .function (.variable ⟨7⟩) (.variable ⟨7⟩) }
    scheme.instantiate 10 =
      (.function (.variable ⟨10⟩) (.variable ⟨10⟩), 11) := by
  rfl

example :
    let scheme : Scheme :=
      { quantified := [⟨7⟩, ⟨9⟩]
        body := .function (.variable ⟨7⟩) (.variable ⟨9⟩) }
    scheme.instantiateWithSubstitution 10 =
      { substitution := [(⟨9⟩, .variable ⟨11⟩), (⟨7⟩, .variable ⟨10⟩)]
        body := .function (.variable ⟨10⟩) (.variable ⟨11⟩)
        next := 12 } := by
  rfl

private def matchedVariable : TypeVarId := ⟨7⟩
private def openOccurrenceVariable : TypeVarId := ⟨42⟩

private def repeatedVariableScheme : Scheme := {
  quantified := [matchedVariable]
  body := .function (.variable matchedVariable) (.variable matchedVariable)
}

/-- Open occurrence types are valid rank-1 scheme instances; closing them is
a separate specialization policy. -/
example : repeatedVariableScheme.matchInstance?
    (.function (.variable openOccurrenceVariable)
      (.variable openOccurrenceVariable)) =
    some [(matchedVariable, .variable openOccurrenceVariable)] := by
  rfl

/-- Repeated occurrences of one quantified variable must select one type. -/
example : repeatedVariableScheme.matchInstance? (.function .word .bool) =
    none := by
  rfl

/-- Phantom quantified variables cannot produce a complete substitution. -/
example : Scheme.matchInstance?
    ({ quantified := [matchedVariable], body := Ty.word } : Scheme) .word =
    none := by
  rfl

/-- Duplicate quantifier identities are rejected at the certificate boundary. -/
example : ({
      quantified := [matchedVariable, matchedVariable]
      body := Ty.variable matchedVariable
    } : Scheme).matchInstance? .word = none := by
  rfl

/-- Unquantified flexible variables remain rigid during scheme matching. -/
example : (Scheme.mono (.variable matchedVariable)).matchInstance?
    (.variable matchedVariable) = some [] := by
  rfl

example : (Scheme.mono (.variable matchedVariable)).matchInstance? .word =
    none := by
  rfl

/-- The exported soundness projection exposes the exact open instantiation. -/
example :
    let substitution : Substitution :=
      [(matchedVariable, .variable openOccurrenceVariable)]
    repeatedVariableScheme.quantified.Nodup ∧
      substitution.domain = repeatedVariableScheme.quantified ∧
      substitution.apply repeatedVariableScheme.body =
        .function (.variable openOccurrenceVariable)
          (.variable openOccurrenceVariable) := by
  exact Scheme.matchInstance?_sound (by rfl)

end Solcore.Test.TypeSystemInference
