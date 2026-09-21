import Solcore.Frontend.TypedTraitResolution

/-! Regression tests for collision-free whole-program trait and impl identities. -/

set_option autoImplicit false

namespace Tests.ProgramIdentity

open Solcore
open Solcore.Frontend
open Solcore.Frontend.TypedTraitResolution
open Solcore.TypeSystem

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"program_identity", by decide⟩], by decide⟩⟩

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨moduleId, index⟩

private def sourceTraitDeclaration := declaration 0
private def sourceImplDeclaration := declaration 1

example : ((sourceTraitDeclaration : ProgramTraitId).declaration?) =
    some sourceTraitDeclaration := by
  rfl

example : (ProgramTraitId.builtin .int).declaration? = none := by
  rfl

example : ProgramTraitId.builtin .int ≠
    ProgramTraitId.declaration sourceTraitDeclaration := by
  decide

example {left right : Resolved.DeclarationId}
    (same : ProgramTraitId.declaration left = .declaration right) :
    left = right := by
  exact ProgramTraitId.declaration.inj same

example : ((sourceImplDeclaration : ProgramImplId).declaration?) =
    some sourceImplDeclaration := by
  rfl

example : (ProgramImplId.builtin .intWord).declaration? = none := by
  rfl

example : ProgramImplId.builtin .intWord ≠
    ProgramImplId.declaration sourceImplDeclaration := by
  decide

example {left right : Resolved.DeclarationId}
    (same : ProgramImplId.declaration left = .declaration right) :
    left = right := by
  exact ProgramImplId.declaration.inj same

private def sourceGoal : Predicate := {
  trait := sourceTraitDeclaration
  subject := .word
  arguments := []
}

private def builtinGoal : Predicate := {
  trait := .builtin .int
  subject := .word
  arguments := []
}

private def sourceRule : ImplRule := {
  id := sourceImplDeclaration
  head := sourceGoal
  wherePredicates := []
}

private def builtinRule : ImplRule := {
  id := .builtin .intWord
  head := builtinGoal
  wherePredicates := []
}

private def sourceResolutionPreservesTags : Bool :=
  match (resolve [builtinRule, sourceRule] 1 sourceGoal).outcome with
  | .success (.byImpl goal implementation []) =>
      decide (goal = sourceGoal ∧
        implementation = ProgramImplId.declaration sourceImplDeclaration)
  | _ => false

private def builtinResolutionPreservesTags : Bool :=
  match (resolve [sourceRule, builtinRule] 1 builtinGoal).outcome with
  | .success (.byImpl goal implementation []) =>
      decide (goal = builtinGoal ∧ implementation = .builtin .intWord)
  | _ => false

private def sourceRuleDoesNotMatchBuiltinGoal : Bool :=
  match (resolve [sourceRule] 1 builtinGoal).outcome with
  | .noSolution => true
  | _ => false

private def builtinRuleDoesNotMatchSourceGoal : Bool :=
  match (resolve [builtinRule] 1 sourceGoal).outcome with
  | .noSolution => true
  | _ => false

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- Exercise disjoint source/builtin identities through typed class resolution. -/
def testProgramIdentity : IO Unit := do
  assertTrue sourceResolutionPreservesTags
    "source trait resolution lost its declaration-tagged implementation"
  assertTrue builtinResolutionPreservesTags
    "builtin trait resolution lost its builtin-tagged implementation"
  assertTrue sourceRuleDoesNotMatchBuiltinGoal
    "source trait identity collided with the builtin Int trait"
  assertTrue builtinRuleDoesNotMatchSourceGoal
    "builtin Int trait identity collided with a source trait declaration"

end Tests.ProgramIdentity
