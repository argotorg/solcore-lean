import Solcore.Frontend.SourceRuntime

/-! Focused executable checks for the finite runtime call graph. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

@[simp] theorem Program.findDefinition?_empty (key : Key) :
    ({ definitions := [] : Program }).findDefinition? key = none := by
  rfl

@[simp] theorem Program.findSignature?_empty (key : Key) :
    ({ definitions := [] : Program }).findSignature? key = none := by
  rfl

private def testPath : Workspace.ModulePath :=
  ⟨[⟨"Runtime", by decide⟩], by decide⟩

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, testPath⟩, index⟩

private def key (index : Nat) : Key :=
  ⟨declaration index, []⟩

private def localId (owner binder : Nat) : Resolved.LocalId :=
  ⟨declaration owner, binder⟩

private def leftParameter : Parameter := (localId 0 0, .bool)
private def rightParameter : Parameter := (localId 1 0, .bool)

/-- A deliberately nonterminating mutual cycle.  Checking succeeds because all
global signatures are collected before either body is inspected. -/
private def cyclicProgram : Program := {
  definitions := [
    {
      key := key 0
      parameters := [leftParameter]
      resultType := .bool
      body := .apply (.global (key 1)) [.local leftParameter.1]
    },
    {
      key := key 1
      parameters := [rightParameter]
      resultType := .bool
      body := .apply (.global (key 0)) [.local rightParameter.1]
    }
  ]
}

example : cyclicProgram.check = .ok ⟨cyclicProgram⟩ := by
  rfl

example (store : Core.Store) :
    (⟨cyclicProgram⟩ : CheckedProgram).run 12 (key 0) [.bool true] store =
      .outOfFuel store := by
  rfl

private def captureParameter : Parameter := (localId 2 0, .bool)
private def lambdaBinder : Resolved.LocalId := localId 2 1
private def lambdaParameter : Parameter := (localId 2 2, .bool)

/-- The lambda ignores its argument and returns a captured entry parameter. -/
private def closureProgram : Program := {
  definitions := [{
    key := key 2
    parameters := [captureParameter]
    resultType := .bool
    body := .letE lambdaBinder
      (.lambda [lambdaParameter] .bool (.local captureParameter.1))
      (.apply (.local lambdaBinder) [.bool false])
  }]
}

example : closureProgram.check = .ok ⟨closureProgram⟩ := by
  rfl

example (store : Core.Store) :
    (⟨closureProgram⟩ : CheckedProgram).run 8 (key 2) [.bool true] store =
      .done (.bool true) store := by
  rfl

example (store : Core.Store) :
    (⟨closureProgram⟩ : CheckedProgram).run 8 (key 2) [] store =
      .fault (.entryArgumentArityMismatch (key 2) 1 0) store := by
  rfl

example (store : Core.Store) :
    (⟨closureProgram⟩ : CheckedProgram).run 8 (key 2)
        [.word Core.Word.zero] store =
      .fault (.entryArgumentTypeMismatch (key 2) 0 .bool .word) store := by
  rfl

end Solcore.Frontend.SourceRuntime
