import Solcore.Abi.StaticWordImplementation

/-! Admission regressions for checked Static Word method implementations. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open Solcore.Abi.V1

private def one : Word := ⟨1, by decide⟩

private def identityProgram : Program := {
  resultType := .function .word .word
  body := .lambda .word .word (.var 0)
}

private theorem identityProgram_checked :
    identityProgram.checkHost = true := by
  decide

private def identityCode : CheckedHostCoreProgram :=
  ⟨identityProgram, identityProgram_checked⟩

example : ∃ implementation,
    WordImplementation.ofCode? identityCode = some implementation :=
  (WordImplementation.ofCode?_exists_iff identityCode).2 ⟨rfl, rfl⟩

private def arithmeticProgram : Program := {
  resultType := .function .word .word
  body :=
    .lambda .word .word
      (.binary .wordAdd (.var 0) (.word one))
}

private theorem arithmeticProgram_checked :
    arithmeticProgram.checkHost = true := by
  decide

private def arithmeticCode : CheckedHostCoreProgram :=
  ⟨arithmeticProgram, arithmeticProgram_checked⟩

example : ∃ implementation,
    WordImplementation.ofCode? arithmeticCode = some implementation :=
  (WordImplementation.ofCode?_exists_iff arithmeticCode).2 ⟨rfl, rfl⟩

/-- The method parameter shifts every fixed host capability by one slot. -/
private def storageReadProgram : Program := {
  resultType := .function .word .word
  body :=
    .lambda .word .word
      (.apply
        (.var (HostFunction.storageRead.index + 1))
        (.var 0))
}

private theorem storageReadProgram_checked :
    storageReadProgram.checkHost = true := by
  decide

private def storageReadCode : CheckedHostCoreProgram :=
  ⟨storageReadProgram, storageReadProgram_checked⟩

example : ∃ implementation,
    WordImplementation.ofCode? storageReadCode = some implementation :=
  (WordImplementation.ofCode?_exists_iff storageReadCode).2 ⟨rfl, rfl⟩

private def wrongResultProgram : Program := {
  resultType := .function .word .bool
  body := .lambda .word .bool (.bool true)
}

private theorem wrongResultProgram_checked :
    wrongResultProgram.checkHost = true := by
  decide

private def wrongResultCode : CheckedHostCoreProgram :=
  ⟨wrongResultProgram, wrongResultProgram_checked⟩

example : WordImplementation.ofCode? wrongResultCode = none := by
  apply (WordImplementation.ofCode?_eq_none_iff wrongResultCode).2
  left
  decide

private def namedDefinition : DataDefinition := {
  constructorPayloadTypes := []
}

private def nonemptyDefinitionsProgram : Program := {
  resultType := .function .word .word
  body := .lambda .word .word (.var 0)
  dataDefinitions := [namedDefinition]
}

private theorem nonemptyDefinitionsProgram_checked :
    nonemptyDefinitionsProgram.checkHost = true := by
  decide

private def nonemptyDefinitionsCode : CheckedHostCoreProgram :=
  ⟨nonemptyDefinitionsProgram, nonemptyDefinitionsProgram_checked⟩

example : WordImplementation.ofCode? nonemptyDefinitionsCode = none := by
  apply (WordImplementation.ofCode?_eq_none_iff
    nonemptyDefinitionsCode).2
  right
  decide

private def rejectedProgram : Program := {
  resultType := .function .word .word
  body := .lambda .word .word (.bool true)
}

private theorem rejectedProgram_rejected :
    rejectedProgram.checkHost = false := by
  decide

example : WordImplementation.ofProgram? rejectedProgram = none :=
  WordImplementation.ofProgram?_of_rejected
    rejectedProgram rejectedProgram_rejected

end Tests
