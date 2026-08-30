import Solcore.Oracle.V5.ProbeValidation

/-! Executable ordering tests for Oracle v5 probe validation. -/

set_option autoImplicit false

namespace Tests.OracleV5ProbeValidation

open Solcore.Core
open Solcore.Oracle.V5
open Solcore.Semantics

private def first : Address := ⟨1, by decide⟩
private def second : Address := ⟨2, by decide⟩
private def slot : Word := ⟨3, by decide⟩

private def distinct : List Probe :=
  [.balance first, .storage first slot, .accountPresence first,
    .balance second]

private def distinctKindsAtOneAddressAreAllowed : Bool :=
  match ProbeValidation.validate distinct with
  | .error _ => false
  | .ok validated => validated.values == distinct

private def repeated : List Probe :=
  [.balance first, .balance second, .balance first, .balance first]

private def firstRepeatedPositionWins : Bool :=
  ProbeValidation.firstDuplicate? repeated == some {
    firstIndex := 0
    secondIndex := 2
    probe := .balance first
  }

private def rejectionPreservesBothIndices : Bool :=
  match ProbeValidation.validate repeated with
  | .ok _ => false
  | .error duplicate =>
      duplicate.firstIndex == 0 && duplicate.secondIndex == 2 &&
        duplicate.probe == .balance first

private def allChecks : Bool :=
  distinctKindsAtOneAddressAreAllowed && firstRepeatedPositionWins &&
    rejectionPreservesBothIndices

private theorem allChecks_exact : allChecks = true := by
  native_decide

def testOracleV5ProbeValidation : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 probe duplicate ordering changed")

end Tests.OracleV5ProbeValidation
