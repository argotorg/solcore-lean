import Solcore.Oracle.V5.Input

/-! Ordered duplicate validation for Oracle v5 world probes. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

/-- The earliest repeated probe and its first prior occurrence. -/
structure DuplicateProbe where
  firstIndex : Nat
  secondIndex : Nat
  probe : Probe
  deriving Repr, BEq, DecidableEq

namespace ProbeValidation

private def firstEqualIndex? (needle : Probe) :
    Nat → List Probe → Option Nat
  | _, [] => none
  | index, candidate :: rest =>
      if candidate = needle then some index
      else firstEqualIndex? needle (index + 1) rest

private def findDuplicateFrom :
    List Probe → Nat → List Probe → Option DuplicateProbe
  | _, _, [] => none
  | previous, secondIndex, probe :: rest =>
      match firstEqualIndex? probe 0 previous with
      | some firstIndex => some { firstIndex, secondIndex, probe }
      | none =>
          findDuplicateFrom (previous ++ [probe]) (secondIndex + 1) rest

/--
Select by the first repeated position, then by the first equal earlier position.
Probe order itself is never canonicalized because it is observable output order.
-/
def firstDuplicate? (probes : List Probe) : Option DuplicateProbe :=
  findDuplicateFrom [] 0 probes

/-- A probe list that cannot contain equal complete tagged values twice. -/
structure ValidatedProbes where
  private mk ::
  values : List Probe
  unique : firstDuplicate? values = none

namespace ValidatedProbes

def length (probes : ValidatedProbes) : Nat := probes.values.length

end ValidatedProbes

/-- Preserve the caller's exact order while rejecting the first duplicate. -/
def validate (probes : List Probe) : Except DuplicateProbe ValidatedProbes :=
  match found : firstDuplicate? probes with
  | some duplicate => .error duplicate
  | none => .ok ⟨probes, found⟩

@[simp] theorem validate_eq_ok_iff (probes : List Probe) :
    (∃ validated, validate probes = .ok validated) ↔
      firstDuplicate? probes = none := by
  constructor
  · rintro ⟨validated, accepted⟩
    unfold validate at accepted
    split at accepted
    · contradiction
    · assumption
  · intro absent
    refine ⟨⟨probes, absent⟩, ?_⟩
    unfold validate
    split
    · simp_all
    · congr

@[simp] theorem validate_values
    {probes : List Probe}
    {validated : ValidatedProbes}
    (accepted : validate probes = .ok validated) :
    validated.values = probes := by
  unfold validate at accepted
  split at accepted
  · contradiction
  · cases accepted
    rfl

end ProbeValidation

end Solcore.Oracle.V5
