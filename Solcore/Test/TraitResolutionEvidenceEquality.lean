import Solcore.Frontend.TraitResolution

/-! Finite comparison tests preserve the previous derived comparison order and
outcomes, including nested premises and the three independently compared fields. -/
set_option autoImplicit false
namespace Tests.TraitResolutionEvidenceEquality
open Solcore.Frontend.TraitResolution
abbrev Proof := Evidence Nat Nat Nat

def leaf (goal implementation : Nat) : Proof := .byImpl ⟨goal, goal + 1, [goal + 2]⟩ implementation []
def nest : Nat → Proof → Proof
  | 0, proof => proof
  | depth + 1, proof => .byImpl ⟨depth, 0, []⟩ depth [leaf depth depth, nest depth proof]

/-- The law holds for any finite tree, not just the test depths. -/
theorem reflects (left right : Proof) (accepted : (left == right) = true) : left = right := eq_of_beq accepted

theorem reflexive (value : Proof) : (value == value) = true := by simp

theorem deep_same (depth : Nat) : (nest depth (leaf 1 2) == nest depth (leaf 1 2)) = true := by simp

private inductive Previous where
  | byImpl (goal : Predicate Nat Nat) (implementation : Nat) (premises : List Previous)
  deriving BEq

private def previous : Proof → Previous
  | .byImpl goal implementation premises => .byImpl goal implementation (premises.map previous)

private def check (name : String) (left right : Proof) (expected : Bool) : IO Unit := do
  let actual := left == right
  unless actual == expected do throw (IO.userError s!"Evidence comparison {name}: unexpected result")
  unless actual == (previous left == previous right) do
    throw (IO.userError s!"Evidence comparison {name}: changed previous comparison")

def run : IO Unit := do
  check "empty premises" (leaf 1 2) (leaf 1 2) true
  check "goal" (leaf 1 2) (leaf 2 2) false
  check "implementation" (leaf 1 2) (leaf 1 3) false
  check "subject" (leaf 1 2) (.byImpl ⟨1, 7, [3]⟩ 2 []) false
  check "goal arguments" (leaf 1 2) (.byImpl ⟨1, 2, [4]⟩ 2 []) false
  check "ordered premises" (.byImpl ⟨0, 0, []⟩ 0 [leaf 1 1, leaf 2 2])
    (.byImpl ⟨0, 0, []⟩ 0 [leaf 2 2, leaf 1 1]) false
  check "premise length" (.byImpl ⟨0, 0, []⟩ 0 [leaf 1 1]) (.byImpl ⟨0, 0, []⟩ 0 []) false
  check "deep equality" (nest 128 (leaf 1 2)) (nest 128 (leaf 1 2)) true
  check "deep difference" (nest 128 (leaf 1 2)) (nest 128 (leaf 1 3)) false
  IO.println "[PASS] structural evidence equality"
end Tests.TraitResolutionEvidenceEquality
