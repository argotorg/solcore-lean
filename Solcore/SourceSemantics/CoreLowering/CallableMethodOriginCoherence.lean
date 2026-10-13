import Solcore.SourceSemantics.CoreLowering.RecursiveMethodOriginIdentity
import Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata

/-! A finite validator compares the complete trees reachable from the actual
caller dictionary and selected roots. It imposes no global implementation
uniqueness condition on the checked program. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodOriginCoherence
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallableNamedMetadata (evidence environment)
abbrev Raw := TypedTraitResolution.Evidence
abbrev Dictionary := SourceTypedRuntime.RuntimeEvidenceEnvironment

def subtrees : Raw → List Raw
  | tree@(.byImpl _ _ premises) => tree :: premises.flatMap subtrees

theorem subtree_mem {raw : Raw} {tree : TraitEvidence}
    (subtree : EvidenceSubtree (evidence raw) tree) :
    ∃ found ∈ subtrees raw, evidence found = tree := by
  generalize eq : evidence raw = root at subtree
  induction subtree generalizing raw with
  | self root =>
    exact ⟨raw, by cases raw; simp [subtrees], eq⟩
  | @premise goal implementation premises premise selected member _ induction =>
    cases raw with
    | byImpl rawGoal rawImplementation rawPremises =>
      simp only [evidence, TraitEvidence.implementation.injEq] at eq
      obtain ⟨_, _, same⟩ := eq
      obtain ⟨child, childMember, childEq⟩ := List.mem_map.mp (same.symm ▸ member)
      obtain ⟨found, foundMember, foundEq⟩ := induction childEq
      refine ⟨found, ?_, foundEq⟩
      simpa only [subtrees] using List.mem_cons_of_mem (.byImpl rawGoal rawImplementation rawPremises)
        (List.mem_flatMap.mpr ⟨child, childMember, foundMember⟩)

private theorem lookup_member {caller : EvidenceEnvironment}
    {goal : ProgramPredicate} {tree : TraitEvidence}
    (found : caller.LooksUp goal tree) : (goal, tree) ∈ caller := by
  induction found with
  | head => simp
  | tail _ _ induction => exact List.mem_cons_of_mem _ induction

def candidates (caller roots : Dictionary) : Dictionary := caller ++ roots.flatMap subtrees

theorem origin_member {caller roots : Dictionary}
    {goal : ProgramPredicate} {tree : TraitEvidence}
    (origin : EvidenceEntryOriginates (environment caller) (roots.map evidence) goal tree) :
    ∃ raw ∈ candidates caller roots,
      SourceTypedRuntime.runtimeEvidenceGoal raw = goal ∧ evidence raw = tree := by
  cases origin with
  | caller found =>
    obtain ⟨raw, member, same⟩ := List.mem_map.mp (lookup_member found)
    exact ⟨raw, List.mem_append_left _ member, (Prod.mk.inj same).1, (Prod.mk.inj same).2⟩
  | root member subtree same =>
    obtain ⟨rawRoot, rawRootMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨raw, rawMember, rawEq⟩ := subtree_mem subtree
    refine ⟨raw, List.mem_append_right _
      (List.mem_flatMap.mpr ⟨rawRoot, rawRootMember, rawMember⟩), ?_, rawEq⟩
    have goalEq := (congrArg TraitEvidence.goal rawEq).trans same
    cases raw
    simpa only [evidence, TraitEvidence.goal, SourceTypedRuntime.runtimeEvidenceGoal,
      SourceCompilationPlan.runtimeEvidenceGoal] using goalEq

def Compatible (goals : List ProgramPredicate) (entries : Dictionary) : Prop :=
  ∀ first ∈ entries, ∀ second ∈ entries,
    SourceTypedRuntime.runtimeEvidenceGoal first ∈ goals →
    SourceTypedRuntime.runtimeEvidenceGoal first = SourceTypedRuntime.runtimeEvidenceGoal second →
    first = second

instance (goals : List ProgramPredicate) (entries : Dictionary) : Decidable (Compatible goals entries) :=
  inferInstanceAs (Decidable (∀ first ∈ entries, ∀ second ∈ entries,
    SourceTypedRuntime.runtimeEvidenceGoal first ∈ goals →
    SourceTypedRuntime.runtimeEvidenceGoal first = SourceTypedRuntime.runtimeEvidenceGoal second → first = second))

theorem coherent {caller roots : Dictionary} {goals : List ProgramPredicate}
    (checked : Compatible goals (candidates caller roots)) :
    RecursiveMethodOriginIdentity.Coherent (environment caller) (roots.map evidence) goals := by
  intro goal member left right first second
  obtain ⟨rawLeft, leftMember, leftGoal, leftEq⟩ := origin_member first
  obtain ⟨rawRight, rightMember, rightGoal, rightEq⟩ := origin_member second
  have same := checked rawLeft leftMember rawRight rightMember (leftGoal.symm ▸ member)
    (leftGoal.trans rightGoal.symm)
  exact leftEq.symm.trans ((congrArg evidence same).trans rightEq)

/-- Successful validation is a certificate about complete actual trees.
Order and repeated assumptions remain in the independent assembly relation. -/
def validate (caller roots : Dictionary) (goals : List ProgramPredicate) :
    Option (PLift (RecursiveMethodOriginIdentity.Coherent
      (environment caller) (roots.map evidence) goals)) :=
  if checked : Compatible goals (candidates caller roots) then
    some ⟨coherent checked⟩
  else none

end Solcore.SourceSemantics.CoreLowering.CallableMethodOriginCoherence
