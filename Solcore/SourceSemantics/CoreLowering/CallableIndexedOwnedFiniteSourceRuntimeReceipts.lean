import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.Dynamic.Preservation

/-! Finite checks establish the independent occurrence-graph invariants for
an unchanged typed Source. Actual context fields and a separately proved
runtime requirement ledger then establish its runtime validity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFiniteSourceRuntimeReceipts
open Frontend.SourceInference

/-- Check category-safe roots and edges as well as erased occurrence identity.
Every equality is decided propositionally; no structural BEq law is assumed. -/
def checkGraph (source : TypedSource) : Bool :=
  decide (nodeOccurrenceIds source).Nodup &&
    (source.nodes.all (fun node => decide (node.occurrenceId.owner = source.owner)) &&
      (source.roots.all (fun root => decide (root.occurrenceId.owner = source.owner)) &&
        (source.roots.all (fun root => (nodeIds source).any (fun known => decide (root = known))) &&
          source.nodes.all (fun node =>
            (nodeChildIds node).all (fun child => (nodeIds source).any (fun known => decide (child = known)))))))

/-- Successful finite checks prove the original declarative graph invariant. -/
theorem checkGraph_sound {source : TypedSource} (accepted : checkGraph source = true) :
    OccurrenceGraphWellFormed source := by
  unfold checkGraph at accepted
  obtain ⟨unique, rest⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨nodes, rest⟩ := Bool.and_eq_true_iff.mp rest
  obtain ⟨roots, rest⟩ := Bool.and_eq_true_iff.mp rest
  obtain ⟨exist, children⟩ := Bool.and_eq_true_iff.mp rest
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (nodeOccurrenceIds source).Nodup
    exact of_decide_eq_true unique
  · intro node member
    change node.occurrenceId.owner = source.owner
    exact of_decide_eq_true (List.all_eq_true.mp nodes node member)
  · intro root member
    change root.occurrenceId.owner = source.owner
    exact of_decide_eq_true (List.all_eq_true.mp roots root member)
  · intro root member
    obtain ⟨known, present, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp exist root member)
    exact (of_decide_eq_true same).symm ▸ present
  · intro node member child edge
    obtain ⟨known, present, same⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp (List.all_eq_true.mp children node member) child edge)
    exact (of_decide_eq_true same).symm ▸ present

/-- The proof is erased during the finite check; the Source remains unchanged. -/
def graphReceipt? (source : TypedSource) : Option (PLift (OccurrenceGraphWellFormed source)) :=
  if accepted : checkGraph source = true then some ⟨checkGraph_sound accepted⟩ else none

/-- These are literal context fields, independent of program execution. -/
structure RuntimeFields (program : Program) (context : Context) (source : TypedSource) : Prop where
  signatures : context.signatures = program.signatures
  owner : context.currentDeclaration = some source.owner
  closed : context.typeParameters = []
  variables_closed : context.typeVariables = []
  residual_variables_open : context.residualTypeVariables = true

/-- Runtime validity follows from the actual checked graph, context fields,
and independent validity of its implementation-backed requirement rows. -/
theorem source_runtime {program : Program} {context : Context} {source : TypedSource}
    (fields : RuntimeFields program context source)
    (accepted : checkGraph source = true)
    (ledger : RuntimeRequirementLedgerValid context) :
    Dynamic.SourceRuntimeValid program context source :=
  { signatures := fields.signatures
    graph := checkGraph_sound accepted
    owner := fields.owner
    closed := fields.closed
    variables_closed := fields.variables_closed
    residual_variables_open := fields.residual_variables_open
    requirements := ledger }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFiniteSourceRuntimeReceipts
