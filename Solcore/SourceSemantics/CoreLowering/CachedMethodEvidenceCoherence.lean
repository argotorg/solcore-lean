import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipal
import Solcore.SourceSemantics.CoreLowering.LeafTraitEvidenceCoherence

/-! A finite compiler cache can authenticate evidence coherence for its actual
method rows. Original method owners exclude ordinary rows; full cached record
equality identifies the reached method without changing its substitution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CachedMethodEvidenceCoherence
open Frontend SourceInference
open RecursiveMethodDictionaryIdentity

def Row (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) : Prop :=
  (∀ definition ∈ (Program.ofChecked compiled.sourceProgram).methods,
    named.specialized.function.typedBody.owner ≠ definition.body.source.owner) ∨
  Coherent compiled.sourceProgram.signatures.resolutionRules named.specialized.assumptions

structure Catalog (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  rows : ∀ named ∈ compiled.indexed.base.functions, Row compiled named

theorem Catalog.of_instantiated {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled) {actual : ExecutableImplMethods.CheckedMethod}
    (cached : CallablePreparedMethodSelection.Cached compiled actual.specialized)
    {implementation : ProgramImplementationSignature} {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : TypeSystem.ParameterSubstitution}
    (instantiated : Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
      implementation method trait definition substitution
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual)) :
    Coherent compiled.sourceProgram.signatures.resolutionRules actual.specialized.assumptions := by
  rcases catalog.rows cached.named (List.mem_of_getElem? cached.selected) with excluded | coherent
  · cases instantiated with
    | intro _ _ _ _ definitionMember _ _ _ _ source _ _ =>
      have sourceOwner : actual.specialized.function.typedBody.owner = definition.body.source.owner := by
        have same := congrArg (fun source : TypedSource => source.owner) source
        exact same
      have namedOwner : cached.named.specialized.function.typedBody.owner =
          actual.specialized.function.typedBody.owner := by rw [cached.same]
      exact False.elim (excluded definition definitionMember (namedOwner.trans sourceOwner))
  · simpa only [cached.same] using coherent

theorem Catalog.of_principal {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled) {actual : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled actual) :
    Coherent compiled.sourceProgram.signatures.resolutionRules actual.specialized.assumptions := by
  obtain ⟨_, _, _, _, _, instantiated⟩ := principal.source_instantiation
  exact catalog.of_instantiated principal.cached instantiated

private def rowsOfLeaf? (compiled : SourceCoreUnifiedCompilation.Compiled)
    {trait : ProgramTraitId} {implementation : ProgramImplId}
    (leaf : LeafTraitEvidenceCoherence.Catalog
      compiled.sourceProgram.signatures.resolutionRules trait implementation) :
    (rows : List SourceCoreGeneralFunctions.Function) →
      Option (PLift (∀ named ∈ rows, Row compiled named))
  | [] => some ⟨by intro named member; cases member⟩
  | named :: rest => do
    let head ← (if excluded : (Program.ofChecked compiled.sourceProgram).methods.all
        (fun definition => decide (named.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
      some ⟨Or.inl (by
        intro definition member
        exact of_decide_eq_true (List.all_eq_true.mp excluded definition member))⟩
      else if traits : named.specialized.assumptions.all (fun goal => decide (goal.trait = trait)) = true then
        some ⟨Or.inr (LeafTraitEvidenceCoherence.coherent leaf (by
          intro goal member
          exact of_decide_eq_true (List.all_eq_true.mp traits goal member)))⟩
      else none : Option (PLift (Row compiled named)))
    let tail ← rowsOfLeaf? compiled leaf rest
    return ⟨by
      intro row member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head.down
      · exact tail.down row member⟩

/-- Only finite source owners and actual assumption trait tags are checked.
The proved leaf catalog supplies complete evidence-tree uniqueness. -/
def of_leaf? (compiled : SourceCoreUnifiedCompilation.Compiled)
    {trait : ProgramTraitId} {implementation : ProgramImplId}
    (leaf : LeafTraitEvidenceCoherence.Catalog
      compiled.sourceProgram.signatures.resolutionRules trait implementation) :
    Option (PLift (Catalog compiled)) := do
  let rows ← rowsOfLeaf? compiled leaf compiled.indexed.base.functions
  return ⟨⟨rows.down⟩⟩

end Solcore.SourceSemantics.CoreLowering.CachedMethodEvidenceCoherence
