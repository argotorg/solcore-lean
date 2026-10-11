import Solcore.SourceSemantics.CoreLowering.CallableAppliedDynamicSourceMaterialization
import Solcore.SourceSemantics.CoreLowering.CallableClosedSchemeSubstitutionAgreement
import Solcore.SourceSemantics.CoreLowering.CallableFlexibleSubstitutionAgreement

/-! Attach the substitution chosen by an actual Dynamic local-scheme use to
the sealed compiler read. The complete matcher and runtime instantiation
determine equal substitution actions; the actual produced-plus-caller evidence
is retained literally. The live descriptor's source ancestry and the matching
scheme/type inputs remain explicit allocation/read obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAppliedRuntimeMaterialization
open Frontend SourceInference TypeSystem
open SourceCoreCallableAncestryReadRecipes

/-- Actual witness preparation determines the same variable lookups as the
runtime instantiation at the same scheme and raw occurrence type. -/
theorem read_lookup_eq
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word}
    (read : Read inputs caller id target)
    {context : Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {binder : TypedBinder} {actual : Ty} {requirements : List RequirementId}
    {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      binder actual requirements semantic produced)
    (sameScheme : binder.scheme = read.binder.scheme)
    (sameType : actual = read.node.rawType) :
    ∀ metavariable, semantic.lookup? metavariable = read.substitution.lookup? metavariable := by
  have matched := CallableAncestryProfiles.SourceComposition.witnesses_matched read.factory
  change SourceSpecialization.matchClosedSchemeInstance? read.binder.scheme
    read.node.rawType = some read.substitution at matched
  apply CallableClosedSchemeSubstitutionAgreement.runtime_instantiation_lookup_eq
    (instantiation := instantiation)
  rw [sameScheme, sameType]
  exact matched

/-- The observed substitution yields exactly the same complete closure as
the read substitution when both retain this actual use's evidence. -/
theorem instantiated_closure_eq
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word}
    (read : Read inputs caller id target)
    {context : Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    (function : Dynamic.GeneralizedClosure) {actual : Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = read.binder.scheme)
    (sameType : actual = read.node.rawType) :
    function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic) =
      function.instantiate read.substitution
        (produced ++ callerEvidence.applySubstitution semantic) :=
  CallableFlexibleSubstitutionAgreement.instantiate_congr
    (read_lookup_eq read instantiation sameScheme sameType) function _

/-- The real Dynamic use, including its observed substitution and evidence,
inherits the authenticated source recipe and exact native lambda header.
This consumes the descriptor's live source attachment; it does not reconstruct
that attachment from metadata ancestry or native frame decoding. -/
theorem materialize
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {callerFrame lexicalFrame : SourceCoreCallablePairedFrames.Frame}
    {caller lexical : SourceCoreCallableAncestryReadRecipes.State}
    {source : TypedSource} {id target : Core.Word}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs lexicalFrame lexical source)
    (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame
      caller lexical id target)
    {definitionContext context : Context} {captured : Dynamic.Environment}
    {binder : TypedBinder} {function : Dynamic.GeneralizedClosure}
    (captures : Dynamic.GeneralizedClosureCaptures definitionContext source captured binder
      recipe.read.entry.view.principal.initializer function)
    (unique : NodeOccurrencesUnique source)
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actual : Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = recipe.read.binder.scheme)
    (sameType : actual = recipe.read.node.rawType) :
    let instantiated := function.instantiate semantic
      (produced ++ callerEvidence.applySubstitution semantic)
    CallableAppliedDynamicSourceMaterialization.Pair inputs
      (.appliedView id target callerFrame lexicalFrame)
      (recipe.read.after lexical) instantiated.source ∧
    CallableAncestryMetadata.eraseRequirements (recipe.read.after lexical).metadata.source =
      CallableAncestryMetadata.eraseRequirements instantiated.source ∧
    ExpressionForm.lambda instantiated.parameters instantiated.resultType instantiated.body =
      recipe.read.template.node.form ∧
    instantiated.captured = captured ∧
    instantiated.evidence = produced ++ callerEvidence.applySubstitution semantic := by
  dsimp only
  rw [instantiated_closure_eq recipe.read function instantiation sameScheme sameType]
  exact CallableAppliedDynamicSourceMaterialization.materialize paired recipe captures unique _

end Solcore.SourceSemantics.CoreLowering.CallableAppliedRuntimeMaterialization
