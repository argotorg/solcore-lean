import Solcore.SourceSemantics.CoreLowering.CallableAppliedRuntimeMaterialization
import Solcore.SourceSemantics.CoreLowering.CallableIndexedHistory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorHeap

/-! A descriptor keeps the real lexical frame together with its independent
Source graph. The native candidate context is retained separately from the
Source substitution history and its requirement metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorOrigin
open Core Frontend SourceInference TypeSystem
open SourceCoreLocalPolymorphism CallableIndexedHistory

structure Origin {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (function : Dynamic.GeneralizedClosure) (binding : Binding) (lexical : Substitution) where
  native : NativeFrame
  ghost : GhostFrame
  metadata : MetadataState
  carried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table native ghost (some metadata)
  paired : CallableAppliedDynamicSourceMaterialization.Pair prepared.ancestry.graph.inputs ghost metadata function.source
  owner : metadata.metadata.owner = binding.caller
  active : metadata.nativeActive = lexical

/-- Materialization uses the actual read dictionary and the descriptor's
lexical Source attachment. Native metadata keeps its own requirement rewrite. -/
theorem Origin.materialize {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    (origin : Origin prepared function binding lexical)
    {callerFrame : SourceCoreCallablePairedFrames.Frame}
    {caller : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word}
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerFrame
      origin.ghost caller origin.metadata id target)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder recipe.read.entry.view.principal.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    {context : Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actual : TypeSystem.Ty} {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = recipe.read.binder.scheme)
    (sameType : actual = recipe.read.node.rawType) :
    let instantiated := function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    CallableAppliedDynamicSourceMaterialization.Pair prepared.ancestry.graph.inputs
      (.appliedView id target callerFrame origin.ghost) (recipe.read.after origin.metadata) instantiated.source ∧
    CallableAncestryMetadata.eraseRequirements (recipe.read.after origin.metadata).metadata.source =
      CallableAncestryMetadata.eraseRequirements instantiated.source ∧
    ExpressionForm.lambda instantiated.parameters instantiated.resultType instantiated.body = recipe.read.template.node.form ∧
    instantiated.captured = function.captured ∧
    instantiated.evidence = produced ++ callerEvidence.applySubstitution semantic :=
  CallableAppliedRuntimeMaterialization.materialize origin.paired recipe captures unique instantiation sameScheme sameType

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorOrigin
