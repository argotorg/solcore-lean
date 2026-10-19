import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedViewFormation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReachedMaterialization

/-! The actual named read combines its stored framed row, original Dynamic
instantiation, compiler wrapper and current physical caller. The returned
positive association retains the same frame used by a following application. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatibleEquality
open CallableIndexedHistory GeneralizedLocalLocatedRows GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
  {lexical : TypeSystem.Substitution} {sourceLocation : Dynamic.Location} {frameLocation : Core.Location}

theorem preserves
    (certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named source scope id reasonAt lowered)
    (recipe : GeneralizedLocalNamedRecipeCompilation.Receipt certificate)
    (located : Located (GeneralizedLocalInstanceValues.model compiled.indexed) descriptor binding lexical
      sourceLocation mapping world heap store)
    (frames : located.Frames frameLocation)
    (sameCaller : named.signature.key = binding.caller) (sameBinder : certificate.read.binder = binding.binder.id)
    (contextExtension : GeneralizedLocalBundleContexts.ContextExtension lexical [])
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming} {actualContext : Core.Context}
    (environments : DataHeap.EnvRepresents (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment certificate.read.binder sourceLocation)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (unique : NodeOccurrencesUnique descriptor.source)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = certificate.read.binding.binder.scheme)
    (sameType : actualType = certificate.read.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState}
    (callerCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      callerNative callerGhost (some caller))
    (callerEq : caller = CallableIndexedNamedGeneration.state named)
    (reference : actual[embedding (scope.length + 1 + compiled.indexed.base.globals.length)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation))
    (snapshot : store.read? frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame callerNative))
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
    ∃ view : View material,
      material.frameLocation = frameLocation ∧ view.location = frameLocation ∧
      lowered.type = CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word view.native) store ∧
      ∃ member : Association compiled mapping world function view.native material.code.receipt.loweredParameters
          material.code.receipt.parameterCore material.code.receipt.resultCore,
        member.AtFrame frameLocation := by
  obtain ⟨material, _descriptor, materialBinding, _lexical, materialCandidate, materialType, _semantic,
      _context, _evidence, _produced, _requirements, materialFrame, rawRead⟩ :=
    GeneralizedLocalReachedMaterialization.preserves_framed located frames certificate.read sameCaller sameBinder
      contextExtension environments lookup agrees unique instantiation sameScheme sameType profile
  have lexicalReference : material.captured.canonical[material.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation) :=
    materialFrame ▸ material.frame_reference
  let view := GeneralizedLocalNamedViewFormation.view recipe material materialBinding materialCandidate
    (materialType.trans sameType) callerCarried callerEq reference lexicalReference
  have evaluated : Evaluates actual store (lowered.expression.rename embedding) (.inRight .word view.native) store :=
    view.formation rawRead snapshot
  have outputType : lowered.type = CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore := by
    have rawType := congrArg SourceCoreBasic.LoweredExpr.type certificate.read.emitted
    exact certificate.type.symm.trans (rawType.trans (materialCandidate ▸ material.native_type))
  exact ⟨material, view, materialFrame, rfl, outputType, evaluated,
    .viewed material view (view.runtime_hasType actualTyped), rfl⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadFormation
