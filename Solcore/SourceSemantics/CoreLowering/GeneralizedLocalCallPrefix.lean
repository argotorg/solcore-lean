import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalDescriptorOrigin
import Solcore.SourceSemantics.CoreLowering.CallableIndexedProtocol

/-! Materialized calls join the retained lexical snapshot to the actual read
recipe. The selected frame has the read's child metadata; the captured frame
keeps its lexical metadata. No equality between these contexts is required. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallPrefix
open Core Frontend SourceInference TypeSystem ReadOnly
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open GeneralizedLocalDescriptorOrigin

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
  {lexical : Substitution}

/-- The completed paired table consumes both authentic parent histories and
the actual read/application factories. It does not reclassify the lexical frame. -/
theorem applied_history (origin : Origin prepared function binding lexical)
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id target : Word}
    (callerCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      callerNative callerGhost (some caller))
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id target) :
    Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table target origin.native
        (SourceCoreCallableIndexedDispatch.readFrame id target callerNative))
      (.appliedView id target callerGhost origin.ghost) (some (recipe.read.after origin.metadata)) := by
  obtain ⟨callerIndex, callerShape, _⟩ := callerCarried.state_shape
  obtain ⟨lexicalIndex, lexicalShape, _⟩ := origin.carried.state_shape
  have callerAt := callerShape ▸ callerCarried
  have lexicalAt := lexicalShape ▸ origin.carried
  simpa only [callerShape, lexicalShape, SourceCoreCallableIndexedDispatch.readFrame] using
    CallableIndexedHistory.applied_complete prepared.ancestry.graph callerAt lexicalAt
      recipe.read recipe.readAccepted recipe.applied recipe.appliedAccepted

/-- The emitted lambda frame load runs in the real current store. The result
is the child state certified by the same read recipe and both parent histories. -/
theorem evaluates (origin : Origin prepared function binding lexical)
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id target : Word}
    (callerCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      callerNative callerGhost (some caller))
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id target)
    {environment : Core.Environment} {store : Store} {lexicalExpression : Core.Expr}
    {referenceIndex location : Nat}
    (selected : DataEquality.Selects environment lexicalExpression (encode prepared.ancestry.layout.frame origin.native))
    (reference : environment[referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.readFrame id target callerNative))) :
    let next := SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table target origin.native
      (SourceCoreCallableIndexedDispatch.readFrame id target callerNative)
    Evaluates environment store
      (SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table prepared.ancestry.layout.frame
        target lexicalExpression (.loadCell (.var referenceIndex)))
      (encode prepared.ancestry.layout.frame next) store ∧
    Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next
      (.appliedView id target callerGhost origin.ghost) (some (recipe.read.after origin.metadata)) := by
  refine ⟨?_, applied_history origin callerCarried recipe⟩
  obtain ⟨position, shape, _⟩ := origin.carried.state_shape
  have selectedAt := shape ▸ selected
  simpa only [shape] using
    CallableIndexedProtocol.lambdaFrame_load prepared.ancestry.graph.table target selectedAt reference read

/-- Native dispatch and independent Source materialization share the exact
read recipe. Captures and the newly resolved evidence remain those of Source. -/
theorem materialized (origin : Origin prepared function binding lexical)
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id target : Word}
    (callerCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      callerNative callerGhost (some caller))
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
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
    Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table target origin.native
        (SourceCoreCallableIndexedDispatch.readFrame id target callerNative))
      (.appliedView id target callerGhost origin.ghost) (some (recipe.read.after origin.metadata)) ∧
    CallableAppliedDynamicSourceMaterialization.Pair prepared.ancestry.graph.inputs
      (.appliedView id target callerGhost origin.ghost) (recipe.read.after origin.metadata) instantiated.source ∧
    CallableAncestryMetadata.eraseRequirements (recipe.read.after origin.metadata).metadata.source =
      CallableAncestryMetadata.eraseRequirements instantiated.source ∧
    ExpressionForm.lambda instantiated.parameters instantiated.resultType instantiated.body = recipe.read.template.node.form ∧
    instantiated.captured = function.captured ∧
    instantiated.evidence = produced ++ callerEvidence.applySubstitution semantic :=
  ⟨applied_history origin callerCarried recipe,
    origin.materialize recipe captures unique instantiation sameScheme sameType⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCallPrefix
