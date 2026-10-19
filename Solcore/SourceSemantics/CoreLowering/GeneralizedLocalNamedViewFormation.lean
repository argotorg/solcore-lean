import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipe
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalViewedFormation

/-! The actual named caller and lexical allocation history instantiate the
static recipe and emitted wrapper for the materialized selected row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedViewFormation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues
open GeneralizedLocalMaterializedAssociation
open GeneralizedLocalNamedRecipeCompilation

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {named : SourceCoreGeneralFunctions.Function} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  {certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named source scope id reasonAt lowered}

theorem target (receipt : Receipt certificate) (material : Materialization compiled mapping world function)
    (binding : material.binding = certificate.read.binding)
    (candidate : material.candidate = certificate.read.candidate) :
    material.code.descriptor.id = receipt.observations.target := by
  have found := material.indexed.descriptor.found
  conv at found => lhs; rw [material.indexed.owner, material.initializer, GeneralizedLocalLambdaEmissionFacts.Emission.substitution,
    binding, candidate, ← receipt.candidate_initializer]
  exact material.descriptorId.trans (Option.some.inj (found.symm.trans receipt.target))

theorem native_types (receipt : Receipt certificate) (material : Materialization compiled mapping world function)
    (candidate : material.candidate = certificate.read.candidate) :
    receipt.parameter = material.code.receipt.parameterCore ∧ receipt.result = material.code.receipt.resultCore := by
  have rawType : certificate.raw.type = certificate.read.candidate.type :=
    congrArg SourceCoreBasic.LoweredExpr.type certificate.read.emitted
  have same := receipt.nativeType.symm.trans (rawType.trans (candidate ▸ material.native_type))
  simpa only [CallableContract.functionType, TaggedFunction.functionType, LanguageResult.resultType,
    Ty.product.injEq, Ty.function.injEq, Ty.sum.injEq, true_and, and_true] using same

private theorem retarget_fields {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    {inputs : SourceCoreCallableAncestryReadRecipes.Inputs base}
    {callerGhost lexicalGhost : GhostFrame} {caller lexical : MetadataState} {id target next : Word}
    (recipe : CallableAppliedViewProvenance.Recipe inputs callerGhost lexicalGhost caller lexical id target)
    (same : target = next) :
    let changed : CallableAppliedViewProvenance.Recipe inputs callerGhost lexicalGhost caller lexical id next := same ▸ recipe
    changed.read.entry = recipe.read.entry ∧ changed.read.binder = recipe.read.binder ∧ changed.read.node = recipe.read.node := by
  subst next
  exact ⟨rfl, rfl, rfl⟩

def view (receipt : Receipt certificate) (material : Materialization compiled mapping world function)
    (binding : material.binding = certificate.read.binding)
    (candidate : material.candidate = certificate.read.candidate)
    (actualType : material.actualType = certificate.read.node.rawType)
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState}
    (callerCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      callerNative callerGhost (some caller))
    (callerEq : caller = CallableIndexedNamedGeneration.state named)
    {embedding : Renaming} {environment : Environment} {location : Core.Location}
    (reference : environment[embedding (scope.length + 1 + compiled.indexed.base.globals.length)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (lexicalReference : material.captured.canonical[material.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location)) : View material := by
  have targetEq := target receipt material binding candidate
  have types := native_types receipt material candidate
  have lexicalEq : material.origin.metadata = CallableIndexedNamedGeneration.state named := by
    rw [material.namedMetadata]
    simp only [binding, ← receipt.binding, receipt.observations.namedCaller, receipt.observations.namedSource]
    rfl
  let originalRecipe := receipt.observations.recipe callerEq lexicalEq callerCarried.authenticates material.origin.carried.authenticates
  have fields := receipt.observations.recipe_fields callerEq lexicalEq callerCarried.authenticates material.origin.carried.authenticates
  let recipe : CallableAppliedViewProvenance.Recipe compiled.indexed.ancestry.graph.inputs callerGhost
      material.origin.ghost caller material.origin.metadata receipt.observations.entry.id material.code.descriptor.id :=
    targetEq.symm ▸ originalRecipe
  have changed := retarget_fields originalRecipe targetEq.symm
  have entryEq : recipe.read.entry = receipt.observations.read.entry := changed.1.trans fields.1
  have schemeEq : recipe.read.binder = receipt.observations.read.binder := changed.2.1.trans fields.2.1
  have nodeEq : recipe.read.node = receipt.observations.read.node := changed.2.2.trans fields.2.2
  exact
    { owner := named.signature.key, active := [], source := certificate.observations.normalized
      scope := scope, expression := id, original := certificate.raw, lowered := lowered
      accepted := certificate.viewAccepted, id := receipt.observations.entry.id
      referenceIndex := scope.length + 1 + compiled.indexed.base.globals.length
      emitted := by
        have emitted := congrArg SourceCoreBasic.LoweredExpr.expression receipt.emitted
        simpa only [types.1, types.2, ← targetEq] using emitted
      callerNative := callerNative, callerGhost := callerGhost, caller := caller, carried := callerCarried
      recipe := recipe
      initializer := by rw [entryEq, receipt.initializer, ← binding]; exact material.descriptorInitializer
      scheme := by rw [schemeEq, receipt.scheme, ← binding]; exact material.binderScheme
      actualType := actualType.trans (receipt.rawType.symm.trans (congrArg ExpressionNode.rawType nodeEq.symm))
      embedding := embedding, environment := environment, location := location, reference := reference
      lexicalReference := lexicalReference }

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedViewFormation
