import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedConstructorApplication

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

theorem freshConstructorRetained
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial allocated constructorState resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {id : ExpressionId} {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation} {arguments : List Syntax.Expr}
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (dataMember : dataType ∈ inferenceContext.signatures.dataTypes)
    (constructorMember : constructor ∈ dataType.constructors)
    (fresh : Detail.freshDataConstructorInstantiation dataType constructor allocated =
      (instantiation, constructorState))
    (accepted : Detail.inferConstructorApplicationFuel childFuel inferenceContext expression id
      instantiation arguments expected constructorState = .ok (inferred, resultState)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  have formation := boundary.scope.formation checked
  have catalog := boundary.scope.catalog checked
  have canonical := boundary.scope.canonical checked
  have invariant := boundary.invariant.allocateExpressionId allocation
  have operational := boundary.operational.allocateExpressionId
  rw [allocation] at operational
  have freshInvariant := invariant.freshConstructor dataType constructor
  have freshOperational := operational.freshConstructor dataType constructor
  rw [fresh] at freshInvariant freshOperational
  have properties := Detail.freshDataConstructorInstantiation_inferenceProperties dataType constructor
    allocated invariant.ready
    (formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember allocated.inference.next)
  rw [fresh] at properties
  have binders := invariant.typeParameterBinders
    (by simpa only [boundary.scope.owner, boundary.scope.parameters] using canonical)
  have activeCatalog : SignatureCatalogWellFormed target.signatures := by
    rw [invariant.signatures_eq_whole, ← boundary.scope.signatures]
    exact catalog
  have activeData : dataType ∈ target.signatures.dataTypes := by
    rw [invariant.signatures_eq_whole, ← boundary.scope.signatures]
    exact dataMember
  have range := selected.body.resources.substitutionRangeAdmissible binders
    invariant.signatures_eq_whole invariant.typeParametersEq invariant.declarationEq invariant.residual
  have valid := freshConstructor_admissible_afterSubstitution activeCatalog binders invariant.residual range
    activeData constructorMember fresh
  have allocatedExpected : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocation]
    exact boundary.expectedBelow
  have allocatedSame : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have allocatedSafe : ∀ binder ∈ allocated.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified allocated type := by
    rw [allocatedSame]
    exact boundary.expectedSafe
  have freshScope := Detail.freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor allocated
  rw [fresh] at freshScope
  have freshBinders : constructorState.localBinders = allocated.localBinders :=
    congrArg LexicalScope.binders freshScope
  have privacy : ∀ binder ∈ constructorState.localBinders,
      ProtectedVariables.SafeTransport binder.scheme.quantified allocated constructorState ∧
      (∀ type ∈ instantiation.payloadTypes,
        ProtectedVariables.Safe binder.scheme.quantified constructorState type) ∧
      ProtectedVariables.Safe binder.scheme.quantified constructorState instantiation.resultType := by
    intro binder member
    have old : binder ∈ allocated.localBinders := freshBinders ▸ member
    have privateTypes := ProtectedVariables.fresh_constructor (dataType := dataType)
      (constructor := constructor) invariant.ready (operational.quantifiersBelow binder old)
      (formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember 0)
    rw [fresh] at privateTypes
    exact privateTypes
  exact constructorApplicationRetained checked recursive accepted boundary.interfaces boundary.extension
    boundary.scope freshInvariant boundary.actual freshOperational properties.2.2.2.1 properties.2.2.2.2
    (fun type member => (allocatedExpected type member).weaken properties.1.next_le)
    (fun binder member => (privacy binder member).2.1)
    (fun binder member => (privacy binder member).2.2)
    (fun binder member type typeMember =>
      (privacy binder member).1 type (allocatedSafe binder (freshBinders ▸ member) type typeMember))
    valid boundary.rawProper boundary.integerPatterns boundary.integerLiterals boundary.requirements
    boundary.expressionRequirements boundary.coercionPrimaries boundary.directChildren boundary.covered
    boundary.actualCovered

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
