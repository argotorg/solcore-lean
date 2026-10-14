import Solcore.Test.SourceCoreSelectedCoercedDirectSource
import Solcore.Test.SourceCoreCoercionPublicFixture
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosedCoercionSourceSelection

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedCoercedDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

structure Row (compiled : SourceCoreUnifiedCompilation.Compiled) where
  named : SourceCoreGeneralFunctions.Function
  index : Nat
  cached : compiled.indexed.base.functions[index]? = some named
  eligible : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Eligible compiled named.specialized

structure Fixture where
  recipe : SourceCoreIndexedSession.Recipe
  checked : checkProgram Tests.SourceCoreCoercionPublic.workspace 1024 = .ok recipe.compiled.sourceProgram
  seeds : List SourceCompiler.Seed
  options : SourceCompiler.Options
  facade : SourceCoreExecution.Compiled
  accepted : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok facade
  selected : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe
  profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled
  closed : CompilerCoercedMethodProfile.Closed recipe.compiled
  make : Row recipe.compiled
  keep : Row recipe.compiled
  makeSignature : ProgramFunctionSignature
  keepSignature : ProgramFunctionSignature
  parameter : TypeSystem.TypeParameterId
  mark : ProgramTraitSignature
  coercion : ProgramTraitSignature
  shape : Tests.SourceCoreCoercionPublic.FactoryShape make.named.specialized.function
    makeSignature keepSignature parameter mark coercion
  identity : Tests.SourceCoreCoercionPublic.SelectedIdentityShape keep.named.specialized.function .bool
  makeResult : make.named.specialized.function.inferredBodyType = .function .unit .word
  makeBinder : shape.binder.scheme = .mono .bool
  keepBinder : identity.binder.scheme = .mono .bool
  target : shape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation keep.named.specialized
  available : SourceTypedRuntime.RuntimeEvidenceEnvironment
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment recipe.compiled.sourceProgram
    make.named.specialized.key make.named.specialized.assumptions = .ok available
  dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  direct : SourceCompilationPlan.exactDirectCallRuntimeEvidence make.named.specialized shape.call.node available shape.call.instantiation = .ok dictionary
  authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence recipe.compiled.sourceProgram.signatures
    keep.named.specialized.key shape.call.instantiation.predicates dictionary = .ok ()
  keepResolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment recipe.compiled.sourceProgram
    keep.named.specialized.key keep.named.specialized.assumptions = .ok dictionary
  method : ExecutableImplMethods.CheckedMethod
  methodSelected : SourceCompilationPlan.checkedCoercionMethod recipe.compiled.sourceProgram
    make.named.specialized shape.call.node available shape.call.step = .ok method
  methodDictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence recipe.compiled.sourceProgram
    make.named.specialized shape.call.node shape.call.step method = .ok methodDictionary
  methodMember : method.specialized ∈ recipe.compiled.indexed.base.plan.specializations
  methodShape : Tests.SourceCoreCoercionPublic.MethodShape method.specialized.function method.synthetic
  methodBinder : methodShape.binder.scheme = .mono .bool
  firstValue : methodShape.first.validated.value = Word.ofNatModulo 41
  secondValue : methodShape.second.validated.value = Word.ofNatModulo 7

private def rowOfObserved {fixture : Tests.SourceCoreCoercionPublic.CompiledFixture}
    {signature : ProgramFunctionSignature} (row : Tests.SourceCoreCoercionPublic.ObservedRow fixture signature) :
    Row fixture.recipe.compiled :=
  ⟨row.named, row.index, row.cached, row.same.symm ▸ row.eligible⟩

/-- Retain only actual checker, compiler, flat-profile and metadata receipts. -/
def fixture : IO Fixture := do
  let original ← Tests.SourceCoreCoercionPublic.compiledFixture
  let actual ← Tests.SourceCoreCoercionPublic.observeProgram original
  let compiled := original.recipe.compiled
  have checked : checkProgram Tests.SourceCoreCoercionPublic.workspace 1024 = .ok compiled.sourceProgram :=
    original.sameProgram.symm ▸ original.checked
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile compiled checked
    | throw (IO.userError "coerced automatic profile rejected")
  let some closed := CompilerCoercedMethodProfile.certify compiled
    | throw (IO.userError "closed method catalog rejected")
  let make := rowOfObserved actual.makeRow.toObservedRow
  let keep := rowOfObserved actual.keepRow
  let shape : Tests.SourceCoreCoercionPublic.FactoryShape make.named.specialized.function
      original.makeSignature original.keepSignature original.parameter original.mark original.coercion :=
    actual.makeRow.same.symm ▸ actual.makeShape
  let identity : Tests.SourceCoreCoercionPublic.SelectedIdentityShape keep.named.specialized.function .bool :=
    actual.keepRow.same.symm ▸ actual.keepShape
  let ⟨makeResult⟩ ← observed (make.named.specialized.function.inferredBodyType = .function .unit .word) "coerced factory result"
  let ⟨makeBinder⟩ ← observed (shape.binder.scheme = .mono .bool) "coerced original make binder"
  let ⟨keepBinder⟩ ← observed (identity.binder.scheme = .mono .bool) "coerced original keep binder"
  let ⟨target⟩ ← observed (shape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation keep.named.specialized) "coerced complete direct instantiation"
  match resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram
      make.named.specialized.key make.named.specialized.assumptions with
  | .error error => throw (IO.userError (reprStr error))
  | .ok available =>
    match direct : SourceCompilationPlan.exactDirectCallRuntimeEvidence make.named.specialized shape.call.node available shape.call.instantiation with
    | .error error => throw (IO.userError (reprStr error))
    | .ok dictionary =>
      match authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence compiled.sourceProgram.signatures
          keep.named.specialized.key shape.call.instantiation.predicates dictionary with
      | .error error => throw (IO.userError (reprStr error))
      | .ok () =>
        let ⟨keepResolved⟩ ← (do
          match accepted : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram
              keep.named.specialized.key keep.named.specialized.assumptions with
          | .error error => throw (IO.userError (reprStr error))
          | .ok actual =>
            let ⟨same⟩ ← observed ((actual == dictionary) = true) "coerced ordered callee dictionary"
            return ⟨eq_of_beq same ▸ accepted⟩ : IO (PLift (
              SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram
                keep.named.specialized.key keep.named.specialized.assumptions = .ok dictionary)))
        match methodSelected : SourceCompilationPlan.checkedCoercionMethod compiled.sourceProgram make.named.specialized
            shape.call.node available shape.call.step with
        | .error error => throw (IO.userError (reprStr error))
        | .ok method =>
          match materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence compiled.sourceProgram
              make.named.specialized shape.call.node shape.call.step method with
          | .error error => throw (IO.userError (reprStr error))
          | .ok methodDictionary =>
            let ⟨methodMember⟩ ← observed (method.specialized ∈ compiled.indexed.base.plan.specializations) "coerced actual full method record"
            let methodShape ← Tests.SourceCoreCoercionPublic.observeMethod method.specialized.function method.synthetic
            let ⟨methodBinder⟩ ← observed (methodShape.binder.scheme = .mono .bool) "coerced method binder"
            let ⟨firstValue⟩ ← observed (methodShape.first.validated.value = Word.ofNatModulo 41) "coerced true result"
            let ⟨secondValue⟩ ← observed (methodShape.second.validated.value = Word.ofNatModulo 7) "coerced false result"
            return {
              recipe := original.recipe
              checked := checked
              seeds := original.seeds
              options := original.options
              facade := original.facadeCompiled
              accepted := by rw [original.sameProgram]; exact original.accepted
              selected := original.issued
              profile := profile
              closed := closed
              make := make
              keep := keep
              makeSignature := original.makeSignature
              keepSignature := original.keepSignature
              parameter := original.parameter
              mark := original.mark
              coercion := original.coercion
              shape := shape
              identity := identity
              makeResult := makeResult
              makeBinder := makeBinder
              keepBinder := keepBinder
              target := target
              available := available
              resolved := resolved
              dictionary := dictionary
              direct := direct
              authenticated := authenticated
              keepResolved := keepResolved
              method := method
              methodSelected := methodSelected
              methodDictionary := methodDictionary
              materialized := materialized
              methodMember := methodMember
              methodShape := methodShape
              methodBinder := methodBinder
              firstValue := firstValue
              secondValue := secondValue
            }

end Tests.SourceCoreSelectedCoercedDirect
