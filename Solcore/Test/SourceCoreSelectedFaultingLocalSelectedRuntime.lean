import Solcore.Test.SourceCoreSelectedFaultingLocalSelectedReflection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedFaultingLocal.FailureBridge
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

def selectedRuntime : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "local"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  let ⟨profile⟩ ← Tests.SourceCoreSelectedGeneralizedLocal.TypingValidation.observe
    (fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "faulting selected callable profile"
  let mut heaps : List Nat := []
  for flag in [true, false] do
    let started ← observeStarted fixture.original row.original.key [.bool flag]
    have sourcePlan := complete_from_source_selected fixture row shape flag typing started profile
    let actual ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match same : actual.val with
    | .failed token returned =>
      have _reflected := reflect_complete typing sourcePlan (same ▸ actual.property)
      unless returned.heapSize > started.session.heapSize do
        throw (IO.userError "selected Source-first fault lost heap effects")
      let .ok (some diagnostic) := returned.diagnostic row.original.key token
        | throw (IO.userError "selected Source-first fault diagnostic missing")
      unless (match diagnostic.error with | .uninitializedLocal _ => true | _ => false) do
        throw (IO.userError "selected Source-first absent-cell fault changed")
      heaps := heaps ++ [started.session.heapSize, returned.heapSize]
      IO.println s!"FAULTING_SELECTED_SOURCE_PUBLIC: flag={flag}, token={token.toNat}, heap={returned.heapSize}"
    | _ => throw (IO.userError "selected Source-first call did not fail")
  unless heaps == [2,17,2,17] do
    throw (IO.userError "selected Source-first exact public heaps changed")
  IO.println s!"FAULTING_SELECTED_SOURCE_HEAPS: {heaps}"
  IO.println "FAULTING_SELECTED_SOURCE_PUBLIC_PASS: originals1/cache1/selected-body1/checked-registry; Source-before-resume; semantic fault/reflection/reached heap/first history"

end Tests.SourceCoreSelectedFaultingLocal.FailureBridge
