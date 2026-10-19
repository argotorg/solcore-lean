import Solcore.Test.SourceCoreSelectedGeneralizedLocalPublic

/-! The complete original checked cache supplies the concrete Source-first
initial public proof. Repeated returned-session calls are runtime companions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The finite scanner retains every actual cached named row. -/
def checkProfile : IO Unit := do
  let _fixture ← compileProfiledFixture
  IO.println "GENERALIZED_LOCAL_ORIGINAL_PROFILE: originals1/cache1/profile1"

/-- Original source typing and its independent execution proof are assembled
before the first target resume. Later calls reuse that exact returned session. -/
def run : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "local"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  if callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true then
    let started ← observeStarted fixture.original row.original.key [.bool true]
    have _sourceFirst : ∃ selected : SelectedInventory fixture row,
        Nonempty (InitialForward selected shape true started callableProfile) := by
      obtain ⟨selected⟩ := fixture.inventory row typing.wellFormed
      exact ⟨selected, initial_from_source selected shape true typing started callableProfile⟩
    let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
      | throw (IO.userError "generalized initial zero fuel did not suspend")
    let .succeeded returned ← suspended.resume 100000 10000
      | throw (IO.userError "generalized initial public execution failed")
    require (returned.value == .product (.word (Word.ofNatModulo 11)) (.bool true))
      "generalized initial Source value changed"
    let mut session := returned.session
    let mut heaps := [started.session.heapSize, session.heapSize]
    match session.start row.original.key [.word (Word.ofNatModulo 1)] runOptions.inputValidationFuel with
    | .ok _ => throw (IO.userError "generalized raw Bool input boundary changed")
    | .error _ => pure ()
    for flag in [false,true] do
      match ← session.run row.original.key [.bool flag] runOptions with
      | .ok (.succeeded completed) =>
        require (completed.value == .product (.word (Word.ofNatModulo 11)) (.bool flag))
          "generalized retained-session Source value changed"
        session := completed.session
        heaps := heaps ++ [session.heapSize]
      | _ => throw (IO.userError "generalized retained-session invocation failed")
    require (heaps == [2,14,26,38]) "generalized exact native heaps changed"
    IO.println "GENERALIZED_LOCAL_COMPLETE_PROFILE: originals1/cache1/profile1"
    IO.println "GENERALIZED_LOCAL_SOURCE_FIRST: original typed body to actual initial public output"
    IO.println s!"GENERALIZED_LOCAL_REUSE_NATIVE_HEAPS: {heaps}"
    IO.println "GENERALIZED_LOCAL_COMPILER_PROFILE_FORWARD_PASS"
  else throw (IO.userError "generalized actual callable catalog disabled")

end Tests.SourceCoreSelectedGeneralizedLocal
