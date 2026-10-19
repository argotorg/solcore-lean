import Solcore.Test.SourceCoreSelectedGeneralizedLocalObserved

/-! Each runtime request constructs its independent Source continuation before
resuming, then retains the exact receipt returned by that one public action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal.ObservedRuntime
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationPublicSessionState (StartedCall)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {shape : Shape row.original.function.typedBody}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}

def CertifiedSession (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody)
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact) : Prop :=
  ∃ (selected : SelectedInventory fixture row)
    (firstStart : Started fixture.original row.original.key [.bool true])
    (first : InitialForward selected shape true firstStart callableProfile),
    Nonempty (first.Retained session [])

def Planned (fixture : ProfiledFixture) (row : Row fixture.original)
    (shape : Shape row.original.function.typedBody)
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (flag : Bool) (call : StartedCall session row.original.key [.bool flag] runOptions) : Prop :=
  ∃ (selected : SelectedInventory fixture row)
    (firstStart : Started fixture.original row.original.key [.bool true])
    (first : InitialForward selected shape true firstStart callableProfile)
    (retained : first.Retained session []), Nonempty (NextForward first retained flag call)

/-- Only the previous public history and the actual new input are used. -/
theorem plan (certified : CertifiedSession fixture row shape callableProfile session)
    (typing : OriginalTyping fixture.original) (flag : Bool)
    (call : StartedCall session row.original.key [.bool flag] runOptions) :
    Planned fixture row shape callableProfile flag call := by
  obtain ⟨selected, firstStart, first, ⟨retained⟩⟩ := certified
  exact ⟨selected, firstStart, first, retained, next_from_source first retained flag typing call⟩

/-- The observation belongs to the exact call whose Source proof was planned. -/
theorem retained {flag : Bool} {call : StartedCall session row.original.key [.bool flag] runOptions}
    (planned : Planned fixture row shape callableProfile flag call)
    (typing : OriginalTyping fixture.original)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    CertifiedSession fixture row shape callableProfile returned.session := by
  obtain ⟨selected, firstStart, first, previous, ⟨next⟩⟩ := planned
  exact ⟨selected, firstStart, first, next.observed_retained typing resumed⟩

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def observeCall {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (key : SourceCoreIndexedSession.Key) (flag : Bool) : IO (StartedCall session key [.bool flag] runOptions) := do
  match started : session.start key [.bool flag] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint => pure ⟨checkpoint, started⟩

/-- Three calls use the actual current session and an independently constructed
Source proof before every resume. All three observed heaps retain those proofs. -/
def run : IO Unit := do
  let fixture ← compileProfiledFixture
  let row ← observeRow fixture.original "local"
  let shape ← observeShape row.original.function.typedBody
  let typing ← observeOriginalTyping fixture.original
  if callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true then
    let firstStart ← observeStarted fixture.original row.original.key [.bool true]
    have firstPlan : ∃ selected : SelectedInventory fixture row,
        Nonempty (InitialForward selected shape true firstStart callableProfile) := by
      obtain ⟨selected⟩ := fixture.inventory row typing.wellFormed
      exact ⟨selected, initial_from_source selected shape true typing firstStart callableProfile⟩
    let firstObserved ← firstStart.call.checkpoint.resumeWithReceipt 100000 10000
    match firstResult : firstObserved.val with
    | .succeeded firstReturned =>
      have firstReceipt := firstResult ▸ firstObserved.property
      have firstCertified : CertifiedSession fixture row shape callableProfile firstReturned.session := by
        obtain ⟨selected, ⟨first⟩⟩ := firstPlan
        exact ⟨selected, firstStart, first, first.observed_retained typing firstReceipt⟩
      require (firstReturned.value == .product (.word (Word.ofNatModulo 11)) (.bool true))
        "first generalized retained Source value changed"
      let secondCall ← observeCall firstReturned.session row.original.key false
      have secondPlan := plan firstCertified typing false secondCall
      let secondObserved ← secondCall.checkpoint.resumeWithReceipt 100000 10000
      match secondResult : secondObserved.val with
      | .succeeded secondReturned =>
        have secondReceipt := secondResult ▸ secondObserved.property
        have secondCertified := retained secondPlan typing secondReceipt
        require (secondReturned.value == .product (.word (Word.ofNatModulo 11)) (.bool false))
          "second generalized retained Source value changed"
        let thirdCall ← observeCall secondReturned.session row.original.key true
        have thirdPlan := plan secondCertified typing true thirdCall
        let thirdObserved ← thirdCall.checkpoint.resumeWithReceipt 100000 10000
        match thirdResult : thirdObserved.val with
        | .succeeded thirdReturned =>
          have thirdReceipt := thirdResult ▸ thirdObserved.property
          have _thirdCertified := retained thirdPlan typing thirdReceipt
          require (thirdReturned.value == .product (.word (Word.ofNatModulo 11)) (.bool true))
            "third generalized retained Source value changed"
          let heaps := [firstStart.session.heapSize, firstReturned.session.heapSize,
            secondReturned.session.heapSize, thirdReturned.session.heapSize]
          require (heaps == [2,14,26,38]) "generalized Source-certified repeated native heaps changed"
          IO.println "GENERALIZED_RETAINED_SOURCE_PUBLIC: originals1/cache1/typing1/profile1; proof before every resume"
          IO.println s!"GENERALIZED_RETAINED_SOURCE_HEAPS: {heaps}"
          IO.println "GENERALIZED_RETAINED_SOURCE_PUBLIC_PASS"
        | _ => throw (IO.userError "third generalized certified call did not succeed")
      | _ => throw (IO.userError "second generalized certified call did not succeed")
    | _ => throw (IO.userError "first generalized certified call did not succeed")
  else throw (IO.userError "generalized callable catalog disabled")

end Tests.SourceCoreSelectedGeneralizedLocal.ObservedRuntime
