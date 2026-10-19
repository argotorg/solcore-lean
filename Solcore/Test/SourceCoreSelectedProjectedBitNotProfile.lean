import Solcore.Test.SourceCoreSelectedProjectedBitNotCapturedSourceFirst

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProjectedBitNot
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def findKey (program : CheckedProgram) (name : String) : IO SourceCoreExecution.Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError "missing function")
private def word (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n)
private def table (entries : List (Nat × Nat)) : SourceCorePublicValues.Value :=
  .mapping .word .word (entries.map fun pair => (word pair.1, word pair.2))
private def complement (n : Nat) : SourceCorePublicValues.Value := .word (Word.ofNatModulo n).bitNot
private def complemented (entries : List (Nat × Nat)) (key : Nat) (value : Nat) : SourceCorePublicValues.Value :=
  .mapping .word .word ((word key, complement value) :: entries.map (fun pair => (word pair.1, word pair.2)))
private def nested : SourceCorePublicValues.Value :=
  .mapping .word mappingType [(word 7, table [(2, 4)])]

private def success {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) :
    IO (SourceCoreExecution.Session artifact) := do
  let pending ← get "projected startup" (session.start key arguments)
  let .outOfFuel suspended ← pending.resume 0 0
    | throw (IO.userError "projected zero fuel did not suspend")
  let .succeeded completed ← suspended.resume 100000 1000
    | throw (IO.userError "projected success missing")
  require (completed.value == expected) "projected result changed"
  pure completed.session

private def failure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreExecution.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (SourceCoreExecution.Session artifact) := do
  let pending ← get "projected fault startup" (session.start key arguments)
  let .failed reason after ← pending.resume 100000 1000
    | throw (IO.userError "projected original read did not fail")
  let some diagnostic ← get "projected diagnostic" (after.diagnostic key reason)
    | throw (IO.userError "projected diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "projected original read diagnostic changed"
  pure after

/-- The unchanged thirteen-declaration program has a complete checked profile.
Independent Source proofs cover fresh mapping inputs, the returned captured
handle, and two retained calls. The twelve-entry named/header regression remains. -/
def run : IO Unit := do
  let proofFixture ← compileNamedHeaderFixture
  let observed ← observeProgram proofFixture
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      proofFixture.recipe.compiled proofFixture.checked
    | throw (IO.userError "projected bit-not named/header selected profile rejected")
  require (proofFixture.recipe.compiled.sourceProgram.functions.length == 13 &&
      proofFixture.recipe.compiled.indexed.base.functions.length == 12 && profile.table.rows.length == 12)
    "projected bit-not selected originals/cache/table changed"
  let initialMap ← observeStarted proofFixture observed.invertRow.original.key
    [publicMap [(Word.ofNatModulo 7, Word.ofNatModulo 4), (Word.ofNatModulo 7, Word.ofNatModulo 99)], word 7]
  have _initialMapProof := initial_unary_from_source observed.invertRow profile observed.invertShape
    (Word.ofNatModulo 7) (Word.ofNatModulo 4) [(Word.ofNatModulo 7, Word.ofNatModulo 99)] initialMap
  let .succeeded mapped ← initialMap.call.checkpoint.resume 100000 1000
    | throw (IO.userError "initial mapping call failed")
  require (mapped.value == complemented [(7,99)] 7 4) "initial mapping first-match output changed"
  let initialDefault ← observeStarted proofFixture observed.invertRow.original.key [publicMap [], word 9]
  have _initialDefaultProof := initial_default_from_source observed.invertRow profile observed.invertShape
    (Word.ofNatModulo 9) initialDefault
  let .succeeded defaulted ← initialDefault.call.checkpoint.resume 100000 1000
    | throw (IO.userError "initial empty mapping call failed")
  require (defaulted.value == complemented [] 9 0) "initial mapping default changed"
  let initialMissing ← observeStarted proofFixture observed.missingRow.original.key
    [publicMap [(Word.ofNatModulo 7, Word.ofNatModulo 4)], word 7]
  have _initialMissingProof := initial_missing_from_source observed.missingRow profile observed.missingShape
    (Word.ofNatModulo 7) (Word.ofNatModulo 4) [] initialMissing
  let .failed reason failed ← initialMissing.call.checkpoint.resume 100000 1000
    | throw (IO.userError "initial mapping key did not fail")
  let some diagnostic ← get "initial mapping diagnostic" (failed.diagnostic observed.missingRow.original.key reason)
    | throw (IO.userError "initial mapping diagnostic missing")
  require (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
    "initial mapping fault changed"
  let reused ← success failed observed.invertRow.original.key [table [(7,4)], word 7] (complemented [] 7 4)
  let initialDataHeaps := [initialMap.session.heapSize, mapped.session.heapSize,
    initialDefault.session.heapSize, defaulted.session.heapSize,
    initialMissing.session.heapSize, failed.heapSize, reused.heapSize]
  require (initialDataHeaps == [13,28,13,28,13,22,37]) "initial mapping exact native heaps changed"
  IO.println s!"PROJECTED_BITNOT_INITIAL_DATA_HEAPS: {initialDataHeaps}"
  let proofStarted ← observeStarted proofFixture observed.keyRow.original.key [word 7]
  have _sourceFirst := initial_then_invert proofFixture observed profile proofStarted
    (Word.ofNatModulo 7) (Word.ofNatModulo 4)
    [(Word.ofNatModulo 7, Word.ofNatModulo 99), (Word.ofNatModulo 2, Word.ofNatModulo 6)]
  let .outOfFuel proofSuspended ← proofStarted.call.checkpoint.resume 0 0
    | throw (IO.userError "projected bit-not selected initial suspension")
  let .succeeded proofInitial ← proofSuspended.resume 100000 1000
    | throw (IO.userError "projected bit-not selected initial helper")
  require (proofInitial.value == word 7) "projected selected initial helper changed"
  let proofAfter ← success proofInitial.session observed.invertRow.original.key
    [table [(7,4),(7,99),(2,6)], word 7] (complemented [(7,99),(2,6)] 7 4)
  let proofMissing ← findKey proofFixture.recipe.compiled.sourceProgram "keyFailure"
  let proofFailed ← failure proofAfter proofMissing [table [(7,4)], word 7]
  let proofReused ← success proofFailed observed.invertRow.original.key
    [table [(7,4)], word 7] (complemented [] 7 4)
  let proofHeaps := [proofStarted.session.heapSize, proofInitial.session.heapSize,
    proofAfter.heapSize, proofFailed.heapSize, proofReused.heapSize]
  require (proofHeaps == [13,19,34,43,58]) "projected selected exact native heaps changed"
  IO.println s!"PROJECTED_BITNOT_SELECTED_CACHE: originals13/cache12/table{profile.table.rows.length}; genuine key failure and same-session reuse passed"
  IO.println s!"PROJECTED_BITNOT_SELECTED_NATIVE_HEAPS: {proofHeaps}"

  let fixture ← compileFixture
  have _sameOriginal : fixture.recipe.compiled.sourceProgram = proofFixture.recipe.compiled.sourceProgram :=
    Except.ok.inj (fixture.checked.symm.trans proofFixture.checked)
  require (fixture.recipe.compiled.sourceProgram.functions.length == 13 &&
      fixture.recipe.compiled.indexed.base.functions.length == 13)
    "projected bit-not complete original cache changed"
  let some fullProfile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile
      fixture.recipe.compiled fixture.checked
    | throw (IO.userError "captured projected unary complete profile rejected")
  require (fullProfile.table.rows.length == 13) "captured complete profile table changed"
  let factory ← Captured.observeFactory fixture
  let capturedStarted ← observeStarted fixture factory.row.original.key
    [publicMap [(Word.ofNatModulo 7, Word.ofNatModulo 4)]]
  have _capturedSourceChain := Captured.from_checked_initial fixture factory fullProfile
    (Word.ofNatModulo 7) (Word.ofNatModulo 4) [] capturedStarted
  let .outOfFuel capturedSuspended ← capturedStarted.call.checkpoint.resume 0 0
    | throw (IO.userError "captured mapping initial suspension")
  let .succeeded capturedMade ← capturedSuspended.resume 100000 1000
    | throw (IO.userError "captured mapping initial factory failed")
  let .function capturedHandle := capturedMade.value
    | throw (IO.userError "captured mapping initial handle missing")
  let capturedPending ← get "captured mapping retained first"
    (capturedMade.session.startHandlePacked capturedHandle (word 7))
  let .outOfFuel capturedFirstSuspended ← capturedPending.resume 0 0
    | throw (IO.userError "captured mapping retained first suspension")
  let .succeeded capturedFirst ← capturedFirstSuspended.resume 100000 1000
    | throw (IO.userError "captured mapping retained first failed")
  let capturedAgain ← get "captured mapping retained second"
    (capturedFirst.session.startHandlePacked capturedHandle (word 7))
  let .succeeded capturedRestored ← capturedAgain.resume 100000 1000
    | throw (IO.userError "captured mapping retained restore failed")
  require (capturedFirst.value == complement 4 && capturedRestored.value == word 4)
    "captured mapping same-handle complement/restore changed"
  let capturedHeaps := [capturedStarted.session.heapSize, capturedMade.session.heapSize,
    capturedFirst.session.heapSize, capturedRestored.session.heapSize]
  require (capturedHeaps == [14,17,32,47]) "captured mapping exact native heaps changed"
  IO.println s!"PROJECTED_BITNOT_CAPTURED_SOURCE_CHAIN_HEAPS: {capturedHeaps}"
  let keyRow ← observeRow fixture "key"
  let started ← observeStarted fixture keyRow.original.key [word 7]
  let .outOfFuel suspended ← started.call.checkpoint.resume 0 0
    | throw (IO.userError "projected bit-not initial suspension")
  let .succeeded initial ← suspended.resume 100000 1000
    | throw (IO.userError "projected bit-not initial helper")
  require (initial.value == word 7) "projected initial helper changed"
  let program := fixture.recipe.compiled.sourceProgram
  let recipe := fixture.recipe
  let mut session := initial.session
  let mut heaps := [started.session.heapSize, initial.session.heapSize]
  for (name, arguments, expected) in [
      ("invert", [table [(7,4),(7,99),(2,6)], word 7], complemented [(7,99),(2,6)] 7 4),
      ("invert", [table [], word 9], complemented [] 9 0),
      ("nested", [nested, word 7, word 2], complement 4),
      ("effects", [table [(7,4)], word 7], complemented [] 7 4),
      ("initialize", [table [], word 7], complemented [] 7 0),
      ("post", [table []], complemented [] 0 0),
      ("stop", [table []], table []),
      ("defaultLocal", [], complement 0)] do
    let key ← findKey recipe.compiled.sourceProgram name
    session ← success session key arguments expected
    heaps := heaps ++ [session.heapSize]
  for (name, arguments) in [
      ("keyFailure", [table [(7,4)], word 7]),
      ("calledKeyFailure", [table [(7,4)], word 7]),
      ("nestedFailure", [nested, word 7, word 2])] do
    let key ← findKey recipe.compiled.sourceProgram name
    session ← failure session key arguments
    heaps := heaps ++ [session.heapSize]
  let invert ← findKey program "invert"
  session ← success session invert [table [(7,4)], word 7] (complemented [] 7 4)
  heaps := heaps ++ [session.heapSize]
  let make ← findKey recipe.compiled.sourceProgram "make"
  let pending ← get "projected captured factory" (session.start make [table [(7,4)]])
  let .succeeded made ← pending.resume 100000 1000
    | throw (IO.userError "projected captured factory failed")
  let .function handle := made.value | throw (IO.userError "projected captured handle missing")
  let pending ← get "projected captured first" (made.session.startHandlePacked handle (word 7))
  let .succeeded first ← pending.resume 100000 1000
    | throw (IO.userError "projected captured first failed")
  let pending ← get "projected captured reuse" (first.session.startHandlePacked handle (word 7))
  let .succeeded last ← pending.resume 100000 1000
    | throw (IO.userError "projected captured reuse failed")
  require (first.value == complement 4 && last.value == word 4) "projected captured result changed"
  heaps := heaps ++ [made.session.heapSize, first.session.heapSize, last.session.heapSize]
  require (heaps == [14,20,35,50,83,104,120,136,143,158,167,182,206,221,224,239,254])
    "projected bit-not exact native heaps changed"
  IO.println s!"PROJECTED_BITNOT_COMPLETE_PROFILE: originals13/cache{recipe.compiled.indexed.base.functions.length}/table{fullProfile.table.rows.length}; captured Source/public complement and restore"
  IO.println s!"PROJECTED_BITNOT_NATIVE_HEAPS: {heaps}"
  IO.println "PROJECTED_BITNOT_COMPILER_PROFILE_FORWARD_PASS"

end Tests.SourceCoreSelectedProjectedBitNot
