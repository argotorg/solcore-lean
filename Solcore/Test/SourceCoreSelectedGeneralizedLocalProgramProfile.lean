import Solcore.Test.SourceCoreSelectedGeneralizedLocalFixture
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedProgramProfiles

/-! The unchanged original program retains a profile for every actual cached
named row. This packet certifies compiler syntax and preparation; original
declarative program typing remains a separate proof obligation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedGeneralizedLocal
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

structure ProfiledFixture where
  original : CompiledFixture
  originals : original.recipe.compiled.sourceProgram.functions.length = 1
  cached : original.recipe.compiled.indexed.base.functions.length = 1
  profiles : CellAwareNamedProgramProfiles.Profile original.recipe.compiled.indexed

def compileProfiledFixture : IO ProfiledFixture := do
  let original ← compileFixture
  if originals : original.recipe.compiled.sourceProgram.functions.length = 1 then
    if cached : original.recipe.compiled.indexed.base.functions.length = 1 then
      match CellAwareNamedProgramProfiles.profile? original.recipe.compiled.indexed with
      | none => throw (IO.userError "original generalized program profile rejected")
      | some profiles => pure ⟨original, originals, cached, profiles⟩
    else throw (IO.userError "original generalized full cache changed")
  else throw (IO.userError "original generalized source count changed")

theorem ProfiledFixture.ready (fixture : ProfiledFixture) :
    SourceCoreIndexedSession.Recipe.prepare fixture.original.recipe.compiled = .ok fixture.original.recipe := by
  obtain ⟨_, _, _, ready⟩ := RecursiveNamedPreparedStageContracts.public_compilation
    fixture.original.accepted fixture.original.selected
  exact ready

theorem ProfiledFixture.body (fixture : ProfiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared fixture.original.recipe.compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.original.recipe.compiled
      (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    {entry : SourceCoreCallableIndexedPrograms.Entry fixture.original.recipe.compiled.indexed.layouts}
    (member : entry ∈ fixture.original.recipe.compiled.indexed.entries) :
    Nonempty (CellAwareNamedBodySupport.Body prepared.compilation
      (CellAwareNamedBodyProducer.Certificate prepared.compilation)
      (RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial fixture.original.recipe.compiled.compatible.checked) header)
      header.context header.function.resultType) := by
  obtain ⟨profile⟩ := fixture.profiles.at_slot prepared.selected
  exact CellAwareNamedBodyReceipt.of_header prepared aligned fixture.ready wellFormed member
    (profile.for_compilation prepared.compilation)

def checkProgramProfile : IO Unit := do
  let _fixture ← compileProfiledFixture
  IO.println "GENERALIZED_LOCAL_COMPLETE_STATIC_INVENTORY: originals1/cache1/profile1"

end Tests.SourceCoreSelectedGeneralizedLocal
