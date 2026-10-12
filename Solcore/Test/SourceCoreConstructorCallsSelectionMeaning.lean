import Solcore.Test.SourceCoreConstructorCallsCommon
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputSelections
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicNestedOutputSelections

def outputMetadata {fixture : CompiledFixture} (observed : ObservedProgram fixture) : DataConstructorInstantiation :=
  ⟨observed.readShape.constructor.id, [], payloadTypes, containerType fixture.dataType⟩

def outputValue {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (first prior factory convert : SourceCorePublicValues.Handle) : SourceCorePublicValues.Value :=
  .constructed (outputMetadata observed) [.function first, .function prior, .function factory, .function convert]

def outputSelection {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (first prior factory convert : SourceCorePublicValues.Handle) :
    Selection (containerType fixture.dataType) (outputValue observed first prior factory convert) :=
  .constructed (.cons .function (.cons .function (.cons .function (.cons .function .nil))))

structure Collected {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (source : Dynamic.Value) (first prior factory convert : SourceCorePublicValues.Handle)
    (entries : List Entry) where
  newEntry : Entry
  priorEntry : Entry
  factoryEntry : Entry
  builtinEntry : Entry
  ordered : entries = [newEntry, priorEntry, factoryEntry, builtinEntry]
  newType : newEntry.sourceType = closureType
  priorType : priorEntry.sourceType = closureType
  factoryType : factoryEntry.sourceType = makerType
  builtinType : builtinEntry.sourceType = convertType
  newHandle : newEntry.handle = first
  priorHandle : priorEntry.handle = prior
  factoryHandle : factoryEntry.handle = factory
  builtinHandle : builtinEntry.handle = convert
  sourceValue : source = .constructed (outputMetadata observed)
    [newEntry.source, priorEntry.source, factoryEntry.source, builtinEntry.source]

theorem selected_uncast {checked : SourceCoreCompatibleCatalog.Checked}
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {type : TypeSystem.Ty} {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : Selection type first} {source : Dynamic.Value} {native : Core.Value}
    {nativeType : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected checked session (same ▸ selection : Selection type second)
      source native nativeType fuel entries) :
    Selected checked session selection source native nativeType fuel entries := by
  cases same
  exact selected

theorem selected_entries {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {source : Dynamic.Value} {first prior factory convert : SourceCorePublicValues.Handle}
    {native : Core.Value} {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : Selected checked session (outputSelection observed first prior factory convert)
      source native type fuel entries) :
    Nonempty (Collected observed source first prior factory convert entries) := by
  cases selected with
  | constructed projection children =>
    cases children with
    | more first tail =>
      cases first
      cases tail with
      | more prior tail =>
        cases prior
        cases tail with
        | more factory tail =>
          cases factory
          cases tail with
          | one builtin =>
            cases builtin
            exact ⟨⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end Tests.SourceCoreConstructorCalls
