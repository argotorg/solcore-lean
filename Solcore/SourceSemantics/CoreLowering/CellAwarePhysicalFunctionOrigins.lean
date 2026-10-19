import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCallableOrigins

/-! Positive callable leaves for heaps containing generalized descriptors.
A materialized local keeps its actual read wrapper and Source instantiation;
there is no projection of that branch to an older lexical closure history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePhysicalFunctionOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

inductive FunctionOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | ordinary {sourceType source native type}
      (retained : CallableIndexedOwnedPreparedPhysicalCellOrigins.FunctionOrigins
        headers keys bodyRegistry faults mapping world sourceType source native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world sourceType source native type
  | generalized {function native bindings parameter result}
      (member : GeneralizedLocalMaterializedAssociation.Association compiled
        mapping world function native bindings parameter result)
      (owner : OwnedKey keys) (framed : member.AtFrame owner.key.frameLocation) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        (FunctionValues.sourceType function) (.closure function) native
        (CallableContract.functionType parameter result)

def functions (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => FunctionOrigins headers keys bodyRegistry faults mapping world
  projection := by
    intro registry mapping world sourceType source native type related
    cases related with
    | ordinary retained =>
      exact (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile).projection
        (registry := registry) retained
    | generalized member _ _ => exact member.projection
  runtime_hasType := by
    intro registry mapping world sourceType source native type related
    cases related with
    | ordinary retained =>
      exact (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile).runtime_hasType
        (registry := registry) retained
    | generalized member _ _ => exact member.runtime_hasType
  source_function := by
    intro registry mapping world sourceType source native type related
    cases related with
    | ordinary retained =>
      exact (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile).source_function
        (registry := registry) retained
    | generalized => exact .closure _
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type
      related registries maps worlds
    cases related with
    | ordinary retained =>
      exact .ordinary ((CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile).extend
        retained registries maps worlds)
    | generalized member owner framed =>
      exact .generalized (member.extend maps worlds) owner (by cases member; exact framed)

theorem includes_prepared (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile).Includes
      (functions headers keys bodyRegistry faults profile) := fun represented => .ordinary represented

theorem runtime_views (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (functions headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type related
  cases related with
  | ordinary retained => exact CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile (registry := registry) retained
  | generalized => exact (Dynamic.ValueRuntimeType.closure _).matches

theorem observations (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionObservations compiled.compatible.checked.catalog (functions headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type related
  cases related with
  | ordinary retained => exact CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile retained
  | generalized member _ _ =>
    cases member with
    | viewed material view typed => exact .contractedAnonymous _ _ _ _ _ profile

theorem builtin (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (represented : ValueRep compiled.compatible.checked registry
      (functions headers keys bodyRegistry faults profile) mapping world sourceType source native type) :
    ∀ function, source = .builtin function →
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        mapping world sourceType (.builtin function) native type := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    cases related with
    | ordinary retained =>
      exact SelectedCompilationBuiltinFunctionOrigins.prepared_builtin profile (.function retained)
    | generalized => intro function impossible; cases impossible
  | compatible same _ ih =>
    intro function selected
    exact .compatible same (ih function selected)
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

theorem stage_origin (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (represented : ValueRep compiled.compatible.checked registry
      (functions headers keys bodyRegistry faults profile) mapping world sourceType source native type) :
    IsFunction source → CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table source native := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    intro shape
    cases related with
    | ordinary retained => exact SelectedCompilationCallableOrigins.prepared_origin profile (registry := registry) (.function retained) shape
    | generalized member _ _ => exact member.stage_origin
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

instance origins (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry faults profile
      (functions headers keys bodyRegistry faults profile) where
  toErasesBuiltinsToContextual := ⟨fun represented => builtin profile represented _ rfl⟩
  origin := stage_origin profile

end Solcore.SourceSemantics.CoreLowering.CellAwarePhysicalFunctionOrigins
