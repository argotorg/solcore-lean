import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCompilerChildCollector

/-! One reusable static qualification facet restricts the positive prepared
closure leaves before payload or heap construction. Ordinary and Principal
Supports keep their original distinct authority. Map/world extension copies the
same Code and Support, so every qualification is preserved directly. Generic
ValueRep and GenericHeap operations use this function model without another
copy of allocation, write or payload recursion APIs. A concrete semantic family
must instantiate both facets from actual compiler collectors; an arbitrary
qualification, or the unrestricted prepared prototype, proves no body meaning.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualQualification
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualCellOrigins (Association)

/-- Qualification concerns the actual immutable compiler packet. It has no
execution, completion, grade or certificate-to-meaning field. Principal support
already contains its selected method, dictionary and cached compilation. -/
structure Facet (compiled : SourceCoreUnifiedCompilation.Compiled) where
  ordinary : ∀ {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context},
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code → Prop
  principal : ∀ {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context},
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code → Prop

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (facet : Facet compiled)
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

/-- Qualification inspects only the actual positive receipt's own Code and
Support. It cannot select or recover another body from the carrier's type. -/
def Association.Qualified
    (association : Association headers keys bodyRegistry faults mapping world function native bindings parameter result) : Prop := by
  cases association with
  | ordinary receipt =>
    cases receipt with
    | ordinary owner captured code history support actualSites sites origin prepared prefixContext globals referenceIndex typed =>
      exact facet.ordinary code support
  | principal receipt =>
    cases receipt with
    | principal owner captured code history support actualSites sites origin prepared globals leading referenceIndex typed =>
      exact facet.principal code support

/-- The original extension changes captures and runtime typing only. Static
qualification sees exactly the original Code, Support and selected authority. -/
theorem Association.Qualified.extend
    (association : Association headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (qualified : Association.Qualified facet association)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association.Qualified facet (association.extend maps worlds) := by
  cases association with
  | ordinary receipt =>
    cases receipt with
    | ordinary owner captured code history support actualSites sites origin prepared prefixContext globals referenceIndex typed =>
      exact qualified
  | principal receipt =>
    cases receipt with
    | principal owner captured code history support actualSites sites origin prepared globals leading referenceIndex typed =>
      exact qualified

/-- The proof is retained beside the exact prepared Association under Type;
public source-shaped membership exposes it under Nonempty. -/
structure QualifiedAssociation
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) where
  association : Association headers keys bodyRegistry faults mapping world function native bindings parameter result
  qualified : Association.Qualified facet association

def QualifiedAssociation.extend
    (member : QualifiedAssociation facet headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    QualifiedAssociation facet headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameter result :=
  ⟨member.association.extend maps worlds, Association.Qualified.extend facet member.association member.qualified maps worlds⟩

abbrev StaticMember
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Prop :=
  Nonempty (QualifiedAssociation facet headers keys bodyRegistry faults mapping world function native bindings parameter result)

theorem StaticMember.forget
    (member : StaticMember facet headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedContextualCellOrigins.StaticMember headers keys bodyRegistry faults
      mapping world function native bindings parameter result := by
  obtain ⟨member⟩ := member
  exact ⟨member.association⟩

theorem StaticMember.extend
    (member : StaticMember facet headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    StaticMember facet headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameter result := by
  obtain ⟨member⟩ := member
  exact ⟨member.extend facet maps worlds⟩

/-- The same original global and builtin authority is preserved. Only closure
leaves acquire the static qualification, at their actual positive constructor. -/
inductive FunctionOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | closure {function : Dynamic.Closure} {native : Value}
      {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
      (member : StaticMember facet headers keys bodyRegistry faults mapping world function native bindings parameter result) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        (FunctionValues.sourceType function) (.closure function) native (CallableContract.functionType parameter result)
  | global {function : Dynamic.GlobalFunction} {sourceType : TypeSystem.Ty} {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world sourceType (.global function) native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world sourceType (.global function) native type
  | builtin {function : Dynamic.BuiltinFunction} {sourceType : TypeSystem.Ty} {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world sourceType (.builtin function) native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world sourceType (.builtin function) native type

theorem FunctionOrigins.forget {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {type : Ty}
    (origin : FunctionOrigins facet headers keys bodyRegistry faults mapping world sourceType source native type) :
    CallableIndexedOwnedPreparedContextualCellOrigins.FunctionOrigins headers keys bodyRegistry faults
      mapping world sourceType source native type := by
  cases origin with
  | closure member => exact .closure (member.forget facet)
  | global related => exact .global related
  | builtin related => exact .builtin related

/-- The receiving registry is independent of the body's preparation registry.
All runtime type/projection facts are the existing forward facts. -/
def functions
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => FunctionOrigins facet headers keys bodyRegistry faults mapping world
  projection := fun origin =>
    (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile).projection
      (registry := bodyRegistry) (origin.forget facet)
  runtime_hasType := fun origin =>
    (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile).runtime_hasType
      (registry := bodyRegistry) (origin.forget facet)
  source_function := fun origin =>
    (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile).source_function
      (registry := bodyRegistry) (origin.forget facet)
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type
      origin registries maps worlds
    cases origin with
    | closure member => exact .closure (member.extend facet maps worlds)
    | global related =>
      exact .global ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
        related registries maps worlds)
    | builtin related =>
      exact .builtin ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
        related registries maps worlds)

theorem functions_include_prepared (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (functions facet headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile) :=
  fun origin => origin.forget facet

/-- The generic recursive payload and heap relations carry the qualification
through every nested function leaf. Their existing generic operations apply. -/
abbrev PayloadOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  ValueRep compiled.compatible.checked registry (functions facet headers keys bodyRegistry faults profile)

abbrev CellOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (functions facet headers keys bodyRegistry faults profile)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualQualification
