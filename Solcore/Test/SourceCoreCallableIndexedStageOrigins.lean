import Solcore.SourceSemantics.CoreLowering.CallableIndexedStageOrigins
import Solcore.Test.SourceCoreCallableIndexedLambdaRuntimeBody

/-! Actual source receipts and compiler tables close function-leaf provenance
under one ambient model. These consumers retain the same formation completion;
contextual provenance requires the actual local-evidence factory receipt. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedStageOrigins
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaRuntimeValues CallableIndexedStageOrigins

abbrev actual_callsite_coverage := @actual_compiled_coverage
abbrev actual_original_formation := @CallableIndexedStageOrigins.formation
abbrev actual_original_completion := @reflects_original
abbrev actual_formation_receipt := @formation_receipt
abbrev actual_capture_condition := @formation_condition

section Model
variable {values : SourceCoreCompatibleValues.Context}
  (indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked)
  {checkedProgram : CheckedProgram} {support : SupportFamily indexed}
  {prior : SupportCondition indexed support}
  {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
  {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
  (accepted : SourceCoreStageCodebook.prepareWithProjection checkedProgram indexed.base.plan project limits firstId =
    .ok indexed.ancestry.graph.inputs.callable.table)
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
  {source : Dynamic.Value} {carrier : Value} {type : Ty}

include accepted in
theorem actual_function_leaf
    (related : RepresentsWith indexed support (provenanceCondition indexed checkedProgram support prior)
      mapping world sourceType source carrier type) :
    CallableLedger.OriginRep indexed.base.plan indexed.ancestry.graph.inputs.callable.table source carrier :=
  origin_of_represents indexed accepted related

include accepted in
theorem retained_parameter_order
    (related : CallableIndexedRetainedNamedValues.Represents indexed world sourceType source carrier type) :
    CallableLedger.OriginRep indexed.base.plan indexed.ancestry.graph.inputs.callable.table source carrier :=
  retained_origin indexed accepted related

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  (captured : Captures indexed mapping world scope function.captured actual)
  (code : Code indexed function scope captured.administrative) (history : History code) (body : support code)

theorem same_source_and_prior
    (condition : provenanceCondition indexed checkedProgram support prior captured code history body) :
    prior captured code history body ∧
    LambdaSourceAlignment.SourceReceipt checkedProgram indexed.base.plan
      code.compilation.owner code.active function.source ∧ NodeOccurrencesUnique function.source := condition

variable
  (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
    (captured : Captures indexed mapping world scope function.captured actual)
    (code : Code indexed function scope captured.administrative) (history : History code) (body : support code),
    prior captured code history body →
    ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
    prior (captured.extend maps worlds) code history body)

include stable in
theorem same_capture_extension
    (condition : provenanceCondition indexed checkedProgram support prior captured code history body)
    {futureMapping : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    provenanceCondition indexed checkedProgram support prior (captured.extend maps worlds) code history body :=
  provenance_stable indexed checkedProgram support prior stable captured code history body condition maps worlds

include stable in
theorem same_model_payload_origin (profile : values.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {sidecar : SourceCoreStageContracts.Sidecar}
    {site : SourceCoreCallableContracts.Callsite}
    (samePlan : sidecar.plan = indexed.base.plan)
    (sameTable : site.table = indexed.ancestry.graph.inputs.callable.table)
    (related : ValueRep values.checked registry
      (model indexed stable profile (checkedProgram := checkedProgram))
      mapping world sourceType source carrier type)
    (callable : Staging.CallBoundary.UserCallable source)
    (actualTable : SourceCoreStageCodebook.prepareWithProjection checkedProgram indexed.base.plan project limits firstId =
      .ok indexed.ancestry.graph.inputs.callable.table) :
    CallableLedger.OriginRep sidecar.plan site.table source carrier :=
  CompatibleAmbientStageOrigins.related_origin
    (function_origins indexed stable profile actualTable samePlan sameTable) related callable
end Model

section Contextual
variable {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
  {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
  {prepared : SourceCoreLocalEvidence.Prepared}

/-- A contextual receipt starts at the actual factory success. Native history
or a source type supplies none of these equalities. -/
theorem actual_contextual_source
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared)
    {sidecar : SourceCoreStageContracts.Sidecar}
    (selected : SourceCoreStageContracts.prepareSidecar plan candidate.origin.caller = .ok sidecar) :
    LambdaSourceAlignment.SourceReceipt program plan candidate.origin.caller prepared.substitution prepared.source ∧
    prepared.source = sidecar.source.applySubstitution prepared.substitution :=
  ⟨.contextual accepted, (LambdaSourceAlignment.SourceReceipt.contextual accepted).source selected⟩
end Contextual

section Boundaries
/-- Only function leaves are strengthened. Scalar representation still uses
its actual primitive representation without an origin hypothesis. -/
theorem scalar_keeps_no_origin
    {checked : SourceCoreCompatibleCatalog.Checked} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (mapping : LocationMap) (world : StoreTyping) (value : Bool) :
    ValueRep checked registry functions mapping world .bool (.bool value) (.bool value) .bool :=
  .bool value

/-- The origin augmentation retains exactly the prior condition on this Code. -/
theorem forget_only_prior
    {values : SourceCoreCompatibleValues.Context} {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
    {checkedProgram : CheckedProgram} {support : SupportFamily indexed} {prior : SupportCondition indexed support}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {actual : Environment} (captured : Captures indexed mapping world scope function.captured actual)
    (code : Code indexed function scope captured.administrative) (history : History code) (body : support code)
    (condition : provenanceCondition indexed checkedProgram support prior captured code history body) :
    prior captured code history body := condition.1
end Boundaries

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedStageOrigins
