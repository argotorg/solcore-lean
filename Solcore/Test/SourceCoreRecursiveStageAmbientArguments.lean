import Solcore.SourceSemantics.CoreLowering.RecursiveStageArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveStagePrimitiveMeaning
import Solcore.Test.SourceRecursiveStageTupleExpressions
import Solcore.Test.SourceCoreRecursiveStagePrimitiveMeaning

/-! The actual primitive receipts supply the staged child meanings for an
ambient argument pack. No child execution premise is added. Ordered effects and
the original semantic fault survive; stage guards remain a separate interface. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 32768
namespace Tests.SourceCoreRecursiveStageAmbientArguments
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly

abbrev semanticFaults (faults : FunctionCalls.FaultRep) : RecursiveStageMeaning.FaultRep
  | .semantic reason, token => faults reason token
  | .stage _ _ _, _ => False

def Children (fuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate := fun scope id code =>
  ∃ tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id code,
    RecursiveStagePrimitiveMeaning.Supported tree

section Actual
variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source) (sameLedger : context.solvedRequirements = solved)
  (runtime : RuntimeRequirementLedgerValid context) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include sameSource sameLedger runtime uninitialized in
theorem primitive_reflects :
    RecursiveStageMeaning.ReflectsFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Children fuel values source context solved reasonAt) (semanticFaults faults) := by
  intro scope id code certified node found mapping world admin environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  obtain ⟨tree, supported⟩ := certified
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, metadata⟩ :=
    RecursiveStagePrimitiveMeaning.reflects functions program stages invocation sameSource uninitialized sameLedger runtime
      supported found environments heaps locals agrees evaluated
  refine ⟨outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds, preserved, metadata⟩
  cases represented with
  | value payload => exact .value payload
  | fault reason => exact .fault reason

include sameSource sameLedger runtime uninitialized in
theorem primitive_preserves (unique : NodeOccurrencesUnique source)
    (extension : SourceCoreRawMetadata.Extends values.registry registry) :
    RecursiveStageMeaning.PreservesFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program stages invocation context (Children fuel values source context solved reasonAt) (semanticFaults faults) := by
  intro scope id code certified node found mapping world admin environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  obtain ⟨tree, supported⟩ := certified
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata⟩ :=
    RecursiveStagePrimitiveMeaning.preserves functions program stages invocation sameSource unique uninitialized
      extension sameLedger runtime supported found environments heaps locals agrees trace
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, preserved, metadata⟩
  cases represented with
  | value payload => exact .value payload
  | fault reason => exact .fault reason

variable {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}
  (tree : DataExpressionSequence.Tree invocation.source (Children fuel values source context solved reasonAt) scope ids types codes)

include sameSource sameLedger runtime uninitialized tree in
theorem pack_reflects
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expressions program stages invocation context environment before ids outcome after ∧
      RecursiveStageArguments.ResultFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld types codes (semanticFaults faults) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  RecursiveStageArguments.reflects_for tree
    (primitive_reflects functions program stages invocation sameSource sameLedger runtime uninitialized)
    environments heaps locals agrees evaluated

include sameSource sameLedger runtime uninitialized tree in
theorem pack_preserves (unique : NodeOccurrencesUnique source)
    (extension : SourceCoreRawMetadata.Extends values.registry registry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.ValuesOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Staging.Recursive.Expressions program stages invocation context environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      RecursiveStageArguments.ResultFor (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld types codes (semanticFaults faults) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, preserved, metadata⟩ :=
    RecursiveStageArguments.preserves_for tree
      (primitive_preserves functions program stages invocation sameSource sameLedger runtime uninitialized unique extension)
      environments heaps locals agrees trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, preserved, metadata⟩
end Actual

section Static
variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode} {code : SourceCoreBasic.LoweredExpr}

theorem literal_child (receipt : CompatibleExpressionLiteralRuntime.Certificate solved source id code) :
    Children fuel values source context solved reasonAt scope id code :=
  ⟨.product (.literal receipt.forget), .product _ (.literal receipt.forget
    (RecursiveStagePrimitiveMeaning.literal_of_certificate receipt))⟩

/-- Successful production lowering supplies the same numeric selection receipt. -/
theorem accepted_child {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {budget : Nat} {compilation : SourceCoreFunctions.Context}
    (found : source.lookupExpression? id = some node) (atomic : CompatibleExpressionLiterals.Atomic node.form)
    (unitType : node.form = .tuple [] → node.type = .unit)
    (special : ∀ child remaining, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child remaining source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt = .ok code) :
    Children fuel values source context compilation.solvedRequirements reasonAt scope id code :=
  literal_child (CompatibleExpressionLiteralRuntime.of_functions found atomic unitType special readPolicy leafPolicy accepted)

theorem empty_children :
    DataExpressionSequence.Tree source (Children fuel values source context solved reasonAt) scope [] [] [] := .nil

theorem singleton_child (found : source.lookupExpression? id = some node)
    (child : Children fuel values source context solved reasonAt scope id code) :
    DataExpressionSequence.Tree source (Children fuel values source context solved reasonAt) scope [id] [node.type] [code] :=
  .single found child

theorem repeated_children (found : source.lookupExpression? id = some node)
    (child : Children fuel values source context solved reasonAt scope id code) :
    DataExpressionSequence.Tree source (Children fuel values source context solved reasonAt) scope
      [id, id, id] [node.type, node.type, node.type] [code, code, code] :=
  .cons found child (.cons found child (.single found child))
end Static

section Legacy
variable {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty}
  {faults : RecursiveStageMeaning.FaultRep} {source : Dynamic.Value} {value : Value}

theorem old_value (represented : model.Represents mapping world sourceType source value type) :
    RecursiveStageMeaning.ResultRepresents model mapping world sourceType type faults (.value source) (.inRight .word value) :=
  RecursiveStageMeaning.ResultRepresents.value represented

theorem old_fault {failure : Staging.Recursive.Failure} {token : Word} (represented : faults failure token) :
    RecursiveStageMeaning.ResultRepresents model mapping world sourceType type faults (.fault failure) (.inLeft type (.word token)) :=
  RecursiveStageMeaning.ResultRepresents.fault represented

theorem old_values {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {sources : List Dynamic.Value} {values : List Value}
    (represented : DataExpressionSequence.Values model mapping world types (codes.map (·.type)) sources values) :
    RecursiveStageArguments.Result model mapping world types codes faults (.values sources)
      (.inRight .word (DataPatternValues.packValues values)) :=
  RecursiveStageArguments.Result.values represented

theorem old_argument_fault {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {reason : Staging.Recursive.Failure} {token : Word} (represented : faults reason token) :
    RecursiveStageArguments.Result model mapping world types codes faults (.fault reason)
      (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) :=
  RecursiveStageArguments.Result.fault represented

abbrev legacy_rejection := @RecursiveStageMeaning.preserves_rejection
abbrev legacy_argument_fault := @RecursiveStageArguments.preserves_call_argument_fault
end Legacy

theorem stage_fault_excluded {faults : FunctionCalls.FaultRep} {scope : Staging.Recursive.Scope}
    {call : ExpressionId} {reason : Staging.CallGuard.Fault} {token : Word} :
    ¬ semanticFaults faults (.stage scope call reason) token := by
  intro impossible
  exact impossible

def run : IO Unit := do
  SourceRecursiveStageTupleExpressions.run
  SourceCoreRecursiveStagePrimitiveMeaning.run
  IO.println "ambient staged packs: existing actual ordered tuple/primitive full-ledger, whole-heap fault and resume audits reused GREEN"

end Tests.SourceCoreRecursiveStageAmbientArguments
