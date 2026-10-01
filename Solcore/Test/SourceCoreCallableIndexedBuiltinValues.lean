import Solcore.SourceSemantics.CoreLowering.CallableIndexedBuiltinValues
import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityMeaning
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual builtin references under a sealed indexed artifact supply all
function-leaf laws. Native captures include the artifact's new nominal frame;
equality observes source builtin identity, independently of capture contents. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedBuiltinValues
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedBuiltinValues CompatiblePayload GeneralHeap

/-- Fresh nominal frame captures are typed under the actual definition suffix. -/
theorem captured_frame {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (world : StoreTyping) : RuntimeEnvironmentHasTypes world
      [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame .empty]
      [prepared.ancestry.layout.frame.type] prepared.layouts.definitions :=
  .cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world (CallableIndexedAmbient.frame_registered prepared) .empty) .nil

theorem leaves_extend {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {registry futureRegistry : SourceCoreRawMetadata.Registry} {mapping futureMap : LocationMap}
    {world futureWorld : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : (model prepared profile).Represents registry mapping world sourceType source value type)
    (registries : SourceCoreRawMetadata.Extends registry futureRegistry) (maps : LocationMap.Extends mapping futureMap)
    (worlds : WorldExtends world futureWorld) :
    (model prepared profile).Represents futureRegistry futureMap futureWorld sourceType source value type :=
  (model prepared profile).extend related registries maps worlds

/-- The real comparator is supplied with proved model laws, not caller law
assumptions. Its result uses the independent source equality relation. -/
theorem comparison_from_receipts {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) (comparator : SourceCoreCompatibleDataEquality.Prepared checked)
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {mapping : LocationMap}
    {leftType rightType : TypeSystem.Ty} {left right : Dynamic.Value} {a b : Value}
    (first : (model prepared profile).Represents registry mapping world leftType left a comparator.type)
    (second : (model prepared profile).Represents registry mapping world rightType right b comparator.type)
    (store : Store) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent left right) ∧
      Evaluates [a, b] store (CompatibleEquality.comparison comparator (.var 0) (.var 1)) (.bool result)
        (CompatibleEquality.preparedStore comparator [a, b] store) :=
  CompatibleEquality.prepared_compare_preserves comparator (identity_faithful prepared)
    (observations prepared profile first) (observations prepared profile second) [a, b] store _ _ (.var rfl) (.var rfl)

section ActualReference
variable {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
  (profile : checked.catalog.callableContracts = true)
  {active : TypeSystem.Substitution} {compilation : SourceCoreFunctions.Context}
  {source : TypedSource} {node : ExpressionNode} {name : String} {function : BuiltinFunctionId}
  {lowered : SourceCoreBasic.LoweredExpr}
  (globals : compilation.globals = prepared.base.globals)
  (accepted : SourceCoreFunctions.builtinReference
    (SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) active)
    compilation source node name function = .ok lowered)
  {world : StoreTyping} {actual : Environment} {actualContext : Core.Context}
  (typed : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions)

include globals accepted typed in
theorem reference_supplies_laws (store : Store) (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) :
    ∃ value, Evaluates actual store lowered.expression (.inRight .word value) store ∧
      (model prepared profile).Represents registry mapping world node.type (.builtin ⟨function⟩) value lowered.type ∧
      CompatibleEquality.Observation checked.catalog registry (Identity prepared) lowered.type (.builtin ⟨function⟩) value := by
  obtain ⟨value, evaluated, related⟩ := formation_of_accepted prepared profile globals accepted typed store registry mapping
  exact ⟨value, evaluated, related, observations prepared profile related⟩
end ActualReference

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function sub(a: integer, b: integer) returns (integer) { return integerSub(a, b); }",
    "function add(a: integer, b: integer) returns (integer) { return integerAdd(a, b); }",
    "function mul(a: integer, b: integer) returns (integer) { return integerMul(a, b); }",
    "function eq(a: integer, b: integer) returns (Bool) { return integerEq(a, b); }",
    "function lt(a: integer, b: integer) returns (Bool) { return integerLt(a, b); }",
    "function from(a: integer) returns (Word) { return wordFromInteger(a); }",
    "function to(a: Word) returns (integer) { return wordToInteger(a); }"
  ]}] }

private def checkComparison {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (function : BuiltinFunctionId) (a b : Value) (expected : Bool) : IO Unit := do
  let comparator ← SourceCompilerFeatureSupport.get "builtin leaf comparator"
    (SourceCoreCompatibleDataEquality.prepare 500 checked function.type)
  let store : Store := [.word (Word.ofNatModulo 41)]
  let expression := CompatibleEquality.comparison comparator (.var 0) (.var 1)
  SourceCompilerFeatureSupport.require (infer? [comparator.type, comparator.type] expression prepared.layouts.definitions == some .bool)
    "builtin comparator rejected actual full definitions"
  let whole := runStateful 100000 (.initial expression [a, b] store)
  SourceCompilerFeatureSupport.require (whole == .done (.bool expected) (CompatibleEquality.preparedStore comparator [a, b] store))
    "builtin identity comparison changed capture-independent source equality or store"
  for fuel in [0, 3, 10, 29] do
    match runStateful fuel (.initial expression [a, b] store) with
    | .outOfFuel state => SourceCompilerFeatureSupport.require (runStateful 100000 state == whole) "builtin leaf equality resume changed result"
    | .done value after => SourceCompilerFeatureSupport.require ((StatefulRunResult.done value after) == whole) "builtin equality prefix changed result"
    | _ => throw (IO.userError "builtin leaf comparator stuck")

def run : IO Unit := do
  let sourceProgram ← SourceCompilerFeatureSupport.get "builtin leaf source checker" (checkProgram workspace)
  let seeds := sourceProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run sourceProgram seeds 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"builtin leaf worklist: {reprStr other}")
  let automatic ← SourceCompilerFeatureSupport.get "builtin leaf compatible artifact" (SourceCoreCompatibleFunctions.prepare sourceProgram plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "builtin leaf indexed artifact" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let snapshot := SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame .empty
  let frameExpression := SourceCoreCallableIndexedDispatch.literal prepared.ancestry.layout.frame .empty
  SourceCompilerFeatureSupport.require ((infer? [] frameExpression automatic.checked.catalog.definitions).isNone)
    "fresh indexed frame unexpectedly belongs to source catalog"
  let environment : Environment := [snapshot, .cellRef .word 0]
  let store : Store := [.word (Word.ofNatModulo 41)]
  let context : Core.Context := [prepared.ancestry.layout.frame.type, .cell .word]
  let mut observed : List (BuiltinFunctionId × Value × Value) := []
  for specialized in prepared.base.plan.specializations do
    let source := specialized.function.typedBody
    let compilation : SourceCoreFunctions.Context :=
      ⟨prepared.base.plan, specialized.key, prepared.base.globals, 0, [], Word.zero⟩
    for raw in source.nodes do
      match raw with
      | .expression node =>
        match node.form with
        | .reference name (.builtinFunction function) =>
          let lowered ← SourceCompilerFeatureSupport.get "actual builtin leaf reference"
            (SourceCoreFunctions.builtinReference
              (SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
              compilation source node name function)
          SourceCompilerFeatureSupport.require (infer? context lowered.expression prepared.layouts.definitions == some (LanguageResult.resultType lowered.type))
            "actual builtin reference rejected fresh frame capture context"
          let value ← match runStateful 1000 (.initial lowered.expression environment store) with
            | .done (.inRight .word value) after =>
              SourceCompilerFeatureSupport.require (after == store) "builtin reference mutated store"
              pure value
            | other => throw (IO.userError s!"actual builtin reference result: {reprStr other}")
          let other ← match runStateful 1000 (.initial lowered.expression [] store) with
            | .done (.inRight .word value) after =>
              SourceCompilerFeatureSupport.require (after == store) "empty capture builtin reference mutated store"
              pure value
            | result => throw (IO.userError s!"empty capture reference: {reprStr result}")
          let descriptor ← SourceCompilerFeatureSupport.get "owned builtin descriptor"
            (SourceCoreCallableContracts.descriptor prepared.ancestry.graph.inputs.callable.table (.builtin function))
          let index ← match BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) with
            | some (_, index) => pure index | none => throw (IO.userError "missing builtin inventory")
          let identity ← match Word.ofNat? (prepared.base.globals.length + index + 1) with
            | some identity => pure identity | none => throw (IO.userError "builtin identity overflow")
          SourceCompilerFeatureSupport.require (value == BuiltinCalls.Protocol.contractedValue function identity descriptor.id environment)
            "actual reference lost identity, descriptor, code or actual captures"
          checkComparison prepared function value other true
          observed := (function, value, other) :: observed
        | _ => pure ()
      | _ => pure ()
  SourceCompilerFeatureSupport.require (observed.length == BuiltinFunctionId.all.length) "builtin fixture missed an accepted branch"
  for (left, a, _) in observed do
    for (right, b, _) in observed do
      if SourceCoreInteger.builtinParameter left == SourceCoreInteger.builtinParameter right &&
          SourceCoreInteger.builtinResult left == SourceCoreInteger.builtinResult right then
        checkComparison prepared left a b (left == right)
  IO.println "indexed builtin leaves: actual identities/descriptors, full-definition captures, source equality and resume GREEN"
end Tests.SourceCoreCallableIndexedBuiltinValues
