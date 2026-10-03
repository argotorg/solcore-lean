import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Actual Header consumers require neither an external packed-parameter
equation nor a native projection callback. Program typing, complete selected
metadata, catalog identity and invocation evidence stay independent. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedHeaderParameterProjections
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedCatalog RecursiveNamedHeaderParameterProjections

section Formal
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment}
  {program : SourceSemantics.Program}
  (header : Header compiled.indexed.ancestry values definitions program)
  (programTyped : ProgramWellFormed program)

include programTyped

theorem actual_raw_type :
    header.instantiation.type = .function
      (TypeSystem.Ty.productMany (header.bindings.map (fun binding => binding.1.scheme.body)))
      header.function.resultType := header_type header programTyped

theorem actual_parameter_pack
    (matched : CallableNamedMetadata.Matches header.named.specialized header.instantiation) :
    header.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd) :=
  parameter_pack header programTyped matched

theorem actual_projections (sameChecked : values.checked = compiled.compatible.checked)
    (matched : CallableNamedMetadata.Matches header.named.specialized header.instantiation) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) := projections header sameChecked programTyped matched

theorem actual_record_projections (sameChecked : values.checked = compiled.compatible.checked)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      header.named.signature.key = .ok header.named.specialized) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) := projections_of_record header sameChecked programTyped record

theorem actual_native_vector
    (matched : CallableNamedMetadata.Matches header.named.specialized header.instantiation) :
    header.bindings.map Prod.snd = header.named.inputs.map Prod.snd :=
  RecursiveNamedParameterPackingFacts.header_native_types header (parameter_pack header programTyped matched)

theorem actual_source_types {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
    {context : SourceSemantics.Context}
    (sameChecked : values.checked = compiled.compatible.checked)
    (sameSignatures : context.signatures = program.signatures)
    (records : ∀ selected, selected ∈ headers →
      SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan selected.named.signature.key =
        .ok selected.named.specialized)
    (evidence : ∀ selected, selected ∈ headers → selected.function.evidence = []) :
    RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context :=
  source_types sameChecked programTyped sameSignatures records evidence
end Formal

theorem unit_arity_boundary :
    SourceCoreCompatibleCatalog.packTypes [] = SourceCoreCompatibleCatalog.packTypes [.unit] ∧
      ([] : List Core.Ty) ≠ [.unit] := by decide

theorem product_arity_boundary :
    SourceCoreCompatibleCatalog.packTypes [.product .word .bool] =
      SourceCoreCompatibleCatalog.packTypes [.word, .bool] ∧
      ([.product .word .bool] : List Core.Ty) ≠ [.word, .bool] := by decide

private def content : String := String.intercalate "\n" [
  "function empty() {}",
  "function unitArg(value: Unit) returns (Unit) { return value; }",
  "function tupleArg(value: (Word, Bool)) returns (Word) { return 1; }",
  "function two(first: Word, second: Bool) returns (Word) { return first; }",
  "function duplicate(first: Word, middle: Bool, last: Word) returns (Word) { return first + last; }",
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function rootUnit() returns (Unit) { return unitArg(()); }",
  "function rootTuple() returns (Word) { return tupleArg((7, true)); }",
  "function rootTwo() returns (Word) { return two(7, true); }",
  "function rootDuplicate() returns (Word) { return duplicate(7, false, 7); }",
  "function rootWord() returns (Word) { return choose(9, true); }",
  "function rootBool() returns (Bool) { return choose(false, 9); }"
]
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- This inspection uses real compiled rows; it does not manufacture a source
ProgramWellFormed or Header certificate from the successful comparisons. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let representation := SourceCoreCompatibleFunctions.representation
    (.initial compiled.compatible.checked) compiled.compilationFuel
  let mut arities : List Nat := []
  let mut vectors : List (List Core.Ty) := []
  let mut generic : List (List TypeSystem.Ty) := []
  for (named, slot) in compiled.indexed.base.functions.zipIdx do
    let specialized ← match compiled.compatible.prepared.plan.specializations.reverse[slot]? with
      | some specialized => pure specialized
      | none => throw (IO.userError "header parameter preparation slot missing")
    let actual ← get "header parameter preparation"
      (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation compiled.sourceProgram representation specialized)
    require (reprStr actual == reprStr named) "header parameter full prepared row changed"
    let selected ← get "header parameter exact selected record"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (reprStr selected == reprStr named.specialized) "header parameter exact record changed"
    let raw := named.inputs.map (fun binding => binding.1.scheme.body)
    let native := named.inputs.map Prod.snd
    require (reprStr (named.inputs.map Prod.fst) == reprStr specialized.function.typedBody.inputs)
      "header parameter ordered source binders changed"
    let projected ← get "header parameter raw projections"
      (raw.mapM compiled.compatible.checked.catalog.project)
    require (projected == native) "header parameter ordered native vector changed"
    let parameter ← match specialized.function.type with
      | .function parameter result =>
        require (parameter == TypeSystem.Ty.productMany raw) "header parameter raw function shape changed"
        require (result == specialized.function.inferredBodyType) "header parameter raw result changed"
        pure parameter
      | _ => throw (IO.userError "header parameter expected actual function type")
    let projectedParameter ← get "header actual whole parameter projection"
      (representation.expressions.projectType (.declaration specialized.key.declaration) parameter)
    let packed := SourceCoreCompatibleCatalog.packTypes native
    require (projectedParameter == named.signature.parameterType && projectedParameter == packed)
      "header actual parameter pack equation changed"
    arities := arities ++ [raw.length]
    vectors := vectors ++ [native]
    if !specialized.parameterSubstitution.isEmpty then
      require (specialized.parameterSubstitution.map Prod.snd == raw)
        "header retained generic substitution/order changed"
      generic := generic ++ [raw]
  require (arities.count 0 == 7 && arities.count 1 == 2 && arities.count 2 == 3 && arities.count 3 == 1)
    s!"header parameter actual arity coverage changed {reprStr arities}"
  require (vectors.contains [] && vectors.contains [.unit] &&
      vectors.contains [.product .word .bool] && vectors.contains [.word, .bool] &&
      vectors.contains [.word, .bool, .word] && vectors.contains [.bool, .word])
    "header parameter Unit/product ambiguity or ordered vectors missing"
  require (generic.length == 2 && generic.contains [.word, .bool] && generic.contains [.bool, .word])
    "header parameter full specialized generic rows changed"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named header parameter projections" content
    ["empty", "rootUnit", "rootTuple", "rootTwo", "rootDuplicate", "rootWord", "rootBool"]
  inspect compiled
  IO.println "recursive named header parameters: actual full selected rows, source shape, ordered projections and parameter pack GREEN"

end Tests.SourceCoreRecursiveNamedHeaderParameterProjections
