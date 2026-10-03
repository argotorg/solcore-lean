import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceSignatureFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Source parameter lists and results come from independent program typing,
signature identity and actual structural body instantiation. Packed type
collisions do not authenticate source parameter rows. The runtime fixture
inspects real generic metadata and both parameter orders. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedSourceSignatureFacts
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedCatalog RecursiveNamedSourceSignatureFacts

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : Core.DataEnvironment} {program : Program}

theorem actual_source_parameters (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    (selected : header.instantiation.declaration = signature.id) :
    signature.parameterTypes.map header.instantiation.parameterSubstitution.apply =
      header.bindings.map (fun binding => binding.1.scheme.body) :=
  (header_shape header programTyped member selected).1

theorem actual_source_result (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    (selected : header.instantiation.declaration = signature.id) :
    header.instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) =
      header.function.resultType := (header_shape header programTyped member selected).2

theorem actual_source_types {ambient : Core.AmbientDefinitions values.checked.catalog.definitions}
    {headers : Inventory prepared values ambient.definitions program} {context : SourceSemantics.Context}
    (programTyped : ProgramWellFormed program) (sameSignatures : context.signatures = program.signatures)
    (projections : ∀ header, header ∈ headers →
      (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
        .ok (header.bindings.map Prod.snd))
    (evidence : ∀ header, header ∈ headers → header.function.evidence = []) :
    RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context :=
  source_types programTyped sameSignatures projections evidence

/-- Packing alone cannot recover a source parameter list. -/
theorem packed_parameter_collision :
    TypeSystem.Ty.productMany [] = TypeSystem.Ty.productMany [.unit] ∧
    ([] : List TypeSystem.Ty) ≠ [.unit] ∧
    TypeSystem.Ty.productMany [.bool, .word] =
      TypeSystem.Ty.productMany [.product .bool .word] ∧
    ([.bool, .word] : List TypeSystem.Ty) ≠ [.product .bool .word] := by
  exact ⟨rfl, by simp, rfl, by simp⟩

private def content : String := String.intercalate "\n" [
  "function first<A, B>(one: A, two: B) returns (A) { return one; }",
  "function reverse<A, B>(one: A, two: B) returns ((B, A)) { return (two, one); }",
  "function wordRoot() returns (Word) { return first(7, true); }",
  "function boolRoot() returns (Bool) { return first(false, 9); }",
  "function pairRoot() returns ((Bool, Word)) { return reverse(11, false); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "source signature facts" content
    ["wordRoot", "boolRoot", "pairRoot"]
  let mut generic := 0
  for named in compiled.indexed.base.functions do
    let signature ← match compiled.sourceProgram.signatures.functions.find? (·.id == named.specialized.declaration) with
      | some signature => pure signature
      | none => throw (IO.userError "source signature facts declaration missing")
    let substitution := named.specialized.parameterSubstitution
    let source := CallableIndexedNamedGeneration.source named
    require (decide (signature.parameterTypes.map substitution.apply = source.inputs.map (fun binder => binder.scheme.body)))
      "source signature facts changed raw parameter positions"
    require (decide (signature.parameterTypes.map substitution.apply = named.inputs.map (fun binding => binding.1.scheme.body)))
      "source signature facts changed complete binder row"
    require (decide (substitution.apply (TypeSystem.Ty.productMany signature.returnTypes) = named.specialized.function.inferredBodyType))
      "source signature facts changed raw result"
    require (decide (substitution.map Prod.fst = signature.scheme.parameters))
      "source signature facts lost declaration order"
    if signature.scheme.parameters.length == 2 then
      require (substitution.length == 2) "source signature facts lost unused/result-independent type argument"
      generic := generic + 1
  require (generic == 3) s!"source signature facts generic coverage changed: {generic}"
  IO.println "source signature facts: independent shape consumers, raw generic parameters/results and full declaration order GREEN"

end Tests.SourceCoreRecursiveNamedSourceSignatureFacts
