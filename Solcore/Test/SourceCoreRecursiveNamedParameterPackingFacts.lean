import Solcore.SourceSemantics.CoreLowering.RecursiveNamedParameterPackingFacts

set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedParameterPackingFacts
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics.CoreLowering RecursiveNamedCatalog RecursiveNamedParameterPackingFacts

theorem ordered_row {left right : List Ty} (arity : left.length = right.length)
    (packed : SourceCoreCompatibleCatalog.packTypes left = SourceCoreCompatibleCatalog.packTypes right) :
    left = right := packed_eq_of_length arity packed

theorem zero_unit_ambiguity :
    SourceCoreCompatibleCatalog.packTypes [] = SourceCoreCompatibleCatalog.packTypes [.unit] ∧
    ([] : List Ty).length ≠ ([.unit] : List Ty).length := by decide

theorem tuple_arity_ambiguity :
    SourceCoreCompatibleCatalog.packTypes [.word, .bool] =
      SourceCoreCompatibleCatalog.packTypes [.product .word .bool] ∧
    ([.word, .bool] : List Ty).length ≠ ([.product .word .bool] : List Ty).length := by decide

variable {checked : CallableAncestryPairedLookup.Checked}
  {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment}
  {program : Solcore.SourceSemantics.Program}

theorem actual_header_native_row (header : Header prepared values definitions program)
    (packed : header.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd)) :
    header.bindings.map Prod.snd = header.named.inputs.map Prod.snd :=
  header_native_types header packed

theorem actual_header_projections (header : Header prepared values definitions program)
    (packed : header.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd))
    (projected : (header.named.inputs.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.named.inputs.map Prod.snd)) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) := header_projections header packed projected

end Tests.SourceCoreRecursiveNamedParameterPackingFacts
