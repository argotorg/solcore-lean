import Solcore.SourceSemantics.CoreLowering.CallableIndexedPreparedInventories

/-! Consumers use the real factory equations. In particular the original
cached named body is typed without an independently supplied global-signature
correspondence or body-typing premise. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedPreparedInventories
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open CallableIndexedPreparedInventories

theorem actual_base (cached : SourceCoreUnifiedCompilation.Compiled) :
    cached.indexed.base = cached.compatible.prepared :=
  indexed_base cached.indexedPrepared

/-- The entire ordered list of full signatures survives preparation. -/
theorem full_ordered_inventory (cached : SourceCoreUnifiedCompilation.Compiled) :
    cached.indexed.base.globals = cached.indexed.base.functions.map (·.signature) :=
  cached_globals cached

theorem other_signature_rejected (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function} {signature : SourceCoreCalls.Signature}
    (selected : cached.indexed.base.functions[index]? = some named)
    (different : signature ≠ named.signature) :
    cached.indexed.base.globals[index]? ≠ some signature := by
  rw [cached_global_at cached selected]
  intro same
  exact different (Option.some.inj same).symm

/-- Only actual entry and function membership remain as static inputs. -/
theorem actual_body_without_global_premise (cached : SourceCoreUnifiedCompilation.Compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
    (member : entry ∈ cached.indexed.entries)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : cached.indexed.base.functions[index]? = some named) :
    ∃ diagnostics code,
      ∃ compiled : CallableIndexedNamedGeneration.Compilation cached.indexed named diagnostics code,
      cached.indexed.secondPass.closures[index]? = some code ∧
      HasType (SourceCoreLocalCell.coreContext (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) ++
        named.signature.parameterType :: cached.indexed.base.globals.map (·.referenceType) ++
        .cell cached.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.body (LanguageResult.resultType named.signature.resultType) cached.indexed.layouts.definitions := by
  obtain ⟨diagnostics, code, compiled, cached, parameters, body⟩ := cached_named_body cached member selected
  exact ⟨diagnostics, code, compiled, cached, body⟩

end Tests.SourceCoreCallableIndexedPreparedInventories
