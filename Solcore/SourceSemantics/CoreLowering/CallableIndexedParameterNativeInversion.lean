import Solcore.SourceSemantics.CoreLowering.CallableIndexedCachedNativeTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeTyping
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates

/-! Invert the actual cached named closure through its frame hook and marked
parameter fold. The original body keeps the packed argument and every hidden
wrapper input in its context. These are syntax typing results; they supply no
source execution or runtime closure authority. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeInversion
open Core Frontend SourceInference CallableIndexedParameterCertificates
open CallableIndexedParameterNativeTyping (finalContext)

/-- The returned variable fixes the body's type before the two temporary
frame binders are removed syntactically. -/
theorem withFrame_body {definitions : DataEnvironment} {context : Core.Context}
    {reference next body : Expr} {result : Ty}
    (typed : HasType context (SourceCoreCallableContextFrames.withFrame reference next body) result definitions) :
    HasType context body result definitions := by
  cases typed with
  | letE saved installed =>
    cases installed with
    | letE write evaluated =>
      cases write with
      | storeCell referenceTyped nextTyped =>
        cases evaluated with
        | letE bodyTyped restored =>
          cases restored with
          | letE restore returned =>
            cases returned with
            | var found =>
              simp at found
              cases found
              exact TypedLexicalWhile.Native.remove_front
                (TypedLexicalWhile.Native.remove_front bodyTyped)

/-- The real allocation receipt fixes each reference type. No per-parameter
typing, payload well-formedness, or ordinary-binder premise is added. -/
theorem tree_body {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {total index : Nat} {output : Ty} {body code : Expr}
    {scope : Scope} {bindings : List Binding}
    (tree : Tree layouts owner active frame globals onError source total output body scope index bindings code)
    {definitions : DataEnvironment} {context : Core.Context} {result : Ty}
    (typed : HasType context code result definitions) :
    HasType (finalContext bindings context) body result definitions := by
  induction tree generalizing context with
  | nil => exact typed
  | @cons scope index binder payload bindings code allocation annotation same tail ih =>
    have next : HasType (OptionalCell.referenceType payload :: context) code result definitions := by
      cases typed with
      | caseE initialized failure continued =>
        exact TypedLexicalWhile.Native.remove_second
          (TypedLexicalWhile.Native.absent_child allocation annotation same continued)
    simpa [finalContext, List.reverse_cons, List.append_assoc] using ih next

theorem accepted_body {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {scope : Scope} {bindings : List Binding} {output : Ty} {body code : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError))
      source scope bindings output SourceCoreFunctions.argumentProjection body = .ok code)
    {definitions : DataEnvironment} {context : Core.Context} {result : Ty}
    (typed : HasType context code result definitions) :
    HasType (finalContext bindings context) body result definitions :=
  tree_body (CallableIndexedParameterCertificates.of_accepted onError accepted) typed

theorem final_context (bindings : List Binding) (context : Core.Context) :
    finalContext bindings context =
      SourceCoreLocalCell.coreContext (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) ++ context := by
  simp [finalContext, SourceCoreLocalCell.coreContext, List.map_reverse, List.map_map, OptionalCell.referenceType]

theorem parameter_native {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    {definitions : DataEnvironment} {context : Core.Context} {result : Ty}
    (typed : HasType context compiled.output result definitions) :
    HasType context compiled.parameterCode result definitions := by
  obtain ⟨origin, index, selected, frame, emitted⟩ :=
    CallableIndexedFormation.namedBody_receipt prepared.ancestry compiled.hook
  rw [emitted] at typed
  exact withFrame_body typed

theorem body_native {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    {definitions : DataEnvironment} {context : Core.Context} {result : Ty}
    (typed : HasType context compiled.output result definitions) :
    HasType (SourceCoreLocalCell.coreContext
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) ++ context)
      compiled.body result definitions := by
  rw [← final_context]
  exact accepted_body _ compiled.parametersCompiled (parameter_native compiled typed)

/-- Actual preparation supplies all native premises for the original source
body code. The raw argument stays after the source parameter references. -/
theorem prepared_named_body {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked} {fuel : Nat}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    (accepted : SourceCoreCallableIndexedPrograms.prepare base fuel = .ok prepared)
    {entry : SourceCoreCallableIndexedPrograms.Entry prepared.layouts} (member : entry ∈ prepared.entries)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : prepared.base.functions[index]? = some named)
    (global : prepared.base.globals[index]? = some named.signature) :
    ∃ diagnostics code, ∃ compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code,
      prepared.secondPass.closures[index]? = some code ∧
      HasType (named.signature.parameterType :: prepared.base.globals.map (·.referenceType) ++
        .cell prepared.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.parameterCode (LanguageResult.resultType named.signature.resultType) prepared.layouts.definitions ∧
      HasType (SourceCoreLocalCell.coreContext (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) ++
        named.signature.parameterType :: prepared.base.globals.map (·.referenceType) ++
        .cell prepared.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.body (LanguageResult.resultType named.signature.resultType) prepared.layouts.definitions := by
  obtain ⟨diagnostics, code, compiled, cached, typed⟩ :=
    CallableIndexedCachedNativeTyping.prepared_named_output accepted member selected global
  refine ⟨diagnostics, code, compiled, cached, parameter_native compiled typed, ?_⟩
  simpa only [List.append_assoc] using body_native compiled typed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeInversion
