import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalControl
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedParameters
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalWhile
import Solcore.Frontend.SourceCoreUnifiedCompilation
import Solcore.SourceSemantics.CoreLowering.CaptureCopiesMarked
import Solcore.SourceSemantics.CoreLowering.FunctionCallBody
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AppliedViews
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls

/-!
# Indexed callables: lambda bodies and typing

Cached native typing, parameter inversion, the lambda body, manifest, invocation and calls.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedCachedNativeTyping
/-! Native typing is extracted from the actual checked entry wrapper. Global
allocation and installation retain their emitted order; removing installer
Unit binders is a syntax typing inversion. This does not identify a source
body or authenticate runtime captures. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedCachedNativeTyping
open Core Frontend SourceInference

theorem allocated_body {definitions : DataEnvironment} {context : Core.Context}
    {signatures : List SourceCoreCalls.Signature} {body : Expr} {result : Ty}
    (typed : HasType context (SourceCoreRecursiveEntry.allocateGlobals signatures body) result definitions) :
    HasType (signatures.reverse.map (·.referenceType) ++ context) body result definitions := by
  induction signatures generalizing context with
  | nil => exact typed
  | cons signature signatures ih =>
    change HasType context (.letE (OptionalCell.allocate signature.functionType)
      (SourceCoreRecursiveEntry.allocateGlobals signatures body)) result definitions at typed
    cases typed with
    | letE allocated rest =>
      cases allocated with
      | newCell empty =>
        have next := ih rest
        simpa [List.reverse_cons, List.map_append, List.append_assoc,
          SourceCoreCalls.Signature.referenceType, OptionalCell.referenceType] using next

private theorem installed_fold {definitions : DataEnvironment} {context : Core.Context}
    {items : List (Expr × Nat)} {body : Expr} {result : Ty}
    (typed : HasType context (items.foldr (fun (closure, index) continuation =>
      .letE (.storeCell (.var index) (.inRight .unit closure)) (continuation.weakenAt 0)) body)
      result definitions) :
    HasType context body result definitions ∧
      ∀ closure index, (closure, index) ∈ items → ∀ functionType,
        context[index]? = some (OptionalCell.referenceType functionType) →
        HasType context closure functionType definitions := by
  induction items with
  | nil => exact ⟨typed, by simp⟩
  | cons item items ih =>
    rcases item with ⟨closure, index⟩
    change HasType context (.letE (.storeCell (.var index) (.inRight .unit closure))
      ((items.foldr (fun (closure, index) continuation =>
        .letE (.storeCell (.var index) (.inRight .unit closure))
          (continuation.weakenAt 0)) body).weakenAt 0)) result definitions at typed
    cases typed with
    | letE write tail =>
      obtain ⟨bodyTyped, remaining⟩ := ih (TypedLexicalWhile.Native.remove_front tail)
      refine ⟨bodyTyped, ?_⟩
      intro selected slot member functionType reference
      rcases List.mem_cons.mp member with same | member
      · cases same
        cases write with
        | storeCell referenceTyped payloadTyped =>
          cases referenceTyped with
          | var found =>
            rw [reference] at found
            cases found
            cases payloadTyped with
            | inRight unitTyped closureTyped => exact closureTyped
      · exact remaining selected slot member functionType reference

theorem installed_body {definitions : DataEnvironment} {context : Core.Context}
    {closures : List Expr} {body : Expr} {result : Ty}
    (typed : HasType context (SourceCoreRecursiveEntry.installFunctions closures body) result definitions) :
    HasType context body result definitions := (installed_fold typed).1

theorem installed_closure {definitions : DataEnvironment} {context : Core.Context}
    {closures : List Expr} {body : Expr} {result functionType : Ty} {index : Nat} {closure : Expr}
    (typed : HasType context (SourceCoreRecursiveEntry.installFunctions closures body) result definitions)
    (selected : closures[index]? = some closure)
    (reference : context[index]? = some (OptionalCell.referenceType functionType)) :
    HasType context closure functionType definitions := by
  have member : (closure, index) ∈ closures.zipIdx := by
    exact List.mk_mem_zipIdx_iff_getElem?.mpr selected
  exact (installed_fold typed).2 closure index member functionType reference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

theorem assembled_native {definitions : DataEnvironment}
    {globals : List SourceCoreCalls.Signature} {functions : List SourceCoreGeneralFunctions.Function}
    {closures : List Expr} {key : SourceSpecialization.SpecializationKey}
    {arguments : SourceCoreBasic.LoweredExpr} {body : Expr} {context : Core.Context} {result : Ty}
    (assembled : SourceCoreGeneralFunctions.assembleCall globals functions closures key arguments = .ok body)
    (typed : HasType context body result definitions) :
    ∃ function index,
      functions.zipIdx.find? (fun entry => decide (entry.1.signature.key = key)) = some (function, index) ∧
      HasType (globals.map (·.referenceType) ++ context)
        (SourceCoreRecursiveEntry.installFunctions closures
          (SourceCoreCalls.call function.signature index arguments.expression Word.zero)) result definitions := by
  unfold SourceCoreGeneralFunctions.assembleCall at assembled
  cases selected : functions.zipIdx.find? (fun entry => decide (entry.1.signature.key = key)) with
  | none => simp [selected, bind, Except.bind, throw] at assembled
  | some pair =>
    rcases pair with ⟨function, index⟩
    simp only [selected, pure, Except.pure, bind, Except.bind] at assembled
    obtain ⟨_, _, assembled⟩ := bind_ok assembled
    cases assembled
    exact ⟨function, index, rfl, by simpa using allocated_body typed⟩

theorem native_compiled_closure {definitions : DataEnvironment}
    {globals : List SourceCoreCalls.Signature} {functions : List SourceCoreGeneralFunctions.Function}
    {closures : List Expr} {key : SourceSpecialization.SpecializationKey}
    {arguments : SourceCoreBasic.LoweredExpr} {body : Expr} {inputs : List Ty} {result : Ty}
    {entry : SourceCoreGeneralEntry.NativeEntry definitions} {index : Nat} {closure : Expr}
    {signature : SourceCoreCalls.Signature}
    (assembled : SourceCoreGeneralFunctions.assembleCall globals functions closures key arguments = .ok body)
    (compiled : SourceCoreGeneralEntry.NativeEntry.compile definitions inputs result body = .ok entry)
    (selected : closures[index]? = some closure) (global : globals[index]? = some signature) :
    HasType (globals.map (·.referenceType) ++ SourceCoreGeneralEntry.nativeInputContext inputs)
      closure signature.functionType definitions := by
  obtain ⟨inputEq, resultEq, bodyEq⟩ := SourceCoreGeneralEntry.NativeEntry.compile_fields compiled
  have typed := entry.bodyTyped
  rw [inputEq, resultEq, bodyEq] at typed
  obtain ⟨_, _, _, installed⟩ := assembled_native assembled typed
  apply installed_closure installed selected
  rw [List.getElem?_append_left]
  · simp [List.getElem?_map, global, SourceCoreCalls.Signature.referenceType]
  · simpa using (List.getElem?_eq_some_iff.mp global).1

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

theorem indexed_assembled_closure {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {closures : List Expr} {key : SourceSpecialization.SpecializationKey}
    {arguments : SourceCoreBasic.LoweredExpr} {body : Expr} {context : Core.Context}
    {definitions : DataEnvironment} {result : Ty} {index : Nat} {closure : Expr}
    {signature : SourceCoreCalls.Signature}
    (assembled : SourceCoreCallableIndexedPrograms.assembleCall ancestry closures key arguments = .ok body)
    (typed : HasType context body result definitions)
    (selected : closures[index]? = some closure) (global : base.globals[index]? = some signature) :
    HasType (base.globals.map (·.referenceType) ++ .cell ancestry.layout.frame.type :: context)
      closure signature.functionType definitions := by
  unfold SourceCoreCallableIndexedPrograms.assembleCall at assembled
  obtain ⟨inner, innerCompiled, assembled⟩ := bind_ok assembled
  have innerCompiled := mapError_ok innerCompiled
  cases assembled
  change HasType context (.letE (.newCell ancestry.layout.frame.type
    (SourceCoreCallableIndexedFrames.empty ancestry.layout.frame)) inner) result definitions at typed
  cases typed with
  | letE allocated entered =>
    cases allocated with
    | newCell empty =>
      obtain ⟨_, _, _, installed⟩ := assembled_native innerCompiled entered
      apply installed_closure installed selected
      rw [List.getElem?_append_left]
      · simp [List.getElem?_map, global, SourceCoreCalls.Signature.referenceType]
      · simpa using (List.getElem?_eq_some_iff.mp global).1

private theorem mapM_member {α β ε : Type} {f : α → Except ε β} {inputs : List α} {outputs : List β}
    (accepted : inputs.mapM f = .ok outputs) {output : β} (member : output ∈ outputs) :
    ∃ input, input ∈ inputs ∧ f input = .ok output := by
  induction inputs generalizing outputs with
  | nil => simp [List.mapM_nil] at accepted; subst outputs; simp at member
  | cons input inputs ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, firstCompiled, accepted⟩ := bind_ok accepted
    obtain ⟨rest, restCompiled, accepted⟩ := bind_ok accepted
    cases accepted
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨input, .head _, firstCompiled⟩
    · obtain ⟨input, found, compiled⟩ := ih restCompiled member
      exact ⟨input, List.mem_cons_of_mem _ found, compiled⟩

/-- Every cached root member retains an actual successful assembly, rather
than a caller-supplied equation identifying its native body. -/
theorem prepared_entry_assembly {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked} {fuel : Nat}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    (accepted : SourceCoreCallableIndexedPrograms.prepare base fuel = .ok prepared)
    {entry : SourceCoreCallableIndexedPrograms.Entry prepared.layouts} (member : entry ∈ prepared.entries) :
    ∃ arguments, SourceCoreCallableIndexedPrograms.assembleCall prepared.ancestry
      prepared.secondPass.closures entry.key arguments = .ok entry.native.body := by
  unfold SourceCoreCallableIndexedPrograms.prepare at accepted
  dsimp only at accepted
  split at accepted
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
  · rename_i ancestry ancestryPrepared
    try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
    split at accepted
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
    · rename_i contexts contextsPrepared
      try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
      split at accepted
      · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
      · rename_i discovery discoveryPrepared
        try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
        obtain ⟨firstPass, _, accepted⟩ := bind_ok accepted
        try dsimp only at accepted
        split at accepted
        · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
        · rename_i discovered scanned
          try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
          split at accepted
          · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
          · rename_i layouts layoutsPrepared
            try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
            obtain ⟨secondPass, _, accepted⟩ := bind_ok accepted
            obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
            obtain ⟨entries, entriesCompiled, accepted⟩ := bind_ok accepted
            cases accepted
            obtain ⟨key, _, action⟩ := mapM_member entriesCompiled member
            cases selected : base.functions.find? (fun function => decide (function.signature.key = key)) with
            | none => simp [selected, bind, Except.bind, throw] at action
            | some function =>
              simp only [selected, pure, Except.pure, bind, Except.bind] at action
              obtain ⟨body, assembled, action⟩ := bind_ok action
              obtain ⟨native, compiled, action⟩ := bind_ok action
              have bodyEq := (SourceCoreGeneralEntry.NativeEntry.compile_fields (mapError_ok compiled)).2.2
              cases action
              exact ⟨_, by simpa only [bodyEq] using assembled⟩

/-- Actual preparation and its checked native root type every installed
closure at its real global slot, including arbitrary wrapper input types. -/
theorem prepared_native_closure {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked} {fuel : Nat}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    (accepted : SourceCoreCallableIndexedPrograms.prepare base fuel = .ok prepared)
    {entry : SourceCoreCallableIndexedPrograms.Entry prepared.layouts} (member : entry ∈ prepared.entries)
    {index : Nat} {closure : Expr} {signature : SourceCoreCalls.Signature}
    (selected : prepared.secondPass.closures[index]? = some closure)
    (global : prepared.base.globals[index]? = some signature) :
    HasType (prepared.base.globals.map (·.referenceType) ++ .cell prepared.ancestry.layout.frame.type ::
      SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      closure signature.functionType prepared.layouts.definitions := by
  obtain ⟨arguments, assembled⟩ := prepared_entry_assembly accepted member
  exact indexed_assembled_closure prepared.ancestry assembled entry.native.bodyTyped selected global

/-- Compiler provenance identifies the exact named output under its argument
and cached global references. Source meaning and parameter-prefix inversion
remain separate from this static conclusion. -/
theorem prepared_named_output {checked : SourceCoreCompatibleCatalog.Checked}
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
        compiled.output (LanguageResult.resultType named.signature.resultType) prepared.layouts.definitions := by
  obtain ⟨diagnostics, code, cached, ⟨compiled⟩⟩ := CallableIndexedNamedGeneration.compiled_at prepared selected
  have typed := prepared_native_closure accepted member cached global
  rw [compiled.emitted] at typed
  cases typed with
  | lambda parameterWF resultWF outputTyped => exact ⟨diagnostics, code, compiled, cached, outputTyped⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedCachedNativeTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeInversion
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedPreparedInventories
/-! Static inventory equalities follow the actual preparation factories.
They remove the caller's global-signature correspondence premise when typing
cached named bodies. They do not certify a source body execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedPreparedInventories
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

theorem compatible_catalog_globals {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} (ownership : checked.signatures = program.signatures)
    {fuel : Nat} {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok prepared) :
    prepared.globals = prepared.functions.map (·.signature) := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  cases seeds : executable.val.seedKeys with
  | nil =>
    simp only [seeds, pure, Except.pure] at accepted
    cases accepted
    rfl
  | cons first rest =>
    simp only [seeds] at accepted
    obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    cases contracts : checked.catalog.callableContracts with
    | false =>
      simp only [contracts, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      rfl
    | true =>
      simp only [contracts, ↓reduceIte] at accepted
      obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨nativeDiagnostics, _, accepted⟩ := bind_ok accepted
      try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      rfl

theorem compatible_automatic_globals {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {fuel : Nat} {limits : SourceCoreRawMetadata.Limits} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel limits = .ok automatic) :
    automatic.prepared.globals = automatic.prepared.functions.map (·.signature) := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  try dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨prepared, preparedAccepted, accepted⟩ := bind_ok accepted
    cases accepted
    exact compatible_catalog_globals _ preparedAccepted

theorem indexed_base {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked} {fuel : Nat}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    (accepted : SourceCoreCallableIndexedPrograms.prepare base fuel = .ok prepared) :
    prepared.base = base := by
  unfold SourceCoreCallableIndexedPrograms.prepare at accepted
  try dsimp only at accepted
  split at accepted
  · cases accepted
  · try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
    split at accepted
    · cases accepted
    · try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
      split at accepted
      · cases accepted
      · try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
        obtain ⟨firstPass, _, accepted⟩ := bind_ok accepted
        try dsimp only at accepted
        split at accepted
        · cases accepted
        · try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
          split at accepted
          · cases accepted
          · try dsimp only [pure, Except.pure, bind, Except.bind] at accepted
            obtain ⟨secondPass, _, accepted⟩ := bind_ok accepted
            obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
            obtain ⟨entries, _, accepted⟩ := bind_ok accepted
            cases accepted
            rfl

theorem cached_globals (cached : SourceCoreUnifiedCompilation.Compiled) :
    cached.indexed.base.globals = cached.indexed.base.functions.map (·.signature) := by
  rw [indexed_base cached.indexedPrepared]
  exact compatible_automatic_globals cached.compatiblePrepared

theorem cached_global_at (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : cached.indexed.base.functions[index]? = some named) :
    cached.indexed.base.globals[index]? = some named.signature := by
  rw [cached_globals]
  simp [selected]

/-- A named function at an actual cached slot needs no separate claim about
its global signature. The original raw argument and wrapper inputs remain. -/
theorem cached_named_body (cached : SourceCoreUnifiedCompilation.Compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
    (member : entry ∈ cached.indexed.entries)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : cached.indexed.base.functions[index]? = some named) :
    ∃ diagnostics code,
      ∃ compiled : CallableIndexedNamedGeneration.Compilation cached.indexed named diagnostics code,
      cached.indexed.secondPass.closures[index]? = some code ∧
      HasType (named.signature.parameterType :: cached.indexed.base.globals.map (·.referenceType) ++
        .cell cached.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.parameterCode (LanguageResult.resultType named.signature.resultType) cached.indexed.layouts.definitions ∧
      HasType (SourceCoreLocalCell.coreContext (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) ++
        named.signature.parameterType :: cached.indexed.base.globals.map (·.referenceType) ++
        .cell cached.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.body (LanguageResult.resultType named.signature.resultType) cached.indexed.layouts.definitions :=
  CallableIndexedParameterNativeInversion.prepared_named_body cached.indexedPrepared member selected
    (cached_global_at cached selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedPreparedInventories
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaMeaning
/-! Lambda formation at the actual generated syntax, including arbitrary
administrative insertions. An ordinary lambda first copies the captured cells
of its creation environment through the marked allocator; the source lambda
copies the same bindings. The newly captured value is kept exactly as created
over the copies. A lambda whose policy does not snapshot it, a generalized
local's initializer, forms directly over its scope. Finite completion
reflection follows from the direct evaluation, not from an equality between
closures captured in different environments. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open CallableIndexedHistory

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}

/-- The source location selected by a capture remains the same actual native
cell through the real embedding, including aliases. -/
theorem Captures.lookup (captured : Captures prepared mapping world scope function.captured actual)
    {binder : Resolved.LocalId} {location : Dynamic.Location}
    (found : Dynamic.Environment.LooksUp function.captured binder location) :
    ∃ index payload target, SourceCoreLocalCell.lookup? scope binder = some (index, payload) ∧
      actual[captured.embedding index]? = some (.cellRef (OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world location target payload := by
  obtain ⟨index, payload, target, selected, reference, represented⟩ := captured.represented.lookup_source found
  exact ⟨index, payload, target, selected, captured.agrees reference, represented⟩

/-- The decorated lambda forms over the actual environment after reading the
frame cell. -/
theorem expression_evaluates
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {store : Store} {location : Location}
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)) :
    Evaluates actual store (code.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding history.native actual)) store :=
  .inRight (.pair (.pair (.inLeft .unit) (.letE (.loadCell (.var (captured.agrees reference)) read) .lambda)) .word)

theorem formation_evaluates
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (shared : code.policy.snapshotLambda code.id = false)
    {store : Store} {location : Location}
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)) :
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding history.native actual)) store := by
  rw [code.emitted_shared shared]
  exact expression_evaluates captured code history reference read

/-- The actual emitted expression and store determine native output typing.
No future world is invented for a read-only formation step. -/
theorem formation_represents
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (shared : code.policy.snapshotLambda code.id = false)
    {store : Store} {location : Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)) :
    Represents prepared mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  have evaluated := formation_evaluates captured code history shared reference read
  obtain ⟨future, _, finalStored, resultTyped⟩ :=
    evaluation_preserves_type evaluated (code.typed.rename captured.respects) captured.typed stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  cases resultTyped with
  | inRight typed => exact .lambda captured code history typed

/-- Source formation copies the creation environment and stores exactly the
caller's raw source, context and evidence with the copies. These are semantic
inputs, not decoded guesses from a native descriptor. No body execution is
involved. -/
theorem source_formation {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program)
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap}
    (snapshot : Dynamic.EnvironmentCopies function.source environment heap function.captured after)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment heap
      code.id (.closure function) after := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound code.sourceFound)
  · rw [code.sourceForm]
    exact .lambda ordinary snapshot
  · rw [coercions]
    exact .nil

/-- The closure an ordinary lambda forms over the copies of its creation
environment: the source copies, the closure's capture layout over the copied
cells, the extended heap relation with the frame cell unchanged, and the Core
evaluation of the emitted copies and lambda. Slots past the scope keep their
canonical values. -/
structure Formed {projects : GenericHeap.Projection}
    (model : GenericHeap.PayloadModel (storageCatalog checked.catalog) projects prepared.layouts.definitions)
    {environment : Dynamic.Environment}
    (current : Captures prepared mapping world scope environment actual)
    (code : Code prepared function scope current.administrative) (history : History code)
    (heap : Dynamic.Heap) (store : Store) (location : Location) where
  captured : Dynamic.Environment
  finalHeap : Dynamic.Heap
  finalStore : Store
  finalMap : LocationMap
  finalWorld : StoreTyping
  closureActual : Core.Environment
  canonical : Core.Environment
  actualContext : Core.Context
  embedding : Renaming
  copy : Dynamic.EnvironmentCopies function.source environment heap captured finalHeap
  represented : DataHeap.EnvRepresents (storageCatalog checked.catalog) finalMap finalWorld current.administrative
    scope captured canonical prepared.layouts.definitions
  agrees : ReadOnly.EnvironmentsAgree embedding canonical closureActual
  respects : Renaming.Respects embedding (SourceCoreLocalCell.coreContext scope ++ current.administrative) actualContext
  typed : RuntimeEnvironmentHasTypes finalWorld closureActual actualContext prepared.layouts.definitions
  slots : ∀ index, scope.length ≤ index → canonical[index]? = current.canonical[index]?
  heaps : GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore
  maps : LocationMap.Extends mapping finalMap
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping store finalMap finalStore
  read : finalStore.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)
  evaluated : Evaluates actual store (code.lowered.expression.rename current.embedding)
    (.inRight .word (value code embedding history.native closureActual)) finalStore

namespace Formed
variable {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (storageCatalog checked.catalog) projects prepared.layouts.definitions}
  {environment : Dynamic.Environment} {current : Captures prepared mapping world scope environment actual}
  {code : Code prepared function scope current.administrative} {history : History code}
  {heap : Dynamic.Heap} {store : Store} {location : Location}

/-- The closure's capture layout over its copies. -/
def captures (formed : Formed model current code history heap store location) :
    Captures prepared formed.finalMap formed.finalWorld scope formed.captured formed.closureActual :=
  ⟨current.administrative, formed.canonical, formed.actualContext, formed.embedding, formed.represented,
    formed.agrees, formed.respects, formed.typed⟩

/-- The formed closure. -/
abbrev closure (formed : Formed model current code history heap store location) : Dynamic.Closure :=
  { function with captured := formed.captured }

/-- The same code, for the formed closure. -/
def closureCode (formed : Formed model current code history heap store location) :
    Code prepared formed.closure scope formed.captures.administrative :=
  code.recapture formed.captured

def closureHistory (formed : Formed model current code history heap store location) :
    History formed.closureCode :=
  history.recapture formed.captured

theorem value_eq (formed : Formed model current code history heap store location) :
    value formed.closureCode formed.captures.embedding history.native formed.closureActual =
      value code formed.embedding history.native formed.closureActual := rfl

theorem reference (formed : Formed model current code history heap store location)
    (referenceIndex : code.referenceIndex = scope.length + 1 + prepared.base.globals.length)
    (reference : current.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location)) :
    formed.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location) := by
  rw [formed.slots _ (by omega)]
  exact reference

/-- The source lambda forms the same closure over the same copies. -/
theorem source (formed : Formed model current code history heap store location) (program : Program)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment heap
      code.id (.closure formed.closure) formed.finalHeap :=
  source_formation formed.closureCode program formed.copy ordinary coercions

/-- The formed native closure, typed by the evaluation of the whole emitted
expression, represents the formed source closure. -/
theorem represents (formed : Formed model current code history heap store location)
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions) :
    Represents prepared formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  obtain ⟨future, _, finalStored, resultTyped⟩ :=
    evaluation_preserves_type formed.evaluated (code.typed.rename current.respects) current.typed stored
  have same : future = formed.finalWorld :=
    finalStored.world_eq.trans formed.heaps.runtime_hasTypes.world_eq.symm
  subst future
  cases resultTyped with
  | inRight typed =>
    have closureTyped : RuntimeValueHasType formed.finalWorld
        (value formed.closureCode formed.captures.embedding formed.closureHistory.native formed.closureActual)
        (CallableContract.functionType formed.closureCode.receipt.parameterCore formed.closureCode.receipt.resultCore)
        prepared.layouts.definitions := typed
    exact Represents.lambda (function := formed.closure) formed.captures formed.closureCode
      formed.closureHistory closureTyped

/-- A completed native formation is the formed closure in the formed store. -/
theorem reflects (formed : Formed model current code history heap store location)
    {result : Core.Value} {after : Store}
    (completed : Evaluates actual store (code.lowered.expression.rename current.embedding) result after) :
    result = .inRight .word (value code formed.embedding history.native formed.closureActual) ∧
      after = formed.finalStore :=
  evaluation_deterministic completed formed.evaluated

end Formed

/-- An ordinary lambda's formation: the marked creation copies of its scope,
then the decorated lambda over the copies. -/
theorem formation {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (storageCatalog checked.catalog) projects prepared.layouts.definitions}
    {environment : Dynamic.Environment}
    (current : Captures prepared mapping world scope environment actual)
    (code : Code prepared function scope current.administrative) (history : History code)
    (copied : code.policy.snapshotLambda code.id = true)
    (referenceIndex : code.referenceIndex = scope.length + 1 + prepared.base.globals.length)
    {heap : Dynamic.Heap} {store : Store} {location : Location}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (reference : current.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)) :
    Nonempty (Formed model current code history heap store location) := by
  have accepted := code.emitted_copied copied
  have base : (fun index : Nat => index) = (· + ([] : Environment).length) := by
    funext index
    simp
  rw [base] at accepted
  rw [referenceIndex] at reference
  obtain ⟨captured, finalHeap, finalCanonical, finalActual, finalActualContext, finalStore, finalMap, finalWorld,
      finalEmbedding, copy, environments, slots, finalHeaps, maps, worlds, frame, finalRead, lookups, types,
      actualTyped, agreement⟩ :=
    CaptureCopies.marked_copies_prefix (pre := []) (preContext := []) accepted rfl
      (CallableIndexedAmbient.frame_registered prepared) current.represented heaps current.agrees rfl
      current.respects current.typed reference read
  have copy := copy.of_copiedBinder (LambdaMetadataViews.MetadataView.copiedBinder code.viewOfSource).symm
  let closure : Captures prepared finalMap finalWorld scope captured finalActual :=
    ⟨current.administrative, finalCanonical, finalActualContext, finalEmbedding, environments, lookups, types,
      actualTyped⟩
  have finalReference : closure.canonical[code.referenceIndex]? =
      some (.cellRef prepared.ancestry.layout.frame.type location) := by
    rw [referenceIndex, slots _ (by omega)]
    exact reference
  have formed := expression_evaluates (function := { function with captured := captured })
    (store := finalStore) (location := location) closure
    (code.recapture captured) (history.recapture captured) finalReference finalRead
  exact ⟨⟨captured, finalHeap, finalStore, finalMap, finalWorld, finalActual, finalCanonical, finalActualContext,
    finalEmbedding, copy, environments, lookups, types, actualTyped, slots, finalHeaps, maps, worlds, frame,
    finalRead, agreement.wrap formed⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
/-! Ordinary lambda generation under a real named entry. Compiler callbacks
fix the source owner and empty native parent; the named seed fixes the complete
source graph. Source context, evidence and capture locations are the actual
formation inputs. Generalized bundles, applied views and whole traversal
coverage remain separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedNamedGeneration CallableIndexedLambdaValues

/-- The source closure stores the exact generation inputs, without deriving
source context or evidence from the native frame. -/
def closure (named : Named) (parameters : List TypedBinder) (result : TypeSystem.Ty) (body : List StatementId)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment) : Dynamic.Closure :=
  ⟨parameters, result, body, source named, captured, context, evidence⟩

private theorem evidence_lambda (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (compilation : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {view : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : view.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller compilation child fuel view scope id reasonAt callables = .ok none := by
  have owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, found, form, owned, requirements, coercions,
    bind, Except.bind, pure, Except.pure]

/-- Successful execution of the actual ordinary callback yields its lambda
branch receipt and all production hook profiles. No lambda-body execution is
an input. Excluding the generalized-initializer override is a static condition. -/
theorem contextual_certificate_with_policy_recipe {checked : SourceCoreCompatibleCatalog.Checked} (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : view.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered) :
    ∃ (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer),
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) (context prepared named)
        view scope id reasonAt = .ok lowered ∧
      Nonempty (CallableIndexedLambdaCertificates.Certificate policy lowerBody fuel (context prepared named)
        view scope id node parameters result body reported reasonAt lowered) ∧
      policy.sourceCells = some (allocator prepared named) ∧
      policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [] ∧
      policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [] ∧
      policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [] ∧
      policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked ∧
      policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
        ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [] ∧
      lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
          ((representation prepared).atContext named.signature.key [])
          (context prepared named).solvedRequirements compiled.own.assignments diagnostics
          (context prepared named).owner
          (SourceCoreGeneralFunctions.contextualBinder
            ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key []) ∧
      CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compiled fuel policy := by
  rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  dsimp only at accepted
  change (SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key |>.mapError SourceCoreBasic.Error.callPreparation) >>= _ = .ok lowered at accepted
  rw [record] at accepted
  simp only [Except.mapError, bind, Except.bind] at accepted
  refine ⟨_, _, accepted, ?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · apply CallableIndexedLambdaCertificates.of_accepted (owner := owner) (found := found) (form := form) (accepted := accepted)
    · change (do
        let actualSource ← SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram prepared.base.plan
          prepared.base.locals named.signature.key none view id
        _) = .ok none
      have unchanged : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram prepared.base.plan
          prepared.base.locals named.signature.key none view id = .ok view := by
        simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
      rw [unchanged]
      simp only [bind, Except.bind, pure, Except.pure, found]
      rw [ordinary]
      simp only [Option.filter_none]
      rw [evidence_lambda _ _ _ _ _ _ _ _ _ found form requirements coercions]
      simp [form]
    · change (do
        let actualSource ← SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram prepared.base.plan
          prepared.base.locals named.signature.key none view id
        SourceCoreCompatibleDataExpressions.readExpression checked actualSource id) = .ok (node, reported)
      simpa [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure] using read
  · change SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [] = _
    rw [prepared.ancestry.graph.inputs.callableSelected]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by funext lambda; simp⟩

/-- The original interface forgets only the additional literal policy fields. -/
theorem contextual_certificate_with_body_recipe {checked : SourceCoreCompatibleCatalog.Checked} (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : view.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered) :
    ∃ (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer),
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) (context prepared named)
        view scope id reasonAt = .ok lowered ∧
      Nonempty (CallableIndexedLambdaCertificates.Certificate policy lowerBody fuel (context prepared named)
        view scope id node parameters result body reported reasonAt lowered) ∧
      policy.sourceCells = some (allocator prepared named) ∧
      policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [] ∧
      policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [] ∧
      policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [] ∧
      policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked ∧
      policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
        ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [] ∧
      lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
          ((representation prepared).atContext named.signature.key [])
          (context prepared named).solvedRequirements compiled.own.assignments diagnostics
          (context prepared named).owner
          (SourceCoreGeneralFunctions.contextualBinder
            ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key []) := by
  obtain ⟨policy, lowerBody, generated, certificate, cells, manifest, hook, callables,
    projector, binderPolicy, bodyRecipe, _policyRecipe⟩ :=
    contextual_certificate_with_policy_recipe prepared compiled record found form owner
      requirements coercions ordinary read accepted
  exact ⟨policy, lowerBody, generated, certificate, cells, manifest, hook, callables,
    projector, binderPolicy, bodyRecipe⟩


/-- Forget only the retained actual body recipe. -/
theorem contextual_certificate_with_binder {checked : SourceCoreCompatibleCatalog.Checked} (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : view.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered) :
    ∃ (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer),
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) (context prepared named)
        view scope id reasonAt = .ok lowered ∧
      Nonempty (CallableIndexedLambdaCertificates.Certificate policy lowerBody fuel (context prepared named)
        view scope id node parameters result body reported reasonAt lowered) ∧
      policy.sourceCells = some (allocator prepared named) ∧
      policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [] ∧
      policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [] ∧
      policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [] ∧
      policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked ∧
      policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
        ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [] := by
  obtain ⟨policy, lowerBody, accepted, certificate, cells, manifest, hook, callables, projector, binderPolicy, _recipe⟩ :=
    contextual_certificate_with_body_recipe prepared compiled record found form owner requirements coercions ordinary read accepted
  exact ⟨policy, lowerBody, accepted, certificate, cells, manifest, hook, callables, projector, binderPolicy⟩

/-- The original interface forgets only the actual binder policy receipt. -/
theorem contextual_certificate {checked : SourceCoreCompatibleCatalog.Checked} (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : view.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered) :
    ∃ (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer),
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) (context prepared named)
        view scope id reasonAt = .ok lowered ∧
      Nonempty (CallableIndexedLambdaCertificates.Certificate policy lowerBody fuel (context prepared named)
        view scope id node parameters result body reported reasonAt lowered) ∧
      policy.sourceCells = some (allocator prepared named) ∧
      policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [] ∧
      policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [] ∧
      policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [] ∧
      policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked := by
  obtain ⟨policy, lowerBody, generated, receipt, allocation, manifest, expression, callables, projector, _binder⟩ :=
    contextual_certificate_with_binder prepared compiled record found form owner requirements coercions ordinary read accepted
  exact ⟨policy, lowerBody, generated, receipt, allocation, manifest, expression, callables, projector⟩

/-- A static ordinary generation site keeps the actual callback receipt. Its
owner and native parent are established by that callback, rather than supplied
as unrelated alignment fields by a consumer. -/
structure Site {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (parameters : List TypedBinder) (result : TypeSystem.Ty) (body : List StatementId)
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (captured : Dynamic.Environment) (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context) where private mk ::
  code : Code prepared (closure named parameters result body sourceContext evidence captured) scope administrative
  compilation : code.compilation = context prepared named
  active : code.active = []
  allocationError : code.allocationError = fun error => .sourceAllocation (reprStr error)
  /-- The site's lambda copies its captures at creation. -/
  snapshots : code.policy.snapshotLambda code.id = true

private theorem descriptor_exists (table : SourceCoreStageCodebook.Table)
    {origin : SourceCoreStageCodebook.Origin} {id : Word} (selected : table.idAt? origin = some id) :
    Nonempty (SourceCoreCallableContracts.Descriptor table origin) := by
  cases accepted : SourceCoreCallableContracts.descriptor table origin with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at accepted
    split at accepted
    · rename_i absent
      rw [selected] at absent
      cases absent
    · cases accepted
  | ok descriptor => exact ⟨descriptor⟩

/-- A genuine same-policy lambda certificate constructs one literal Site.
The policy and child fuel are retained before any contextual forgetting. -/
theorem of_certificate {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (receipt : CallableIndexedLambdaCertificates.Certificate policy lowerBody fuel (context prepared named)
      view scope id node parameters result body reported reasonAt lowered)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      (context prepared named) view scope id reasonAt = .ok lowered)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (allocationProfile : policy.sourceCells = some (allocator prepared named))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [])
    (expressionProfile : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (snapshots : policy.snapshotLambda id = true)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧ site.code.policy = policy ∧
      site.code.lowerBody = lowerBody ∧ site.code.fuel = fuel ∧ site.code.view = view ∧
      site.code.reasonAt = reasonAt ∧ site.code.sourceNode = sourceNode ∧ site.code.node = node ∧
      HEq site.code.receipt receipt := by
  have parameterProjected := receipt.parameterProjected
  have resultProjected := receipt.resultProjected
  rw [projector] at parameterProjected resultProjected
  have parameterProjected := CompatibleExpressionReads.projectType_of_accepted parameterProjected
  have resultProjected := CompatibleExpressionReads.projectType_of_accepted resultProjected
  have projection : checked.catalog.project (FunctionValues.sourceType
      (closure named parameters result body sourceContext evidence captured)) =
      .ok (CallableContract.functionType receipt.parameterCore receipt.resultCore) := by
    change checked.catalog.project (.function (TypeSystem.Ty.productMany (parameters.map (·.scheme.body))) result) = _
    rw [receipt.parameterTypes]
    simp [SourceCoreCompatibleCatalog.Catalog.project, parameterProjected, resultProjected,
      SourceCoreCompatibleCatalog.Catalog.functionType, profile, bind, Except.bind, pure, Except.pure]
  have reportedType : reported = CallableContract.functionType receipt.parameterCore receipt.resultCore := by
    have h := receipt.checked
    rw [callables] at h
    unfold SourceCoreBasic.ensureType at h
    split at h
    · assumption
    · cases h
  have typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType (CallableContract.functionType receipt.parameterCore receipt.resultCore))
      prepared.layouts.definitions := by
    simpa only [congrArg SourceCoreBasic.LoweredExpr.type receipt.emitted, reportedType] using typed
  have hook := receipt.expressionHook
  rw [expressionProfile] at hook
  obtain ⟨origin, _, selected, _, _, _, _, _⟩ := CallableIndexedFormation.expressionHook_receipt prepared.ancestry hook
  rw [(lookupExpression?_sound found).2] at selected
  obtain ⟨descriptor⟩ := descriptor_exists _ selected
  let code : Code prepared (closure named parameters result body sourceContext evidence captured) scope administrative := {
    policy, lowerBody, fuel, compilation := context prepared named, active := [], view, viewOfSource,
    id, sourceNode, sourceFound, sourceForm, node, found, form, reported, reasonAt, lowered, receipt, accepted,
    allocationError := fun error => .sourceAllocation (reprStr error), allocationProfile, manifest, expressionProfile,
    callables, descriptor, projection, typed }
  exact ⟨⟨code, rfl, rfl, rfl, snapshots⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.refl receipt⟩

/-- Build every static code field from the actual named callback's accepted
ordinary lambda branch. Canonical metadata and native checking remain explicit,
but no generation-history alignment is assumed. -/
theorem of_contextual_with_policy_recipe {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
        site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
          ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [] ∧
        site.code.lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
          ((representation prepared).atContext named.signature.key [])
          (context prepared named).solvedRequirements compiled.own.assignments diagnostics
          (context prepared named).owner
          (SourceCoreGeneralFunctions.contextualBinder
            ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key []) ∧
        CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named site.code := by
  obtain ⟨policy, lowerBody, accepted, ⟨receipt⟩, allocationProfile, manifest, expressionProfile, callables, projector, binderPolicy, bodyRecipe, policyRecipe⟩ :=
    contextual_certificate_with_policy_recipe prepared compiled record found (form.trans sourceForm) owner requirements coercions ordinary read accepted
  obtain ⟨site, identifier, emitted, samePolicy, sameBody, sameFuel, _view, _reasonAt, _sourceNode, _node, _receipt⟩ :=
    of_certificate prepared sourceContext evidence captured receipt accepted profile viewOfSource
      sourceFound sourceForm found form allocationProfile manifest expressionProfile callables projector
      (by rw [policyRecipe.snapshotLambda]) typed
  have actualBody : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compiled site.code :=
    sameBody.trans bodyRecipe
  have actualPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe
      compiled site.code.fuel site.code.policy := by
    rw [sameFuel, samePolicy]
    exact policyRecipe
  exact ⟨site, identifier, emitted,
    (congrArg SourceCoreFunctions.Policy.lowerBinder samePolicy).trans binderPolicy,
    sameBody.trans bodyRecipe,
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained.of_recipes
      compiled actualBody actualPolicy site.compilation⟩

/-- The original Site interface forgets only its correlated full-policy proof. -/
theorem of_contextual_with_body_recipe {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
        site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
          ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [] ∧
        site.code.lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
          ((representation prepared).atContext named.signature.key [])
          (context prepared named).solvedRequirements compiled.own.assignments diagnostics
          (context prepared named).owner
          (SourceCoreGeneralFunctions.contextualBinder
            ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key []) := by
  obtain ⟨site, identifier, emitted, binderPolicy, bodyRecipe, _policyRecipe⟩ :=
    of_contextual_with_policy_recipe prepared compiled record sourceContext evidence captured
      profile viewOfSource sourceFound sourceForm found form owner requirements coercions
      ordinary read accepted typed
  exact ⟨site, identifier, emitted, binderPolicy, bodyRecipe⟩


/-- Forget only the selected Code body recipe. -/
theorem of_contextual_with_binder {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
        site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
          ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [] := by
  obtain ⟨site, siteId, siteLowered, binderPolicy, _recipe⟩ := of_contextual_with_body_recipe prepared compiled record
    sourceContext evidence captured profile viewOfSource sourceFound sourceForm found form owner requirements coercions
    ordinary read accepted typed
  exact ⟨site, siteId, siteLowered, binderPolicy⟩

/-- The original site factory preserves its complete Code and output fields. -/
theorem of_contextual {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered := by
  obtain ⟨site, siteId, siteLowered, _binder⟩ := of_contextual_with_binder prepared compiled record
    sourceContext evidence captured profile viewOfSource sourceFound sourceForm found form owner requirements coercions
    ordinary read accepted typed
  exact ⟨site, siteId, siteLowered⟩

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {capturedSource : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope}

/-- The named seed and factory-created site agree on full source, owner and
native parent. Source context, evidence and captured locations remain exactly
the arguments to the closure constructor. -/
def Site.historyAt {administrative : Core.Context}
    (site : Site prepared named parameters result body sourceContext evidence capturedSource scope administrative)
    {origin : Word}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized) :
    History site.code where
  native := SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin
  ghost := .named origin
  metadata := state named
  carried := named_complete prepared.ancestry.graph (seed prepared selected record)
  source := rfl
  owner := by rw [site.compilation]; rfl
  active := site.active.symm

/-- The real named entry hook supplies the selected origin; consumers do not
invent a matching graph index or any of the three history alignment fields. -/
theorem Site.history {administrative : Core.Context}
    (site : Site prepared named parameters result body sourceContext evidence capturedSource scope administrative)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized) :
    ∃ origin, prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      ∃ history : History site.code,
        history.native = SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin ∧
        history.ghost = .named origin ∧ history.metadata = state named := by
  obtain ⟨origin, selected, _, _⟩ := compiled.history record
  exact ⟨origin, selected, site.historyAt selected record, rfl, rfl, rfl⟩

/-- A real initial frame read justifies the administrative write. An explicit
prefix frame contract transports that exact token to the generation store;
it is not inferred from native typing or arbitrary preceding code. -/
theorem installed_after_prefix {origin : Word} {before after : Store} {location : Location}
    {saved : Value} {mapping futureMapping : LocationMap}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (read : before.read? location = some saved) (unmapped : location ∉ mapping)
    (preserved : AdministrativePreserved mapping
      (before.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) futureMapping after) :
    location ∉ futureMapping ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) (.named origin) after := by
  have installed := CallableIndexedNamedGeneration.installed selected record read
  have bound := (List.getElem?_eq_some_iff.mp installed.read).1
  obtain ⟨absent, same⟩ := preserved location unmapped bound
  exact ⟨absent, same.trans installed.read, installed.history⟩

/-- Generation and completed reflection at this accepted site, following an
administratively preserving prefix from the real named entry. Runtime capture
authentication is supplied independently and the actual captured environment
is retained, including hidden slots. -/
theorem Site.formation_after_prefix
    {mapping world actual}
    (captured : Captures prepared mapping world scope capturedSource actual)
    (site : Site prepared named parameters result body sourceContext evidence capturedSource scope captured.administrative)
    {origin : Word}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (program : Program) (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout site.code.sourceNode.requirements site.code.sourceNode.coercions [])
    (coercions : site.code.sourceNode.coercions = [])
    {entryStore store : Store} {location : Location} {saved : Value} {entryMap : LocationMap}
    (entryRead : entryStore.read? location = some saved) (unmapped : location ∉ entryMap)
    (preserved : AdministrativePreserved entryMap
      (entryStore.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) mapping store)
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects prepared.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (copied : site.code.policy.snapshotLambda site.code.id = true)
    (referenceIndex : site.code.referenceIndex = scope.length + 1 + prepared.base.globals.length)
    (reference : captured.canonical[site.code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location)) :
    ∃ formed : Formed model captured site.code (site.historyAt selected record) heap store location,
      Dynamic.ExpressionEvaluates program sourceContext evidence (source named) capturedSource heap site.code.id
        (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (site.code.lowered.expression.rename captured.embedding)
        (.inRight .word (value site.code formed.embedding
          (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) formed.closureActual))
        formed.finalStore ∧
      Represents prepared formed.finalMap formed.finalWorld
        (FunctionValues.sourceType (closure named parameters result body sourceContext evidence capturedSource))
        (.closure formed.closure)
        (value site.code formed.embedding (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)
          formed.closureActual)
        (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) := by
  obtain ⟨_, cell⟩ := installed_after_prefix selected record entryRead unmapped preserved
  obtain ⟨formed⟩ := formation captured site.code (site.historyAt selected record) copied referenceIndex heaps
    reference cell.read
  exact ⟨formed, formed.source program ordinary coercions, formed.evaluated,
    formed.represents heaps.runtime_hasTypes⟩

theorem Site.reflects_after_prefix
    {mapping world actual}
    (captured : Captures prepared mapping world scope capturedSource actual)
    (site : Site prepared named parameters result body sourceContext evidence capturedSource scope captured.administrative)
    {origin : Word}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (program : Program) (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout site.code.sourceNode.requirements site.code.sourceNode.coercions [])
    (coercions : site.code.sourceNode.coercions = [])
    {entryStore store after : Store} {location : Location} {saved output : Value} {entryMap : LocationMap}
    (entryRead : entryStore.read? location = some saved) (unmapped : location ∉ entryMap)
    (preserved : AdministrativePreserved entryMap
      (entryStore.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) mapping store)
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects prepared.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (copied : site.code.policy.snapshotLambda site.code.id = true)
    (referenceIndex : site.code.referenceIndex = scope.length + 1 + prepared.base.globals.length)
    (reference : captured.canonical[site.code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (completed : Evaluates actual store (site.code.lowered.expression.rename captured.embedding) output after) :
    ∃ formed : Formed model captured site.code (site.historyAt selected record) heap store location,
      output = .inRight .word (value site.code formed.embedding
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) formed.closureActual) ∧
      after = formed.finalStore ∧
      Dynamic.ExpressionEvaluates program sourceContext evidence (source named) capturedSource heap site.code.id
        (.closure formed.closure) formed.finalHeap ∧
      Represents prepared formed.finalMap formed.finalWorld
        (FunctionValues.sourceType (closure named parameters result body sourceContext evidence capturedSource))
        (.closure formed.closure)
        (value site.code formed.embedding (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)
          formed.closureActual)
        (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) := by
  obtain ⟨_, cell⟩ := installed_after_prefix selected record entryRead unmapped preserved
  obtain ⟨formed⟩ := formation captured site.code (site.historyAt selected record) copied referenceIndex heaps
    reference cell.read
  obtain ⟨sameOutput, sameStore⟩ := formed.reflects completed
  exact ⟨formed, sameOutput, sameStore, formed.source program ordinary coercions,
    formed.represents heaps.runtime_hasTypes⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewPrefix
/-! A closure's entry copies its captured cells and then installs its
parameters, reaching the actual monomorphic call context. Its
finite continuation agreement comes from the production allocation receipts;
the compiler view is retained independently of the canonical closure source.
Body correspondence remains a separate concrete static certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

/-- The allocation authenticator observes the same owner, binder inputs,
forms, and statement metadata in every genuine metadata view. -/
theorem sourceView_eq {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view) :
    SourceCoreAllocationCodebook.sourceView source = SourceCoreAllocationCodebook.sourceView view := by
  have go {before after : List Node} (related : DataPatternValues.ListRel LambdaMetadataViews.NodeView before after) :
      before.map (fun node => match node with
        | .expression expression => SourceCoreAllocationCodebook.MetadataNode.expression expression.id expression.form
        | .statement statement => .statement statement) =
      after.map (fun node => match node with
        | .expression expression => SourceCoreAllocationCodebook.MetadataNode.expression expression.id expression.form
        | .statement statement => .statement statement) := by
    induction related with
    | nil => rfl
    | cons head _ ih =>
      cases head with
      | expression sameId sameForm => simp only [List.map_cons, sameId, sameForm, ih]
      | statement => exact congrArg (List.cons _) ih
  simp only [SourceCoreAllocationCodebook.sourceView, metadata.owner, metadata.inputs, metadata.roots]
  exact congrArg (fun nodes => SourceCoreAllocationCodebook.MetadataSource.mk view.owner view.inputs view.roots nodes) (go metadata.nodes)

structure Entry (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : SourceCoreCallableIndexedFrames.Frame) (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (scope : Scope) (bindings : List Binding)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (parameterCode body : Expr) where private mk ::
  copies : Dynamic.Environment
  copiedHeap : Dynamic.Heap
  copiedContext : Core.Context
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  copy : Dynamic.EnvironmentCopies function.source function.captured before copies copiedHeap
  allocation : Dynamic.BindersAllocate copies copiedHeap function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext bindings copiedContext) ambient.definitions
  reference : canonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + globals]? =
    some (.cellRef layout.type contextLocation)
  read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)
  unmapped : contextLocation ∉ mapping
  agreement : ContinuationAgreement actual initialStore (parameterCode.rename ξ) actualBody store (body.rename embedding)

private theorem liftMany_insertion (count cutoff : Nat) :
    DataMatchCoreAllocation.liftMany count (Renaming.insertion cutoff) = Renaming.insertion (cutoff + count) := by
  induction count generalizing cutoff with
  | zero => rfl
  | succ count ih =>
    simp only [DataMatchCoreAllocation.liftMany, Renaming.lift_insertion, ih]
    congr 1
    omega

namespace Stateful

/-- The entry copies the closure's captured cells through the marked
allocator, then the actual prefix receipts construct parameter allocation, the
typed body environment and the surviving context-reference slot. Its read and
unmapped status follow from allocation preservation. The protected state
crosses the copies administratively and is rebound to the copied slots. No
final body facts are assumed. -/
theorem entry_of_accepted_with_spine_of_copies
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts layout
      (CompatibleAmbientHeap.payloadModel values.checked registry functions))
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (rebinds : ProtectedStateTransition.Rebinds protocol)
    {function : Dynamic.Closure} {view : TypedSource} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body allocatedCode parameterCode : Expr}
    (inputIds : function.source.inputs.map TypedBinder.id = view.inputs.map TypedBinder.id)
    (copies : SourceSemantics.CaptureBinders.copiedBinder? function.source =
      SourceSemantics.CaptureBinders.copiedBinder? view)
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      view scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok allocatedCode)
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
      view scope (· + 1) allocatedCode = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (kinds : ∀ binding ∈ bindings, function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope function.captured canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (types : Renaming.Respects ξ (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) ::
      (SourceCoreLocalCell.coreContext scope ++ administrative)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native) :
    ∃ entry : Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body,
      ∃ added copied : Environment, added.length = bindings.length ∧ entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  obtain ⟨copiesEnvironment, copiedHeap, copiedCanonical, copiedActual, copiedContext, copiedStore, copiedMap,
      copiedWorld, copiedEmbedding, copy, copiedEnvironments, slots, copiedHeaps, copiedMaps, copiedWorlds,
      copiedFrame, copiedRead, copiedLookups, _copiedTypes, copiedTyped, copyAgreement⟩ :=
    CaptureCopies.marked_copies_prefix (pre := [DataPatternValues.packValues nativeArguments])
      (preContext := [SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)])
      copied definitions registered environments heaps actualLayout rfl types actualTyped reference read
  have sourceCopy := copy.of_copiedBinder copies.symm
  obtain ⟨copiedUnmapped, _⟩ := copiedFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
  obtain ⟨extendedState, extendedRelated⟩ := ProtectedStateTransition.AdministrativeTransport.transition protocol
    transport initial copiedMaps copiedWorlds copiedFrame sourceCopy.metadata_extends
  obtain ⟨reboundState, reboundRelated⟩ := rebinds extendedState copiedCanonical slots
  have copiedReference : copiedCanonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation) := by
    rw [slots _ (by omega)]
    exact reference
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) copiedCanonical
      (DataPatternValues.packValues nativeArguments :: copiedCanonical) := by
    intro index value found; exact found
  have length : (bindings.map Prod.snd).length = nativeArguments.length := by simpa using represented.length.2
  obtain ⟨environment, heap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
      allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, sourceLayout, lookups, spine, finalTyped, agreement, transition⟩ :=
    CallableIndexedParameterTyped.Stateful.prefix_typed tree protocol producer definitions registered
      (represented.extend copiedMaps copiedWorlds) copiedEnvironments copiedHeaps
      sourceLayout copiedLookups copiedTyped (allTypes := bindings.map Prod.snd) (named := false) rfl (by simp) length
      (fun {_ _} found => by simpa using found)
      (by
        intro binding member
        have same := congrArg (fun ids : List Resolved.LocalId =>
          ids.any (fun id => decide (id = binding.1.id))) inputIds
        simp only [List.any_map] at same
        exact same.symm.trans (kinds binding member))
      (by simpa using copiedReference) copiedRead copiedUnmapped reboundState readyAt
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have finalReference : finalCanonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + globals]? =
      some (.cellRef layout.type contextLocation) := by
    rw [canonicalEq]
    simp only [List.length_append, List.length_map, List.length_reverse]
    have index : bindings.length + scope.length + 1 + globals = added.length + (scope.length + 1 + globals) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using copiedReference
  have finalLookups : EnvironmentsAgree (Renaming.comp embedding (Renaming.insertion bindings.length))
      finalCanonical finalActual := by
    intro index value found
    apply lookups
    have transported := sourceLayout found
    simpa only [liftMany_insertion, Nat.zero_add] using transported
  have bodyEq : (body.weakenAt bindings.length).rename embedding =
      body.rename (Renaming.comp embedding (Renaming.insertion bindings.length)) := by
    rw [← Expr.rename_insertion, Expr.rename_comp]
  rw [bodyEq] at agreement
  obtain ⟨finalUnmapped, unchanged⟩ := preservation contextLocation copiedUnmapped (List.getElem?_eq_some_iff.mp copiedRead).1
  rw [← parameters] at allocated
  have mono := FunctionCallBody.mono_binders extended
  have copiedLocals := Dynamic.EnvironmentCopies.agrees initialLocals sourceCopy
  refine ⟨⟨copiesEnvironment, copiedHeap, copiedContext, environment, heap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, Renaming.comp embedding (Renaming.insertion bindings.length),
    sourceCopy, allocated, by simpa [CallableIndexedParameters.scope_eq] using finalEnvironments, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 copiedLocals allocated,
    copiedMaps.trans maps, copiedWorlds.trans worlds, copiedFrame.trans preservation,
    sourceCopy.metadata_extends.trans (GenericLexicalContext.binders_metadata allocated), finalLookups, finalTyped,
    finalReference, unchanged.trans copiedRead, finalUnmapped, copyAgreement.continuation.trans agreement⟩,
    added, copiedCanonical, prefixLength, canonicalEq, slots, ?_⟩
  have composed : ProtectedStateTransition.Transition protocol initial
      ⟨bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
        finalMap, finalWorld, heap, finalStore, finalCanonical⟩ := by
    obtain ⟨reached, related⟩ := transition
    exact ⟨reached, protocol.trans (protocol.trans extendedRelated reboundRelated) related⟩
  simpa only [CallableIndexedParameters.scope_eq] using composed

/-- Compatibility with the original full metadata-view receipt. -/
theorem entry_of_accepted_with_spine
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts layout
      (CompatibleAmbientHeap.payloadModel values.checked registry functions))
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (rebinds : ProtectedStateTransition.Rebinds protocol)
    {function : Dynamic.Closure} {view : TypedSource} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body allocatedCode parameterCode : Expr}
    (viewOfSource : LambdaMetadataViews.MetadataView function.source view)
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      view scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok allocatedCode)
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
      view scope (· + 1) allocatedCode = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (kinds : ∀ binding ∈ bindings, function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope function.captured canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (types : Renaming.Respects ξ (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) ::
      (SourceCoreLocalCell.coreContext scope ++ administrative)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native) :
    ∃ entry : Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body,
      ∃ added copied : Environment, added.length = bindings.length ∧ entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := by
  exact entry_of_accepted_with_spine_of_copies functions onError protocol producer transport rebinds
    (congrArg (List.map TypedBinder.id) viewOfSource.inputs) (LambdaMetadataViews.MetadataView.copiedBinder viewOfSource)
    accepted copied parameters kinds extended definitions registered represented environments heaps initialLocals
    actualLayout types actualTyped reference read unmapped initial readyAt

end Stateful

theorem entry_of_accepted_with_spine
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {view : TypedSource} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body allocatedCode parameterCode : Expr}
    (viewOfSource : LambdaMetadataViews.MetadataView function.source view)
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      view scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok allocatedCode)
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
      view scope (· + 1) allocatedCode = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (kinds : ∀ binding ∈ bindings, function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope function.captured canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (types : Renaming.Respects ξ (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) ::
      (SourceCoreLocalCell.coreContext scope ++ administrative)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    ∃ entry : Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body,
      ∃ added copied : Environment, added.length = bindings.length ∧ entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) := by
  obtain ⟨entry, added, copied, length, spine, slots, _transition⟩ :=
    Stateful.entry_of_accepted_with_spine functions onError ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer layouts layout
        (CompatibleAmbientHeap.payloadModel values.checked registry functions))
      ProtectedStateTransition.OrdinaryAllocation.unitTransport ProtectedStateTransition.OrdinaryAllocation.unitRebinds
      viewOfSource accepted copied parameters kinds extended definitions registered represented environments heaps
      initialLocals actualLayout types actualTyped reference read unmapped () (by intro index state read; trivial)
  exact ⟨entry, added, copied, length, spine, slots⟩

/-- The original receipt forgets only the certified canonical allocation prefix. -/
theorem entry_of_accepted
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {view : TypedSource} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body allocatedCode parameterCode : Expr}
    (viewOfSource : LambdaMetadataViews.MetadataView function.source view)
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      view scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok allocatedCode)
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
      view scope (· + 1) allocatedCode = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (kinds : ∀ binding ∈ bindings, function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope function.captured canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (types : Renaming.Respects ξ (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) ::
      (SourceCoreLocalCell.coreContext scope ++ administrative)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    Nonempty (Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body) := by
  obtain ⟨entry, _⟩ := entry_of_accepted_with_spine functions onError viewOfSource accepted copied parameters kinds
    extended definitions registered represented environments heaps initialLocals actualLayout types actualTyped
    reference read unmapped
  exact ⟨entry⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaPrefix
/-! A closure's entry copies its captured cells and then installs its
parameters, reaching the actual monomorphic call context. Its
finite continuation agreement comes from the production allocation receipts;
body correspondence comes from the extracted mixed lexical certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

structure Entry (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : SourceCoreCallableIndexedFrames.Frame) (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (scope : Scope) (bindings : List Binding)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (parameterCode body : Expr) where private mk ::
  copies : Dynamic.Environment
  copiedHeap : Dynamic.Heap
  copiedContext : Core.Context
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  copy : Dynamic.EnvironmentCopies function.source function.captured before copies copiedHeap
  allocation : Dynamic.BindersAllocate copies copiedHeap function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext bindings copiedContext) ambient.definitions
  reference : canonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + globals]? =
    some (.cellRef layout.type contextLocation)
  read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)
  unmapped : contextLocation ∉ mapping
  agreement : ContinuationAgreement actual initialStore (parameterCode.rename ξ) actualBody store (body.rename embedding)

/-- Actual prefix receipts copy the captured cells and construct parameter
allocation, the typed body environment and the surviving context-reference
slot. Its read and unmapped status follow from allocation preservation. No
final body facts are assumed. -/
theorem entry_of_accepted
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {scope : Scope} {bindings : List Binding} {output : Ty} {body allocatedCode parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok allocatedCode)
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
      function.source scope (· + 1) allocatedCode = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (kinds : ∀ binding ∈ bindings, function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope function.captured canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (types : Renaming.Respects ξ (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) ::
      (SourceCoreLocalCell.coreContext scope ++ administrative)) actualContext)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    Nonempty (Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body) := by
  obtain ⟨entry⟩ := CallableIndexedLambdaViewPrefix.entry_of_accepted functions onError
    (LambdaMetadataViews.MetadataView.refl function.source) accepted copied parameters kinds extended definitions
    registered represented environments heaps initialLocals actualLayout types actualTyped reference read unmapped
  exact ⟨⟨entry.copies, entry.copiedHeap, entry.copiedContext, entry.environment, entry.heap, entry.canonical,
    entry.actualBody, entry.store, entry.mapping, entry.world, entry.embedding, entry.copy, entry.allocation,
    entry.environments, entry.heaps, entry.locals, entry.maps, entry.worlds, entry.frame, entry.metadata,
    entry.lookups, entry.actualTyped, entry.reference, entry.read, entry.unmapped, entry.agreement⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaManifest
/-! Actual lambda manifests select only existing lexical references. Their
private binder is threaded into the subsequent parameter environment through
an explicit renaming; no closure or store is compared by exact weakening. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaManifest
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open SourceCoreLambdaTemplates

private theorem manifest_rename (fields : List (Word × Ty)) (ξ : Renaming) :
    (scopeManifest fields).rename ξ = scopeManifest fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih => simp [scopeManifest, Expr.rename, ih]

private theorem captures_rename (scope : SourceCoreLocalCell.Scope) (references ξ : Renaming) :
    (SourceCoreSourceCells.captures references scope).rename ξ =
      SourceCoreSourceCells.captures (Renaming.comp ξ references) scope := by
  induction scope generalizing references with
  | nil => rfl
  | cons head rest ih => cases rest with
    | nil => rfl
    | cons next tail => simp only [SourceCoreSourceCells.captures, Expr.rename, ih]; rfl

private theorem shifted (body : Expr) (ξ : Renaming) :
    (body.weakenAt 0).rename ξ.lift = body.rename (Renaming.comp (Renaming.insertion 0) ξ) := by
  rw [← Expr.rename_insertion, Expr.rename_comp]
  rfl

private theorem fields_typed {world : StoreTyping} {definitions : DataEnvironment}
    (fields : List (Word × Ty)) :
    RuntimeValueHasType world (scopeManifestValue fields) (scopeManifestType fields) definitions := by
  induction fields with
  | nil => exact .unit
  | cons head rest ih => exact .pair (.pair .word (.inLeft .unit)) ih

/-- This shape comes from the actual hook's successful traversal. It does not
assert source history or call semantics. -/
theorem of_hook {checked : SourceCoreCompatibleCatalog.Checked}
    {inventory : Inventory checked} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {node : ExpressionNode}
    {parameter result : Ty} {body emitted : Expr}
    (accepted : hook inventory owner active compilation source scope node parameter result body = .ok emitted) :
    ∃ descriptor fields, emitted = manifestBody descriptor fields (SourceCoreSourceCells.captures id scope) body := by
  simp only [hook, bind, Except.bind, pure, Except.pure, throw] at accepted
  repeat' first | split at accepted | contradiction
  all_goals exact ⟨_, _, (Except.ok.inj accepted).symm⟩

/-- A finite manifest prefix is constructed from mapped captures. Both its
runtime type and bidirectional continuation agreement use the real environment. -/
theorem agreement {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {source : Dynamic.Environment} {canonical actual : Environment}
    {argument : Value} {ξ : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical definitions)
    (agrees : EnvironmentsAgree ξ (argument :: canonical) actual)
    (descriptor : Word) (fields : List (Word × Ty))
    (body : Expr) (store : Store) :
    ∃ manifest,
      RuntimeValueHasType world manifest
        (.product .word (.product (scopeManifestType fields) (SourceCoreSourceCells.captureType scope))) definitions ∧
      ContinuationAgreement actual store
        ((manifestBody descriptor fields (SourceCoreSourceCells.captures id scope) body).rename ξ)
        (manifest :: actual) store (body.rename (Renaming.comp (Renaming.insertion 0) ξ)) := by
  have capturesAgree : EnvironmentsAgree (fun index => ξ (index + 1)) canonical actual := by
    intro index value found
    exact agrees (index := index + 1) found
  obtain ⟨captured, selected, typed⟩ := CallableIndexedOrdinaryAllocation.captures_typed related capturesAgree
  refine ⟨.pair (.word descriptor) (.pair (scopeManifestValue fields) captured), .pair .word (.pair (fields_typed fields) typed), ?_⟩
  simp only [manifestBody, Expr.rename, manifest_rename, shifted]
  apply ContinuationAgreement.letE
  apply Evaluates.pair .word (Evaluates.pair (scopeManifest_evaluates fields actual store) ?_)
  rw [← Expr.rename_insertion, Expr.rename_comp, captures_rename]
  exact selected.evaluates store

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaManifest
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBody
/-! A concrete lexical builtin statement tree discharges the body after the
actual lambda parameter fold. Both directions preserve the original captures,
source allocation order and every retained native temporary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
  {scope : Scope} {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
  (program : Program)
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {bindings : List Binding} {output : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming}

include definitions registered extension contextValid unique uninitialized missing faithful functionLeaves functionTypes in
/-- Finite source body execution completes the actual parameter prefix. The
source allocation is the one retained by the constructed entry. -/
theorem preserves
    (entry : CallableIndexedLambdaPrefix.Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (certificate : BuiltinNamedBody.Certificate layouts owner active layout globals onError readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : FunctionCallBody.Trace program function context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (parameterCode.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        administrative program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) entry.environment entry.heap after outcome := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, reached⟩ :=
    certificate.preserves functions extension definitions registered program contextValid unique uninitialized missing faithful functionLeaves functionTypes entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped trace
  exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, represented, heaps,
    entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata, reached⟩

include definitions registered extension contextValid unique uninitialized missing faithful functionLeaves functionTypes in
/-- Completed native prefix execution constructs the independent source trace
at the installed call context, without a universal body reflection premise. -/
theorem reflects
    (entry : CallableIndexedLambdaPrefix.Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (certificate : BuiltinNamedBody.Certificate layouts owner active layout globals onError readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates actual store (parameterCode.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        administrative program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) entry.environment entry.heap after outcome := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, reached⟩ :=
    certificate.reflects functions extension definitions registered program contextValid unique uninitialized missing faithful functionLeaves functionTypes entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped (entry.agreement.unwrap evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, entry.maps.trans maps,
    entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata, reached⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaInvocation
/-! Ordinary lambda entry uses the formation receipt's actual capture and
code, installs its authenticated lexical state, and constructs the parameter
prefix. The concrete body certificate is static; it contains no body run. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

structure Body {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program) where
  source : code.view = function.source
  frame : Dynamic.ClosureFrame program function
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  extended : MonoBindersExtend function.source.owner function.context function.parameters types context
  kinds : ∀ binding ∈ code.receipt.loweredParameters,
    function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false
  referenceIndex : code.referenceIndex = scope.length + 1 + prepared.base.globals.length
  readFuel : Nat
  policy : SourceCoreLoops.Policy
  bodyFuel : Nat
  certificate : BuiltinNamedBody.Certificate prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError readFuel values
    function.source context code.compilation.solvedRequirements code.reasonAt
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body function.resultType code.receipt.resultCore policy bodyFuel code.compilation.internalReason
    code.compilation.internalReason code.receipt.body
  valid : CompatibleExpressionLiterals.ContextValid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source

theorem parameters {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) :
    function.parameters = code.receipt.loweredParameters.map Prod.fst :=
  (FunctionCode.Parameters.of_accepted code.receipt.parametersCompiled).binders.symm

theorem prefix_accepted {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (source : code.view = function.source) :
    SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame prepared.base.globals.length
        (prepared.layouts.allocatorAt code.compilation.owner code.active code.allocationError))
      function.source scope code.receipt.loweredParameters code.receipt.resultCore SourceCoreFunctions.argumentProjection
      (code.receipt.body.weakenAt code.receipt.loweredParameters.length) = .ok code.receipt.allocatedBody := by
  have accepted := code.receipt.allocated
  simpa only [CallableIndexedLambdaCertificates.parameterBody, code.allocationProfile, source] using accepted

theorem copies_accepted {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (source : code.view = function.source) :
    SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame prepared.base.globals.length
        (prepared.layouts.allocatorAt code.compilation.owner code.active code.allocationError)))
      function.source scope (· + 1) code.receipt.allocatedBody = .ok code.receipt.copiedBody := by
  have copied := code.receipt.copied
  rw [code.allocationProfile] at copied
  simpa only [source] using copied

def bodyEmbedding (ξ : Renaming) : Renaming :=
  Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0)
    (Renaming.comp (Renaming.insertion 1) ξ.lift))

private theorem body_rename (body : Expr) (ξ : Renaming) :
    (((body.weakenAt 1).rename ξ.lift.lift).weakenAt 0).weakenAt 0 = body.rename (bodyEmbedding ξ) := by
  simp only [← Expr.rename_insertion, Expr.rename_comp, bodyEmbedding]
  congr 1
  funext index
  cases index <;> rfl

private theorem body_agrees {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (argument lexical saved : Value) :
    EnvironmentsAgree (bodyEmbedding ξ) (argument :: canonical) (.unit :: saved :: argument :: lexical :: actual) := by
  intro index value found
  cases index with
  | zero => exact found
  | succ index => exact agrees found

/-- After the manifest, the packed argument and the captured slots keep their
types through the body embedding. -/
private theorem body_respects {ξ : Renaming} {context actualContext : Core.Context}
    (respects : Renaming.Respects ξ context actualContext) (manifestType frameType argumentType : Ty) :
    Renaming.Respects (Renaming.comp (Renaming.insertion 0) (bodyEmbedding ξ)) (argumentType :: context)
      (manifestType :: .unit :: frameType :: argumentType :: frameType :: actualContext) := by
  intro index type found
  cases index with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
    subst type
    rfl
  | succ index =>
    simpa [bodyEmbedding, Renaming.comp, Renaming.insertion, Renaming.lift] using respects (by simpa using found)

private theorem reference_typed {definitions : DataEnvironment} {world : StoreTyping} {environment : Environment}
    {context : Core.Context} {index location : Nat} {type : Ty}
    (typed : RuntimeEnvironmentHasTypes world environment context definitions)
    (found : environment[index]? = some (.cellRef type location)) : world[location]? = some type := by
  have atType : context[index]? = some (.cell type) := by
    rw [← typed.type_tags]
    simp [List.getElem?_map, found, Value.type]
  obtain ⟨value, selected, related⟩ := typed.lookup atType
  have same := Option.some.inj (selected.symm.trans found)
  subst value
  cases related with | cellRef typed => exact typed

structure Entry {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
    (registry : SourceCoreRawMetadata.Registry) (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location) (current : NativeFrame) (currentGhost : GhostFrame) where private mk ::
  next : NativeFrame
  nextHistory : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next
    (.lambda code.descriptor.id history.ghost) (some history.metadata)
  actual : Environment
  actualContext : Core.Context
  embedding : Renaming
  entry : CallableIndexedLambdaPrefix.Entry prepared.ancestry.layout.frame prepared.base.globals.length location next values
    (model prepared profile) registry function body.context scope code.receipt.loweredParameters arguments before
    (store.set location (encode prepared.ancestry.layout.frame next)) mapping world captured.administrative
    actualContext actual embedding code.receipt.copiedBody code.receipt.body
  wrap : ∀ {result bodyStore}, Evaluates entry.actualBody entry.store (code.receipt.body.rename entry.embedding) result bodyStore →
    Evaluates (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result (bodyStore.set location (encode prepared.ancestry.layout.frame current))
  unwrap : ∀ {result finalStore},
    Evaluates (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore →
    ∃ bodyStore, Evaluates entry.actualBody entry.store (code.receipt.body.rename entry.embedding) result bodyStore ∧
      finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current)
  unmapped : location ∉ mapping
  referenceTyped : world[location]? = some prepared.ancestry.layout.frame.type
  currentHistory : Current prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost
  currentRead : store.read? location = some (encode prepared.ancestry.layout.frame current)

/-- Every native prefix step is derived from its actual compiler receipt.
The caller token and lexical token have independent carried histories. -/
theorem entry_exists {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
      mapping world code.receipt.loweredParameters arguments nativeArguments)
    {before : Dynamic.Heap} {store : Store} {location : Location}
    {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
    (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
    (unmapped : location ∉ mapping)
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true) :
    Nonempty (Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost) := by
  let layout := prepared.ancestry.layout.frame
  let argument := DataPatternValues.packValues nativeArguments
  let saved := encode layout current
  let lexical := encode layout history.native
  let next := SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id history.native current
  have registered := CallableIndexedAmbient.frame_registered prepared
  have caller : CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table layout location current currentGhost store :=
    ⟨read, .stable currentCarried⟩
  have nextHistory := ordinary_complete prepared.ancestry.graph history.carried currentCarried allowed
  have refTyped := reference_typed captured.represented.runtime_hasTypes reference
  obtain ⟨installedHeaps, installedCurrent⟩ := CallableIndexedBodyFrames.install registered heaps unmapped refTyped caller (.stable nextHistory)
  have hook := code.receipt.bodyHook
  rw [code.manifest] at hook
  obtain ⟨descriptor, fields, emitted⟩ := CallableIndexedLambdaManifest.of_hook hook
  let actual := .unit :: saved :: argument :: lexical :: capturedActual
  have actualLayout : EnvironmentsAgree (bodyEmbedding captured.embedding) (argument :: captured.canonical) actual :=
    body_agrees captured.agrees argument lexical saved
  have actualTyped : RuntimeEnvironmentHasTypes world actual
      (.unit :: layout.type :: SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) :: layout.type :: captured.actualContext)
      prepared.layouts.definitions :=
    .cons .unit (.cons (encode_runtime_typed world registered current)
      (.cons (CallableIndexedParameters.Arguments.pack_typed represented)
        (.cons (encode_runtime_typed world registered history.native) captured.typed)))
  obtain ⟨manifest, manifestTyped, manifestAgreement⟩ := CallableIndexedLambdaManifest.agreement
    captured.represented actualLayout descriptor fields code.receipt.copiedBody (store.set location (encode layout next))
  obtain ⟨entry⟩ := CallableIndexedLambdaPrefix.entry_of_accepted (model prepared profile) code.allocationError
    (prefix_accepted code body.source) (copies_accepted code body.source) (parameters code) body.kinds body.extended rfl
    registered represented captured.represented installedHeaps locals
    (GenericExpressionMeaning.agree_prefix actualLayout manifest) (body_respects captured.respects _ layout.type _)
    (.cons manifestTyped actualTyped) (body.referenceIndex ▸ reference) installedCurrent.read unmapped
  have selectedReference : (argument :: lexical :: capturedActual)[captured.embedding code.referenceIndex + 2]? =
      some (.cellRef layout.type location) := by simpa using captured.agrees reference
  have selected : DataEquality.Selects (argument :: lexical :: capturedActual)
      (.var (captured.embedding code.referenceIndex + 2)) (.cellRef layout.type location) := .var selectedReference
  have nextEvaluation : Evaluates (saved :: argument :: lexical :: capturedActual) store
      ((SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table layout code.descriptor.id (.var 1)
        (.loadCell (.var (captured.embedding code.referenceIndex + 2)))).weakenAt 0)
      (encode layout next) store := by
    obtain ⟨position, nativeEq, _⟩ := history.carried.state_shape
    dsimp only [next, lexical]
    rw [nativeEq, CallableIndexedRenaming.lambdaFrame_weaken]
    simpa only [Expr.weakenAt, Nat.zero_le, ↓reduceIte] using
      (CallableIndexedProtocol.lambdaFrame_load (layout := layout)
        (environment := saved :: argument :: encode layout (.state (Int.ofNat position)) :: capturedActual)
        (lexical := .var 2) (referenceIndex := captured.embedding code.referenceIndex + 3)
        prepared.ancestry.graph.table code.descriptor.id (.var rfl)
        (by simpa [Nat.add_assoc] using captured.agrees reference) read)

  have wrapper : code.body.rename captured.embedding.lift.lift =
      withFrame (.var (captured.embedding code.referenceIndex + 2))
        (SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table layout code.descriptor.id (.var 1)
          (.loadCell (.var (captured.embedding code.referenceIndex + 2))))
        ((code.receipt.rawBody.weakenAt 1).rename captured.embedding.lift.lift) := by
    simp only [Code.body, NamedCalls.withFrame_rename, CallableIndexedRenaming.lambdaFrame, Expr.rename, Renaming.lift]
    rfl
  have agreement : ContinuationAgreement actual (store.set location (encode layout next))
      (code.receipt.rawBody.rename (bodyEmbedding captured.embedding)) entry.actualBody entry.store
      (code.receipt.body.rename entry.embedding) := by
    rw [emitted]
    exact manifestAgreement.trans entry.agreement
  refine ⟨⟨next, nextHistory, _, _, _, entry, ?_, ?_, unmapped, refTyped, .stable currentCarried, read⟩⟩
  · intro result bodyStore evaluated
    rw [wrapper]
    apply CallableContextFrames.withFrame_evaluates selected read nextEvaluation
    rw [body_rename]
    exact agreement.wrap evaluated
  · intro result finalStore evaluated
    rw [wrapper] at evaluated
    obtain ⟨nextValue, nextStore, bodyStore, nextEval, bodyEval, finalEq⟩ :=
      CallableContextFrames.withFrame_reflects selected read evaluated
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEval nextEvaluation
    rw [body_rename] at bodyEval
    exact ⟨bodyStore, agreement.unwrap bodyEval, finalEq⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls
/-! Ordinary closure calls combine concrete lexical builtin bodies with the
actual indexed frame and marked parameter prefix. The lambda's generation
receipt and caller history remain semantic inputs. Completed native execution
constructs the independent source call; no body execution is an input. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaInvocation
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

private theorem retained_not_closure {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (related : CallableIndexedRetainedNamedValues.Represents prepared world sourceType source native type) :
    ∀ function, source ≠ .closure function := by
  cases related with
  | retained canonical =>
    cases canonical with
    | builtin prior => cases prior; intro function; simp [CallableNamedReversal.value]
    | named => intro function; simp [CallableNamedReversal.value]

/-- Inversion retains the exact closure environment and renamed body from its
formation receipt. Named and builtin leaves cannot supply this case. -/
theorem represented_closure {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {function : Dynamic.Closure} {native : Value} {type : Ty}
    (related : Represents prepared mapping world sourceType (.closure function) native type) :
    ∃ (scope : Scope) (actual : Environment) (captured : Captures prepared mapping world scope function.captured actual),
      ∃ (code : Code prepared function scope captured.administrative) (history : History code),
      sourceType = FunctionValues.sourceType function ∧
      native = value code captured.embedding history.native actual ∧
      type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
  cases related with
  | retained prior => exact False.elim (retained_not_closure prior function rfl)
  | lambda captured code history _ => exact ⟨_, _, captured, code, history, rfl, rfl, rfl⟩

/-- Apply the authenticated payload after argument and callee evaluation.
Descriptor stage guards and expression evaluation order belong to the enclosing
call head, and are not replaced by this payload law. -/
def applyPayload : Expr := .apply (.second (.first (.var 0))) (.var 1)

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))

include extension uninitialized missing in
theorem Entry.preserves
    (entry : Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost)
    {copies environment : Dynamic.Environment} {copied bound after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copied)
    (allocated : Dynamic.BindersAllocate copies copied function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy entry.entry.copy
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  have registered := CallableIndexedAmbient.frame_registered prepared
  obtain ⟨result, bodyStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    CallableIndexedLambdaBody.preserves (model prepared profile) extension rfl registered program body.valid body.unique uninitialized missing
      (identity_faithful prepared) (observations prepared profile) (runtime_views prepared profile) entry.entry body.certificate trace
  have bodyEval := entry.wrap (entry.entry.agreement.unwrap evaluated)
  have callEval : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result (bodyStore.set location (encode prepared.ancestry.layout.frame current)) :=
    .apply (.second (.first (.var rfl))) (.var rfl) bodyEval
  obtain ⟨restoredHeap, restoredFrame, restoredCaller⟩ := CallableIndexedBodyFrames.restore registered entry.unmapped entry.referenceTyped
    (show CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost store from
      ⟨entry.currentRead, entry.currentHistory⟩) finalHeaps worlds frame
  exact ⟨result, _, finalMap, finalWorld, callEval, related, restoredHeap, maps, worlds, restoredFrame, metadata, restoredCaller⟩

include extension uninitialized missing in
theorem Entry.reflects
    (entry : Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost)
    {result : Value} {finalStore : Store}
    (evaluated : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result finalStore) :
    ∃ copies copied environment bound outcome after finalMap finalWorld,
      Dynamic.EnvironmentCopies function.source function.captured before copies copied ∧
      Dynamic.BindersAllocate copies copied function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function body.context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  cases evaluated with
  | apply callee argument applied =>
    have expected : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store (.second (.first (.var 0)))
        (.closure code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore)
          (code.body.rename captured.embedding.lift.lift) (encode prepared.ancestry.layout.frame history.native :: capturedActual)) store :=
      .second (.first (.var rfl))
    obtain ⟨sameClosure, sameStore⟩ := evaluation_deterministic callee expected
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj sameClosure
    rw [sameStore] at argument
    obtain ⟨sameArgument, sameAfter⟩ := evaluation_deterministic argument
      (show Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store (.var 1) (DataPatternValues.packValues nativeArguments) store from .var rfl)
    rw [sameArgument, sameAfter] at applied
    obtain ⟨bodyStore, bodyEval, finalEq⟩ := entry.unwrap applied
    have registered := CallableIndexedAmbient.frame_registered prepared
    obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
      CallableIndexedLambdaBody.reflects (model prepared profile) extension rfl registered program body.valid body.unique uninitialized missing
        (identity_faithful prepared) (observations prepared profile) (runtime_views prepared profile) entry.entry body.certificate
        (entry.entry.agreement.wrap bodyEval)
    obtain ⟨restoredHeap, restoredFrame, restoredCaller⟩ := CallableIndexedBodyFrames.restore registered entry.unmapped entry.referenceTyped
      (show CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost store from
        ⟨entry.currentRead, entry.currentHistory⟩) finalHeaps worlds frame
    subst finalStore
    exact ⟨entry.entry.copies, entry.entry.copiedHeap, entry.entry.environment, entry.entry.heap, outcome, after,
      finalMap, finalWorld, entry.entry.copy, entry.entry.allocation, trace,
      related, restoredHeap, maps, worlds, restoredFrame, metadata, restoredCaller⟩

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem reflects {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {result : Value} {finalStore : Store}
    (evaluated : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨entry⟩ := entry_exists captured code history body profile represented heaps locals reference read currentCarried unmapped allowed
  obtain ⟨copies, copied, environment, bound, outcome, after, finalMap, finalWorld, copy, allocated, trace, rest⟩ :=
    Entry.reflects captured code history body profile extension uninitialized missing entry evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace.call body.frame body.extended copy allocated, rest⟩

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem preserves {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have arity : function.parameters.length = arguments.length := by rw [parameters code]; simpa using represented.length.1
  obtain ⟨types, context, copies, copied, environment, bound, extended, copy, allocated, trace⟩ :=
    FunctionCallBody.Outcome.trace arity executed
  have sameTypes : types = body.types := extended.bodyTypes_eq.symm.trans body.extended.bodyTypes_eq
  subst types
  have sameContext := extended.functional body.extended
  subst context
  obtain ⟨entry⟩ := entry_exists captured code history body profile represented heaps locals reference read currentCarried unmapped allowed
  exact Entry.preserves captured code history body profile extension uninitialized missing entry copy allocated trace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaTemplatePermission
/-! Template permission follows the actual compiler hook and the actual
prepared inventory. Source and native active substitutions remain distinct;
no call entry or body execution is asserted here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaTemplatePermission
open Core Frontend SourceInference CallableIndexedLambdaValues
open CallableAppliedViewProvenance

private theorem find_unique_key {α β : Type} [DecidableEq β] (items : List α) (key : α → β)
    (unique : (items.map key).Nodup) {item : α} (member : item ∈ items) :
    items.find? (fun candidate => decide (key candidate = key item)) = some item := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | member
    · subst item; simp
    · have different : key head ≠ key item := by
        intro same
        exact unique.1 (List.mem_map.mpr ⟨item, member, same.symm⟩)
      simpa [List.find?_cons, different] using ih unique.2 member

private theorem type_beq (left right : Core.Ty) : (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Core.instBEqTy.beq, Core.instBEqDataTypeId.beq]
  rename_i left right
  cases left; cases right; simp_all

/-- The successful raw hook retains its actual first selected template and
all checked native header fields. -/
theorem hook_template {checked : SourceCoreCompatibleCatalog.Checked}
    {inventory : SourceCoreLambdaTemplates.Inventory checked}
    {owner : SourceCompilationPlan.Key} {active : TypeSystem.Substitution}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {node : ExpressionNode}
    {parameter result : Core.Ty} {body emitted : Expr}
    (accepted : SourceCoreLambdaTemplates.hook inventory owner active compilation source scope
      node parameter result body = .ok emitted) :
    ∃ template, inventory.lambdas.find? (fun candidate => decide
        (candidate.owner = owner ∧ candidate.id = node.id ∧ candidate.active = active)) = some template ∧
      node.form = template.node.form ∧ parameter = template.parameterType ∧ result = template.resultType := by
  unfold SourceCoreLambdaTemplates.hook at accepted
  split at accepted
  · next template found =>
    simp only [bind, Except.bind, pure, Except.pure] at accepted
    split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · next shape =>
        have shape : node.form = template.node.form ∧ parameter = template.parameterType ∧
            result = template.resultType := by
          have checks : node.form = template.node.form ∧
              (parameter == template.parameterType) = true ∧ (result == template.resultType) = true := by
            simpa [bne, and_assoc] using shape
          exact ⟨checks.1, (type_beq _ _).mp checks.2.1, (type_beq _ _).mp checks.2.2⟩
        exact ⟨template, found, shape⟩
  · cases accepted

/-- Prepared templates refer to actual rows in the same selected table. -/
theorem prepared_entry {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    (inputs : SourceCoreCallableAncestryPreparation.Inputs base)
    {template : SourceCoreLambdaTemplates.Lambda} (authentic : PreparedTemplate base template) :
    ∃ entry, entry ∈ inputs.callable.table.entries ∧
      entry.origin = .lambda template.owner template.id template.active ∧
      entry.id = template.descriptor := by
  obtain ⟨_, _, callable, entry, _, _, _, _, _, _, selected, member, origin, id, _⟩ := authentic
  cases Option.some.inj (selected.symm.trans inputs.callableSelected)
  exact ⟨entry, member, origin, id⟩

/-- Equal actual lookup keys select the same full node in the prepared source. -/
theorem prepared_node {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    {left right : SourceCoreLambdaTemplates.Lambda}
    (leftPrepared : PreparedTemplate base left) (rightPrepared : PreparedTemplate base right)
    (owner : left.owner = right.owner) (id : left.id = right.id)
    (active : left.active = right.active) : left.node = right.node := by
  obtain ⟨receipts, metadata, _, _, _, _, _, _, receiptsAccepted, metadataAccepted,
    _, _, _, _, contextFound, _, _, _, _, nodeFound, _⟩ := leftPrepared
  obtain ⟨otherReceipts, otherMetadata, _, _, _, _, _, _, otherReceiptsAccepted,
    otherMetadataAccepted, _, _, _, _, otherContextFound, _, _, _, _, otherNodeFound, _⟩ := rightPrepared
  cases Except.ok.inj (receiptsAccepted.symm.trans otherReceiptsAccepted)
  cases Except.ok.inj (metadataAccepted.symm.trans otherMetadataAccepted)
  rw [owner, active] at contextFound
  have contexts := Option.some.inj (contextFound.symm.trans otherContextFound)
  rw [contexts, id] at nodeFound
  exact Option.some.inj (nodeFound.symm.trans otherNodeFound)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- The actual code and inventory determine the same descriptor, full source
node, ordered lambda parameters and native header. -/
theorem selected {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) :
    ∃ template, prepared.ancestry.graph.inputs.templates.lambdaAt? code.descriptor.id = some template ∧
      PreparedTemplate prepared.base template ∧
      template.owner = code.compilation.owner ∧ template.id = code.id ∧ template.active = code.active ∧
      template.node.form = .lambda function.parameters function.resultType function.body := by
  have hook := code.receipt.bodyHook
  rw [code.manifest] at hook
  obtain ⟨hookTemplate, hookFound, hookForm, _, _⟩ := hook_template hook
  have hookKeys : hookTemplate.owner = code.compilation.owner ∧ hookTemplate.id = code.node.id ∧ hookTemplate.active = code.active := by
    simpa using List.find?_some hookFound
  have hookPrepared := prepared_template prepared.ancestry.graph.inputs.templatesPrepared
    (List.mem_of_find?_eq_some hookFound)
  obtain ⟨entry, entryMember, entryOrigin, entryId⟩ :=
    prepared_entry prepared.ancestry.graph.inputs hookPrepared
  have nodeId := (lookupExpression?_sound code.found).2
  have origin : entry.origin = .lambda code.compilation.owner code.id code.active := by
    rw [entryOrigin, hookKeys.1, hookKeys.2.1, nodeId, hookKeys.2.2]
  have idAt := code.descriptor.found
  unfold SourceCoreStageCodebook.Table.idAt? at idAt
  have entryFound := find_unique_key _ _ prepared.ancestry.graph.inputs.callable.table.originsUnique entryMember
  simp only [origin] at entryFound
  rw [entryFound] at idAt
  have descriptor : hookTemplate.descriptor = code.descriptor.id := entryId.symm.trans (Option.some.inj idAt)
  cases found : prepared.ancestry.graph.inputs.templates.lambdaAt? code.descriptor.id with
  | none =>
    have rejected := List.find?_eq_none.mp found hookTemplate (List.mem_of_find?_eq_some hookFound)
    simp [descriptor] at rejected
  | some template =>
    have authentic := prepared_template prepared.ancestry.graph.inputs.templatesPrepared
      (List.mem_of_find?_eq_some found)
    have templateId : template.descriptor = code.descriptor.id := by simpa using List.find?_some found
    obtain ⟨other, otherMember, otherOrigin, otherId⟩ :=
      prepared_entry prepared.ancestry.graph.inputs authentic
    have leftLookup := CallableAncestryPairedValidation.stage_entry_self _ entryMember
    have rightLookup := CallableAncestryPairedValidation.stage_entry_self _ otherMember
    simp only [entryId, descriptor, otherId, templateId] at leftLookup rightLookup
    have same := Option.some.inj (leftLookup.symm.trans rightLookup)
    have origins := SourceCoreStageCodebook.Origin.lambda.inj (otherOrigin.symm.trans (same ▸ origin))
    have nodeSame := prepared_node authentic hookPrepared
      (origins.1.trans hookKeys.1.symm)
      (origins.2.1.trans (hookKeys.2.1.trans nodeId).symm)
      (origins.2.2.trans hookKeys.2.2.symm)
    refine ⟨template, rfl, authentic, origins.1, origins.2.1, origins.2.2, ?_⟩
    exact congrArg ExpressionNode.form nodeSame |>.trans (hookForm.symm.trans (code.form.trans code.sourceForm))

/-- Permission is checked in the exact source and native-active history
retained by this actual code. -/
theorem lambda_allowed (code : Code prepared function scope administrative) (history : History code) :
    SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs
      history.metadata code.descriptor.id = true := by
  obtain ⟨template, found, authentic, owner, id, active, form⟩ := selected code
  obtain ⟨entry, member, origin, descriptor⟩ := prepared_entry prepared.ancestry.graph.inputs authentic
  have selectedId : template.descriptor = code.descriptor.id := by simpa using List.find?_some found
  have entryFound := CallableAncestryPairedValidation.stage_entry_self _ member
  rw [descriptor, selectedId] at entryFound
  have sourceFound := code.sourceFound
  rw [← history.source, ← id] at sourceFound
  simp [SourceCoreCallableAncestryPairedPreparation.lambdaAllowed, found, entryFound, origin,
    history.owner, owner, history.active, active, sourceFound, code.sourceForm, form]

/-- The actual permission discharges ordinary dispatch from any separately
carried stable caller. The caller need not share the lexical physical frame. -/
theorem ordinary_history (code : Code prepared function scope administrative) (history : History code)
    {currentNative : CallableIndexedHistory.NativeFrame} {currentGhost : CallableIndexedHistory.GhostFrame}
    {current : Option CallableIndexedHistory.MetadataState}
    (carried : CallableIndexedHistory.Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      currentNative currentGhost current) :
    CallableIndexedHistory.Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id
        history.native currentNative)
      (.lambda code.descriptor.id history.ghost) (some history.metadata) :=
  CallableIndexedHistory.ordinary_complete prepared.ancestry.graph history.carried carried
    (lambda_allowed code history)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaTemplatePermission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedAppliedStageOrigins
/-! Applied-view stage origins retain the actual two-parent recipe and both
metadata factories. A supplied full source equality connects an actual Code to
that recipe; its ordered header then follows from the actual lookup. The
rewritten source is not identified with a substitution-only source receipt,
and this module does not construct body typing or an execution law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedAppliedStageOrigins
open Frontend SourceInference GeneralHeap CallableAppliedViewProvenance
open SourceCoreCallableAncestryReadRecipes CallContractCertificates AuthenticatedCallableLedger

variable {checked : Checked} {base : Base checked} {inputs : Inputs base}
  {callerFrame lexicalFrame : Frame} {caller lexical : MetadataState} {view target : Core.Word}
  (recipe : Recipe inputs callerFrame lexicalFrame caller lexical view target)

/-- All closure components come from the same applied lexical recipe. Its
context, captured cells and dictionary remain independently supplied. -/
structure Alignment (function : Dynamic.Closure) : Prop where
  source : function.source = (recipe.read.after lexical).metadata.source
  parameters : function.parameters = recipe.applied.parameters.map
    (TypedBinder.applySubstitution recipe.read.substitution)
  result : function.resultType = recipe.read.substitution.apply recipe.applied.resultType
  body : function.body = recipe.applied.body

variable {function : Dynamic.Closure}

theorem origin {contract : SourceCoreStageContracts.Contract}
    (canonical : CanonicalHeader inputs recipe.read.template contract)
    (retained : recipe.read.descriptor.contract = some contract)
    (aligned : Alignment recipe function) :
    CallableLedger.LambdaOrigin base.plan recipe.read.template.owner recipe.read.template.id
      recipe.read.template.active function contract :=
  .applied recipe canonical retained rfl rfl rfl aligned.source aligned.parameters aligned.result aligned.body

private theorem descriptor_id : recipe.read.descriptor.id = target :=
  of_decide_eq_true (List.find?_some
    (p := fun entry : SourceCoreStageCodebook.Entry => decide (entry.id = target)) recipe.read.descriptorSelected)

theorem origin_rep {contract : SourceCoreStageContracts.Contract}
    (canonical : CanonicalHeader inputs recipe.read.template contract)
    (retained : recipe.read.descriptor.contract = some contract)
    (aligned : Alignment recipe function) (payload : Core.Value) :
    CallableLedger.OriginRep base.plan inputs.callable.table (.closure function) (.pair payload (.word target)) := by
  have related := CallableLedger.OriginRep.closure (raw := payload)
    (List.mem_of_find?_eq_some recipe.read.descriptorSelected) recipe.read.templateOrigin retained
    (origin recipe canonical retained aligned)
  simpa only [descriptor_id recipe] using related

private theorem lambda_original {plan : SourceCompilationPlan.Plan} {owner : SourceCompilationPlan.Key}
    {id : ExpressionId} {active : TypeSystem.Substitution} {count : Nat}
    {attached : Option SourceCoreStageContracts.Contract}
    (authenticated : CallEntryCertificates.OriginContract plan (.lambda owner id active) count attached) :
    ∃ contract, attached = some contract ∧ Nonempty (LambdaSource plan owner id active contract) := by
  cases authenticated with
  | originalLambda prepared accepted => exact ⟨_, rfl, ⟨.original _ _ _ prepared accepted⟩⟩
  | contextualLambda prepared accepted => exact ⟨_, rfl, ⟨.contextual _ _ _ _ prepared accepted⟩⟩

private theorem site_of_prepared
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (accepted : SourceCoreStageCodebook.prepareWithProjection base.sourceProgram base.plan project limits firstId = .ok inputs.callable.table) :
    ∃ site : LambdaSite base.plan inputs.callable.table recipe.read.template.owner recipe.read.template.id
      recipe.read.template.active target, site.entry = recipe.read.descriptor := by
  have authenticated := CallEntryCertificates.prepareWithProjection_authenticates accepted recipe.read.descriptor
    (List.mem_of_find?_eq_some recipe.read.descriptorSelected)
  unfold CallEntryCertificates.Authenticated at authenticated
  rw [recipe.read.templateOrigin] at authenticated
  obtain ⟨contract, retained, ⟨original⟩⟩ := lambda_original authenticated
  exact ⟨⟨_, List.mem_of_find?_eq_some recipe.read.descriptorSelected, recipe.read.templateOrigin,
    descriptor_id recipe, contract, retained, original⟩, rfl⟩

/-- The returned recursive scope uses the semantic substitution. The selected
codebook row retains the separate native active context. -/
theorem selected
    {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {ownership : checked.signatures = program.signatures} {fuel : Nat}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (table : SourceCoreStageCodebook.prepareWithProjection base.sourceProgram base.plan project limits firstId = .ok inputs.callable.table)
    {sidecar : SourceCoreStageContracts.Sidecar}
    (prepared : SourceCoreStageContracts.prepareSidecar base.plan sidecar.caller.key = .ok sidecar)
    (sameOwner : recipe.read.template.owner = sidecar.caller.key)
    (aligned : Alignment recipe function)
    (owner : function.source.owner = sidecar.caller.key.declaration) :
    (RecursiveStageRegistry.registry base.sourceProgram base.plan inputs.callable.table).Closure function
      (RecursiveStageRegistry.scope sidecar (recipe.read.substitution.compose lexical.metadata.active) function) := by
  obtain ⟨contract, retained, canonical⟩ := header_of_prepared accepted table recipe.read
  obtain ⟨site, entryEq⟩ := site_of_prepared recipe table
  have contractEq : site.contract = contract := Option.some.inj (site.retained.symm.trans (entryEq ▸ retained))
  let site' : LambdaSite base.plan inputs.callable.table sidecar.caller.key recipe.read.template.id
      recipe.read.template.active target := {
    entry := site.entry, member := site.member, origin := by rw [← sameOwner]; exact site.origin
    id_eq := site.id_eq, contract := site.contract, retained := site.retained
    original := sameOwner ▸ site.original }
  have provenance : CallableLedger.LambdaOrigin base.plan sidecar.caller.key recipe.read.template.id
      recipe.read.template.active function site'.contract := by
    change CallableLedger.LambdaOrigin _ _ _ _ _ site.contract
    rw [contractEq]
    exact .applied recipe canonical retained rfl sameOwner rfl
      aligned.source aligned.parameters aligned.result aligned.body
  exact .applied recipe rfl rfl rfl prepared sameOwner site' aligned.source owner provenance

section Code
variable {indexed : SourceCoreCallableIndexedPrograms.Prepared checked}
  {callerFrame lexicalFrame : Frame} {caller lexical : MetadataState} {view target : Core.Word}
  (recipe : Recipe indexed.ancestry.graph.inputs callerFrame lexicalFrame caller lexical view target)
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : CallableIndexedLambdaValues.Code indexed function scope administrative)

/-- Actual lookup and the recipe's full source equality determine the lambda
header. A native type or history alone supplies neither premise. -/
theorem code_alignment
    (source : function.source = (recipe.read.after lexical).metadata.source)
    (sameId : code.id = recipe.read.entry.view.principal.initializer) : Alignment recipe function := by
  have found := code.sourceFound
  rw [source, sameId] at found
  have nodeEq := Option.some.inj (found.symm.trans recipe.source_node)
  have forms := ExpressionForm.lambda.inj
    (code.sourceForm.symm.trans ((congrArg ExpressionNode.form nodeEq).trans recipe.source_node_form))
  exact ⟨source, forms.1, forms.2.1, forms.2.2⟩

/-- The actual indexed closure carrier receives the same descriptor's origin.
Static body/evidence transport remains a separate obligation. -/
theorem code_origin
    {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {ownership : checked.signatures = program.signatures} {fuel : Nat}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok indexed.base)
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (table : SourceCoreStageCodebook.prepareWithProjection indexed.base.sourceProgram indexed.base.plan project limits firstId =
      .ok indexed.ancestry.graph.inputs.callable.table)
    (source : function.source = (recipe.read.after lexical).metadata.source)
    (sameId : code.id = recipe.read.entry.view.principal.initializer)
    (sameTarget : code.descriptor.id = target)
    (embedding : Core.Renaming) (native : CallableIndexedHistory.NativeFrame) (captured : Core.Environment) :
    CallableLedger.OriginRep indexed.base.plan indexed.ancestry.graph.inputs.callable.table (.closure function)
      (CallableIndexedLambdaValues.value code embedding native captured) := by
  obtain ⟨contract, retained, canonical⟩ := header_of_prepared accepted table recipe.read
  have related := origin_rep recipe canonical retained (code_alignment recipe code source sameId)
    (.pair (.inLeft .word .unit) (.closure code.receipt.parameterCore
      (Core.LanguageResult.resultType code.receipt.resultCore) (code.body.rename embedding.lift.lift)
      (SourceCoreCallableIndexedFrames.encode indexed.ancestry.layout.frame native :: captured)))
  simpa only [CallableIndexedLambdaValues.value, sameTarget] using related
end Code

end Solcore.SourceSemantics.CoreLowering.CallableIndexedAppliedStageOrigins
end
