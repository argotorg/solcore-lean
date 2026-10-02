import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeInversion

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
