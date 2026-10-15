import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBuiltinOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.RecursivePublicCallableArity
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectClosureBounds
import Solcore.SourceSemantics.CoreLowering.RecursivePublicPackedArguments
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinArgumentRows

/-! The authentic builtin identity supplies its ordered parameter row. The
primitive application proof keeps the caller, heap and store unchanged while
relating the actual result to independent Source application. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectBuiltinBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

section Packed
variable {initial completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : SelectedCompilationPhysicalProgramSupport.Support compiled headers keys initial)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry completion.result.context.registry)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)
  (heapTyped : Dynamic.HeapWellTyped context before)
  {function : BuiltinFunctionId} {native : Value} {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before (.builtin ⟨function⟩) (.function parameter result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world (.function parameter result) (.builtin ⟨function⟩) native
    (CallableContract.functionType parameterCore resultCore))
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world before store)

  {packedSource : Dynamic.Value} {packedNative : Value}
  (packedTyped : Dynamic.ValueHasType context before packedSource parameter)
  (packedRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world parameter packedSource packedNative parameterCore)

local notation "functions" => SelectedCompilationPhysicalProgramSupport.functions support
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
/-- Actual complete builtin execution determines the same Source primitive
result and unchanged caller; no builtin body law is supplied by a caller. -/
theorem reflects_packed_at_arity {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.builtin ⟨function⟩) sources.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.builtin ⟨function⟩) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  have builtin := SelectedCompilationPhysicalBuiltinOrigins.builtin_member support.profile calleeRelated ⟨function⟩ rfl
  have nativeType : CallableContract.functionType parameterCore resultCore =
      CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) := by
    generalize sourceTypeEq : function.type = sourceType at builtin
    cases builtin
    rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  have signature : parameter = TypeSystem.Ty.productMany function.parameterTypes ∧ result = function.returnType := by
    rcases calleeTyped.builtin_inv with ordinary | staged
    · exact TypeSystem.Ty.function.inj ordinary
    · obtain ⟨inner, impossible, _typed⟩ := staged
      cases impossible
  have packed := packedRelated
  rw [signature.1] at packed
  obtain ⟨sources, values, nativeTypesRow, rows, packing, packedEq, packedType⟩ :=
    RecursivePublicPackedArguments.values function.parameterTypes packed
  have expectedLength : function.parameterTypes.length = (CompatibleBuiltinMeaning.argumentTypes function).length := by
    cases function <;> rfl
  have nativeRow : nativeTypesRow = CompatibleBuiltinMeaning.argumentTypes function :=
    CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
      (rows.length.2.2.symm.trans expectedLength)
      (packedType.symm.trans (nativeTypes.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function).symm))
  rw [nativeRow] at rows
  have evaluation : EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore := by
    rw [← packedEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail completed
  obtain ⟨sourceResult, trace, representedResult, applied, finalStoreEq⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.reflects functions (SelectedCompilationPhysicalProgramSupport.observations support) builtin rows evaluation
  subst finalStore
  rw [← signature.2, ← nativeTypes.2] at representedResult
  refine ⟨sources, packing, rows.length.1.symm ▸ RecursivePublicCallableArity.Arity.builtin ⟨function⟩, Staging.Recursive.Size.stepSize [], .value sourceResult,
    before, mapping, world, trace, representedResult, heaps, .refl _, .refl _, .refl _ _, .refl _,
    caller, (protocol headers keys).refl caller, stable, ?_⟩
  intro source same
  cases same
  exact ⟨signature.2 ▸ applied.preserves.2, heapTyped⟩

include support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
theorem reflects_packed {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.builtin ⟨function⟩) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, packing, _arity, meaning⟩ := reflects_packed_at_arity support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated completed
  exact ⟨sources, packing, meaning⟩

include support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
/-- The actual primitive argument arity fixes its unpacking. Typed primitive
inputs exclude Source dispatch faults; all caller state remains unchanged. -/
theorem preserves_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    (arityAt : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.builtin ⟨function⟩) sources.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.builtin ⟨function⟩) sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  have builtin := SelectedCompilationPhysicalBuiltinOrigins.builtin_member support.profile calleeRelated ⟨function⟩ rfl
  have nativeType : CallableContract.functionType parameterCore resultCore =
      CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) := by
    generalize sourceTypeEq : function.type = sourceType at builtin
    cases builtin
    rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  have signature : parameter = TypeSystem.Ty.productMany function.parameterTypes ∧ result = function.returnType := by
    rcases calleeTyped.builtin_inv with ordinary | staged
    · exact TypeSystem.Ty.function.inj ordinary
    · obtain ⟨inner, impossible, _typed⟩ := staged
      cases impossible
  have packed := packedRelated
  rw [signature.1] at packed
  obtain ⟨decodedSources, values, nativeTypesRow, rows, decodedPacking, packedEq, packedType⟩ :=
    RecursivePublicPackedArguments.values function.parameterTypes packed
  have expectedLength : function.parameterTypes.length = (CompatibleBuiltinMeaning.argumentTypes function).length := by
    cases function <;> rfl
  have nativeRow : nativeTypesRow = CompatibleBuiltinMeaning.argumentTypes function :=
    CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
      (rows.length.2.2.symm.trans expectedLength)
      (packedType.symm.trans (nativeTypes.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function).symm))
  rw [nativeRow] at rows
  have arity : function.parameterTypes.length = sources.length := arityAt.builtin_count
  have sameSources : decodedSources = sources :=
    decodedPacking.injective_of_length_eq packing (rows.length.1.symm.trans arity)
  subst decodedSources
  obtain ⟨nativeSize, value, evaluated, representedResult, sameHeap, _sourceGrade⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.preserves functions (SelectedCompilationPhysicalProgramSupport.observations support) builtin rows trace
  subst after
  rw [← signature.2, ← nativeTypes.2] at representedResult
  have padded : EvaluationSize nativeSize (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value store := by
    rw [packedEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail evaluated
  obtain ⟨source, sameOutcome, _sameHeap, _size, applied⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.source_value functions (SelectedCompilationPhysicalProgramSupport.observations support) rows trace
  cases sameOutcome
  refine ⟨value, store, mapping, world, padded.sound, representedResult, heaps,
    .refl _, .refl _, .refl _ _, .refl _, caller, (protocol headers keys).refl caller, stable, ?_⟩
  intro source same
  cases same
  exact ⟨signature.2 ▸ applied.preserves.2, heapTyped⟩

include support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
/-- Successful Source execution supplies the genuine arity automatically. -/
theorem preserves_value_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.builtin ⟨function⟩) sources (.value sourceResult) after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        (.value sourceResult) after value finalStore finalMap finalWorld callFaults := by
  exact preserves_packed support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated
    packing (.of_value trace) trace

end Packed
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectBuiltinBounds
