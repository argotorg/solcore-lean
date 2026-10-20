import Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourcePrefixLifting
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceApplicationLifting
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyCompiler
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageApplicationArity
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping

/-! Original indirect calls lift through the actual generalized local value.
The retained materialization supplies its real body compiler and parameter
context; ordered arguments keep their reached descriptor cells and effects. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceIndirectLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open CellAwareScopeSourceLiftBounds (LiftsAt)
open Staging.Recursive.Lifting (ApplicationLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functions : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry semanticFaults profile functions]
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages compiled

include positive port runtime unique in
/-- The finite compiler certificate determines the actual callee and call
body. The only recursive inputs are the ordered argument children. -/
theorem indirect {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (covers : invocation.evidence.Covers context)
    (budget : Nat)
    (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      invocation.source scope callee reasonAt compiler.calleeCode)
    (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source children scope ids sourceTypes compiler.codes)
    (childLift : ∀ size, size < budget → LiftsAt bridge context model named stages invocation children size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named stages invocation children faults size)
    (calleeMeaning : ∀ size, CellAwareScopeGeneralizedReadBounds.PreservesAt
      bridge context model named stages invocation faults size) :
    LiftsAt bridge context model named stages invocation
      (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Point scope id lowered) budget := by
  intro current expression code point actualNode found parentTyped
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial admitted authority physical owner ownerFrame execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨_parameter, _result, _rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation expression (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  rcases CellAwareScopeSourcePrefixLifting.lift_prefix
    (functions := functions) bridge profile compiler port calleeCertificate calleeRecipe sourceTyped
    tree unique parentTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame
    budget childLift preservation calleeMeaning execution (Nat.le_refl _) with complete | application
  · exact complete
  · obtain ⟨_calleeSize, _argumentsSize, _callSize, sourceValue, _calleeHeap, _argumentsHeap, sources, _callEvidence,
      calleeTrace, accepted, argumentsTrace, called, _smaller, prefixResult⟩ := application
    obtain ⟨rawParameter, rawResult, functionType, bundle, _originalResult,
      _calleeStore, _calleeMap, _calleeWorld, _carrier, _values, _argumentsStore, _finalMap, _finalWorld,
      _originalNode, _originalMetadata, _calleePost, calleeTyped, _firstGate, _argumentsNative,
      _represented, _calleeRelated, strong, _callView, _boundary, _heaps, _maps, _worlds,
      _frame, _heapMetadata, _effect, _reached, _related, _admitted⟩ := prefixResult
    obtain ⟨function, _native, _bindings, _parameterCore, _resultCore, sourceValueEq, _nativeEq, association, _atFrame⟩ :=
      strong sourceValue rfl
    cases sourceValueEq
    have lifted : ApplicationLift (Program.ofChecked compiled.sourceProgram) stages invocation context _argumentsHeap
        (.closure function) sources outcome after := by
      by_cases arity : function.parameters.length = sources.length
      · have rawCallee : Dynamic.ValueHasType context _calleeHeap (.closure function)
            (.function rawParameter rawResult) := by
          simpa only [functionType] using calleeTyped
        obtain ⟨_parameters, _sourceResult, signatures, sourceCode, evidence, _captures⟩ := rawCallee.closure_function_inv
        have frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function :=
          ⟨signatures.trans runtime.signatures, sourceCode.owner, sourceCode,
            sourceCode.requirement_ledger.idsUnique, evidence⟩
        obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
          CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler port.sourceParent
            tree unique parentTyped port.calleeFound
        obtain ⟨_nativeCallee, _representedCallee, _strong, _calleeHeaps, _calleeMaps, _calleeWorlds,
          _calleeFrame, calleeMetadata, _calleeEffect, _calleeReached, _calleeRelated, calleeAdmission⟩ := _calleePost
        obtain ⟨sourceValuesTyped, _heapTyped, argumentMetadata⟩ :=
          CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping.values_at wellFormed runtime covers
            (locals.mono calleeMetadata) calleeAdmission.at_value.2.heap argumentsTyped argumentsTrace
        obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack sources
        have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime
          (rawCallee.mono argumentMetadata) _admitted.heap sourceValuesTyped packing bundle arity.symm
        cases association with
        | viewed material _view _typed =>
          obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
          exact GeneralizedLocalSourceApplicationLifting.selected_application material inputs wellFormed raw arity called
      · exact SelectedCompilationStageApplicationArity.closure_mismatch arity called
    obtain ⟨staged, reached, applied, adapted⟩ := lifted
    exact ⟨staged, reached, .applied occurrence compiler.argumentCoercions calleeTrace.sound accepted
      argumentsTrace.sound port.sourceParent.arity applied, adapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceIndirectLifting
