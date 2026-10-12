import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedReadDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds

/-! Actual finite named terminal bodies construct both staged directions
without an external expression meaning premise. The accepted child compiler
receipt retains its original raw typing and every literal/read/product site.
The actual issuer and receiver interpret read failures. Full reached caller
state, lazy mapping writes and independent Source/native grades are retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt Terminal)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {expression : ExpressionId}

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure header.function child)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  (ordinary : CompatibleExpressionProducts.Ordinary header.function.source
    compiled.indexed.base.locals (CallableIndexedNamedGeneration.context compiled.indexed prepared.named).owner)
  (syntaxTree : CompatibleExpressionProducts.Syntax header.function.source expression)
  (sameLedger : header.context.solvedRequirements = header.solved)
  (runtimeLedger : RuntimeRequirementLedgerValid header.context)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context child.source)
  (covers : child.evidence.Covers header.context)

variable
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrative
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before header.context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State
    ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge header.context initial)

include aligned diagnostic receiver selected wellFormed terminal ordinary syntaxTree sameLedger runtimeLedger runtime covers environments heaps locals agrees typed admitted
/-- The original named body Source typing and genuine selected child scope
construct preservation from the actual finite child tree. The body
trace and nested failure scope remain recursively staged. -/
theorem preserves_body (budget : Nat)
    {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages size child
      header.context environment before header.function.body finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult header.function.resultType bodyOutcome outcome)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (header.body.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) finalMap finalWorld
        header.function.resultType header.output (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge header.context header.function.resultType outcome reached := by
  have uniqueChild : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  have childTree : (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source header.context header.solved header.reasonAt)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression terminal.child := by
    simpa only [stages.source selected] using
      CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.finite_child
        prepared aligned terminal selected wellFormed ordinary syntaxTree
  have certifies : ∀ lowered,
      header.policy.lowerExpression terminal.childFuel header.function.source
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
      (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source header.context header.solved header.reasonAt) (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered := by
    intro lowered generated
    have same : terminal.child = lowered := Except.ok.inj (terminal.generated.symm.trans generated)
    exact same ▸ childTree
  have readFault : ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead compiled.indexed.fuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        child.source header.context header.reasonAt scope id lowered →
      ∀ location, CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
        (.uninitializedLocation location) (header.reasonAt id) := by
    intro scope id lowered receipt location
    exact CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized
      prepared diagnostic aligned receiver (by simpa only [stages.source selected] using receipt) location
  have children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow bridge header.context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
      stages child (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source header.context header.solved header.reasonAt) (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) budget := by
    intro childSize _smaller
    exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.preserves bridge functions
      completion.result.extension sameLedger runtimeLedger (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) readFault
      (fun reason token represented => CallableIndexedOwnedPublicDecodedStagedCallFaults.of_semantic represented)
      uniqueChild wellFormed runtime covers childSize
  have view : LambdaMetadataViews.MetadataView child.source header.function.source := by
    rw [stages.source selected]
    exact .refl _
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨staticFinal, facts, bodyTyped, complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  have scopedBodyTyped : StatementsHaveType child.source
      {returnType := header.function.resultType} header.context header.function.body staticFinal facts := by
    simpa only [stages.source selected] using bodyTyped
  exact CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.preserves_body
    (receipt := terminal) (view := view) (bridge := bridge) (bodyTyped := scopedBodyTyped) (complete := complete)
    (certifies := certifies) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    unique budget children (trace := trace) (matched := matched) (within := within)

include aligned diagnostic receiver selected wellFormed terminal ordinary syntaxTree sameLedger runtimeLedger runtime covers environments heaps locals agrees typed admitted
/-- Literal native body completion reflects to an independently graded staged
Source body, using the same accepted Header code and actual parameter state.
The complete returned pool and successful Source post are retained. -/
theorem reflects_body (budget : Nat)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (header.body.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize child
        header.context environment before header.function.body header.context
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome) after ∧
      Staging.Recursive.BodyResult header.function.resultType
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) finalMap finalWorld
        header.function.resultType header.output (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge header.context header.function.resultType outcome reached := by
  have uniqueChild : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  have childTree : (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source header.context header.solved header.reasonAt)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression terminal.child := by
    simpa only [stages.source selected] using
      CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.finite_child
        prepared aligned terminal selected wellFormed ordinary syntaxTree
  have certifies : ∀ lowered,
      header.policy.lowerExpression terminal.childFuel header.function.source
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
      (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source header.context header.solved header.reasonAt) (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered := by
    intro lowered generated
    have same : terminal.child = lowered := Except.ok.inj (terminal.generated.symm.trans generated)
    exact same ▸ childTree
  have readFault : ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead compiled.indexed.fuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        child.source header.context header.reasonAt scope id lowered →
      ∀ location, CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
        (.uninitializedLocation location) (header.reasonAt id) := by
    intro scope id lowered receipt location
    exact CallableIndexedOwnedPreparedStagedNamedReadDiagnostics.uninitialized
      prepared diagnostic aligned receiver (by simpa only [stages.source selected] using receipt) location
  have children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow bridge header.context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
      stages child (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source header.context header.solved header.reasonAt) (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) budget := by
    intro childSize _smaller
    exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.reflects bridge functions
      completion.result.extension sameLedger runtimeLedger (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) readFault
      (fun reason token represented => CallableIndexedOwnedPublicDecodedStagedCallFaults.of_semantic represented)
      uniqueChild wellFormed runtime covers childSize
  have view : LambdaMetadataViews.MetadataView child.source header.function.source := by
    rw [stages.source selected]
    exact .refl _
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨staticFinal, facts, bodyTyped, complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  have scopedBodyTyped : StatementsHaveType child.source
      {returnType := header.function.resultType} header.context header.function.body staticFinal facts := by
    simpa only [stages.source selected] using bodyTyped
  exact CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.reflects_body
    (receipt := terminal) (view := view) (bridge := bridge) (bodyTyped := scopedBodyTyped) (complete := complete)
    (certifies := certifies) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    unique budget children (completed := completed) (within := within)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteNamedBodyBounds
