import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.PreparedAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenStoredCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MixedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedBareAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MatchSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.Staging.Internal.FaultCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedCanonicalSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedScopedPreservation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedImperative
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedFlows
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerPolicies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DiscardSequences

/-!
# Staged bounds: lambda bodies

Lambda bodies by shape, lexical, imperative, branching and nested: compiler receipts and support, body and application bounds, and read roots.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts
/-! The original body callback determines one branching flow, allocator and
finish footer at the authentic closure Code. This contains only compiler facts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleEncoding (bind_ok)
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative) {stages : Staging.Recursive.Registry}

structure Choice where
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  packet : Branching code stages
  callback : packet.policy.lowerExpression = FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  reason : packet.reasonAt = code.reasonAt
  assignments : CompatibleAssignmentStatements.AssignmentPolicy packet.policy (.initial compiled.compatible.checked) invalidProjection invalidOperand missingDefault
  unaryPolicy : CompatibleBitNotStatements.Policy packet.policy (.initial compiled.compatible.checked) invalidProjection invalidUnary missingDefault
  readPolicy : packet.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    packet.policy.lowerBinder code.view scope binder =
      SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked code.view scope binder
  allocationPolicy : packet.policy.sourceCells = some
    (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
      compiled.indexed.base.globals.length
      (compiled.indexed.layouts.allocatorAt packet.allocationOwner packet.active packet.onError))

  matchCompilation : SourceCoreCompatibleDataMatches.Context
  matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess packet.policy matchCompilation
  matchValues : matchCompilation.values = .initial compiled.compatible.checked
  matchDefinitions : matchCompilation.definitions = compiled.indexed.layouts.definitions
  matchAllocator : matchCompilation.sourceCells = some
    (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
      compiled.indexed.base.globals.length
      (compiled.indexed.layouts.allocatorAt packet.allocationOwner packet.active packet.onError))
  matchLedger : matchCompilation.solvedRequirements = code.compilation.solvedRequirements

/-- The selected token function belongs to the same actual issued compilation. -/
def Choice.Issued (named : Named) (choice : Choice code (stages := stages)) : Prop :=
  ∃ (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation compiled.indexed named diagnostics namedCode),
      CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics ∧
      choice.invalidOperand = GenericAssignmentDiagnostics.token compilation.own.assignments ∧
      choice.invalidUnary = GenericAssignmentUnaryDiagnostics.unaryToken compilation.own.assignments ∧
      choice.invalidProjection = (fun site root => diagnostics.placeReason named.signature.key site root none) ∧
      choice.missingDefault = (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))

/-- The actual retained lowerer supplies all allocator and binder callbacks;
none is inferred from a native result type. -/
private theorem choose_with_token (named : Named)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation code)
    (sameCompilation : code.compilation = context compiled.indexed named)
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ choice : Choice code (stages := stages),
      choice.invalidOperand = GenericAssignmentDiagnostics.token compilation.own.assignments ∧
      choice.invalidUnary = GenericAssignmentUnaryDiagnostics.unaryToken compilation.own.assignments ∧
      choice.invalidProjection = (fun site root => diagnostics.placeReason named.signature.key site root none) ∧
      choice.missingDefault = (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw)) := by
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    (congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe).trans
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
        compiled.indexed named compilation.own.assignments diagnostics expression)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  let baseMatch : SourceCoreCompatibleDataMatches.Context :=
    ⟨.initial compiled.compatible.checked, (context compiled.indexed named).solvedRequirements,
      some (allocator compiled.indexed named), none⟩
  have matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy
      (CompatibleMatchAmbientLowering.withDefinitions baseMatch compiled.indexed.layouts.definitions) := by
    apply CompatibleMatchAmbientLowering.PolicySuccess.extend (show policy.lowerMatch = some
      (SourceCoreCompatibleDataMatches.lowerWithReasons baseMatch) from rfl)
    exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩
  refine ⟨{
    invalidProjection := fun site root => diagnostics.placeReason named.signature.key site root none
    invalidUnary := fun site root => compilation.own.assignments.reasonAt site root .bitNot
    invalidOperand := fun site root operator => if operator = .equal then Word.zero else compilation.own.assignments.reasonAt site root (.value operator)
    missingDefault := fun site root type => diagnostics.placeReason named.signature.key site root (some type)
    packet := {
      policy := policy
      fuel := code.fuel
      reasonAt := code.reasonAt
      fellThrough := code.compilation.internalReason
      escaped := code.compilation.internalReason
      allocationOwner := named.signature.key
      active := []
      onError := fun error => .sourceAllocation (reprStr error)
      flow := flow
      accepted := generated
      emitted := (Except.ok.inj returned).symm
      shape := shape
      child := child
      selected := selected }
    callback := rfl
    reason := rfl
    assignments := ?_
    unaryPolicy := rfl
    readPolicy := rfl
    binderPolicy := ?_
    allocationPolicy := rfl
    matchCompilation := CompatibleMatchAmbientLowering.withDefinitions baseMatch compiled.indexed.layouts.definitions
    matchPolicy := matchPolicy
    matchValues := rfl
    matchDefinitions := rfl
    matchAllocator := rfl
    matchLedger := by rw [sameCompilation] }, rfl, rfl, rfl, rfl⟩
  · refine ⟨rfl, rfl, ?_⟩
    change some _ = some _
    apply congrArg some
    funext expression fuel source scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl
  · intro current binder mono
    change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
    simp only [SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil, ↓reduceIte]
    rfl

/-- The original generic receipt still forgets only the actual token identity. -/
theorem choose (named : Named)
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (sameCompilation : code.compilation = context compiled.indexed named)
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Choice code (stages := stages)) := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  obtain ⟨choice, _⟩ := choose_with_token code named compilation recipe sameCompilation shape child selected
  exact ⟨choice⟩

/-- Exact retained issuance authenticates the token of the chosen compiler packet. -/
theorem choose_issued (named : Named)
    (retained : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained named code)
    (sameCompilation : code.compilation = context compiled.indexed named)
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ choice : Choice code (stages := stages), choice.Issued code named := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, issued, recipe, _policy, _same⟩ := retained
  obtain ⟨choice, token, unaryToken, projectionToken, missingToken⟩ := choose_with_token code named compilation recipe sameCompilation shape child selected
  exact ⟨choice, diagnostics, namedCode, compilation, issued, token, unaryToken, projectionToken, missingToken⟩

/-- Actual full-source preparation and receiver issuance interpret each admitted token. -/
theorem Choice.Issued.operands {named : Named} {choice : Choice code (stages := stages)}
    (issued : choice.Issued code named) {index : Nat}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (sourceEq : function.source = source named)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (origin : AssignmentDiagnosticOrigins.Occurs function.source site assignment operator rhs)
    (profile : operator = .equal ∨ assignment.target.type = .word) :
    AssignmentOperandDiagnostics.OperandsLaw
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) operator
      (choice.invalidOperand site assignment.target.root operator) := by
  obtain ⟨diagnostics, namedCode, compilation, actual, token, _unaryToken, _projectionToken, _missingToken⟩ := issued
  obtain ⟨first, prepared⟩ := CallableIndexedOwnedIssuedAssignmentRecipes.assignments_prepared selected compilation actual
  rw [token]
  rw [sourceEq] at origin
  exact PreparedBranchingAssignmentDiagnostics.operands prepared
    (fun _ _ represented => CallableIndexedOwnedIssuedAssignmentRecipes.operands compilation actual receiver represented)
    origin profile

/-- The same retained compiler table supplies every original unary diagnostic. -/
theorem Choice.Issued.unary {named : Named} {choice : Choice code (stages := stages)}
    (issued : choice.Issued code named) {index : Nat}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (sourceEq : function.source = source named)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    (origin : GenericAssignmentUnaryDiagnostics.UnaryOccurs function.source site assignment)
    (rawWord : assignment.target.type = .word) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.invalidUnaryOperand .bitNot) (choice.invalidUnary site assignment.target.root) := by
  obtain ⟨diagnostics, namedCode, compilation, actual, _operandToken, token, _projectionToken, _missingToken⟩ := issued
  obtain ⟨first, prepared⟩ := CallableIndexedOwnedIssuedAssignmentRecipes.assignments_prepared selected compilation actual
  rw [token]
  rw [sourceEq] at origin
  exact GenericAssignmentUnaryDiagnostics.prepared_unary_included prepared
    (fun _ _ represented => CallableIndexedOwnedPublicUnaryAssignmentDiagnostics.compilation_unary
      compilation actual receiver represented) origin rawWord

/-- Place tokens come from the same real issuing inventory as this closure. -/
theorem Choice.Issued.assignmentAuthority {named : Named} {choice : Choice code (stages := stages)}
    (issued : choice.Issued code named) {index : Nat}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (sourceEq : function.source = source named)
    (unique : NodeOccurrencesUnique function.source) :
    Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled function.source
      choice.invalidProjection choice.missingDefault) := by
  obtain ⟨diagnostics, namedCode, compilation, actual, _operands, _unary, projectionToken, missingToken⟩ := issued
  obtain ⟨issuer, present, _base, places⟩ := actual
  refine ⟨{
    owner := named.signature.key
    row := named.specialized
    record := CallableIndexedActualNamedSourceReceipts.cached_record compiled selected compilation.hook
    sourceEq := sourceEq
    unique := unique
    issuer := issuer
    present := present
    invalidToken := ?_
    missingToken := ?_ }⟩
  · intro site root
    simp only [projectionToken, SourceCoreDataPlaceFaultSites.Program.placeReason, places]
  · intro site root raw
    simp only [missingToken, SourceCoreDataPlaceFaultSites.Program.placeReason, places]

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport
/-! Original typed closure syntax and the retained compiler callback produce
a branching packet for the same Code. Every child keeps the current lexical
context, exact accepted callback and native typing. No execution law is stored. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching BranchingSupport parameterScope)
open CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
  {stages : Staging.Recursive.Registry} (choice : Choice code (stages := stages))

include frame in
/-- The complete native body supplies local typing; authentic metadata views
and binder receipts recover the original Source tree without changing code. -/
theorem collected
    (view : CallableIndexedOwnedContextualLambdaProvenance.BodyView code)
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context)
    (sourceSignatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (hidden : GenericImperativeMatch.MatchHiddenFresh function.source)
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
    (ledger : inputs.context.solvedRequirements = code.compilation.solvedRequirements)
    (projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {faults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs function.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator
        (choice.invalidOperand site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs function.source site assignment →
      assignment.target.type = .word → faults (.invalidUnaryOperand .bitNot)
        (choice.invalidUnary site assignment.target.root))
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source expressionSyntax
      inputs.context (.statements true function.body) function.resultType)
    (children : ∀ context, Dynamic.RuntimeContextFields inputs.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations function.source scope context →
      expressionSyntax id → Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      function.source.lookupExpression? id = some node → ExpressionHasType function.source context id node.type →
      choice.packet.policy.lowerExpression fuel code.view scope id choice.packet.reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType compiled.indexed.layouts.definitions → certificates context scope id lowered) :
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected choice.invalidProjection choice.missingDefault (faults := faults) compiled.indexed.layouts choice.packet.allocationOwner choice.packet.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length choice.packet.onError
      (.initial compiled.compatible.checked) function.source expressionSyntax
      (TypedCertificate function.source certificates) compiled.indexed.layouts.definitions administrative
      inputs.context (parameterScope code) (.statements true function.body) function.resultType code.receipt.resultCore choice.packet.flow := by
  let changed := CallableIndexedLambdaBodyViewEdits.changed function.source code.view
  have edited : LocalView function.source code.view changed := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have native := CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native code
  rw [choice.packet.emitted] at native
  obtain ⟨nativeType, native⟩ := TypedLexicalWhile.Native.finished_flow native
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_parameters (values := .initial compiled.compatible.checked) code inputs frame captured
  exact CallableIndexedOwnedPreparedNativeBranchingCollectors.collected edited
    (CallableIndexedLambdaBodyViewEdits.avoids view) frame.code.graph.nodeOccurrencesUnique
    choice.readPolicy choice.binderPolicy choice.allocationPolicy choice.assignments choice.unaryPolicy operands unary
    choice.matchPolicy choice.matchValues choice.matchDefinitions choice.matchAllocator hidden catalog
    (ledger.trans choice.matchLedger.symm) children
    syntaxTree rfl choice.packet.shape (.refl _) runtime.variables_closed runtime.residual_variables_open sourceSignatures
    declarations (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩)) projection choice.packet.accepted native

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNestedBranchingLambdaBodyBounds
/-! The retained canonical packet supplies the existing scoped flow engine
with the actual retained nested frame and global slots. Local allocation, mutation and finite loops
keep those slots and the reached pool throughout every direct or index child. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNestedBranchingLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching NestedBranchingSupport parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (ordinary : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults)
  (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin ordinary history)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) ordinary.caller)
  (packet : Branching code stages)
  (support : NestedBranchingSupport headers keys ordinary stages packet)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments ordinary.body.types)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "inputs" => ordinary.body.toContext
local notation "canonicalBridge" =>
  CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner ordinary.caller
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private theorem forget_post {index : ProtectedStateTransition.Index}
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    (state : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner ordinary.caller).State index)
    (post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      canonicalBridge
      context type outcome state) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys))
      context type outcome state.val := by
  cases outcome with
  | value value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨post.rows, post.successful⟩
    | stage origin call reason => exact post

variable (semantic : ∀ reason token, semanticFaults reason token → CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      completion.result.diagnostics (.semantic reason) token))

include support observed origin prefixContext stable beforeTyped argumentsTyped semantic faithful observations assignmentInterpretation in
/-- Preservation receives the actual Source-selected scope and allocation.
The already constructed parameter admission feeds the strict recursive whole-body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry
      arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩)
    {budget : Nat}
    (recursiveChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {bodySize : Nat} (within : bodySize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid ordinary.body.extended
  rw [← stages.source selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source ordinary.body.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have tree := support.tree child selected
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true function.body := by
    rw [stages.source selected]
    exact packet.shape
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact ordinary.body.frame.code.graph.nodeOccurrencesUnique
  have actualPacket := CallableIndexedOwnedLambdaNestedEntries.source_packet
    captured code history inputs functions owner ordinary.caller observed prefixContext origin.metadata
    caller entry added length copied spine kept reached
  let initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers)
      owner ordinary.caller).State
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩ := ⟨reached, actualPacket⟩
  have canonicalAdmitted : CallableIndexedOwnedSourceAdmission.Admission canonicalBridge ordinary.body.context initial :=
    ⟨admitted.heap, admitted.rows⟩
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  obtain ⟨flowValue, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativePreservation.preserves_at (compiled := compiled) (faults := callFaults)
      canonicalBridge
      (CallableIndexedOwnedNestedCanonicalState.bindings owner ordinary.caller)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner ordinary.caller)
      functions faithful observations completion.result.extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner ordinary.caller
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner
        (headers := headers) owner ordinary.caller (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller =>
        CallableIndexedOwnedPreparedStagedCanonicalScopedExpressionBounds.preserves_children
          support.complete support.zero support.wellFormed support.globals profile
          ((stages.source selected).trans ordinary.source)
          (by rw [stages.source selected]; exact ordinary.body.unique)
          (by
            intro size smaller context child scope expression lowered root
            exact recursiveChildren size smaller root)
          children owner context smaller)
      unique tree (support.sites child selected completion.result.context.registry) semantic
      (by
        rw [stages.source selected]
        obtain ⟨port⟩ := support.assignmentAuthority
        exact assignmentInterpretation port functions _) rfl shape originalTyping ordinary.body.projection within entry.entry.environments entry.entry.heaps
      entry.entry.locals entry.entry.lookups entry.entry.actualTyped entry.entry.reference entry.entry.read
      entry.entry.unmapped initial conditioned canonicalAdmitted trace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    unique sourceTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function ordinary.body.projection represented controlClosed
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated
      packet.fellThrough packet.escaped entry.entry.embedding
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, bodyStore, finalMap, finalWorld, ?_, representedBody, heaps,
    maps, worlds, frame, metadata, returned.val, related, forget_post (captured := captured) (code := code) ordinary owner returned post⟩
  simpa only [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody

include support observed origin prefixContext stable beforeTyped argumentsTyped semantic functionTypes faithful observations assignmentInterpretation in
/-- Reflection uses the literal chosen scope and real prefix allocation. It
constructs the original body trace and full post without a new body callback. -/
theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments before store
      owner.key.frameLocation (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (recursiveChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {nativeSize : Nat} (within : nativeSize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached packet.child nativeSize := by
  intro value bodyStore completed
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq ordinary.body.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends) entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields ordinary.body.extended
  have heapTyped : Dynamic.HeapWellTyped ordinary.body.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      ordinary.body.context reached := ⟨heapTyped, rows⟩
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid ordinary.body.extended
  rw [← stages.source packet.selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements packet.child.source ordinary.body.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have graph : OccurrenceGraphWellFormed packet.child.source := by
    rw [stages.source packet.selected]
    exact valid.code.graph
  have tree := support.tree packet.child packet.selected
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape packet.child.source true function.body := by
    rw [stages.source packet.selected]
    exact packet.shape
  have actualPacket := CallableIndexedOwnedLambdaNestedEntries.native_packet
    captured code history inputs functions owner ordinary.caller observed prefixContext origin.metadata
    caller entry reached
  let initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers)
      owner ordinary.caller).State
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap,
        entry.store, entry.canonical⟩ := ⟨reached, actualPacket⟩
  have canonicalAdmitted : CallableIndexedOwnedSourceAdmission.Admission canonicalBridge ordinary.body.context initial :=
    ⟨admitted.heap, admitted.rows⟩
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  have bodyTrace := completed
  rw [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace within
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativeFlow.reflects_at (compiled := compiled) (faults := callFaults)
      canonicalBridge
      (CallableIndexedOwnedNestedCanonicalState.bindings owner ordinary.caller)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner ordinary.caller)
      functions functionTypes faithful observations completion.result.extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedNestedCanonicalState.markedProducer owner ordinary.caller
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner
        (headers := headers) owner ordinary.caller (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller =>
        CallableIndexedOwnedPreparedStagedCanonicalScopedExpressionBounds.reflects_children
          support.complete support.zero support.wellFormed support.globals profile
          ((stages.source packet.selected).trans ordinary.source)
          (by rw [stages.source packet.selected]; exact ordinary.body.unique)
          (by
            intro size smaller context child scope expression lowered root
            exact recursiveChildren size smaller root)
          children owner context smaller)
      graph tree (support.sites packet.child packet.selected completion.result.context.registry) semantic
      (by
        rw [stages.source packet.selected]
        obtain ⟨port⟩ := support.assignmentAuthority
        exact assignmentInterpretation port functions _) rfl shape originalTyping ordinary.body.projection (Nat.le_of_lt strict) entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped initial
      conditioned canonicalAdmitted flowTrace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    graph.nodeOccurrencesUnique sourceTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function ordinary.body.projection represented controlClosed
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound
      packet.fellThrough packet.escaped entry.embedding
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  exact ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld, trace,
    represented.body_result, representedBody, heaps, maps, worlds, frame, metadata, returned.val, related, forget_post (captured := captured) (code := code) ordinary owner returned post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNestedBranchingLambdaBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNestedBranchingLambdaApplicationBounds
/-! The retained scoped body fills the public closure application ports from
canonical expression children. Actual parameter installation retains its
binding spine, while the saved caller receives the exact reached pool and post. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNestedBranchingLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching NestedBranchingSupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (ordinary : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults)
  (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin ordinary history)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) ordinary.caller)
  (packet : Branching code stages)
  (support : NestedBranchingSupport headers keys ordinary stages packet)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments ordinary.body.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
    completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) callerContext callerSource)

local notation "inputs" => ordinary.body.toContext
local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token → CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))

include support observed origin prefixContext stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime semantic assignmentInterpretation in
/-- The genuine Source application chooses its own scope and parameter entry.
The same internally constructed body port returns through the saved caller. -/
theorem application_preserves {budget : Nat}
    (recursiveChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size
      invocation callContext before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationSpineBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable budget
    (fun entry added length copied spine kept reached childSize strict =>
      CallableIndexedOwnedPreparedStagedNestedBranchingLambdaBodyBounds.source_body_at (semantic := semantic)
        (assignmentInterpretation := assignmentInterpretation)
        (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
        (observations := CallableIndexedOwnedContextualFunctionViews.observations profile)
        (profile := profile) (captured := captured) (code := code) (history := history)
        (ordinary := ordinary) (origin := origin) (prefixContext := prefixContext)
        (packet := packet) (support := support) (owner := owner) (caller := caller)
        (observed := observed) (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry added length copied spine kept reached recursiveChildren children (Nat.le_of_lt strict))
    trace within

include support observed origin prefixContext stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime semantic assignmentInterpretation in
/-- Native application selects its real strict body child. The packet's
chosen Source scope supplies that body and the original returned caller post. -/
theorem application_reflects
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (recursiveChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation callContext before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable packet.child packet.selected valid budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedNestedBranchingLambdaBodyBounds.native_body_at (semantic := semantic)
        (assignmentInterpretation := assignmentInterpretation)
        (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
        (observations := CallableIndexedOwnedContextualFunctionViews.observations profile)
        (functionTypes := CallableIndexedOwnedContextualFunctionViews.runtime_views profile)
        (profile := profile) (captured := captured) (code := code) (history := history)
        (ordinary := ordinary) (origin := origin) (prefixContext := prefixContext)
        (packet := packet) (support := support) (owner := owner) (caller := caller)
        (observed := observed) (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached valid recursiveChildren children (Nat.le_of_lt strict))
    completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNestedBranchingLambdaApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBranchingLambdaBodyBounds
/-! The retained canonical packet supplies the existing scoped flow engine
with actual captured global slots. Local allocation, mutation and finite loops
keep those slots and the reached pool throughout every direct or index child. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBranchingLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching CanonicalBranchingSupport parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Branching code stages)
  (support : CanonicalBranchingSupport headers code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations code.compilation.administrativePrefix scope captured.canonical owner.key.frameLocation)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "canonicalBridge" =>
  CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
    (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner code.compilation.administrativePrefix)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private theorem forget_post (callerPrefix : Nat) {index : ProtectedStateTransition.Index}
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    (state : (CallableIndexedOwnedExpressionHeads.argumentProtocol (headers := headers) owner callerPrefix).State index)
    (post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner callerPrefix).forgetSlots
      context type outcome state) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys))
      context type outcome state.val := by
  cases outcome with
  | value value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨post.rows, post.successful⟩
    | stage origin call reason => exact post

variable (semantic : ∀ reason token, semanticFaults reason token → CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      completion.result.diagnostics (.semantic reason) token))

include support observed stable beforeTyped argumentsTyped semantic faithful observations assignmentInterpretation in
/-- Preservation receives the actual Source-selected scope and allocation.
The already constructed parameter admission feeds the strict recursive whole-body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry
      arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {bodySize : Nat} (within : bodySize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source inputs.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have tree := support.tree child selected
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true function.body := by
    rw [stages.source selected]
    exact packet.shape
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact support.frame.code.graph.nodeOccurrencesUnique
  have slots := CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix
    captured code owner code.compilation.administrativePrefix observed added length copied spine kept
  let initial : (CallableIndexedOwnedExpressionHeads.argumentProtocol (headers := headers)
      owner code.compilation.administrativePrefix).State
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩ := ⟨reached, slots⟩
  have canonicalAdmitted : CallableIndexedOwnedSourceAdmission.Admission canonicalBridge inputs.context initial :=
    ⟨admitted.heap, admitted.rows⟩
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  have flowResult :=
    CallableIndexedOwnedAdmittedStagedScopedImperativePreservation.preserves_at (compiled := compiled) (faults := callFaults)
      canonicalBridge
      (CallableIndexedOwnedCanonicalState.bindings owner code.compilation.administrativePrefix)
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner code.compilation.administrativePrefix)
      functions faithful observations completion.result.extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedCanonicalState.markedProducer owner code.compilation.administrativePrefix
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedCanonicalState.readyAt_of_stableOwner
        (headers := headers) owner code.compilation.administrativePrefix (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨rawType, root⟩ := certified
        exact children size smaller
          (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.CanonicalRootAt.ofRoot root) owner
          (CallableIndexedOwnedExpressionHeads.canonicalCaller owner code.compilation.administrativePrefix)
          ⟨rfl, rfl, rfl⟩)
      unique tree (support.sites child selected completion.result.context.registry) semantic
      (by
        rw [stages.source selected]
        obtain ⟨port⟩ := support.assignmentAuthority
        exact assignmentInterpretation port functions _) rfl shape originalTyping support.projection within entry.entry.environments entry.entry.heaps
      entry.entry.locals entry.entry.lookups entry.entry.actualTyped entry.entry.reference entry.entry.read
      entry.entry.unmapped initial conditioned canonicalAdmitted trace
  obtain ⟨flowValue, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ := flowResult
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    unique sourceTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function support.projection represented controlClosed
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated
      packet.fellThrough packet.escaped entry.entry.embedding
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, bodyStore, finalMap, finalWorld, ?_, representedBody, heaps,
    maps, worlds, frame, metadata, returned.val, related, forget_post owner code.compilation.administrativePrefix returned post⟩
  simpa only [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody

include support observed stable beforeTyped argumentsTyped semantic functionTypes faithful observations assignmentInterpretation in
/-- Reflection uses the literal chosen scope and real prefix allocation. It
constructs the original body trace and full post without a new body callback. -/
theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments before store
      owner.key.frameLocation (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {nativeSize : Nat} (within : nativeSize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached packet.child nativeSize := by
  intro value bodyStore completed
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends) entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      inputs.context reached := ⟨heapTyped, rows⟩
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source packet.selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements packet.child.source inputs.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have graph : OccurrenceGraphWellFormed packet.child.source := by
    rw [stages.source packet.selected]
    exact valid.code.graph
  have tree := support.tree packet.child packet.selected
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape packet.child.source true function.body := by
    rw [stages.source packet.selected]
    exact packet.shape
  obtain ⟨added, copied, length, spine, kept⟩ := entry.spine
  have slots := CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix
    captured code owner code.compilation.administrativePrefix observed added length copied spine kept
  let initial : (CallableIndexedOwnedExpressionHeads.argumentProtocol (headers := headers)
      owner code.compilation.administrativePrefix).State
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap,
        entry.store, entry.canonical⟩ := ⟨reached, slots⟩
  have canonicalAdmitted : CallableIndexedOwnedSourceAdmission.Admission canonicalBridge inputs.context initial :=
    ⟨admitted.heap, admitted.rows⟩
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  have bodyTrace := completed
  rw [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace within
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativeFlow.reflects_at (compiled := compiled) (faults := callFaults)
      canonicalBridge
      (CallableIndexedOwnedCanonicalState.bindings owner code.compilation.administrativePrefix)
      (CallableIndexedOwnedCanonicalState.administrativeTransport owner code.compilation.administrativePrefix)
      functions functionTypes faithful observations completion.result.extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedCanonicalState.markedProducer owner code.compilation.administrativePrefix
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedCanonicalState.readyAt_of_stableOwner
        (headers := headers) owner code.compilation.administrativePrefix (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨rawType, root⟩ := certified
        exact children size smaller
          (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.CanonicalRootAt.ofRoot root) owner
          (CallableIndexedOwnedExpressionHeads.canonicalCaller owner code.compilation.administrativePrefix)
          ⟨rfl, rfl, rfl⟩)
      graph tree (support.sites packet.child packet.selected completion.result.context.registry) semantic
      (by
        rw [stages.source packet.selected]
        obtain ⟨port⟩ := support.assignmentAuthority
        exact assignmentInterpretation port functions _) rfl shape originalTyping support.projection (Nat.le_of_lt strict) entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped initial
      conditioned canonicalAdmitted flowTrace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    graph.nodeOccurrencesUnique sourceTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function support.projection represented controlClosed
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound
      packet.fellThrough packet.escaped entry.embedding
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  exact ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld, trace,
    represented.body_result, representedBody, heaps, maps, worlds, frame, metadata, returned.val, related, forget_post owner code.compilation.administrativePrefix returned post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBranchingLambdaBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBranchingLambdaApplicationBounds
/-! The retained scoped body fills the public closure application ports from
canonical expression children. Actual parameter installation retains its
binding spine, while the saved caller receives the exact reached pool and post. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBranchingLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching CanonicalBranchingSupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Branching code stages)
  (support : CanonicalBranchingSupport headers code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations code.compilation.administrativePrefix scope captured.canonical owner.key.frameLocation)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
    completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) callerContext callerSource)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token → CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))

include support observed stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime semantic assignmentInterpretation in
/-- The genuine Source application chooses its own scope and parameter entry.
The same internally constructed body port returns through the saved caller. -/
theorem application_preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size
      invocation callContext before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationSpineBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable budget
    (fun entry added length copied spine kept reached childSize strict =>
      CallableIndexedOwnedPreparedStagedCanonicalBranchingLambdaBodyBounds.source_body_at (semantic := semantic)
        (assignmentInterpretation := assignmentInterpretation)
        (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
        (observations := CallableIndexedOwnedContextualFunctionViews.observations profile)
        (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (observed := observed) (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry added length copied spine kept reached children (Nat.le_of_lt strict))
    trace within

include support observed stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime semantic assignmentInterpretation in
/-- Native application selects its real strict body child. The packet's
chosen Source scope supplies that body and the original returned caller post. -/
theorem application_reflects
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation callContext before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable packet.child packet.selected valid budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedCanonicalBranchingLambdaBodyBounds.native_body_at (semantic := semantic)
        (assignmentInterpretation := assignmentInterpretation)
        (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
        (observations := CallableIndexedOwnedContextualFunctionViews.observations profile)
        (functionTypes := CallableIndexedOwnedContextualFunctionViews.runtime_views profile)
        (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (observed := observed) (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached valid children (Nat.le_of_lt strict))
    completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalBranchingLambdaApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalTerminalLambdaBodyBounds
/-! A supported terminal body uses its literal compiler receipt and the
actual parameter entry. The selected registry supplies its original Source
scope, and the retained Code supplies the compiler metadata view. Original
body typing and parameter admission are constructed before the used strict
expression hypothesis is invoked. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalTerminalLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
  {faults : RecursiveStageMeaning.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (callerPrefix : Nat)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {expression : ExpressionId}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
  (terminal : Receipt policy fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    expression function.body code.receipt.resultCore reasonAt fellThrough escaped code.receipt.body)
  {certificate : GenericExpressionMeaning.Certificate}
  (certifies : ∀ lowered,
    policy.lowerExpression terminal.childFuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression reasonAt = .ok lowered →
    certificate
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression lowered)

private theorem forget_post {index : ProtectedStateTransition.Index}
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    (state : (CallableIndexedOwnedExpressionHeads.argumentProtocol (headers := headers) owner callerPrefix).State index)
    (post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner callerPrefix).forgetSlots
      context type outcome state) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys))
      context type outcome state.val := by
  cases outcome with
  | value value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨post.rows, post.successful⟩
    | stage origin call reason => exact post

include observed stable beforeTyped argumentsTyped terminal certifies in
/-- The actual Source closure rule supplies its selected scope and frame.
The same compiler body and parameter pool satisfy the Source body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    (budget bodySize : Nat) (within : bodySize ≤ budget)
    (children : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
        (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner callerPrefix).forgetSlots inputs.context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        stages child certificate faults budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := faults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have view : LambdaMetadataViews.MetadataView child.source code.view := by
    rw [stages.source selected]
    exact code.viewOfSource
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at bodyTyped
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact valid.code.graph.nodeOccurrencesUnique
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  have slots := CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix
    captured code owner callerPrefix observed added length copied spine kept
  let initial : (CallableIndexedOwnedExpressionHeads.argumentProtocol (headers := headers) owner callerPrefix).State
      ⟨_, entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := ⟨reached, slots⟩
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
      frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.preserves_body
    (receipt := terminal) (view := view) (bridge := (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner callerPrefix).forgetSlots)
    (bodyTyped := bodyTyped) (complete := completes) (certifies := certifies)
    (environments := entry.entry.environments) (heaps := entry.entry.heaps)
    (locals := entry.entry.locals) (agrees := entry.entry.lookups)
    (typed := entry.entry.actualTyped) (initial := initial) (admitted := ⟨admitted.heap, admitted.rows⟩)
    unique budget (children child selected) trace matched within
  exact ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, returned.val, related, forget_post owner callerPrefix returned post⟩

include observed stable beforeTyped argumentsTyped terminal certifies in
/-- Native completion uses the same retained parameter prefix and original
registry scope. Its independently graded Source body is constructed from the
strict expression reflection at that actual entry. -/
theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (valid : Dynamic.ClosureFrame program function)
    (budget nativeSize : Nat) (within : nativeSize ≤ budget)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner callerPrefix).forgetSlots inputs.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child certificate faults budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := faults)
      captured code history inputs functions owner caller entry reached child nativeSize := by
  intro value bodyStore completed
  have view : LambdaMetadataViews.MetadataView child.source code.view := by
    rw [stages.source selected]
    exact code.viewOfSource
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at bodyTyped
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact valid.code.graph.nodeOccurrencesUnique
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends) entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  obtain ⟨added, copied, length, spine, kept⟩ := entry.spine
  have slots := CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix
    captured code owner callerPrefix observed added length copied spine kept
  let initial : (CallableIndexedOwnedExpressionHeads.argumentProtocol (headers := headers) owner callerPrefix).State
      ⟨_, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := ⟨reached, slots⟩
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner callerPrefix).forgetSlots inputs.context initial := ⟨heapTyped, rows⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, meaning,
      heaps, maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.reflects_body
      (receipt := terminal) (view := view) (bridge := (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner callerPrefix).forgetSlots)
      (bodyTyped := bodyTyped) (complete := completes) (certifies := certifies)
      (environments := entry.environments) (heaps := entry.heaps)
      (locals := entry.locals) (agrees := entry.lookups) (typed := entry.actualTyped)
      (initial := initial) (admitted := admitted) unique budget children completed within
  exact ⟨sourceSize, inputs.context,
    CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome,
    outcome, after, finalMap, finalWorld, trace, matched, meaning,
    heaps, maps, worlds, frame, metadata, returned.val, related, forget_post owner callerPrefix returned post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalTerminalLambdaBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalTerminalLambdaApplicationBounds
/-! The actual retained closure application constructs its terminal body
ports from the same compiler receipt and strict expression hypotheses.
Parameter installation and caller restoration use their original producers;
semantic and stage failures keep their exact Source scope and reached state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalTerminalLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
  {faults : RecursiveStageMeaning.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (callerPrefix : Nat)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {expression : ExpressionId}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
  (terminal : Receipt policy fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    expression function.body code.receipt.resultCore reasonAt fellThrough escaped code.receipt.body)
  {certificate : GenericExpressionMeaning.Certificate}
  (certifies : ∀ lowered,
    policy.lowerExpression terminal.childFuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression reasonAt = .ok lowered →
    certificate
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression lowered)


variable (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid program callerContext callerSource)

include observed stable beforeTyped argumentsTyped terminal certifies represented heaps locals reference currentCarried allowed callerRuntime in
/-- The strict body port is manufactured at the genuine parameter entry.
The Source application and both native prefixes run once. -/
theorem application_preserves (budget : Nat)
    (children : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
        (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner callerPrefix).forgetSlots inputs.context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        stages child certificate faults budget)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies program stages size invocation callContext before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := registry) (faults := faults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationSpineBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable budget
    (fun entry added length copied spine kept reached childSize strict =>
      CallableIndexedOwnedPreparedStagedCanonicalTerminalLambdaBodyBounds.source_body_at
        captured code history inputs functions owner caller callerPrefix observed stable beforeTyped argumentsTyped terminal certifies
        entry added length copied spine kept reached budget childSize (Nat.le_of_lt strict) children)
    trace within

include observed stable beforeTyped argumentsTyped terminal certifies represented heaps locals reference currentCarried allowed callerRuntime in
/-- Reflection selects the authentic strict native body child and constructs
its independently graded Source body from the expression hypothesis. -/
theorem application_reflects (child : Staging.Recursive.Scope)
    (selected : stages.Closure function child) (valid : Dynamic.ClosureFrame program function)
    (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner callerPrefix).forgetSlots inputs.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child certificate faults budget)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies program stages sourceSize invocation callContext before
        (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := registry) (faults := faults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable child selected valid budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedCanonicalTerminalLambdaBodyBounds.native_body_at
        captured code history inputs functions owner caller callerPrefix observed stable beforeTyped argumentsTyped terminal certifies
        entry reached child selected valid budget childSize (Nat.le_of_lt strict) children)
    completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalTerminalLambdaApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaBodyBounds
/-! The chosen branching packet supplies the existing shape-independent body
ports at the genuine parameter entry. Original parameter admission and native
allocation typing are reused literally. Strong numeric Root induction supplies
the evaluated children; no whole-body meaning is a static packet field. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching BranchingSupport parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Branching code stages)
  (support : BranchingSupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token → CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      completion.result.diagnostics (.semantic reason) token))

include support stable beforeTyped argumentsTyped semantic faithful observations assignmentInterpretation in
/-- Preservation receives the actual Source-selected scope and allocation.
The already constructed parameter admission feeds the strict recursive whole-body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry
      arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {bodySize : Nat} (within : bodySize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source inputs.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have tree := support.tree child selected
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true function.body := by
    rw [stages.source selected]
    exact packet.shape
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact support.frame.code.graph.nodeOccurrencesUnique
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  obtain ⟨flowValue, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativePreservation.preserves_at (compiled := compiled) (faults := callFaults)
      CallableIndexedOwnedBodyRestorationAdmission.bridge
      (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      (CallableIndexedOwnedFunctionState.administrativeTransport headers keys)
      functions faithful observations completion.result.extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedMarkedAllocation.producer headers keys
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
        (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root⟩ := certified
        exact children size smaller root ⟨rfl, rfl, rfl⟩)
      unique tree (support.sites child selected completion.result.context.registry) semantic
      (by
        rw [stages.source selected]
        obtain ⟨port⟩ := support.assignmentAuthority
        exact assignmentInterpretation port functions _) rfl shape originalTyping support.projection within entry.entry.environments entry.entry.heaps
      entry.entry.locals entry.entry.lookups entry.entry.actualTyped entry.entry.reference entry.entry.read
      entry.entry.unmapped reached conditioned admitted trace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    unique sourceTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function support.projection represented controlClosed
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated
      packet.fellThrough packet.escaped entry.entry.embedding
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, bodyStore, finalMap, finalWorld, ?_, representedBody, heaps,
    maps, worlds, frame, metadata, returned, related, post⟩
  simpa only [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody

include support stable beforeTyped argumentsTyped semantic functionTypes faithful observations assignmentInterpretation in
/-- Reflection uses the literal chosen scope and real prefix allocation. It
constructs the original body trace and full post without a new body callback. -/
theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments before store
      owner.key.frameLocation (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {nativeSize : Nat} (within : nativeSize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached packet.child nativeSize := by
  intro value bodyStore completed
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends) entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      inputs.context reached := ⟨heapTyped, rows⟩
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source packet.selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements packet.child.source inputs.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have graph : OccurrenceGraphWellFormed packet.child.source := by
    rw [stages.source packet.selected]
    exact valid.code.graph
  have tree := support.tree packet.child packet.selected
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape packet.child.source true function.body := by
    rw [stages.source packet.selected]
    exact packet.shape
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  have bodyTrace := completed
  rw [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace within
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativeFlow.reflects_at (compiled := compiled) (faults := callFaults)
      CallableIndexedOwnedBodyRestorationAdmission.bridge
      (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      (CallableIndexedOwnedFunctionState.administrativeTransport headers keys)
      functions functionTypes faithful observations completion.result.extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedMarkedAllocation.producer headers keys
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
        (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root⟩ := certified
        exact children size smaller root ⟨rfl, rfl, rfl⟩)
      graph tree (support.sites packet.child packet.selected completion.result.context.registry) semantic
      (by
        rw [stages.source packet.selected]
        obtain ⟨port⟩ := support.assignmentAuthority
        exact assignmentInterpretation port functions _) rfl shape originalTyping support.projection (Nat.le_of_lt strict) entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped reached
      conditioned admitted flowTrace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    graph.nodeOccurrencesUnique sourceTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function support.projection represented controlClosed
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound
      packet.fellThrough packet.escaped entry.embedding
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  exact ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld, trace,
    represented.body_result, representedBody, heaps, maps, worlds, frame, metadata, returned, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaApplicationBounds
/-! A chosen real branching body fills the existing closure application ports.
Parameter installation and the saved caller restoration remain their original
producers. The body ports are manufactured from static support and the strict
Root induction hypothesis, preserving the literal returned pool and post. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching BranchingSupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Branching code stages)
  (support : BranchingSupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
    completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) callerContext callerSource)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token → CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))

include support stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime semantic assignmentInterpretation in
/-- The genuine Source application chooses its own scope and parameter entry.
The same internally constructed body port returns through the saved caller. -/
theorem application_preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size
      invocation callContext before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedBranchingLambdaBodyBounds.source_body_at (semantic := semantic)
        (assignmentInterpretation := assignmentInterpretation)
        (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
        (observations := CallableIndexedOwnedContextualFunctionViews.observations profile)
        (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached children (Nat.le_of_lt strict))
    trace within

include support stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime semantic assignmentInterpretation in
/-- Native application selects its real strict body child. The packet's
chosen Source scope supplies that body and the original returned caller post. -/
theorem application_reflects
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation callContext before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable packet.child packet.selected valid budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedBranchingLambdaBodyBounds.native_body_at (semantic := semantic)
        (assignmentInterpretation := assignmentInterpretation)
        (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
        (observations := CallableIndexedOwnedContextualFunctionViews.observations profile)
        (functionTypes := CallableIndexedOwnedContextualFunctionViews.runtime_views profile)
        (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached valid children (Nat.le_of_lt strict))
    completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaBodyBounds
/-! The chosen imperative packet supplies the existing shape-independent body
ports at the genuine parameter entry. Original parameter admission and native
allocation typing are reused literally. Strong numeric Root induction supplies
the evaluated children; no whole-body meaning is a static packet field. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Imperative ImperativeSupport parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Imperative code stages)
  (support : ImperativeSupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support stable beforeTyped argumentsTyped in
/-- Preservation receives the actual Source-selected scope and allocation.
The already constructed parameter admission feeds the strict recursive whole-body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry
      arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {bodySize : Nat} (within : bodySize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source inputs.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have tree := support.tree child selected
  have shape : CallableIndexedOwnedPreparedStagedBareAssignmentTree.Shape child.source function.body := by
    rw [stages.source selected]
    exact packet.shape
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact support.frame.code.graph.nodeOccurrencesUnique
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  obtain ⟨flowValue, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedImperativePreservation.preserves_at
      CallableIndexedOwnedBodyRestorationAdmission.bridge
      (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      (CallableIndexedOwnedFunctionState.administrativeTransport headers keys)
      functions completion.result.extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedMarkedAllocation.producer headers keys
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)).toOrdinary
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
        (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root⟩ := certified
        exact children size smaller root ⟨rfl, rfl, rfl⟩)
      unique tree rfl rfl shape originalTyping support.projection within entry.entry.environments entry.entry.heaps
      entry.entry.locals entry.entry.lookups entry.entry.actualTyped entry.entry.reference entry.entry.read
      entry.entry.unmapped reached conditioned admitted trace
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated
      packet.fellThrough packet.escaped entry.entry.embedding
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, bodyStore, finalMap, finalWorld, ?_, representedBody, heaps,
    maps, worlds, frame, metadata, returned, related, post⟩
  simpa only [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody

include support stable beforeTyped argumentsTyped in
/-- Reflection uses the literal chosen scope and real prefix allocation. It
constructs the original body trace and full post without a new body callback. -/
theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments before store
      owner.key.frameLocation (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {nativeSize : Nat} (within : nativeSize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached packet.child nativeSize := by
  intro value bodyStore completed
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends) entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      inputs.context reached := ⟨heapTyped, rows⟩
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source packet.selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements packet.child.source inputs.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have graph : OccurrenceGraphWellFormed packet.child.source := by
    rw [stages.source packet.selected]
    exact valid.code.graph
  have tree := support.tree packet.child packet.selected
  have shape : CallableIndexedOwnedPreparedStagedBareAssignmentTree.Shape packet.child.source function.body := by
    rw [stages.source packet.selected]
    exact packet.shape
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  have bodyTrace := completed
  rw [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace within
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedImperativeFlow.reflects_at
      CallableIndexedOwnedBodyRestorationAdmission.bridge
      (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      (CallableIndexedOwnedFunctionState.administrativeTransport headers keys)
      functions completion.result.extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedMarkedAllocation.producer headers keys
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)).toOrdinary
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
        (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root⟩ := certified
        exact children size smaller root ⟨rfl, rfl, rfl⟩)
      graph tree rfl rfl shape originalTyping support.projection (Nat.le_of_lt strict) entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped reached
      conditioned admitted flowTrace
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound
      packet.fellThrough packet.escaped entry.embedding
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  exact ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld, trace,
    represented.body_result, representedBody, heaps, maps, worlds, frame, metadata, returned, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaApplicationBounds
/-! A chosen real imperative body fills the existing closure application ports.
Parameter installation and the saved caller restoration remain their original
producers. The body ports are manufactured from static support and the strict
Root induction hypothesis, preserving the literal returned pool and post. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Imperative ImperativeSupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Imperative code stages)
  (support : ImperativeSupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
    completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) callerContext callerSource)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime in
/-- The genuine Source application chooses its own scope and parameter entry.
The same internally constructed body port returns through the saved caller. -/
theorem application_preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size
      invocation callContext before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedImperativeLambdaBodyBounds.source_body_at
        (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached children (Nat.le_of_lt strict))
    trace within

include support stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime in
/-- Native application selects its real strict body child. The packet's
chosen Source scope supplies that body and the original returned caller post. -/
theorem application_reflects
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation callContext before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable packet.child packet.selected valid budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedImperativeLambdaBodyBounds.native_body_at
        (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached valid children (Nat.le_of_lt strict))
    completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaBodyBounds
/-! The chosen lexical packet supplies the existing shape-independent body
ports at the genuine parameter entry. Original parameter admission and native
allocation typing are reused literally. Strong numeric Root induction supplies
the evaluated children; no whole-body meaning is a static packet field. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Lexical LexicalSupport parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Lexical code stages)
  (support : LexicalSupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support stable beforeTyped argumentsTyped in
/-- Preservation receives the actual Source-selected scope and allocation.
The already constructed parameter admission feeds the strict recursive whole-body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry
      arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {bodySize : Nat} (within : bodySize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  have tree := support.tree child selected
  have shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape child.source function.body := by
    rw [stages.source selected]
    exact packet.shape
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact support.frame.code.graph.nodeOccurrencesUnique
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  obtain ⟨flowValue, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalPreservation.preserves
      CallableIndexedOwnedBodyRestorationAdmission.bridge
      (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      functions rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedMarkedAllocation.producer headers keys
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)).toOrdinary
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
        (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root⟩ := certified
        exact children size smaller root ⟨rfl, rfl, rfl⟩)
      unique tree rfl shape support.projection within entry.entry.environments entry.entry.heaps
      entry.entry.locals entry.entry.lookups entry.entry.actualTyped entry.entry.reference entry.entry.read
      entry.entry.unmapped reached conditioned admitted trace
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated
      packet.fellThrough packet.escaped entry.entry.embedding
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, bodyStore, finalMap, finalWorld, ?_, representedBody, heaps,
    maps, worlds, frame, metadata, returned, related, post⟩
  simpa only [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody

include support stable beforeTyped argumentsTyped in
/-- Reflection uses the literal chosen scope and real prefix allocation. It
constructs the original body trace and full post without a new body callback. -/
theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments before store
      owner.key.frameLocation (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {nativeSize : Nat} (within : nativeSize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached packet.child nativeSize := by
  intro value bodyStore completed
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends) entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      inputs.context reached := ⟨heapTyped, rows⟩
  have tree := support.tree packet.child packet.selected
  have shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape packet.child.source function.body := by
    rw [stages.source packet.selected]
    exact packet.shape
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  have bodyTrace := completed
  rw [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace within
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFlow.reflects
      CallableIndexedOwnedBodyRestorationAdmission.bridge
      (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      functions rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedMarkedAllocation.producer headers keys
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)).toOrdinary
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
        (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨root⟩ := certified
        exact children size smaller root ⟨rfl, rfl, rfl⟩)
      tree rfl shape support.projection (Nat.le_of_lt strict) entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped reached
      conditioned admitted flowTrace
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound
      packet.fellThrough packet.escaped entry.embedding
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  exact ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld, trace,
    represented.body_result, representedBody, heaps, maps, worlds, frame, metadata, returned, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaApplicationBounds
/-! A chosen real lexical body fills the existing closure application ports.
Parameter installation and the saved caller restoration remain their original
producers. The body ports are manufactured from static support and the strict
Root induction hypothesis, preserving the literal returned pool and post. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Lexical LexicalSupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Lexical code stages)
  (support : LexicalSupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
    completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) callerContext callerSource)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime in
/-- The genuine Source application chooses its own scope and parameter entry.
The same internally constructed body port returns through the saved caller. -/
theorem application_preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size
      invocation callContext before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedLexicalLambdaBodyBounds.source_body_at
        (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached children (Nat.le_of_lt strict))
    trace within

include support stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime in
/-- Native application selects its real strict body child. The packet's
chosen Source scope supplies that body and the original returned caller post. -/
theorem application_reflects
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation callContext before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable packet.child packet.selected valid budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedLexicalLambdaBodyBounds.native_body_at
        (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached valid children (Nat.le_of_lt strict))
    completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEmptyLambdaApplicationBounds
/-! Empty ordinary closure bodies run their actual compiled unit footer.
The original parameter allocation and saved caller restoration supply the
same reached pool, heap and post as every other application branch. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEmptyLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Empty EmptySupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Empty code stages)
  (support : EmptySupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
    completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) callerContext callerSource)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include packet in
private theorem footer_evaluates (actual : Environment) (initial : Store) (ξ : Renaming) :
    Evaluates actual initial (code.receipt.body.rename ξ) (.inRight .word .unit) initial := by
  rw [packet.emitted, packet.nativeUnit]
  have renamed : (CompatibleStatements.finish .unit (LocalLoop.fallthrough .unit)
      code.compilation.internalReason code.compilation.internalReason).rename ξ =
      CompatibleStatements.finish .unit (LocalLoop.fallthrough .unit)
        code.compilation.internalReason code.compilation.internalReason := by
    simp [CompatibleStatements.finish, LocalControl.finish, LocalLoop.toControl,
      LocalLoop.fallthrough, LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt,
      Expr.rename, Renaming.lift]
  rw [renamed]
  exact LocalControl.finish_fallthrough .unit
    (LocalLoop.toControl_normal _ code.compilation.internalReason (LocalLoop.fallthrough_evaluates .unit actual initial))
    (by simpa [LanguageResult.success, Expr.weakenAt] using
      (show Evaluates (.unit :: .inLeft .unit .unit :: actual) initial
        (.inRight .word .unit) (.inRight .word .unit) initial from .inRight .unit))

private theorem empty_trace {program : Program} {stages : Staging.Recursive.Registry}
    {size : Nat} {child : Staging.Recursive.Scope} {context finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {ids : List StatementId}
    {outcome : Staging.Recursive.BodyOutcome} (empty : ids = [])
    (trace : Staging.Recursive.Size.Statements program stages size child context environment heap
      ids finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ after = heap := by
  subst ids
  cases trace
  exact ⟨rfl, rfl, rfl⟩

private theorem empty_outcome {type : TypeSystem.Ty} {environment : Dynamic.Environment}
    {outcome : Staging.Recursive.Outcome}
    (matched : Staging.Recursive.BodyResult type (.fallthrough environment) outcome) :
    outcome = .value .unit := by
  cases matched
  rfl

private theorem unit_typed {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {type : TypeSystem.Ty} (same : type = .unit) : Dynamic.ValueHasType context heap .unit type := by
  subst type
  exact .unit

private theorem unit_result (sourceType : TypeSystem.Ty) (nativeType : Ty)
    (raw : sourceType = .unit) (native : nativeType = .unit) (m : LocationMap) (w : StoreTyping) :
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
      m w sourceType nativeType callFaults (.value .unit) (.inRight .word .unit) := by
  subst sourceType
  subst nativeType
  exact .value .unit

include packet stable beforeTyped argumentsTyped in
private theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    (bodySize : Nat) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  obtain ⟨rfl, rfl, rfl⟩ := empty_trace packet.empty trace
  obtain rfl := empty_outcome matched
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  refine ⟨_, entry.entry.store, entry.entry.mapping, entry.entry.world,
    footer_evaluates (captured := captured) (code := code) (packet := packet) _ _ _, ?_, entry.entry.heaps,
    .refl _, .refl _, .refl _ _, .refl _, reached, .refl _, ?_⟩
  · exact unit_result (profile := profile) _ _ packet.unit packet.nativeUnit _ _
  · change CallableIndexedOwnedSourceAdmission.PostAdmission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      inputs.context function.resultType (.value .unit) reached
    refine ⟨admitted.rows, ?_⟩
    intro value same
    cases same
    exact ⟨unit_typed packet.unit, admitted.heap⟩

include packet stable beforeTyped argumentsTyped in
private theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (nativeSize : Nat) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached packet.child nativeSize := by
  intro value bodyStore completed
  have evaluated := footer_evaluates (captured := captured) (code := code) (packet := packet) entry.actual entry.store entry.embedding
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluated
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends) entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  refine ⟨Staging.Recursive.Size.stepSize [], inputs.context, .fallthrough entry.environment,
    .value .unit, entry.heap, entry.mapping, entry.world, ?_, ?_, ?_, entry.heaps,
    .refl _, .refl _, .refl _ _, .refl _, reached, .refl _, ?_⟩
  · simpa only [packet.empty] using
      (Staging.Recursive.Size.Statements.nil (program := Program.ofChecked compiled.sourceProgram)
        (registry := stages) (scope := packet.child) (context := inputs.context)
        (environment := entry.environment) (heap := entry.heap))
  · rw [packet.unit]
    exact .unit
  · exact unit_result (profile := profile) _ _ packet.unit packet.nativeUnit _ _
  · change CallableIndexedOwnedSourceAdmission.PostAdmission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      inputs.context function.resultType (.value .unit) reached
    refine ⟨rows, ?_⟩
    intro result same
    cases same
    exact ⟨unit_typed packet.unit, heapTyped⟩

include packet stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime in
/-- The real Source call allocates its parameters before the empty body and
restores the actual saved caller after its unit result. -/
theorem application_preserves
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size
      invocation callContext before (.closure function) arguments outcome after) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable size
    (fun entry reached childSize _strict =>
      source_body_at (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached childSize)
    trace (Nat.le_refl size)

include packet stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime in
/-- Native completion determines the unchanged body store and unit result;
reflection reconstructs the original empty Source body with its own grade. -/
theorem application_reflects
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation callContext before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable packet.child packet.selected valid size
    (fun entry reached childSize _strict =>
      native_body_at (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached valid childSize)
    completed (Nat.le_refl size)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEmptyLambdaApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEmptyBodyCompilerReceipts
/-! The actual retained callback compiles an empty body to its original
fallthrough footer. The independent BodyWith supplies the result projection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEmptyBodyCompilerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Empty EmptySupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {named : Named} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {stages : Staging.Recursive.Registry}

/-- Every field comes from this exact Code, original static body and selected scope. -/
theorem of_empty
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) registry faults)
    (empty : function.body = []) (unit : function.resultType = .unit)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Σ packet : Empty code stages,
      EmptySupport code body.toContext stages packet faults) := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have applied := congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    applied.trans (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
      compiled.indexed named compilation.own.assignments diagnostics expression)
  have generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason =
      .ok (LocalLoop.fallthrough code.receipt.resultCore) := by
    exact (congrArg (fun statements => SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      statements code.receipt.resultCore code.reasonAt true code.compilation.internalReason) empty).trans (by simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy])
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  rw [generated] at accepted
  have emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore
      (LocalLoop.fallthrough code.receipt.resultCore) code.compilation.internalReason
      code.compilation.internalReason := Except.ok.inj accepted.symm
  have nativeUnit : code.receipt.resultCore = .unit := by
    have projected := body.projection
    have atUnit := (congrArg compiled.compatible.checked.catalog.project unit).symm.trans projected
    exact Except.ok.inj atUnit.symm
  exact ⟨⟨⟨empty, unit, nativeUnit, emitted, child, selected⟩, ⟨body.frame⟩⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEmptyBodyCompilerReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerReceipts
/-! The original body callback determines one lexical flow, allocator and
finish footer at the authentic closure Code. This contains only compiler facts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleEncoding (bind_ok)
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Lexical parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative) {stages : Staging.Recursive.Registry}

structure Choice where
  packet : Lexical code stages
  callback : packet.policy.lowerExpression = FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  reason : packet.reasonAt = code.reasonAt
  readPolicy : packet.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    packet.policy.lowerBinder code.view scope binder =
      SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked code.view scope binder
  allocationPolicy : packet.policy.sourceCells = some
    (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
      compiled.indexed.base.globals.length
      (compiled.indexed.layouts.allocatorAt packet.allocationOwner packet.active packet.onError))

/-- The actual retained lowerer supplies all allocator and binder callbacks;
none is inferred from a native result type. -/
theorem choose (named : Named)
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape function.source function.body)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Choice code (stages := stages)) := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    (congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe).trans
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
        compiled.indexed named compilation.own.assignments diagnostics expression)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  refine ⟨{
    packet := {
      policy := policy
      fuel := code.fuel
      reasonAt := code.reasonAt
      fellThrough := code.compilation.internalReason
      escaped := code.compilation.internalReason
      allocationOwner := named.signature.key
      active := []
      onError := fun error => .sourceAllocation (reprStr error)
      flow := flow
      accepted := generated
      emitted := (Except.ok.inj returned).symm
      shape := shape
      child := child
      selected := selected }
    callback := rfl
    reason := rfl
    readPolicy := rfl
    binderPolicy := ?_
    allocationPolicy := rfl }⟩
  intro current binder mono
  change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
  simp only [SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil, ↓reduceIte]
  rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerSupport
/-! Actual closure flow compilation supplies each child at its genuine lexical
context. Reached-only metadata transports the same allocations and native code
back to original Source. Child factories receive compiler and typing facts only. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Lexical LexicalSupport parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedLexicalContextCertificates

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
  {stages : Staging.Recursive.Registry} (choice : Choice code (stages := stages))

/-- Static declarations are insensitive to the exact allowed metadata edit. -/
theorem scope_declarations {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    (declared : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations view scope context := by
  intro binder original index type found root
  exact declared binder original index type found (by simpa only [rootBinder metadata] using root)

include frame in
/-- Native typing is inverted from the actual lambda once. Each expression
factory sees its original typed node, accepted view callback and real context. -/
theorem tree
    (view : CallableIndexedOwnedContextualLambdaProvenance.BodyView code)
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context)
    (sourceSignatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (syntaxTree : GenericLexicalStatements.Syntax function.source expressionSyntax
      inputs.context true function.body function.resultType)
    (children : ∀ context, Dynamic.RuntimeContextFields inputs.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations function.source scope context →
      expressionSyntax id → Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      function.source.lookupExpression? id = some node → ExpressionHasType function.source context id node.type →
      choice.packet.policy.lowerExpression fuel code.view scope id choice.packet.reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType compiled.indexed.layouts.definitions → certificates context scope id lowered) :
    GenericLexicalStatements.Tree compiled.indexed.layouts choice.packet.allocationOwner choice.packet.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length choice.packet.onError
      (.initial compiled.compatible.checked) function.source
      (TypedCertificate function.source certificates)
      inputs.context (parameterScope code) true function.body function.resultType code.receipt.resultCore choice.packet.flow := by
  let changed := CallableIndexedLambdaBodyViewEdits.changed function.source code.view
  have edited : LocalView function.source code.view changed := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have avoids := CallableIndexedLambdaBodyViewEdits.avoids view
  have unique := frame.code.graph.nodeOccurrencesUnique
  have viewedSyntax := CallableLambdaViewSourceTyping.lexical_syntax_with edited avoids unique
    (fun _ _ original => original) syntaxTree
    (fun id member => Reaches.root (List.mem_map.mpr ⟨id, member, rfl⟩))
  have reverse : LocalView code.view function.source changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  have native := CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native code
  rw [choice.packet.emitted] at native
  obtain ⟨nativeType, native⟩ := TypedLexicalWhile.Native.finished_flow native
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_parameters (values := .initial compiled.compatible.checked) code inputs frame captured
  have extracted := CallableIndexedOwnedPreparedNativeLexicalCollectors.tree_of_typed_flow_with_residual true
    (values := .initial compiled.compatible.checked)
    choice.readPolicy choice.binderPolicy choice.allocationPolicy
    (certificates := fun context scope id lowered => Dynamic.RuntimeContextFields inputs.context context →
      Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      TypedCertificate function.source certificates context scope id lowered)
    (fun context _closed _residual _signatures scope fuel id node lowered declarations syntaxValue found typed accepted nativeType childTyped fields reached => by
      have originalFound : function.source.lookupExpression? id = some node :=
        (expression_lookup edited avoids reached).trans found
      have originalTyped := CallableLambdaViewStaticTyping.expression_original edited avoids unique typed reached
      exact ⟨node, originalFound, originalTyped,
        children context fields (scope_declarations code.viewOfSource.symm declarations)
          syntaxValue reached originalFound originalTyped accepted childTyped⟩)
    viewedSyntax runtime.variables_closed runtime.residual_variables_open sourceSignatures
    (scope_declarations code.viewOfSource declarations) projection choice.packet.accepted native
  have discharged := Tree.discharge_context extracted (.refl _)
  exact CallableLambdaViewBodyTree.body reverse (avoids.view edited.metadata)
    (fun _ _ id _ reached child => child (reached.metadata edited.metadata.symm)) discharged

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots
/-! Ordinary closure reads at real lexical contexts are recovered from actual
body callbacks. Original frames, declarations, metadata and issued diagnostic
provenance supply every static Root field; no execution law is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability CallableLambdaViewEdits
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls Syntax PolicyOn)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor MetadataOn)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots (OriginalAuthority)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt Root)
open CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerReceipts (Choice)

private theorem read_no_calls
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (root : Certificate policy body compilation readFuel values source context reasonAt scope id lowered)
    {callFuel : Nat} {callScope : SourceCoreLocalCell.Scope} {callId callee : ExpressionId}
    {ids : List ExpressionId} {metadata : IndirectCallResolution} {code : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body callFuel compilation source
      callScope callId callee ids metadata reasonAt code) (path : Calls compiler root) : False := by
  cases path with
  | here sequence children =>
    have identity := Option.some.inj (compiler.found.symm.trans found)
    have same := compiler.originalForm
    rw [identity, form] at same
    cases same
  | @method_child current id otherFuel code types outer sequence children child childCode member inside =>
    have identity := Option.some.inj (outer.metadata.found.symm.trans found)
    rcases outer.operator.form with ⟨operator, operand, otherForm, _⟩ | ⟨operator, left, right, otherForm, _⟩
    all_goals rw [identity, form] at otherForm; cases otherForm
  | @group current id other inner innerNode code actual otherForm innerFound type child inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @tuple_child current id other tupleIds types codes header sequence children child childCode member inside =>
    have identity := Option.some.inj (header.metadata.found.symm.trans found)
    have same := header.form
    rw [identity, form] at same
    cases same
  | @constructor_child current id other instantiation constructorIds tag headerWord codes header otherForm admissible ranges count nodes sequence children child childCode member inside =>
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst other
    simp [form] at otherForm
  | @builtin_child current id otherCallee otherIds function otherFuel code outer calleeTyped sourceType nativeTypes sequence children child childCode member inside =>
    have identity := Option.some.inj (outer.metadata.found.symm.trans found)
    have same := outer.form
    rw [identity, form] at same
    cases same
  | @direct_child current id callee directIds instantiation fuel code types outer calleeTyped application sequence children child childCode member inside =>
    have identity := Option.some.inj (outer.metadata.found.symm.trans found)
    have same := outer.form
    rw [identity, form] at same
    cases same
  | @call_child current id otherCallee otherIds otherMetadata otherFuel code types outer sequence children child childCode member inside =>
    have identity := Option.some.inj (outer.found.symm.trans found)
    have same := outer.originalForm
    rw [identity, form] at same
    cases same
  | @unary_child scope id node operand childNode operator operandType resultType core childCode actual otherForm childFound inputType outputType profile child inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @binary_left scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode actual otherForm leftFound rightFound leftType rightType outputType profile first second inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @binary_right scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode actual otherForm leftFound rightFound leftType rightType outputType profile first second inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @conditional_condition scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode actual otherForm conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @conditional_then scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode actual otherForm conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @conditional_else scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode actual otherForm conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @index_base scope id other base key baseNode keyNode layout comparison first second header keyFound otherForm sourceType firstTree secondTree inside
  | @index_key scope id other base key baseNode keyNode layout comparison first second header keyFound otherForm sourceType firstTree secondTree inside =>
    have identity := Option.some.inj (header.metadata.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm




/-- Reached view metadata follows from full original metadata and the exact
unchanged body footprint retained by this Code. -/
theorem viewed_metadata {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {named : CallableIndexedNamedGeneration.Named}
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView code)
    (original : MetadataFor compiled.indexed named function.source) :
    MetadataOn compiled.indexed named code.view
      (fun id => Reaches code.view (function.body.map NodeId.statement) (.expression id)) := by
  let edited := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have avoids := CallableIndexedLambdaBodyViewEdits.avoids bodyView
  have originalTree : ∀ id, Reaches code.view (function.body.map NodeId.statement) (.expression id) →
      Syntax code.view id → Syntax function.source id := fun id reached tree =>
    CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.syntax_original edited avoids tree
      (reached.metadata code.viewOfSource.symm)
  have lookup : ∀ id, Reaches code.view (function.body.map NodeId.statement) (.expression id) →
      ∀ node, code.view.lookupExpression? id = some node → function.source.lookupExpression? id = some node :=
    fun id reached node found => (bodyView id (reached.metadata code.viewOfSource.symm)).trans found
  exact {
    requirements := fun id reached tree node found => original.requirements id (originalTree id reached tree) node (lookup id reached node found)
    coercions := fun id reached tree node found => original.coercions id (originalTree id reached tree) node (lookup id reached node found)
    initializer := fun id reached tree => original.initializer id (originalTree id reached tree)
    arguments := fun id reached tree node found => original.arguments id (originalTree id reached tree) node (lookup id reached node found)
    localRead := fun id reached tree node found => original.localRead id (originalTree id reached tree) node (lookup id reached node found) }

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (original : MetadataFor compiled.indexed support.caller.named function.source)
  {stages : Staging.Recursive.Registry} (choice : Choice code (stages := stages))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include provenance receiver wellFormed original in
/-- The Source lexical context is the exact context supplied by typed
compiler traversal, and diagnostics are restricted to this body's real reads. -/
theorem of_child
    {context : SourceSemantics.Context} {current : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope} (selected : stages.Closure function invocation)
    (fields : Dynamic.RuntimeContextFields support.body.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (typed : ExpressionHasType function.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation code.view current id code.reasonAt = .ok lowered) :
    Nonempty (RootAt compiled context invocation current id lowered faults) := by
  let edited := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have avoids := CallableIndexedLambdaBodyViewEdits.avoids provenance.body_view
  have sourceProfile := (CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.retained_policy_for
    provenance.policy_recipe original current code.reasonAt).on
      (fun id => Reaches function.source (function.body.map NodeId.statement) (.expression id))
  have viewProfile := CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.retained_policy_on
    provenance.policy_recipe (viewed_metadata provenance.body_view original) current code.reasonAt
  have viewedFound : code.view.lookupExpression? id = some node :=
    (provenance.body_view id reached).symm.trans found
  have viewedTree : Syntax code.view id := .leaf (.read viewedFound form)
  have compiledChild := CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.accepted_original_on
    edited avoids sourceProfile viewProfile code.callables fuel viewedTree reached accepted
  have sameSource := stages.source selected
  have unique : NodeOccurrencesUnique invocation.source := by rw [sameSource]; exact support.body.unique
  have childFound : invocation.source.lookupExpression? id = some node := by simpa only [sameSource] using found
  have childTyped : ExpressionHasType invocation.source context id node.type := by simpa only [sameSource] using typed
  have childProfile : PolicyOn code.policy code.compilation compiled.indexed.fuel
      (.initial compiled.compatible.checked) invocation.source current code.reasonAt
      (fun id => Reaches invocation.source (function.body.map NodeId.statement) (.expression id)) := by
    simpa only [sameSource] using sourceProfile
  have childDeclarations : CompatibleExpressionReads.ScopeDeclarations invocation.source current context := by
    simpa only [sameSource] using declarations
  have childTree : Syntax invocation.source id := .leaf (.read childFound form)
  have childReached : Reaches invocation.source (function.body.map NodeId.statement) (.expression id) := by
    simpa only [sameSource] using reached
  have childAccepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation invocation.source current id code.reasonAt = .ok lowered := by
    simpa only [sameSource] using compiledChild
  have coercions : ∀ id node, Syntax invocation.source id →
      invocation.source.lookupExpression? id = some node → node.coercions = [] := by
    intro expression actual tree found
    exact original.coercions expression (by simpa only [sameSource] using tree) actual
      (by simpa only [sameSource] using found)
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions_on
    unique childDeclarations childProfile (fun parent found edge => Reaches.expression parent found edge)
    (fun id node _ tree found => coercions id node tree found) childTree childReached childFound childTyped childAccepted
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation) certificate := by
    intro callFuel callScope callId callee ids callMetadata code compiler path
    exact False.elim (read_no_calls childFound form certificate compiler path)
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
    support.body.frame support.body.extended).1.transport fields
  let root : Root compiled code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context invocation code.reasonAt current id lowered node.type faults := {
    compilerFuel := fuel
    accepted := childAccepted
    certificate := certificate
    node := node
    found := childFound
    rawResult := rfl
    typed := childTyped
    sameLedger := fields.solvedRequirements.trans support.body.valid.ledger
    runtimeLedger := fields.runtimeRequirementLedger support.body.valid.runtime
    unique := unique
    wellFormed := wellFormed
    runtime := by simpa only [sameSource] using runtime
    covers := by rw [stages.evidence selected]; exact fields.covers support.body.valid.covers
    actualFunctionType := by rw [code.callables]; rfl
    uninitialized := by
      intro current child lowered receipt path location
      exact CallableIndexedOwnedContextualLambdaReadDiagnostics.uninitialized support provenance.body_reasons receiver
        (Reaches.from_root reached (by simpa only [sameSource] using path))
        (by simpa only [sameSource] using receipt) location
    callsReady := ready
    noMethods := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_methods_of_policy_on _ childTree childReached childProfile
    noDirect := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax _ childTree
    noIndexes := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax _ childTree }
  exact ⟨RootAt.ofRoot root⟩


include provenance receiver wellFormed original in
/-- The lexical packet is one actual caller of the shared read producer. -/
theorem of_accepted
    {context : SourceSemantics.Context} {current : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope} (selected : stages.Closure function invocation)
    (fields : Dynamic.RuntimeContextFields support.body.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (typed : ExpressionHasType function.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : choice.packet.policy.lowerExpression fuel code.view current id choice.packet.reasonAt = .ok lowered) :
    Nonempty (RootAt compiled context invocation current id lowered faults) := by
  apply of_child code support provenance receiver wellFormed original selected fields declarations reached found form typed
  simpa only [choice.callback, choice.reason, FunctionCode.children] using accepted


/-- The first lexical closure fragment permits any number of original reads. -/
def Read (source : TypedSource) (id : ExpressionId) : Prop :=
  ∃ node name binder, source.lookupExpression? id = some node ∧
    node.form = .reference name (.local binder)

include provenance receiver wellFormed original in
/-- The authentic original compiler traversal constructs every Root at its
real post-let context. The caller supplies only Source grammar facts. -/
def support_reads
    (syntaxTree : GenericLexicalStatements.Syntax function.source (Read function.source)
      support.body.context true function.body function.resultType) :
    CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.LexicalSupport
      code support.body.toContext stages choice.packet faults := by
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
    support.body.frame support.body.extended).1
  have sourceSignatures : support.body.context.signatures = compiled.compatible.checked.signatures :=
    (runtime.signatures.trans
      (RecursiveNamedSelectedExpressionFactory.header_program_signatures
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) support.caller).symm).trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := support.caller))
  refine ⟨support.body.frame, support.body.projection, ?_⟩
  intro child selected
  have actual := CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerSupport.tree
    code support.body.toContext support.body.frame choice provenance.body_view provenance.scope_declarations
    sourceSignatures support.body.projection syntaxTree
    (certificates := fun context scope id lowered => Nonempty (RootAt compiled context child scope id lowered faults))
    (fun context fields current fuel id node lowered declarations read reached found typed accepted _nativeType _native => by
      obtain ⟨readNode, name, binder, readFound, form⟩ := read
      have same := Option.some.inj (readFound.symm.trans found)
      subst readNode
      exact of_accepted code support provenance receiver wellFormed original choice selected fields declarations
        reached found form typed accepted)
  simpa only [stages.source selected] using actual

include provenance receiver wellFormed original in
omit choice in
/-- A packet and its static support are chosen together inside Prop from the
retained lowerer. No classical selector or independently assumed Tree is used. -/
theorem of_reads
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    (shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape function.source function.body)
    (syntaxTree : GenericLexicalStatements.Syntax function.source (Read function.source)
      support.body.context true function.body function.resultType)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Packet code stages,
      CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Support
        headers code support.body.toContext stages packet faults) := by
  obtain ⟨choice⟩ := CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerReceipts.choose
    code support.caller.named provenance.policy_recipe.body_recipe shape child selected
  exact ⟨⟨.lexical choice.packet,
    support_reads code support provenance receiver wellFormed original choice syntaxTree⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaReadRoots
/-! Actual ordinary closure reads construct the expression Roots needed by
conditional and match branches, bare assignments and lexical statements. The retained compiler chooses one
branching packet; no Source execution or whole-body law is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaReadRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability CallableLambdaViewEdits
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots (Read)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (original : MetadataFor compiled.indexed support.caller.named function.source)
  {stages : Staging.Recursive.Registry} (choice : Choice code (stages := stages))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include provenance receiver wellFormed original in
/-- Every original read is issued at its real lexical context, including the
RHS and later reads after a genuine assignment or local allocation. -/
def support_reads
    (choiceIssued : choice.Issued code support.caller.named)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (Read function.source)
      support.body.context (.statements true function.body) function.resultType) :
    CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.BranchingSupport
      code support.body.toContext stages choice.packet faults := by
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
    support.body.frame support.body.extended).1
  have sourceSignatures : support.body.context.signatures = compiled.compatible.checked.signatures :=
    (runtime.signatures.trans
      (RecursiveNamedSelectedExpressionFactory.header_program_signatures
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) support.caller).symm).trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := support.caller))
  have ownership : LocalIdentityOwnership function.source := by
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate support.caller wellFormed
    rw [support.source]
    change LocalIdentityOwnership support.caller.named.specialized.function.typedBody
    rw [← support.caller.agreement.source, support.caller.frame.source]
    exact certificate.local_identity_ownership
  refine ⟨support.body.frame, support.body.projection, choice.invalidProjection, choice.missingDefault,
    choiceIssued.assignmentAuthority code support.caller.selected support.source support.body.unique, ?_⟩
  intro child selected
  have actual := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerSupport.collected
    code support.body.toContext support.body.frame choice provenance.body_view provenance.scope_declarations
    sourceSignatures (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    (CallableIndexedOwnedPublicSignatureCatalog.well_formed compiled wellFormed)
    support.body.valid.ledger support.body.projection
    (fun origin rawProfile => choiceIssued.operands code support.caller.selected support.source receiver origin rawProfile)
    (fun origin rawWord => choiceIssued.unary code support.caller.selected support.source receiver origin rawWord) syntaxTree
    (certificates := fun context scope id lowered => Nonempty (RootAt compiled context child scope id lowered faults))
    (fun context fields current fuel id node lowered declarations read reached found typed accepted _nativeType _native => by
      obtain ⟨readNode, name, binder, readFound, form⟩ := read
      have same := Option.some.inj (readFound.symm.trans found)
      subst readNode
      apply CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.of_child
        code support provenance receiver wellFormed original selected fields declarations reached found form typed
      simpa only [choice.callback, choice.reason, FunctionCode.children] using accepted)
  have weakened := CallableLambdaViewMatchRuntimeCertificates.transport_with
    (LocalView.refl function.source) (by intro id member; cases member)
    support.body.unique (fun _ _ _ => True.intro)
    (fun _ _ _ _ _ value => value) actual.tree
    (fun id member => Reaches.root (List.mem_map.mpr ⟨id, member, rfl⟩))
  rw [stages.source selected]
  refine ⟨weakened, ?_⟩
  intro currentRegistry
  obtain ⟨tree, sites⟩ := PreparedBranchingCatalogTransport.weaken support.body.unique
    (actual.sites currentRegistry)
  exact sites

include provenance receiver wellFormed original in
omit choice in
/-- The real lowerer and typed original syntax produce the same-model packet
and all static support together, without selecting a proof as runtime data. -/
theorem of_reads
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (Read function.source)
      support.body.context (.statements true function.body) function.resultType)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Packet code stages,
      CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Support
        headers code support.body.toContext stages packet faults) := by
  obtain ⟨choice, choiceIssued⟩ := CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts.choose_issued
    code support.caller.named provenance.issued_recipe support.compilation shape child selected
  exact ⟨⟨.branching choice.packet,
    support_reads code support provenance receiver wellFormed original choice choiceIssued syntaxTree⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaReadRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaCompilerReceipts
/-! The original body callback determines one imperative flow, allocator and
finish footer at the authentic closure Code. This contains only compiler facts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaCompilerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleEncoding (bind_ok)
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Imperative parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative) {stages : Staging.Recursive.Registry}

structure Choice where
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  packet : Imperative code stages
  callback : packet.policy.lowerExpression = FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  reason : packet.reasonAt = code.reasonAt
  assignments : CompatibleAssignmentStatements.AssignmentPolicy packet.policy (.initial compiled.compatible.checked) invalidProjection invalidOperand missingDefault
  readPolicy : packet.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    packet.policy.lowerBinder code.view scope binder =
      SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked code.view scope binder
  allocationPolicy : packet.policy.sourceCells = some
    (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
      compiled.indexed.base.globals.length
      (compiled.indexed.layouts.allocatorAt packet.allocationOwner packet.active packet.onError))

/-- The actual retained lowerer supplies all allocator and binder callbacks;
none is inferred from a native result type. -/
theorem choose (named : Named)
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (shape : CallableIndexedOwnedPreparedStagedBareAssignmentTree.Shape function.source function.body)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Choice code (stages := stages)) := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    (congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe).trans
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
        compiled.indexed named compilation.own.assignments diagnostics expression)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  refine ⟨{
    invalidProjection := fun site root => diagnostics.placeReason named.signature.key site root none
    invalidOperand := fun site root operator => if operator = .equal then Word.zero else compilation.own.assignments.reasonAt site root (.value operator)
    missingDefault := fun site root type => diagnostics.placeReason named.signature.key site root (some type)
    packet := {
      policy := policy
      fuel := code.fuel
      reasonAt := code.reasonAt
      fellThrough := code.compilation.internalReason
      escaped := code.compilation.internalReason
      allocationOwner := named.signature.key
      active := []
      onError := fun error => .sourceAllocation (reprStr error)
      flow := flow
      accepted := generated
      emitted := (Except.ok.inj returned).symm
      shape := shape
      child := child
      selected := selected }
    callback := rfl
    reason := rfl
    assignments := ?_
    readPolicy := rfl
    binderPolicy := ?_
    allocationPolicy := rfl }⟩
  · refine ⟨rfl, rfl, ?_⟩
    change some _ = some _
    apply congrArg some
    funext expression fuel source scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl
  · intro current binder mono
    change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
    simp only [SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil, ↓reduceIte]
    rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaCompilerReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaCompilerSupport
/-! Original typed closure syntax and the retained compiler callback produce
an imperative packet for the same Code. Every child keeps the current lexical
context, exact accepted callback and native typing. No execution law is stored. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaCompilerSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Imperative ImperativeSupport parameterScope)
open CallableIndexedOwnedPreparedStagedImperativeLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
  {stages : Staging.Recursive.Registry} (choice : Choice code (stages := stages))

include frame in
/-- The complete native body supplies local typing; authentic metadata views
and binder receipts recover the original Source tree without changing code. -/
theorem tree
    (view : CallableIndexedOwnedContextualLambdaProvenance.BodyView code)
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context)
    (sourceSignatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (syntaxTree : GenericImperativeMatch.Syntax function.source expressionSyntax
      inputs.context (.statements true function.body) function.resultType)
    (children : ∀ context, Dynamic.RuntimeContextFields inputs.context context →
      ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations function.source scope context →
      expressionSyntax id → Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      function.source.lookupExpression? id = some node → ExpressionHasType function.source context id node.type →
      choice.packet.policy.lowerExpression fuel code.view scope id choice.packet.reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType compiled.indexed.layouts.definitions → certificates context scope id lowered) :
    GenericImperativeMatch.Tree compiled.indexed.layouts choice.packet.allocationOwner choice.packet.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length choice.packet.onError
      (.initial compiled.compatible.checked) function.source expressionSyntax
      (TypedCertificate function.source certificates) compiled.indexed.layouts.definitions administrative
      inputs.context (parameterScope code) (.statements true function.body) function.resultType code.receipt.resultCore choice.packet.flow := by
  let changed := CallableIndexedLambdaBodyViewEdits.changed function.source code.view
  have edited : LocalView function.source code.view changed := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have native := CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native code
  rw [choice.packet.emitted] at native
  obtain ⟨nativeType, native⟩ := TypedLexicalWhile.Native.finished_flow native
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_parameters (values := .initial compiled.compatible.checked) code inputs frame captured
  exact CallableIndexedOwnedPreparedNativeBareImperativeCollectors.tree edited
    (CallableIndexedLambdaBodyViewEdits.avoids view) frame.code.graph.nodeOccurrencesUnique
    choice.readPolicy choice.binderPolicy choice.allocationPolicy choice.assignments children
    syntaxTree rfl choice.packet.shape (.refl _) runtime.variables_closed runtime.residual_variables_open sourceSignatures
    declarations (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩)) projection choice.packet.accepted native

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaCompilerSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaReadRoots
/-! Actual ordinary closure reads construct the expression Roots needed by
bare assignments and lexical statements. The retained compiler chooses one
imperative packet; no Source execution or whole-body law is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaReadRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability CallableLambdaViewEdits
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedImperativeLambdaCompilerReceipts (Choice)
open CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots (Read)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (original : MetadataFor compiled.indexed support.caller.named function.source)
  {stages : Staging.Recursive.Registry} (choice : Choice code (stages := stages))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include provenance receiver wellFormed original in
/-- Every original read is issued at its real lexical context, including the
RHS and later reads after a genuine assignment or local allocation. -/
def support_reads
    (syntaxTree : GenericImperativeMatch.Syntax function.source (Read function.source)
      support.body.context (.statements true function.body) function.resultType) :
    CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.ImperativeSupport
      code support.body.toContext stages choice.packet faults := by
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
    support.body.frame support.body.extended).1
  have sourceSignatures : support.body.context.signatures = compiled.compatible.checked.signatures :=
    (runtime.signatures.trans
      (RecursiveNamedSelectedExpressionFactory.header_program_signatures
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) support.caller).symm).trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := support.caller))
  refine ⟨support.body.frame, support.body.projection, ?_⟩
  intro child selected
  have actual := CallableIndexedOwnedPreparedStagedImperativeLambdaCompilerSupport.tree
    code support.body.toContext support.body.frame choice provenance.body_view provenance.scope_declarations
    sourceSignatures support.body.projection syntaxTree
    (certificates := fun context scope id lowered => Nonempty (RootAt compiled context child scope id lowered faults))
    (fun context fields current fuel id node lowered declarations read reached found typed accepted _nativeType _native => by
      obtain ⟨readNode, name, binder, readFound, form⟩ := read
      have same := Option.some.inj (readFound.symm.trans found)
      subst readNode
      apply CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.of_child
        code support provenance receiver wellFormed original selected fields declarations reached found form typed
      simpa only [choice.callback, choice.reason, FunctionCode.children] using accepted)
  have weakened := CallableLambdaViewMatchRuntimeCertificates.transport_with
    (LocalView.refl function.source) (by intro id member; cases member)
    support.body.unique (fun _ _ _ => True.intro)
    (fun _ _ _ _ _ value => value) actual
    (fun id member => Reaches.root (List.mem_map.mpr ⟨id, member, rfl⟩))
  simpa only [stages.source selected] using weakened

include provenance receiver wellFormed original in
omit choice in
/-- The real lowerer and typed original syntax produce the same-model packet
and all static support together, without selecting a proof as runtime data. -/
theorem of_reads
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    (shape : CallableIndexedOwnedPreparedStagedBareAssignmentTree.Shape function.source function.body)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (Read function.source)
      support.body.context (.statements true function.body) function.resultType)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Packet code stages,
      CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Support
        headers code support.body.toContext stages packet faults) := by
  obtain ⟨choice⟩ := CallableIndexedOwnedPreparedStagedImperativeLambdaCompilerReceipts.choose
    code support.caller.named provenance.policy_recipe.body_recipe shape child selected
  exact ⟨⟨.imperative choice.packet,
    support_reads code support provenance receiver wellFormed original choice syntaxTree⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaReadRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaOriginalConditions
/-! The original closure frame and actual BodyWith parameter context construct
per-scope source authority. Genuine captured declarations, coercion exclusions,
program validity and read-fault authority remain explicit. Child grammar,
compiler policy and exact issued-call readiness are separate static obligations.
No body execution or expression meaning law is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaOriginalConditions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditions OriginalConditionsOn)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {stages : Staging.Recursive.Registry}
  {registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (code : Code compiled.indexed function scope administrative)
  (body : CallableIndexedLambdaStaticBodySupport.BodyWith
    (values := .initial compiled.compatible.checked) expressionSyntax certificates code
    (Program.ofChecked compiled.sourceProgram) registry semanticFaults)

/-- The original parameter installation is shared by every actual selected
scope. Its ledger, covering evidence and node identity come from the same body. -/
theorem at_selected_scope
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context)
    (coercions : ∀ id node, Syntax function.source id →
      function.source.lookupExpression? id = some node → node.coercions = [])
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {readFuel : Nat} {reasonAt : ExpressionId → Word}
    {child : Staging.Recursive.Scope} (selected : stages.Closure function child)
    (uninitialized : ∀ current id lowered,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        child.source body.toContext.context reasonAt current id lowered →
      ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) :
    OriginalConditions compiled code.policy code.compilation readFuel body.toContext.context child
      reasonAt (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      semanticFaults := {
  declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code body.toContext body.frame captured selected
  coercions := by
    simpa only [stages.source selected] using coercions
  sameLedger := body.valid.ledger
  runtimeLedger := body.valid.runtime
  unique := by
    rw [stages.source selected]
    exact body.unique
  wellFormed := wellFormed
  runtime := by
    rw [stages.source selected]
    exact (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
      body.frame body.toContext.extended).1
  covers := by
    rw [stages.evidence selected]
    exact body.valid.covers
  actualFunctionType := by
    rw [code.callables]
    rfl
  uninitialized := uninitialized }

/-- The same admission facts with faults restricted to actual body references. -/
theorem at_selected_scope_on
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context)
    (coercions : ∀ id node, Syntax function.source id →
      function.source.lookupExpression? id = some node → node.coercions = [])
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {roots : List NodeId}
    {readFuel : Nat} {reasonAt : ExpressionId → Word}
    {child : Staging.Recursive.Scope} (selected : stages.Closure function child)
    (uninitialized : ∀ current id lowered,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        child.source body.toContext.context reasonAt current id lowered →
      Reaches child.source roots (.expression id) →
      ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) :
    OriginalConditionsOn compiled code.policy code.compilation readFuel body.toContext.context child
      reasonAt (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      roots semanticFaults := {
  declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code body.toContext body.frame captured selected
  coercions := by
    simpa only [stages.source selected] using coercions
  sameLedger := body.valid.ledger
  runtimeLedger := body.valid.runtime
  unique := by
    rw [stages.source selected]
    exact body.unique
  wellFormed := wellFormed
  runtime := by
    rw [stages.source selected]
    exact (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
      body.frame body.toContext.extended).1
  covers := by
    rw [stages.evidence selected]
    exact body.valid.covers
  actualFunctionType := by
    rw [code.callables]
    rfl
  uninitialized := uninitialized }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaOriginalConditions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadLambdaMetadata
/-! Original source metadata for any number of ordinary local reads and lambda
occurrences. The recursive expression grammar excludes lambda formation, so
only actual read nodes contribute its policy exclusions. Statement structure
and the number or placement of reads are unrestricted here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadLambdaMetadata
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)

/-- One original occurrence is either an ordinary read with its exact metadata,
or a lambda whose formation uses a separate compiler certificate. -/
def NodeMetadata (node : ExpressionNode) : Prop :=
  (∃ name binder, node.form = .reference name (.local binder) ∧
    node.requirements = [] ∧ node.coercions = []) ∨
  (∃ parameters result body, node.form = .lambda parameters result body)

private theorem syntax_not_lambda {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId} (tree : Syntax source id)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) : False := by
  cases tree with
  | leaf product =>
    cases product with
    | literal other atomic =>
      have same := Option.some.inj (other.symm.trans found)
      subst node
      rw [form] at atomic
      cases atomic
    | read other shape | group other shape _ | pair other shape _ _ =>
      have same := Option.some.inj (other.symm.trans found)
      subst node
      rw [form] at shape
      cases shape
  | group other shape _ | tuple other shape _ | call other shape _ _ | constructor other shape _ _
  | unary other shape _ | binary other shape _ _ | conditional other shape _ _ _ =>
    have same := Option.some.inj (other.symm.trans found)
    subst node
    rw [form] at shape
    cases shape

private theorem read_of_syntax {source : TypedSource}
    (nodes : ∀ id node, source.lookupExpression? id = some node → NodeMetadata node)
    {id : ExpressionId} {node : ExpressionNode}
    (tree : Syntax source id) (found : source.lookupExpression? id = some node) :
    ∃ name binder, node.form = .reference name (.local binder) ∧
      node.requirements = [] ∧ node.coercions = [] := by
  rcases nodes id node found with read | ⟨parameters, result, body, form⟩
  · exact read
  · exact False.elim (syntax_not_lambda tree found form)

/-- The complete original occurrence metadata and authentic empty local
polymorphism catalog discharge the retained production policy exclusions. -/
theorem metadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : CallableIndexedNamedGeneration.Named) {source : TypedSource}
    (nodes : ∀ id node, source.lookupExpression? id = some node → NodeMetadata node)
    (locals : prepared.base.locals.bindings = []) : MetadataFor prepared named source where
  requirements := by
    intro id tree node found
    obtain ⟨_, _, _, requirements, _⟩ := read_of_syntax nodes tree found
    exact requirements
  coercions := by
    intro id tree node found
    obtain ⟨_, _, _, _, coercions⟩ := read_of_syntax nodes tree found
    exact coercions
  initializer := by intro id tree; simp only [locals, List.find?_nil]
  arguments := by
    intro id tree node found callee ids actual form
    obtain ⟨_, _, read, _, _⟩ := read_of_syntax nodes tree found
    rw [read] at form
    cases form
  localRead := by intro id tree node found name binder form; simp only [locals, List.any_nil]

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadLambdaMetadata
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRetainedSequenceConditions
/-! Retained compiler policies and reached body metadata supply the actual
sequence conditions. Source declarations and diagnostic attribution are static
facts; body admission comes from the original closure frame and parameter
extension. No execution or called-body law is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRetainedSequenceConditions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableLambdaBodyReachability
open CallableIndexedOwnedContextualLambdaProvenance (BodyView)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor MetadataOn retained_policy_for retained_policy_on)
open CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories (Choice Conditions)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {named : CallableIndexedNamedGeneration.Named} {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (code : Code compiled.indexed function scope administrative)
  (body : CallableIndexedLambdaStaticBodySupport.BodyWith
    (values := .initial compiled.compatible.checked) expressionSyntax certificates code
    (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)

/-- Every proof refers to the same original Code, full Source and entry context. -/
def conditions_on
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (bodyView : BodyView code)
    (original : MetadataFor compiled.indexed named function.source)
    (viewed : MetadataOn compiled.indexed named code.view
      (fun id => Reaches code.view (function.body.map NodeId.statement) (.expression id)))
    (treeSyntax : ∀ id, Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      Syntax code.view id)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      scope function.context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (uninitialized : ∀ current id lowered,
      CompatibleExpressionReads.LoweredRead compiled.indexed.fuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        function.source body.context code.reasonAt current id lowered →
      Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      ∀ location, semanticFaults (.uninitializedLocation location) (code.reasonAt id))
    (choice : Choice code (stages := stages)) : Conditions code body choice where
  readFuel := compiled.indexed.fuel
  changed := CallableIndexedLambdaBodyViewEdits.changed function.source code.view
  edited := by
    intro child selected
    rw [stages.source selected]
    exact CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  avoids := by
    intro child selected
    rw [stages.source selected]
    exact CallableIndexedLambdaBodyViewEdits.avoids bodyView
  sourceProfile := by
    intro child selected
    rw [stages.source selected]
    exact (retained_policy_for retained original _ _).on _
  viewProfile := retained_policy_on retained viewed _ _
  syntaxTree := by
    intro expression child used
    exact treeSyntax expression
      (CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.children_reached
        choice.packet.receipt.tree code.viewOfSource expression child used)
  original := by
    intro child selected
    exact CallableIndexedOwnedPreparedStagedLambdaOriginalConditions.at_selected_scope_on
      code body declarations (fun id node tree found => original.coercions id tree node found)
        wellFormed selected
      (by simpa only [stages.source selected, choice.reason] using uninitialized)

/-- Legacy global metadata and faults specialize to the actual body. -/
def conditions
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (bodyView : BodyView code)
    (original : MetadataFor compiled.indexed named function.source)
    (viewed : MetadataFor compiled.indexed named code.view)
    (treeSyntax : ∀ id, Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      Syntax code.view id)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      scope function.context)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (uninitialized : ∀ current id lowered,
      CompatibleExpressionReads.LoweredRead compiled.indexed.fuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        function.source body.context code.reasonAt current id lowered →
      ∀ location, semanticFaults (.uninitializedLocation location) (code.reasonAt id))
    (choice : Choice code (stages := stages)) : Conditions code body choice :=
  conditions_on code body retained bodyView original (viewed.on _)
    treeSyntax declarations wellFormed
    (fun current id lowered receipt _reached => uninitialized current id lowered receipt) choice

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRetainedSequenceConditions
end
