import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicUnaryAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.PreparedBranchingAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
import Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchAmbientLowering

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
      choice.invalidUnary = GenericAssignmentUnaryDiagnostics.unaryToken compilation.own.assignments

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
      choice.invalidUnary = GenericAssignmentUnaryDiagnostics.unaryToken compilation.own.assignments := by
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
    matchLedger := by rw [sameCompilation] }, rfl, rfl⟩
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
  obtain ⟨choice, token, unaryToken⟩ := choose_with_token code named compilation recipe sameCompilation shape child selected
  exact ⟨choice, diagnostics, namedCode, compilation, issued, token, unaryToken⟩

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
  obtain ⟨diagnostics, namedCode, compilation, actual, token, _unaryToken⟩ := issued
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
  obtain ⟨diagnostics, namedCode, compilation, actual, _operandToken, token⟩ := issued
  obtain ⟨first, prepared⟩ := CallableIndexedOwnedIssuedAssignmentRecipes.assignments_prepared selected compilation actual
  rw [token]
  rw [sourceEq] at origin
  exact GenericAssignmentUnaryDiagnostics.prepared_unary_included prepared
    (fun _ _ represented => CallableIndexedOwnedPublicUnaryAssignmentDiagnostics.compilation_unary
      compilation actual receiver represented) origin rawWord

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts
