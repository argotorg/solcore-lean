import Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndexBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedIndexDiagnostics
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeOperatorBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedCallPorts
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeBuiltinValueBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectHeadBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeReadProductBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeGeneralizedReadProjection

/-! Structural recursion on the genuine named compiler tree fills every child
expression. Generalized reads and materialized application use their concrete
internal leaves; no whole-expression meaning is stored in a certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeExpressionBounds
open CallableIndexedNamedGeneration (Compilation)
open GeneralizedLocalInitializerCompilation (namedPolicy)
open CellAwareNamedExpressionCertificates (Tree)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : Compilation compiled.indexed named diagnostics code)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  (authority : CellAwareNamedCallPorts.Authority (compiled := compiled) named invocation)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functionModel identities)
  (functionTypes : FunctionRuntimeViews functionModel)
  (indices : CellAwareNamedIndexDiagnostics.Ready compiled invocation.source reasonAt)
  {readFaults : FunctionCalls.FaultRep}
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead compiled.indexed.fuel (.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, readFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, readFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private def Three (scope : SourceCoreLocalCell.Scope) (test yes no : ExpressionId)
    (a b c : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = test ∧ code = a) ∨ (child = yes ∧ code = b) ∨ (child = no ∧ code = c))

omit positive in
private theorem product_values : CallableIndexedOwnedPreparedStagedPairBounds.ProductValues (model := valueModel) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include positive bridge profile receiver stagePrepared authority wellFormed runtime covers unique
  extension sameLedger runtimeLedger faithful functionLeaves functionTypes indices uninitialized semantic in
theorem preserves_tree
    (builtins : (CallableIndexedBuiltinValues.model compiled.indexed profile).Includes functionModel)
    (generalized : ∀ size, CellAwareScopeGeneralizedReadBounds.PreservesAt bridge context valueModel named stages invocation callFaults size)
    (applications : ∀ size, CellAwareScopeApplicationBounds.PreservesAt bridge context valueModel named stages invocation callFaults size)
    {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree generation rootFuel invocation.source context reasonAt scope id lowered)
    (size : Nat) :
    PreservesAt bridge context valueModel named stages invocation (Point scope id lowered) callFaults size := by
  induction tree generalizing size with
  | plain receipt =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeReadProductBounds.preserves bridge functionModel extension
      GeneralizedLocalDescriptorHeap.ordinary_cells sameLedger runtimeLedger callFaults uninitialized semantic unique size receipt
  | builtin receipt =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeBuiltinValueBounds.preserves bridge functionModel profile builtins callFaults unique size ⟨receipt⟩
  | generalized receipt recipe =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeGeneralizedReadProjection.preserves bridge context valueModel named stages invocation callFaults
      (generalized size) ⟨reasonAt, receipt, ⟨recipe⟩⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    have children : PreservesBelow bridge context valueModel named stages invocation (Point scope inner lowered) callFaults size :=
      fun childSize _smaller => ih childSize
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeGroupBounds.group_preserves bridge unique size children size (Nat.le_refl _)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    have children : PreservesBelow bridge context valueModel named stages invocation
        (Two scope left right first second) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopePairBounds.pair_preserves bridge unique (product_values profile) size children size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType
      firstTree secondTree firstIH secondIH =>
    have children : PreservesBelow bridge context valueModel named stages invocation
        (Two scope base key first second) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact firstIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact secondIH childSize ⟨rfl, rfl, rfl⟩
    obtain ⟨port⟩ := indices header
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeIndexBounds.preserves bridge functionModel callFaults unique wellFormed runtime covers
      header keyFound form sourceType faithful functionLeaves functionTypes
      ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩
      (port.missing receiver functionModel keyFound form) size children ⟨rfl, rfl, rfl⟩
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    have children : PreservesBelow bridge context valueModel named stages invocation
        (Point scope operand ⟨core.operandType, childCode⟩) callFaults size :=
      fun childSize _smaller => ih childSize
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeOperatorBounds.preserves_at bridge functionModel size size (Nat.le_refl _)
      unique wellFormed runtime covers children
      (.unary metadata form childFound inputType outputType operatorProfile ⟨rfl, rfl, rfl⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH rightIH =>
    have children : PreservesBelow bridge context valueModel named stages invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeOperatorBounds.preserves_at bridge functionModel size size (Nat.le_refl _)
      unique wellFormed runtime covers children
      (.binary metadata form leftFound rightFound leftType rightType outputType operatorProfile
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    have children : PreservesBelow bridge context valueModel named stages invocation
        (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; exact testIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; exact yesIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; exact noIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeOperatorBounds.preserves_at bridge functionModel size size (Nat.le_refl _)
      unique wellFormed runtime covers children
      (.conditional metadata form testFound yesFound noFound testType yesType noType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩)
  | @call id callee ids metadata fuel lowered types compiler calleeReceipt calleeRecipe parent sequence children ih =>
    have childMeaning : PreservesBelow bridge context valueModel named stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) callFaults size := by
      intro childSize _smaller current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member childSize ⟨rfl, rfl, rfl⟩
    obtain ⟨port⟩ := CellAwareNamedCallPorts.port generation compiler authority rfl parent calleeReceipt
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeIndirectHeadBounds.preserves bridge receiver stagePrepared rfl profile
      wellFormed runtime covers unique (CellAwareNamedCallPorts.function_type generation)
      compiler port calleeReceipt calleeRecipe sequence size
      (fun childSize _smaller => generalized childSize) childMeaning
      (fun childSize _smaller => applications childSize) ⟨rfl, rfl, rfl⟩

include positive bridge profile receiver stagePrepared authority wellFormed runtime covers unique
  extension sameLedger runtimeLedger faithful functionLeaves functionTypes indices uninitialized semantic in
theorem reflects_tree
    (builtins : (CallableIndexedBuiltinValues.model compiled.indexed profile).Includes functionModel)
    (generalized : ∀ size, CellAwareScopeGeneralizedReadBounds.ReflectsAt bridge context valueModel named stages invocation callFaults size)
    (applications : ∀ size, CellAwareScopeApplicationBounds.ReflectsAt bridge context valueModel named stages invocation callFaults size)
    {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree generation rootFuel invocation.source context reasonAt scope id lowered)
    (size : Nat) :
    ReflectsAt bridge context valueModel named stages invocation (Point scope id lowered) callFaults size := by
  induction tree generalizing size with
  | plain receipt =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeReadProductBounds.reflects bridge functionModel extension
      GeneralizedLocalDescriptorHeap.ordinary_cells sameLedger runtimeLedger callFaults uninitialized semantic unique size receipt
  | builtin receipt =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeBuiltinValueBounds.reflects bridge functionModel profile builtins callFaults size ⟨receipt⟩
  | generalized receipt recipe =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeGeneralizedReadProjection.reflects bridge context valueModel named stages invocation callFaults
      (generalized size) ⟨reasonAt, receipt, ⟨recipe⟩⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeGroupBounds.group_reflects bridge unique size (ih size)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    have children : ReflectsBelow bridge context valueModel named stages invocation
        (Two scope left right first second) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopePairBounds.pair_reflects bridge unique (product_values profile) size children size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType
      firstTree secondTree firstIH secondIH =>
    have children : ReflectsBelow bridge context valueModel named stages invocation
        (Two scope base key first second) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact firstIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact secondIH childSize ⟨rfl, rfl, rfl⟩
    obtain ⟨port⟩ := indices header
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeIndexBounds.reflects bridge functionModel callFaults unique wellFormed runtime covers
      header keyFound form sourceType faithful functionLeaves functionTypes
      ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩
      (port.missing receiver functionModel keyFound form) size children ⟨rfl, rfl, rfl⟩
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    have children : ReflectsBelow bridge context valueModel named stages invocation
        (Point scope operand ⟨core.operandType, childCode⟩) callFaults size :=
      fun childSize _smaller => ih childSize
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeOperatorBounds.reflects_at bridge functionModel size size (Nat.le_refl _)
      unique wellFormed runtime covers children
      (.unary metadata form childFound inputType outputType operatorProfile ⟨rfl, rfl, rfl⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH rightIH =>
    have children : ReflectsBelow bridge context valueModel named stages invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeOperatorBounds.reflects_at bridge functionModel size size (Nat.le_refl _)
      unique wellFormed runtime covers children
      (.binary metadata form leftFound rightFound leftType rightType outputType operatorProfile
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    have children : ReflectsBelow bridge context valueModel named stages invocation
        (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) callFaults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; exact testIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; exact yesIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; exact noIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeOperatorBounds.reflects_at bridge functionModel size size (Nat.le_refl _)
      unique wellFormed runtime covers children
      (.conditional metadata form testFound yesFound noFound testType yesType noType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩)
  | @call id callee ids metadata fuel lowered types compiler calleeReceipt calleeRecipe parent sequence children ih =>
    have childMeaning : ReflectsBelow bridge context valueModel named stages invocation
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) callFaults size := by
      intro childSize _smaller current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member childSize ⟨rfl, rfl, rfl⟩
    obtain ⟨port⟩ := CellAwareNamedCallPorts.port generation compiler authority rfl parent calleeReceipt
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareScopeIndirectHeadBounds.reflects bridge receiver stagePrepared rfl profile
      wellFormed runtime covers unique (CellAwareNamedCallPorts.function_type generation)
      compiler port calleeReceipt calleeRecipe sequence size
      (fun childSize _smaller => generalized childSize) childMeaning
      (fun childSize _smaller => applications childSize) ⟨rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionTreeBounds
