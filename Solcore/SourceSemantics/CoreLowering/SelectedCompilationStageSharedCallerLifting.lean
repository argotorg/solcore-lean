import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCallerHeadHandlers
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationSharedCallerBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageReadProductLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndexLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConstructors
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConditional
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftOperators
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBuiltin

/-! The exact finite compiler tree supplies ordinary-to-staged child lifting.
Each call continuation carries its actual receipt and path in that tree.
Closed staged preservation advances the physical state between ordered children;
its execution grade is independent of the ordinary lifting budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageSharedCallerLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls DirectCalls MethodCalls)
open CallableIndexedOwnedPreparedStagedCallerHeadHandlers
open CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority (IndexReady)
universe u
open CallableLambdaBodyReachability
open SelectedCompilationStageLiftBounds
open SelectedCompilationStageCallerHeadHandlers (Laws Direct Method Indirect)

open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

variable {readFuel : Nat}

section Generic

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (unique : NodeOccurrencesUnique invocation.source)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

variable
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (uninitialized : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))
  {faultRoot : ExpressionId}
  (uninitializedOn : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    Reaches invocation.source [.expression faultRoot] (.expression child) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))

local notation "bridge" => callerBridge

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include callerBridge receiver functions runtime unique
  observations extension semantic sameLedger runtimeLedger uninitializedOn in
private theorem preserves {budget rootScope rootId rootCode}
    (root : Certificate policy body compilation readFuel
      (.initial compiled.compatible.checked) invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId))
    (directHeads : Direct bridge model stages callFaults budget root)
    (methodHeads : Method bridge model stages callFaults budget root)
    (indexReady : IndexReady root)
    (indirectHeads : Indirect bridge model stages callFaults budget root) :
    ∀ size, PreservesAt bridge context model stages invocation
      (Point rootScope rootId rootCode) callFaults size := by
  intro size
  exact SelectedCompilationSharedCallerBounds.preserves_reached_with_functions
    bridge receiver functions runtime unique observations extension semantic
    sameLedger runtimeLedger uninitializedOn size root reached
    (fun compiler path callee application sequence childSize _within =>
      (directHeads compiler path callee application sequence).1 childSize)
    (fun compiler path sequence childSize _within =>
      (methodHeads compiler path sequence).1 childSize)
    indexReady
    (fun compiler path sequence childSize _within =>
      (indirectHeads compiler path sequence).1 childSize)
    size (Nat.le_refl _)

include callerBridge receiver functions runtime unique
  observations extension semantic sameLedger runtimeLedger uninitializedOn in
/-- Finite compiler structure supplies every ordered child lift. Call heads
are indexed by their actual compiler receipt and path in this same tree. -/
theorem laws (budget : Nat) {rootScope rootId rootCode}
    (root : Certificate policy body compilation readFuel
      (.initial compiled.compatible.checked) invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    Direct bridge model stages callFaults budget root →
    Method bridge model stages callFaults budget root → IndexReady root →
    Indirect bridge model stages callFaults budget root →
    Laws (context := context) (invocation := invocation) bridge model stages callFaults budget (Point rootScope rootId rootCode) := by
  revert reached
  induction root with
  | leaf tree =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations extension semantic
        sameLedger runtimeLedger uninitializedOn (.leaf tree) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      intro size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationStageReadProductLifting.lifts bridge functions extension
        sameLedger runtimeLedger unique size tree
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations extension semantic
        sameLedger runtimeLedger uninitializedOn (.unary metadata form found inputType outputType unaryProfile child) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression operand) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)]) := by
        apply Laws.entries
        intro child code member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        have pair := Prod.mk.inj member
        obtain ⟨rfl, rfl⟩ := pair
        exact ih reached0 (fun compiler inside => directHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => methodHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => indirectHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside))
      intro size within
      exact SelectedCompilationStageLiftOperators.unary bridge size
        (childCode := ⟨core.operandType, childCode⟩) metadata form unique found
        (children := RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)])
        ⟨rfl, by simp⟩ (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within))
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType scalar firstTree secondTree ihFirst ihSecond =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations extension semantic
        sameLedger runtimeLedger uninitializedOn (.index header keyFound form sourceType scalar firstTree secondTree) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression base) :=
        .expression reached header.metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression key) :=
        .expression reached header.metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope [(base, first), (key, second)]) := by
        apply Laws.entries
        intro child code member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          exact ihFirst reached0
            (fun compiler inside => directHeads compiler (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (scalar := scalar) (firstTree := firstTree) (secondTree := secondTree) inside)) (fun compiler inside => methodHeads compiler (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (scalar := scalar) (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (scalar := scalar) (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun compiler inside => indirectHeads compiler (.index_base
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (scalar := scalar) (firstTree := firstTree) (secondTree := secondTree) inside))

        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          exact ihSecond reached1
            (fun compiler inside => directHeads compiler (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (scalar := scalar) (firstTree := firstTree) (secondTree := secondTree) inside)) (fun compiler inside => methodHeads compiler (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (scalar := scalar) (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (scalar := scalar) (firstTree := firstTree) (secondTree := secondTree) inside))
            (fun compiler inside => indirectHeads compiler (.index_key
              (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType)
              (scalar := scalar) (firstTree := firstTree) (secondTree := secondTree) inside))

      intro size within
      exact SelectedCompilationStageIndexLifting.index bridge header keyFound form unique
        (children := RecursiveStageTupleMeaning.Entries rootScope [(base, first), (key, second)])
        ⟨rfl, by simp⟩ ⟨rfl, by simp⟩ size
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations extension semantic
        sameLedger runtimeLedger uninitializedOn (.binary metadata form leftFound rightFound leftType rightType outputType binaryProfile first second) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)]) := by
        apply Laws.entries
        intro child code member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          exact ihFirst reached0 (fun compiler inside => directHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => methodHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => indirectHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside))
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          exact ihSecond reached1 (fun compiler inside => directHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => methodHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => indirectHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside))
      intro size within
      exact SelectedCompilationStageLiftOperators.binary bridge size
        (leftCode := ⟨operatorMode.operandType operator, leftCode⟩)
        (rightCode := ⟨operatorMode.operandType operator, rightCode⟩) metadata form unique leftFound rightFound
        (children := RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)])
        ⟨rfl, by simp⟩ ⟨rfl, by simp⟩
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations extension semantic
        sameLedger runtimeLedger uninitializedOn (.conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression condition) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression thenId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached2 : Reaches invocation.source [.expression faultRoot] (.expression elseId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) := by
        apply Laws.entries
        intro child code member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1 | member2
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          exact ihCondition reached0 (fun compiler inside => directHeads compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => methodHeads compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => indirectHeads compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside))
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          exact ihThen reached1 (fun compiler inside => directHeads compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => methodHeads compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => indirectHeads compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside))
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          exact ihElse reached2 (fun compiler inside => directHeads compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => methodHeads compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => indirectHeads compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside))
      intro size within
      exact SelectedCompilationStageLiftConditional.conditional bridge functions size
        (conditionCode := ⟨.bool, conditionCode⟩) (thenCode := ⟨type, thenCode⟩)
        (elseCode := ⟨type, elseCode⟩) metadata form unique
        (children := RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)])
        rfl ⟨rfl, by simp⟩ ⟨rfl, by simp⟩ ⟨rfl, by simp⟩
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations extension semantic
        sameLedger runtimeLedger uninitializedOn (.group metadata form innerFound sourceType child) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (Point rootScope inner code) := by
        exact ih innerReached (fun compiler inside => directHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => methodHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => indirectHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside))
      intro size within current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact SelectedCompilationStageGroupLifting.group bridge unique size
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within))
        (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations extension semantic
        sameLedger runtimeLedger uninitializedOn (.tuple header sequence children) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) := by
        apply Laws.entries
        intro child code member
        exact ih child code member (childReached child code member)
          (fun compiler inside => directHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => methodHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => indirectHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside))
      intro size within
      exact SelectedCompilationStageLiftConstructors.tuple bridge size header.metadata header.form unique sequence
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations extension semantic
        sameLedger runtimeLedger uninitializedOn (.constructor header form admissible ranges count nodes sequence children) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) := by
        apply Laws.entries
        intro child code member
        exact ih child code member (childReached child code member)
          (fun compiler inside => directHeads compiler
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside)) (fun compiler inside => methodHeads compiler
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside)) (fun compiler inside => indirectHeads compiler
            (.constructor_child (header := header) (form := form) (admissible := admissible)
              (ranges := ranges) (count := count) (nodes := nodes)
              (sequence := sequence) (children := children) member inside))

      intro size within
      exact SelectedCompilationStageLiftConstructors.constructor bridge size header.metadata form unique
        (CompatibleSourceInstantiationClosure.constructor_valid admissible runtime.variables_closed ranges) sequence
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @builtin id callee ids function fuel lowered compiler calleeTyped sourceType nativeTypes sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations extension semantic
        sameLedger runtimeLedger uninitializedOn (.builtin compiler calleeTyped sourceType nativeTypes sequence children) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (by simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) := by
        apply Laws.entries
        intro child code member
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => indirectHeads nested
            (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside))

      intro size within
      exact SelectedCompilationStageLiftBuiltin.builtin bridge size
        compiler.metadata compiler.form unique sequence
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @direct id callee ids instantiation fuel lowered types compiler calleeTyped application sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations extension semantic
        sameLedger runtimeLedger uninitializedOn (.direct compiler calleeTyped application sequence children) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.metadata.found
        simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) := by
        apply Laws.entries
        intro child code member
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside))
          (fun nested inside => indirectHeads nested
            (.direct_child (outer := compiler) (calleeTyped := calleeTyped) (application := application)
              (sequence := sequence) (children := children) member inside))

      intro size within
      exact (directHeads compiler (.here calleeTyped application sequence children)
        calleeTyped application sequence).2 size within
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @method id fuel lowered types compiler sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations extension semantic
        sameLedger runtimeLedger uninitializedOn (.method compiler sequence children) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have childReached : ∀ child code, (child, code) ∈ compiler.arguments.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (compiler.argument_references (List.of_mem_zip member).1)
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope (compiler.arguments.zip compiler.codes)) := by
        apply Laws.entries
        intro child code member
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          (fun nested inside => methodHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
            (.method_child (outer := compiler) (sequence := sequence) (children := children) member inside))
          (fun nested inside => indirectHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))

      intro size within
      exact (methodHeads compiler (.here sequence children) sequence).2 size within
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads
      refine ⟨preserves bridge receiver functions runtime unique observations extension semantic
        sameLedger runtimeLedger uninitializedOn (.call compiler sequence children) reached
        directHeads methodHeads indexReady indirectHeads, ?_⟩
      have childReached : ∀ child code, (child, code) ∈ compiler.entries →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.found
        simp only [CallableIndirectCallCertificates.Receipt.entries, List.mem_cons] at member
        rcases member with same | member
        · have sameId : child = callee := congrArg Prod.fst same
          simp [compiler.originalForm, ExpressionForm.references, sameId]
        · simp [compiler.originalForm, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : Laws (context := context) (invocation := invocation) bridge model stages callFaults budget
          (RecursiveStageTupleMeaning.Entries rootScope compiler.entries) := by
        apply Laws.entries
        intro child code member
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => indirectHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside))
      intro size within
      exact (indirectHeads compiler (.here sequence children) sequence).2 size within
        (fun child smaller => childMeaning.2 child (Nat.le_trans (Nat.le_of_lt smaller) within)) childMeaning.1

include callerBridge receiver functions runtime unique
  observations extension semantic sameLedger runtimeLedger uninitializedOn in
/-- Projection consumed by the ordinary-trace induction. All child laws are
constructed by the finite certificate recursion above. -/
theorem lifts_reached_with_functions (budget : Nat) {rootScope rootId rootCode}
    (root : Certificate policy body compilation readFuel
      (.initial compiled.compatible.checked) invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId))
    (directHeads : Direct bridge model stages callFaults budget root)
    (methodHeads : Method bridge model stages callFaults budget root)
    (indexReady : IndexReady root)
    (indirectHeads : Indirect bridge model stages callFaults budget root)
    (size : Nat) (within : size ≤ budget) :
    LiftsAt bridge context model stages invocation (Point rootScope rootId rootCode) size := by
  exact (laws bridge receiver functions runtime unique observations extension semantic
    sameLedger runtimeLedger uninitializedOn budget root reached
    directHeads methodHeads indexReady indirectHeads).2 size within

end Generic
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageSharedCallerLifting
