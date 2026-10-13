import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCallerHeadHandlers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedGeneralCallHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorBounds

/-! One structural recursion supplies ordered child laws for every supported
expression. Genuine call receipts select internal head continuations, allowing
legacy and physical method callers to use their own reached state authority.
Source and native execution grades stay independent. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSharedRecursiveCallerBounds
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

open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

variable {readFuel : Nat}

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
  (namedTerminals : ∀ header, header ∈ headers → Body header)

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

local notation "bridge" => callerBridge.forgetSlots

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include callerBridge receiver profile wellFormed runtime covers unique
  observations extension semantic sameLedger runtimeLedger uninitializedOn in
/-- Every strict Source child is supplied by structural recursion at its actual
reached state. The numeric family supplies only the chosen called-body laws below the fixed
budget; all caller child laws are constructed here. -/
theorem preserves_reached
    (budget : Nat) {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    PreservesDirect bridge model stages callFaults budget root →
    PreservesMethod bridge model stages callFaults budget root → IndexReady root →
    PreservesIndirect bridge model stages callFaults budget root → ∀ size, size ≤ budget →
      PreservesAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  revert reached
  induction root with
  | leaf tree =>
      intro reached _directHeads _methodHeads _indexReady _indirectHeads size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.preserves_reached
        bridge functions extension sameLedger runtimeLedger callFaults uninitializedOn semantic
        unique wellFormed runtime covers size ⟨tree, reached⟩
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression operand) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        have pair := Prod.mk.inj member
        obtain ⟨rfl, rfl⟩ := pair
        intro node
        exact ih reached0 (fun compiler inside => directHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => methodHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => indirectHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .unary metadata form found inputType outputType unaryProfile (by exact ⟨rfl, by simp⟩)
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType scalar firstTree secondTree ihFirst ihSecond =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression base) :=
        .expression reached header.metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression key) :=
        .expression reached header.metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(base, first), (key, second)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
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
            childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
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
            childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      obtain ⟨port⟩ := indexReady header keyFound form sourceType scalar (.here firstTree secondTree)
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedIndexHeadBounds.preserves
        bridge functions callFaults unique wellFormed runtime covers header keyFound form sourceType scalar
        (children := RecursiveStageTupleMeaning.Entries current [(base, first), (key, second)])
        ⟨rfl, by simp⟩ ⟨rfl, by simp⟩ (port.missing receiver functions keyFound form)
        size childMeaning ⟨rfl, rfl, rfl⟩
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihFirst reached0 (fun compiler inside => directHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => methodHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => indirectHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond reached1 (fun compiler inside => directHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => methodHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => indirectHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .binary metadata form leftFound rightFound leftType rightType outputType binaryProfile (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression condition) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression thenId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached2 : Reaches invocation.source [.expression faultRoot] (.expression elseId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1 | member2
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
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
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
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
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          intro node
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
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (Point rootScope inner code) callFaults size := by
        intro childSize _smaller current child actual point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih innerReached (fun compiler inside => directHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => methodHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => indirectHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size
        childMeaning size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun compiler inside => directHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => methodHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => indirectHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_preserves
        bridge functions callFaults unique wellFormed runtime covers size childMeaning
        ⟨node, ids, types, codes, rfl, header, sequence⟩
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
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
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedConstructorHeadBounds.constructor_preserves
        bridge functions extension callFaults unique wellFormed runtime covers size childMeaning
        header form admissible ranges count nodes sequence ⟨rfl, rfl, rfl⟩
  | @builtin id callee ids function fuel lowered compiler calleeTyped sourceType nativeTypes sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (by simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
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
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds.preserves
        bridge functions observations callFaults unique wellFormed runtime covers
        (compiler.result ▸ compiler.metadata) compiler.form nativeTypes size sequence childMeaning
        ⟨rfl, rfl, compiler.output⟩
  | @direct id callee ids instantiation fuel lowered types compiler calleeTyped application sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.metadata.found
        simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
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
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      exact directHeads compiler (.here calleeTyped application sequence children)
        calleeTyped application sequence size within childMeaning point
  | @method id fuel lowered types compiler sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ compiler.arguments.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (compiler.argument_references (List.of_mem_zip member).1)
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (compiler.arguments.zip compiler.codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          (fun nested inside => methodHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
            (.method_child (outer := compiler) (sequence := sequence) (children := children) member inside))
          (fun nested inside => indirectHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      exact methodHeads compiler (.here sequence children) sequence size within childMeaning point
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ compiler.entries →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.found
        simp only [CallableIndirectCallCertificates.Receipt.entries, List.mem_cons] at member
        rcases member with same | member
        · have sameId : child = callee := congrArg Prod.fst same
          simp [compiler.originalForm, ExpressionForm.references, sameId]
        · simp [compiler.originalForm, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope compiler.entries) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => indirectHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      exact indirectHeads compiler (.here sequence children) sequence size within childMeaning point

include callerBridge receiver profile wellFormed runtime covers unique
  observations extension semantic sameLedger runtimeLedger uninitializedOn in
/-- Every child native grade comes from structural recursion. The returned
Source grade is independent, including exact nested stage failure scope. -/
theorem reflects_reached
    (budget : Nat)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    ReflectsDirect bridge model stages callFaults budget root →
    ReflectsMethod bridge model stages callFaults budget root → IndexReady root →
    ReflectsIndirect bridge model stages callFaults budget root → ∀ size, size ≤ budget →
      ReflectsAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  revert reached
  induction root with
  | leaf tree =>
      intro reached _directHeads _methodHeads _indexReady _indirectHeads size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.reflects_reached
        bridge functions extension sameLedger runtimeLedger callFaults uninitializedOn semantic
        unique wellFormed runtime covers size ⟨tree, reached⟩
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression operand) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        have pair := Prod.mk.inj member
        obtain ⟨rfl, rfl⟩ := pair
        intro node
        exact ih reached0 (fun compiler inside => directHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => methodHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => indirectHeads compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .unary metadata form found inputType outputType unaryProfile (by exact ⟨rfl, by simp⟩)
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType scalar firstTree secondTree ihFirst ihSecond =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression base) :=
        .expression reached header.metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression key) :=
        .expression reached header.metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(base, first), (key, second)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
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
            childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
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
            childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      obtain ⟨port⟩ := indexReady header keyFound form sourceType scalar (.here firstTree secondTree)
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedIndexHeadBounds.reflects
        bridge functions callFaults unique wellFormed runtime covers header keyFound form sourceType scalar
        (children := RecursiveStageTupleMeaning.Entries current [(base, first), (key, second)])
        ⟨rfl, by simp⟩ ⟨rfl, by simp⟩ (port.missing receiver functions keyFound form)
        size childMeaning ⟨rfl, rfl, rfl⟩
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihFirst reached0 (fun compiler inside => directHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => methodHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => indirectHeads compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond reached1 (fun compiler inside => directHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => methodHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => indirectHeads compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .binary metadata form leftFound rightFound leftType rightType outputType binaryProfile (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression condition) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression thenId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached2 : Reaches invocation.source [.expression faultRoot] (.expression elseId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1 | member2
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
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
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
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
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          intro node
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
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsAt bridge context model stages invocation
          (Point rootScope inner code) callFaults size := by
        intro current child actual point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih innerReached (fun compiler inside => directHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => methodHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => indirectHeads compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) size within ⟨rfl, rfl, rfl⟩
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size
        childMeaning (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults (size + 1) := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun compiler inside => directHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => methodHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => indirectHeads compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt_succ _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_reflects
        bridge functions callFaults unique wellFormed runtime covers size childMeaning
        ⟨node, ids, types, codes, rfl, header, sequence⟩
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
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
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedConstructorHeadBounds.constructor_reflects
        bridge functions extension callFaults unique wellFormed runtime covers size childMeaning
        header form admissible ranges count nodes sequence ⟨rfl, rfl, rfl⟩
  | @builtin id callee ids function fuel lowered compiler calleeTyped sourceType nativeTypes sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (by simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
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
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds.reflects
        bridge functions observations callFaults unique wellFormed runtime covers
        (compiler.result ▸ compiler.metadata) compiler.form nativeTypes size sequence childMeaning
        ⟨rfl, rfl, compiler.output⟩
  | @direct id callee ids instantiation fuel lowered types compiler calleeTyped application sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.metadata.found
        simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
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
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      exact directHeads compiler (.here calleeTyped application sequence children)
        calleeTyped application sequence size within childMeaning point
  | @method id fuel lowered types compiler sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ compiler.arguments.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (compiler.argument_references (List.of_mem_zip member).1)
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (compiler.arguments.zip compiler.codes)) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          (fun nested inside => methodHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
            (.method_child (outer := compiler) (sequence := sequence) (children := children) member inside))
          (fun nested inside => indirectHeads nested (.method_child (outer := compiler)
            (sequence := sequence) (children := children) member inside))
          childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      exact methodHeads compiler (.here sequence children) sequence size within childMeaning point
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro reached directHeads methodHeads indexReady indirectHeads size within
      have childReached : ∀ child code, (child, code) ∈ compiler.entries →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.found
        simp only [CallableIndirectCallCertificates.Receipt.entries, List.mem_cons] at member
        rcases member with same | member
        · have sameId : child = callee := congrArg Prod.fst same
          simp [compiler.originalForm, ExpressionForm.references, sameId]
        · simp [compiler.originalForm, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope compiler.entries) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => directHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => methodHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType indexScalar inside => indexReady indexed indexFound indexForm indexType indexScalar
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => indirectHeads nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      exact indirectHeads compiler (.here sequence children) sequence size within childMeaning point

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSharedRecursiveCallerBounds
