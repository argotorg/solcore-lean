import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorBounds

/-! Structural recursion over the actual finite caller certificate constructs
all caller child expression meanings internally. Unary, binary and conditional
roots retain their recursive child certificates and reachable call authority. Grouping reflects at the same native
grade, and singleton tuples use the inclusive native child budget. Calls retain
the exact compiler entry vector and consume only static authority for calls
reachable in this root. Independent Source grades, fault scopes and reached
caller posts are retained. Chosen called-body strict laws are internal inputs;
the later numeric body family must construct them. No arbitrary-terminal law
is inferred. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor ReflectsBelowFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation (PreservesBelowFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls)
universe u
open CallableLambdaBodyReachability

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

variable {readFuel : Nat}

/-- Authority is required only for actual calls inside this exact root. Each
Port carries original prepared compiler metadata, with no execution field. -/
def CallsReady {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) : Prop :=
  ∀ {callFuel callScope callId actualCallee actualIds actualMetadata actualCode}
    (compiler : CallableIndirectCallCertificates.Receipt policy body callFuel compilation
      invocation.source callScope callId actualCallee actualIds actualMetadata reasonAt actualCode),
    Calls compiler root → Nonempty
      (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
        (compiled := compiled) (invocation := invocation) compiler)

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
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
  (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), TerminalFor association stages)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)

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

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closureTerminals namedTerminals
  sameLedger runtimeLedger uninitializedOn in
/-- Every strict Source child is supplied by structural recursion at its actual
reached state. The numeric family supplies only the chosen called-body laws below the fixed
budget; all caller child laws are constructed here. -/
theorem preserves_reached
    (budget : Nat)
    (closureChildren : ∀ size, size ≤ budget →
      ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      PreservesBelowFor (registry := completion.result.context.registry) (faults := callFaults)
        association (closureTerminals association) functions size)
    (namedChildren : ∀ size, size ≤ budget → ∀ header (member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
        header model stages child
        (namedTerminals header member).certificate callFaults size) {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    CallsReady root → ∀ size, size ≤ budget →
      PreservesAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  revert reached
  induction root with
  | leaf tree =>
      intro reached _ports size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.preserves_reached
        bridge functions extension sameLedger runtimeLedger callFaults uninitializedOn semantic
        unique wellFormed runtime covers size ⟨tree, reached⟩
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro reached ports size within
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
        exact ih reached0 (fun compiler inside => ports compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .unary metadata form found inputType outputType unaryProfile (by exact ⟨rfl, by simp⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro reached ports size within
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
          exact ihFirst reached0 (fun compiler inside => ports compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond reached1 (fun compiler inside => ports compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .binary metadata form leftFound rightFound leftType rightType outputType binaryProfile (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro reached ports size within
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
          exact ihCondition reached0 (fun compiler inside => ports compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihThen reached1 (fun compiler inside => ports compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihElse reached2 (fun compiler inside => ports compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro reached ports size within
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (Point rootScope inner code) callFaults size := by
        intro childSize _smaller current child actual point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih innerReached (fun compiler inside => ports compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size
        childMeaning size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro reached ports size within
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
          (fun compiler inside => ports compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_preserves
        bridge functions callFaults unique wellFormed runtime covers size childMeaning
        ⟨node, ids, types, codes, rfl, header, sequence⟩
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro reached ports size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun compiler inside => ports compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedConstructorHeadBounds.constructor_preserves
        bridge functions extension callFaults unique wellFormed runtime covers size childMeaning
        header form admissible ranges count nodes sequence ⟨rfl, rfl, rfl⟩
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro reached ports size within
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
          (fun nested inside => ports nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      obtain ⟨port⟩ := ports compiler (.here sequence children)
      have calleeCertified : RecursiveStageTupleMeaning.Entries rootScope compiler.entries
          rootScope callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.preserves
        bridge receiver stagePrepared rfl profile wellFormed runtime covers unique
        actualFunctionType observations closureTerminals namedTerminals
        compiler port calleeCertified sequence size childMeaning
        (closureChildren size within) (namedChildren size within) ⟨rfl, rfl, rfl⟩

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closureTerminals namedTerminals
  sameLedger runtimeLedger uninitializedOn in
/-- Every child native grade comes from structural recursion. The returned
Source grade is independent, including exact nested stage failure scope. -/
theorem reflects_reached (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (budget : Nat)
    (closureChildren : ∀ size, size ≤ budget →
      ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      ReflectsBelowFor (registry := completion.result.context.registry) (faults := callFaults)
        association (closureTerminals association) functions size)
    (namedChildren : ∀ size, size ≤ budget → ∀ header (member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
        header model stages child
        (namedTerminals header member).certificate callFaults size)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    CallsReady root → ∀ size, size ≤ budget →
      ReflectsAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  revert reached
  induction root with
  | leaf tree =>
      intro reached _ports size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.reflects_reached
        bridge functions extension sameLedger runtimeLedger callFaults uninitializedOn semantic
        unique wellFormed runtime covers size ⟨tree, reached⟩
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro reached ports size within
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
        exact ih reached0 (fun compiler inside => ports compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .unary metadata form found inputType outputType unaryProfile (by exact ⟨rfl, by simp⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro reached ports size within
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
          exact ihFirst reached0 (fun compiler inside => ports compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond reached1 (fun compiler inside => ports compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .binary metadata form leftFound rightFound leftType rightType outputType binaryProfile (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro reached ports size within
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
          exact ihCondition reached0 (fun compiler inside => ports compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihThen reached1 (fun compiler inside => ports compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihElse reached2 (fun compiler inside => ports compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro reached ports size within
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsAt bridge context model stages invocation
          (Point rootScope inner code) callFaults size := by
        intro current child actual point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih innerReached (fun compiler inside => ports compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) size within ⟨rfl, rfl, rfl⟩
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size
        childMeaning (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro reached ports size within
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
          (fun compiler inside => ports compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt_succ _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_reflects
        bridge functions callFaults unique wellFormed runtime covers size childMeaning
        ⟨node, ids, types, codes, rfl, header, sequence⟩
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro reached ports size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun compiler inside => ports compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedConstructorHeadBounds.constructor_reflects
        bridge functions extension callFaults unique wellFormed runtime covers size childMeaning
        header form admissible ranges count nodes sequence ⟨rfl, rfl, rfl⟩
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro reached ports size within
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
          (fun nested inside => ports nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      obtain ⟨port⟩ := ports compiler (.here sequence children)
      have calleeCertified : RecursiveStageTupleMeaning.Entries rootScope compiler.entries
          rootScope callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.reflects
        bridge receiver stagePrepared rfl profile wellFormed runtime covers unique
        actualFunctionType observations closureTerminals namedTerminals
        stageEq compiler port calleeCertified sequence size childMeaning
        (closureChildren size within) (namedChildren size within) ⟨rfl, rfl, rfl⟩

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closureTerminals namedTerminals
  sameLedger runtimeLedger uninitialized in
/-- Every strict Source child is supplied by structural recursion at its actual
reached state. The numeric family supplies only the chosen called-body laws below the fixed
budget; all caller child laws are constructed here. -/
theorem preserves
    (budget : Nat)
    (closureChildren : ∀ size, size ≤ budget →
      ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      PreservesBelowFor (registry := completion.result.context.registry) (faults := callFaults)
        association (closureTerminals association) functions size)
    (namedChildren : ∀ size, size ≤ budget → ∀ header (member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow (headers := headers) (keys := keys)
        header model stages child
        (namedTerminals header member).certificate callFaults size) {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) :
    CallsReady root → ∀ size, size ≤ budget →
      PreservesAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  exact preserves_reached (faultRoot := rootId) bridge receiver stagePrepared profile
    wellFormed runtime covers unique actualFunctionType observations extension semantic
    closureTerminals namedTerminals sameLedger runtimeLedger
    (fun current child code receipt _reached => uninitialized current child code receipt)
    budget closureChildren namedChildren root (.root (by simp))


include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closureTerminals namedTerminals
  sameLedger runtimeLedger uninitialized in
/-- Every child native grade comes from structural recursion. The returned
Source grade is independent, including exact nested stage failure scope. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (budget : Nat)
    (closureChildren : ∀ size, size ≤ budget →
      ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      ReflectsBelowFor (registry := completion.result.context.registry) (faults := callFaults)
        association (closureTerminals association) functions size)
    (namedChildren : ∀ size, size ≤ budget → ∀ header (member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow (headers := headers) (keys := keys)
        header model stages child
        (namedTerminals header member).certificate callFaults size)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) :
    CallsReady root → ∀ size, size ≤ budget →
      ReflectsAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  exact reflects_reached (faultRoot := rootId) bridge receiver stagePrepared profile
    wellFormed runtime covers unique actualFunctionType observations extension semantic
    closureTerminals namedTerminals sameLedger runtimeLedger
    (fun current child code receipt _reached => uninitialized current child code receipt)
    stageEq budget closureChildren namedChildren root (.root (by simp))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
