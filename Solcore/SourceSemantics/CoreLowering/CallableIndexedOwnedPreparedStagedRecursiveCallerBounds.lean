import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteCallHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorBounds

/-! Structural recursion over the actual finite caller certificate constructs
all child expression meanings internally. Unary, binary and conditional roots
retain their recursive child certificates and reachable call authority. Grouping reflects at the same native
grade, and singleton tuples use the inclusive native child budget. Calls retain
the exact compiler entry vector and consume only static authority for calls
reachable in this root. Independent Source grades, fault scopes and reached
caller posts are retained. No child or called-body execution law is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds (FiniteFor)
open CallableIndexedOwnedPreparedStagedFiniteNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls)
universe u

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
      (CallableIndexedOwnedPreparedStagedFiniteCallHeadBounds.Port
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
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    Nonempty (FiniteFor (registry := completion.result.context.registry) (stages := stages) association))
  (namedTerminals : ∀ header, header ∈ headers → Nonempty (Terminal header))
  (namedCovers : ∀ header, header ∈ headers → ∀ {child : Staging.Recursive.Scope},
    stages.Closure header.function child → child.evidence.Covers header.context)

variable
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (uninitialized : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
  sameLedger runtimeLedger uninitialized in
/-- Every strict Source child is supplied by structural recursion at its actual
reached state. No semantic continuation appears in the public inputs. -/
theorem preserves {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) :
    CallsReady root → ∀ size,
      PreservesAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  induction root with
  | leaf tree =>
      intro _ports size current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.preserves
        bridge functions extension sameLedger runtimeLedger callFaults uninitialized semantic
        unique wellFormed runtime covers size tree
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        have pair := Prod.mk.inj member
        obtain ⟨rfl, rfl⟩ := pair
        intro node
        exact ih (fun compiler inside => ports compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .unary metadata form found inputType outputType unaryProfile (by exact ⟨rfl, by simp⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihFirst (fun compiler inside => ports compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond (fun compiler inside => ports compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .binary metadata form leftFound rightFound leftType rightType outputType binaryProfile (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1 | member2
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihCondition (fun compiler inside => ports compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihThen (fun compiler inside => ports compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihElse (fun compiler inside => ports compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (Point rootScope inner code) callFaults size := by
        intro childSize _smaller current child actual point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih (fun compiler inside => ports compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size
        childMeaning size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun compiler inside => ports compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_preserves
        bridge functions callFaults unique wellFormed runtime covers size childMeaning
        ⟨node, ids, types, codes, rfl, header, sequence⟩
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun compiler inside => ports compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedConstructorHeadBounds.constructor_preserves
        bridge functions extension callFaults unique wellFormed runtime covers size childMeaning
        header form admissible ranges count nodes sequence ⟨rfl, rfl, rfl⟩
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro ports size
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope compiler.entries) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun nested inside => ports nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      obtain ⟨port⟩ := ports compiler (.here sequence children)
      have calleeCertified : RecursiveStageTupleMeaning.Entries rootScope compiler.entries
          rootScope callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedFiniteCallHeadBounds.preserves
        bridge receiver stagePrepared rfl profile wellFormed runtime covers unique
        actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
        compiler port calleeCertified sequence size childMeaning ⟨rfl, rfl, rfl⟩

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
  sameLedger runtimeLedger uninitialized in
/-- Every child native grade comes from structural recursion. The returned
Source grade is independent, including exact nested stage failure scope. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) :
    CallsReady root → ∀ size,
      ReflectsAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  induction root with
  | leaf tree =>
      intro _ports size current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.reflects
        bridge functions extension sameLedger runtimeLedger callFaults uninitialized semantic
        unique wellFormed runtime covers size tree
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        have pair := Prod.mk.inj member
        obtain ⟨rfl, rfl⟩ := pair
        intro node
        exact ih (fun compiler inside => ports compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .unary metadata form found inputType outputType unaryProfile (by exact ⟨rfl, by simp⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihFirst (fun compiler inside => ports compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond (fun compiler inside => ports compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .binary metadata form leftFound rightFound leftType rightType outputType binaryProfile (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1 | member2
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihCondition (fun compiler inside => ports compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihThen (fun compiler inside => ports compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihElse (fun compiler inside => ports compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro ports size
      have childMeaning : ReflectsAt bridge context model stages invocation
          (Point rootScope inner code) callFaults size := by
        intro current child actual point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih (fun compiler inside => ports compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) size ⟨rfl, rfl, rfl⟩
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size
        childMeaning (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults (size + 1) := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun compiler inside => ports compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_reflects
        bridge functions callFaults unique wellFormed runtime covers size childMeaning
        ⟨node, ids, types, codes, rfl, header, sequence⟩
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun compiler inside => ports compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedConstructorHeadBounds.constructor_reflects
        bridge functions extension callFaults unique wellFormed runtime covers size childMeaning
        header form admissible ranges count nodes sequence ⟨rfl, rfl, rfl⟩
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro ports size
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope compiler.entries) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member
          (fun nested inside => ports nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) childSize ⟨rfl, rfl, rfl⟩
      obtain ⟨port⟩ := ports compiler (.here sequence children)
      have calleeCertified : RecursiveStageTupleMeaning.Entries rootScope compiler.entries
          rootScope callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedFiniteCallHeadBounds.reflects
        bridge receiver stagePrepared rfl profile wellFormed runtime covers unique
        actualFunctionType observations extension semantic closurePackets namedTerminals namedCovers
        stageEq compiler port calleeCertified sequence size childMeaning ⟨rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerBounds
