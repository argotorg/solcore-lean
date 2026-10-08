import Solcore.SourceSemantics.CoreLowering.IndexFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralTree
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedCompositions
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxyMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexTerminal

/-! Arbitrarily nested data/control/general-key index expressions use actual
runtime typing for every generated comparator capture. Recursive induction
closes all child meanings against the common ambient heap relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneral
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open CompatibleExpressionIndices CoreProof
open GenericExpressionMeaning (agree_prefix rename_prefix)
open DataPatternValues

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : Scope}

/-- Static leaf support indexes the existing tree and its exact children.
It contains only leaf membership, with no execution or heap law. -/
inductive Tree.LiteralSites (literals : GenericExpressionMeaning.Certificate) :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Tree fuel values source context solved reasonAt scope id lowered → Prop where
  | proxy {id lowered} (receipt : CompatibleExpressionProxies.Certificate values source scope id lowered)
      :
      LiteralSites literals (Tree.proxy (scope := scope) receipt)
  | fragment {id lowered}
      (child : CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope id lowered)
      (childSites : CompatibleExpressionRecursive.Tree.LiteralSites literals child) :
      LiteralSites literals (Tree.fragment (scope := scope) child)
  | group {id node inner innerNode lowered}
      (metadata : Metadata values.checked source id node lowered.type)
      (form : node.form = .group inner) (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Tree fuel values source context solved reasonAt scope inner lowered)
      (childSites : Tree.LiteralSites literals child) :
      LiteralSites literals (Tree.group (scope := scope) metadata form innerFound sourceType child)
  | pair {id node left right leftNode rightNode first second}
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode) (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (firstTree : Tree fuel values source context solved reasonAt scope left first)
      (secondTree : Tree fuel values source context solved reasonAt scope right second)
      (firstTreeSites : Tree.LiteralSites literals firstTree) (secondTreeSites : Tree.LiteralSites literals secondTree) :
      LiteralSites literals (Tree.pair (scope := scope) metadata form leftFound rightFound sourceType firstTree secondTree)
  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : Metadata values.checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : UnaryProfile operator operandType resultType core)
      (child : Tree fuel values source context solved reasonAt scope operand ⟨core.operandType, childCode⟩)
      (childSites : Tree.LiteralSites literals child) :
      LiteralSites literals (Tree.unary (scope := scope) metadata form found inputType outputType profile child)
  | binary {id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      (metadata : Metadata values.checked source id node (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = operandType)
      (outputType : node.type = resultType)
      (profile : BinaryProfile operator operandType resultType mode)
      (first : Tree fuel values source context solved reasonAt scope left ⟨mode.operandType operator, leftCode⟩)
      (second : Tree fuel values source context solved reasonAt scope right ⟨mode.operandType operator, rightCode⟩)
      (firstSites : Tree.LiteralSites literals first) (secondSites : Tree.LiteralSites literals second) :
      LiteralSites literals (Tree.binary (scope := scope) metadata form leftFound rightFound leftType rightType outputType profile first second)
  | conditional {id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      (metadata : Metadata values.checked source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (thenFound : source.lookupExpression? thenId = some thenNode)
      (elseFound : source.lookupExpression? elseId = some elseNode)
      (conditionType : conditionNode.type = .bool)
      (thenType : thenNode.type = node.type) (elseType : elseNode.type = node.type)
      (conditionTree : Tree fuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree fuel values source context solved reasonAt scope thenId ⟨type, thenCode⟩)
      (elseTree : Tree fuel values source context solved reasonAt scope elseId ⟨type, elseCode⟩)
      (conditionTreeSites : Tree.LiteralSites literals conditionTree) (thenTreeSites : Tree.LiteralSites literals thenTree) (elseTreeSites : Tree.LiteralSites literals elseTree) :
      LiteralSites literals (Tree.conditional (scope := scope) metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree)
  | constructor {id node instantiation ids tag header codes}
      (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
      (form : node.form = .constructor instantiation ids)
      (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
      (count : ids.length = instantiation.payloadTypes.length)
      (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
      (children : ∀ child code, (child, code) ∈ ids.zip codes →
        Tree fuel values source context solved reasonAt scope child code)
      (childrenSites : ∀ child code (member : (child, code) ∈ ids.zip codes),
        Tree.LiteralSites literals (children child code member)) :
      LiteralSites literals (Tree.constructor (scope := scope) receipt form valid count nodes children)
  | member {id node base baseNode name index identity branches result child}
      (metadata : Metadata values.checked source id node result)
      (baseMetadata : Metadata values.checked source base baseNode child.type)
      (form : node.form = .member base name index)
      (layout : CompatibleExpressionMembers.Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result)
      (childTree : Tree fuel values source context solved reasonAt scope base child)
      (childTreeSites : Tree.LiteralSites literals childTree) :
      LiteralSites literals (Tree.member (scope := scope) metadata baseMetadata form layout childTree)
  | index {id node base key baseNode keyNode layout comparison first second}
      (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (firstTree : Tree fuel values source context solved reasonAt scope base first)
      (secondTree : Tree fuel values source context solved reasonAt scope key second)
      (firstTreeSites : Tree.LiteralSites literals firstTree) (secondTreeSites : Tree.LiteralSites literals secondTree) :
      LiteralSites literals (Tree.index (scope := scope) header keyFound form sourceType firstTree secondTree)

/-- The exact old tree restricted to the supplied static leaf certificates. -/
def Tree.WithLiterals (literals : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun current id lowered => ∃ tree : Tree fuel values source context solved reasonAt current id lowered,
    tree.LiteralSites literals

/-- Ordinary literal membership supplies support for every original tree. -/
theorem Tree.literalSites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree fuel values source context solved reasonAt scope id lowered) :
    tree.LiteralSites (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code) := by
  induction tree with
  | proxy receipt => exact .proxy receipt
  | fragment child => exact .fragment child child.literalSites
  | group metadata form innerFound sourceType child childIH => exact .group metadata form innerFound sourceType child childIH
  | pair metadata form leftFound rightFound sourceType firstTree secondTree firstTreeIH secondTreeIH => exact .pair metadata form leftFound rightFound sourceType firstTree secondTree firstTreeIH secondTreeIH
  | unary metadata form found inputType outputType profile child childIH => exact .unary metadata form found inputType outputType profile child childIH
  | binary metadata form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH => exact .binary metadata form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH
  | conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeIH thenTreeIH elseTreeIH => exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeIH thenTreeIH elseTreeIH
  | constructor receipt form valid count nodes children childrenIH => exact .constructor receipt form valid count nodes children childrenIH
  | member metadata baseMetadata form layout childTree childTreeIH => exact .member metadata baseMetadata form layout childTree childTreeIH
  | index header keyFound form sourceType firstTree secondTree firstTreeIH secondTreeIH => exact .index header keyFound form sourceType firstTree secondTree firstTreeIH secondTreeIH

private def Entries (scope : Scope) (entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)) :
    GenericExpressionMeaning.Certificate := fun current id code => current = scope ∧ (id, code) ∈ entries

private def Children (scope : Scope) (ids : List ExpressionId) (codes : List SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate := fun current id code => current = scope ∧ (id, code) ∈ ids.zip codes

private theorem valuesRep {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world types natives sources payloads) :
    ValuesRep values.checked registry functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

private theorem missing_excludes {values : List Dynamic.Value} {index : Nat} {value : Dynamic.Value}
    (missing : Dynamic.ValueIndexMissing values index) (selected : Dynamic.ValueAt values index value) : False := by
  induction missing with
  | nil => cases selected
  | tail rest ih => cases selected with | tail child => exact ih child

private theorem at_functional {values : List Dynamic.Value} {index : Nat} {first second : Dynamic.Value}
    (left : Dynamic.ValueAt values index first) (right : Dynamic.ValueAt values index second) : first = second := by
  induction left with
  | head => cases right; rfl
  | tail _ ih => cases right with | tail rest => exact ih rest

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {literals : GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension unique in
theorem preserves_with_literals_and_post
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (constructorJoins : ScalarConstructorFaultPostContracts.Joins post listPost values program context evidence source)
    (memberJoins : ScalarMemberFaultPostContracts.Joins post values program context evidence source)
    (indexJoins : IndexFaultPostContracts.IndexJoins post values program context evidence source)
    (literalMeaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults post)
    (readMeaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults post)
    (proxyMeaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionProxies.Certificate values source) faults post)
    (terminalProvider : IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt (fun _ => True) faults post) :
    ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults post := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | proxy receipt => exact proxyMeaning receipt
  | fragment child childSites =>
    exact ReachedLoweredReadOutcomePorts.typed_preserves_of_unrestricted
      (CompatibleExpressionRecursive.preserves_with_literals_and_post functions extension program evidence unique sequenceJoins ordinaryJoins constructorJoins memberJoins literalMeaning readMeaning) ⟨child, childSites⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(inner, lowered)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩
      · exact ih
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves_with_post functions program evidence unique sequenceJoins ordinaryJoins meaning (.group metadata form innerFound sourceType (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree firstTreeSites secondTreeSites leftIH rightIH =>
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(left, first), (right, second)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves_with_post functions program evidence unique sequenceJoins ordinaryJoins meaning (.pair metadata form leftFound rightFound sourceType (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @unary id node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child childSites ih =>
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(operand, ⟨core.operandType, childCode⟩)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩
      · exact ih
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves_with_post functions program evidence unique sequenceJoins ordinaryJoins meaning (.unary (childCode := childCode) metadata form childFound inputType outputType profile (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile firstTree secondTree firstSites secondSites leftIH rightIH =>
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(left, ⟨mode.operandType operator, leftCode⟩), (right, ⟨mode.operandType operator, rightCode⟩)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves_with_post functions program evidence unique sequenceJoins ordinaryJoins meaning (.binary (leftCode := leftCode) (rightCode := rightCode) metadata form leftFound rightFound leftType rightType outputType profile (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeSites thenTreeSites elseTreeSites conditionIH thenIH elseIH =>
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact conditionIH
      · exact thenIH
      · exact elseIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves_with_post functions program evidence unique sequenceJoins ordinaryJoins meaning (.conditional (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) metadata form conditionFound thenFound elseFound conditionType thenType elseType (⟨rfl, by simp⟩) (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children childrenSites ih =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Children scope ids codes) faults post := by
      intro current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member
    have sequence := sequence_of_nodes (scope := scope) (certificate := Children scope ids codes) count nodes (fun id code member => (⟨rfl, member⟩ : Children scope ids codes scope id code))
    obtain ⟨sourceOutcome, sourceTrace, packed⟩ := constructor_inv receipt.metadata form unique valid trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      TypedDataExpressionSequence.preserves_with_post sequence sequenceJoins meaning environments heaps locals agrees actualTyped sourceTrace
    cases represented with
    | @values sources payloadValues payloads =>
      cases packed
      have projected := receipt.metadata.projected
      rw [receipt.sourceType] at projected
      refine ⟨.inRight .word (.constructed tag (.pair (.word header) (packValues payloadValues))), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
      · rw [CompatibleExpressionConstructors.construct_rename]; exact CompatibleExpressionConstructors.construct_success tag header evaluated
      · rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
          receipt.selected projected receipt.registered (valuesRep payloads))
    | fault matched =>
      cases packed
      cases sourceTrace with
      | fault failed =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [CompatibleExpressionConstructors.construct_rename]; exact CompatibleExpressionConstructors.construct_failure tag header evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          ScalarConstructorFaultPostContracts.arguments_fault_outcome constructorJoins
            receipt form valid count nodes failed retained⟩

  | @member id node base baseNode name index identity branches result child metadata baseMetadata form layout childTree childTreeSites ih =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have raw := member_inv metadata form unique trace
    cases raw with
    | value childTrace selected =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, sourceChild, native, shape, sourceAt, related, completed⟩ := member_success layout payload evaluated
        cases shape
        have same := at_functional sourceAt selected
        subst sourceChild
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact completed,
          .value related, finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
    | failure childTrace =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact LanguageResult.bind_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          ScalarMemberFaultPostContracts.base_fault_outcome memberJoins metadata baseMetadata form layout childTrace retained⟩
    | shape childTrace invalid =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, _⟩ := member_success layout payload evaluated
        subst_vars
        exact False.elim (invalid .intro)
    | position childTrace missing =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, selected, _⟩ := member_success layout payload evaluated
        cases shape
        exact False.elim (missing_excludes missing selected)

  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree firstTreeSites secondTreeSites firstIH secondIH =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rcases (index_inv header.metadata form unique trace).split with ⟨reason, rfl, failed⟩ | ⟨baseSource, middle, baseTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, metadata,
          indexJoins.base_outcome header keyFound form sourceType failed retained⟩
        rw [index_rename comparison header.registered header.comparisonType]
        exact LanguageResult.bind_failure _ evaluated
    · obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped (.value baseTrace)
      cases represented with
      | @value _ baseValue baseRep =>
        have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
        rcases tail with ⟨reason, rfl, failed⟩ | ⟨keySource, keyTrace, terminal⟩
        · obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (.fault failed)
          cases represented with
          | fault matched =>
            refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
              indexJoins.key_outcome header keyFound form sourceType baseTrace failed retained⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            exact LanguageResult.bind_success _ firstEval (LanguageResult.bind_failure _ secondEval)
        · obtain ⟨value, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, _keyPost⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (.value keyTrace)
          cases represented with
          | @value _ keyValue keyRep =>
            obtain ⟨actualOutcome, result, finalStore, finalWorld, terminal', related, lookup, finalHeaps, worlds, frame, uniqueResult, _parentTrace, terminalPost⟩ :=
              terminalProvider header sourceType trivial (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace keyTrace
            have same := uniqueResult outcome terminal
            subst actualOutcome
            refine ⟨result, finalStore, keyMap, finalWorld, ?_, related, finalHeaps,
              firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
              (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, terminalPost⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            apply SourceCoreCompatibleDataExpressions.index_completed layout (reasonAt id) firstEval secondEval
            simpa only [CompatibleMapping.Transport.expression_weaken] using lookup


include extension faithful functionLeaves functionTypes unique uninitialized missing in
theorem preserves_with_literals
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.TypedPreserves.forget
    (preserves_with_literals_and_post (functions := functions) (extension := extension) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence) (unique := unique)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source)
      (ExpressionFailurePostContracts.Preserves.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Preserves.of_trivial
        (certificate := CompatibleExpressionReads.LoweredRead fuel values source context reasonAt)
        (by
          intro scope id lowered receipt
          exact CompatibleExpressionReads.loweredRead_preserves functions extension program context evidence reasonAt uninitialized unique receipt))
      (ExpressionFailurePostContracts.TypedPreserves.of_trivial
        (CompatibleExpressionProxies.preserves functions extension program context evidence unique faults))
      (IndexFaultPostContracts.trivial_general_terminal functions registry program context evidence reasonAt
        faithful functionLeaves functionTypes missing))

include extension faithful functionLeaves functionTypes valid unique uninitialized missing in
theorem preserves :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact preserves_with_literals functions extension faithful functionLeaves functionTypes program evidence unique uninitialized missing
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults) ⟨tree, tree.literalSites⟩

include extension in
theorem reflects_with_literals_and_post
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (constructorJoins : ScalarConstructorFaultPostContracts.Joins post listPost values program context evidence source)
    (memberJoins : ScalarMemberFaultPostContracts.Joins post values program context evidence source)
    (indexJoins : IndexFaultPostContracts.IndexJoins post values program context evidence source)
    (literalMeaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults post)
    (readMeaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults post)
    (proxyMeaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionProxies.Certificate values source) faults post)
    (terminalProvider : IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt (fun _ => True) faults post) :
    ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults post := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | proxy receipt => exact proxyMeaning receipt
  | fragment child childSites =>
    exact ReachedLoweredReadOutcomePorts.typed_reflects_of_unrestricted
      (CompatibleExpressionRecursive.reflects_with_literals_and_post functions extension program evidence sequenceJoins ordinaryJoins constructorJoins memberJoins literalMeaning readMeaning) ⟨child, childSites⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(inner, lowered)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩
      · exact ih
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects_with_post functions program evidence sequenceJoins ordinaryJoins meaning (.group metadata form innerFound sourceType (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree firstTreeSites secondTreeSites leftIH rightIH =>
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(left, first), (right, second)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects_with_post functions program evidence sequenceJoins ordinaryJoins meaning (.pair metadata form leftFound rightFound sourceType (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @unary id node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child childSites ih =>
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(operand, ⟨core.operandType, childCode⟩)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩
      · exact ih
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects_with_post functions program evidence sequenceJoins ordinaryJoins meaning (.unary (childCode := childCode) metadata form childFound inputType outputType profile (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile firstTree secondTree firstSites secondSites leftIH rightIH =>
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(left, ⟨mode.operandType operator, leftCode⟩), (right, ⟨mode.operandType operator, rightCode⟩)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects_with_post functions program evidence sequenceJoins ordinaryJoins meaning (.binary (leftCode := leftCode) (rightCode := rightCode) metadata form leftFound rightFound leftType rightType outputType profile (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeSites thenTreeSites elseTreeSites conditionIH thenIH elseIH =>
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact conditionIH
      · exact thenIH
      · exact elseIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects_with_post functions program evidence sequenceJoins ordinaryJoins meaning (.conditional (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) metadata form conditionFound thenFound elseFound conditionType thenType elseType (⟨rfl, by simp⟩) (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children childrenSites ih =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Children scope ids codes) faults post := by
      intro current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member
    have sequence := sequence_of_nodes (scope := scope) (certificate := Children scope ids codes) count nodes (fun id code member => (⟨rfl, member⟩ : Children scope ids codes scope id code))
    rw [CompatibleExpressionConstructors.construct_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        TypedDataExpressionSequence.reflects_with_post sequence sequenceJoins meaning environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_failure tag header childEvaluation)
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid (.fault failed) (.fault _),
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
            ScalarConstructorFaultPostContracts.arguments_fault_outcome constructorJoins
              receipt form valid count nodes failed retained⟩
    | caseRight childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        TypedDataExpressionSequence.reflects_with_post sequence sequenceJoins meaning environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | values payloads =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_success tag header childEvaluation)
        have projected := receipt.metadata.projected
        rw [receipt.sourceType] at projected
        refine ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace (.values _),
          ?_, finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
        rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
          receipt.selected projected receipt.registered (valuesRep payloads))

  | @member id node base baseNode name index identity branches result child metadata baseMetadata form layout childTree childTreeSites ih =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [member_rename layout] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure result baseEvaluation (body := .matchData identity (LanguageResult.resultType result) (.var 0) branches)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.failure failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata,
            ScalarMemberFaultPostContracts.base_fault_outcome memberJoins metadata baseMetadata form layout failed retained⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, selected, native, shape, sourceAt, related, expected⟩ := member_success layout payload baseEvaluation
        subst_vars
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.value childTrace sourceAt), .value related,
            finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩

  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree firstTreeSites secondTreeSites firstIH secondIH =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure layout.valueType baseEvaluation (body :=
          LanguageResult.bind layout.valueType ((second.expression.rename ξ).weakenAt 0)
            (SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.baseFailure failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
            indexJoins.base_outcome header keyFound form sourceType failed retained⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨outcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | @value baseSource baseValue baseRep =>
        cases trace with
        | value baseTrace =>
          have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
          cases branch with
          | caseLeft keyEvaluation ignored =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment keyEvaluation
            cases represented with
            | fault matched =>
              rw [rename_prefix] at keyEvaluation
              have expected := LanguageResult.bind_success layout.valueType baseEvaluation
                (LanguageResult.bind_failure layout.valueType keyEvaluation (body :=
                  SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              cases trace with
              | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.keyFailure baseTrace failed),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                  indexJoins.key_outcome header keyFound form sourceType baseTrace failed retained⟩
          | caseRight keyEvaluation lookupEvaluation =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, keyMap, keyWorld, trace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, _keyPost⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment keyEvaluation
            cases represented with
            | @value keySource keyValue keyRep =>
              cases trace with
              | value keyTrace =>
                obtain ⟨outcome, result, endStore, finalWorld, terminal, related, lookup, finalHeaps, worlds, frame, uniqueResult, _parentTrace, terminalPost⟩ :=
                  terminalProvider header sourceType trivial (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                    (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace keyTrace
                rw [rename_prefix] at keyEvaluation
                have expected := SourceCoreCompatibleDataExpressions.index_completed (comparison := comparison.expression) layout (reasonAt id) baseEvaluation keyEvaluation
                  (by simpa only [CompatibleMapping.Transport.expression_weaken] using lookup)
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
                exact ⟨outcome, after, keyMap, finalWorld, index_intro header.metadata form (terminal.trace baseTrace keyTrace),
                  related, finalHeaps, firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
                  (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, terminalPost⟩


include extension faithful functionLeaves functionTypes uninitialized missing in
theorem reflects_with_literals
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.TypedReflects.forget
    (reflects_with_literals_and_post (functions := functions) (extension := extension) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source)
      (ExpressionFailurePostContracts.Reflects.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Reflects.of_trivial
        (certificate := CompatibleExpressionReads.LoweredRead fuel values source context reasonAt)
        (by
          intro scope id lowered receipt
          exact CompatibleExpressionReads.loweredRead_reflects functions extension program context evidence reasonAt uninitialized receipt))
      (ExpressionFailurePostContracts.TypedReflects.of_trivial
        (CompatibleExpressionProxies.reflects functions extension program context evidence faults))
      (IndexFaultPostContracts.trivial_general_terminal functions registry program context evidence reasonAt
        faithful functionLeaves functionTypes missing))

include extension faithful functionLeaves functionTypes valid uninitialized missing in
theorem reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact reflects_with_literals functions extension faithful functionLeaves functionTypes program evidence uninitialized missing
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults) ⟨tree, tree.literalSites⟩

/- Preserve generated ordinary API names by aliasing the sole shared main. -/
abbrev preserves._simp_1_1 := @preserves_with_literals_and_post._simp_1_3
abbrev preserves._simp_1_2 := @preserves_with_literals_and_post._simp_1_4
abbrev reflects._simp_1_1 := @reflects_with_literals_and_post._simp_1_3
abbrev reflects._simp_1_2 := @reflects_with_literals_and_post._simp_1_4

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneral
