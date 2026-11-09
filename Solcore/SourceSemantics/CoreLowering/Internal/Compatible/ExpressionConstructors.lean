import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.PrimitiveExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionContextualConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionPrimitives

/-!
# Compatible expressions: constructors and members

Meaning and extraction of constructors, member layouts and trees, and proxy meaning.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ScalarConstructorFaultPostContracts
/-! Constructor fault transport retains the actual header and argument row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ScalarConstructorFaultPostContracts
open Core Frontend SourceInference CompatibleExpressionConstructors ExpressionFailurePostContracts

structure Joins (post : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (values : ValuesContext) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) : Prop where
  arguments : ∀ {id node instantiation ids tag header codes environment before reason after token mapping world store},
    Header values source id node instantiation tag header codes →
    node.form = .constructor instantiation ids →
    SourceSemantics.DataConstructorInstantiation.Valid context instantiation →
    ids.length = instantiation.payloadTypes.length →
    Nodes source ids instantiation.payloadTypes codes →
    Dynamic.ExpressionsFault program context evidence source environment before ids reason after →
    listPost program context evidence source environment before ids reason after token mapping world store →
    post program context evidence source environment before id reason after token mapping world store

theorem trivial_joins (values : ValuesContext) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    Joins TrivialExpressionPost TrivialExpressionsPost values program context evidence source where
  arguments := by intros; trivial

theorem arguments_fault_outcome {post : ExpressionFaultPost} {listPost : ExpressionsFaultPost}
    {values : ValuesContext} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    (joins : Joins post listPost values program context evidence source)
    {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation}
    {ids : List ExpressionId} {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {token : Word} {childType parentType : Ty} {mapping : GeneralHeap.LocationMap}
    {world : StoreTyping} {store : Store}
    (receipt : Header values source id node instantiation tag header codes)
    (form : node.form = .constructor instantiation ids)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    (count : ids.length = instantiation.payloadTypes.length)
    (nodes : Nodes source ids instantiation.payloadTypes codes)
    (failed : Dynamic.ExpressionsFault program context evidence source environment before ids reason after)
    (retained : ListOutcomePost listPost program context evidence source environment before ids childType
      (.error reason) after (.inLeft childType (.word token)) mapping world store) :
    OutcomePost post program context evidence source environment before id parentType
      (.fault reason) after (.inLeft parentType (.word token)) mapping world store :=
  ⟨token, rfl, joins.arguments receipt form valid count nodes failed (ListOutcomePost.fault retained)⟩

end Solcore.SourceSemantics.CoreLowering.ScalarConstructorFaultPostContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorMeaning
/-! Every constructor argument's execution is derived by structural induction.
The compatible raw metadata ID, actual temporary slots, shared heap and
administrative frame are retained in both finite directions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload DataPatternValues

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : Scope}

/-- Static leaf support indexes the existing tree and its exact children.
It contains only leaf membership, with no execution or heap law. -/
inductive Tree.LiteralSites (literals : GenericExpressionMeaning.Certificate) :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Tree fuel values source context solved reasonAt scope id lowered → Prop where
  | fragment {id lowered}
      (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered)
      (treeSites : CompatibleExpressionConditionals.Tree.LiteralSites literals tree) :
      LiteralSites literals (Tree.fragment (scope := scope) tree)
  | constructor {id node instantiation ids tag header codes}
      (receipt : Header values source id node instantiation tag header codes)
      (form : node.form = .constructor instantiation ids)
      (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
      (count : ids.length = instantiation.payloadTypes.length)
      (nodes : Nodes source ids instantiation.payloadTypes codes)
      (children : ∀ child code, (child, code) ∈ ids.zip codes →
        Tree fuel values source context solved reasonAt scope child code)
      (childrenSites : ∀ child code (member : (child, code) ∈ ids.zip codes),
        Tree.LiteralSites literals (children child code member)) :
      LiteralSites literals (Tree.constructor (scope := scope) receipt form valid count nodes children)

/-- The exact old tree restricted to the supplied static leaf certificates. -/
def Tree.WithLiterals (literals : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun current id lowered => ∃ tree : Tree fuel values source context solved reasonAt current id lowered,
    tree.LiteralSites literals

/-- Ordinary literal membership supplies support for every original tree. -/
theorem Tree.literalSites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree fuel values source context solved reasonAt scope id lowered) :
    tree.LiteralSites (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code) := by
  induction tree with
  | fragment tree => exact .fragment tree tree.literalSites
  | constructor receipt form valid count nodes children childrenIH => exact .constructor receipt form valid count nodes children childrenIH

private def Children (scope : Scope) (ids : List ExpressionId) (codes : List SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate := fun current id code => current = scope ∧ (id, code) ∈ ids.zip codes

theorem construct_rename (tag : ConstructorId) (header : Word) (arguments : Expr) (ξ : Renaming) :
    (SourceCoreCompatibleDataExpressions.construct tag header arguments).rename ξ =
      SourceCoreCompatibleDataExpressions.construct tag header (arguments.rename ξ) := by
  simp [SourceCoreCompatibleDataExpressions.construct, LanguageResult.bind, LanguageResult.success, Expr.rename, Renaming.lift]

theorem construct_success {environment : Environment} {before after : Store}
    (tag : ConstructorId) (header : Word) {arguments : Expr} {value : Value}
    (evaluated : Evaluates environment before arguments (.inRight .word value) after) :
    Evaluates environment before (SourceCoreCompatibleDataExpressions.construct tag header arguments)
      (.inRight .word (.constructed tag (.pair (.word header) value))) after :=
  LanguageResult.bind_success _ evaluated (.inRight (.construct (.pair .word (.var rfl))))

theorem construct_failure {environment : Environment} {before after : Store}
    (tag : ConstructorId) (header : Word) {arguments : Expr} {type : Ty} {reason : Word}
    (evaluated : Evaluates environment before arguments (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreCompatibleDataExpressions.construct tag header arguments)
      (.inLeft (.namedData tag.owner) (.word reason)) after :=
  LanguageResult.bind_failure _ evaluated

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

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {literals : GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include extension unique in
theorem preserves_with_literals_and_post [FunctionCalls.FaultTokens faults]
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (constructorJoins : ScalarConstructorFaultPostContracts.Joins post listPost values program context evidence source)
    (literalMeaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults post)
    (readMeaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults post) :
    ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults post := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | fragment child treeSites =>
    exact CompatibleExpressionConditionals.preserves_with_literals_and_post (fuel := fuel) (reasonAt := reasonAt) functions program evidence unique sequenceJoins ordinaryJoins literalMeaning readMeaning ⟨child, treeSites⟩
  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children childrenSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after environments heaps locals agrees trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have meaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Children scope ids codes) faults post := by
      intro current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member
    have sequence := sequence_of_nodes (scope := scope) (certificate := Children scope ids codes) count nodes (fun id code member => (⟨rfl, member⟩ : Children scope ids codes scope id code))
    obtain ⟨sourceOutcome, sourceTrace, packed⟩ := constructor_inv receipt.metadata form unique valid trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      sequence.preserves_with_post sequenceJoins meaning environments heaps locals agrees sourceTrace
    cases represented with
    | @values sources payloadValues payloads =>
      cases packed
      have projected := receipt.metadata.projected
      rw [receipt.sourceType] at projected
      refine ⟨.inRight .word (.constructed tag (.pair (.word header) (packValues payloadValues))), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
      · rw [construct_rename]; exact construct_success tag header evaluated
      · rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
          receipt.selected projected receipt.registered (valuesRep payloads))
    | fault matched =>
      cases packed
      cases sourceTrace with
      | fault failed =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [construct_rename]; exact construct_failure tag header evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          ScalarConstructorFaultPostContracts.arguments_fault_outcome constructorJoins
            receipt form valid count nodes failed retained⟩

include extension in
theorem reflects_with_literals_and_post [FunctionCalls.FaultTokens faults]
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (constructorJoins : ScalarConstructorFaultPostContracts.Joins post listPost values program context evidence source)
    (literalMeaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults post)
    (readMeaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults post) :
    ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults post := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | fragment child treeSites =>
    exact CompatibleExpressionConditionals.reflects_with_literals_and_post (fuel := fuel) (reasonAt := reasonAt) functions program evidence sequenceJoins ordinaryJoins literalMeaning readMeaning ⟨child, treeSites⟩
  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children childrenSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore environments heaps locals agrees evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have meaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Children scope ids codes) faults post := by
      intro current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member
    have sequence := sequence_of_nodes (scope := scope) (certificate := Children scope ids codes) count nodes (fun id code member => (⟨rfl, member⟩ : Children scope ids codes scope id code))
    rw [construct_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        sequence.reflects_with_post sequenceJoins meaning environments heaps locals agrees childEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (construct_failure tag header childEvaluation)
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid (.fault failed) (.fault _),
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
            ScalarConstructorFaultPostContracts.arguments_fault_outcome constructorJoins
              receipt form valid count nodes failed retained⟩
    | caseRight childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        sequence.reflects_with_post sequenceJoins meaning environments heaps locals agrees childEvaluation
      cases represented with
      | values payloads =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (construct_success tag header childEvaluation)
        have projected := receipt.metadata.projected
        rw [receipt.sourceType] at projected
        refine ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace (.values _),
          ?_, finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
        rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
          receipt.selected projected receipt.registered (valuesRep payloads))

include extension unique uninitialized in
theorem preserves_with_literals [FunctionCalls.FaultTokens faults]
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.Preserves.forget
    (preserves_with_literals_and_post (functions := functions) (extension := extension) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence) (unique := unique)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ExpressionFailurePostContracts.Preserves.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Preserves.of_trivial
        (certificate := CompatibleExpressionReads.LoweredRead fuel values source context reasonAt)
        (by
          intro scope id lowered receipt
          exact CompatibleExpressionReads.loweredRead_preserves functions extension program context evidence reasonAt uninitialized unique receipt)))

include extension contextValid unique uninitialized in
theorem preserves [FunctionCalls.FaultTokens faults] :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact preserves_with_literals functions extension program evidence unique uninitialized
    (CompatibleExpressionLiterals.preserves functions program context evidence contextValid unique faults) ⟨tree, tree.literalSites⟩


include extension uninitialized in
theorem reflects_with_literals [FunctionCalls.FaultTokens faults]
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.Reflects.forget
    (reflects_with_literals_and_post (functions := functions) (extension := extension) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ExpressionFailurePostContracts.Reflects.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Reflects.of_trivial
        (certificate := CompatibleExpressionReads.LoweredRead fuel values source context reasonAt)
        (by
          intro scope id lowered receipt
          exact CompatibleExpressionReads.loweredRead_reflects functions extension program context evidence reasonAt uninitialized receipt)))

include extension contextValid uninitialized in
theorem reflects [FunctionCalls.FaultTokens faults] :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact reflects_with_literals functions extension program evidence uninitialized
    (CompatibleExpressionLiterals.reflects functions program context evidence contextValid source faults) ⟨tree, tree.literalSites⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorExtraction
/-! Actual successful Functions lowering supplies recursive constructor
receipts; raw source typing supplies original payload types and closed
constructor validity. Child semantic evaluations are never premises. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
open Core Frontend SourceInference DataPatternValues
open CompatibleEncoding (bind_ok)

structure PolicyFor (policy : SourceCoreFunctions.Policy) (context : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource) (scope : Scope)
    (reasonAt : ExpressionId → Word) : Prop where
  special : ∀ id, Syntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower context child budget source scope id reasonAt) = .ok none
  read : ∀ id, Syntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

theorem constructor_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .constructor instantiation ids)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) context source scope id reasonAt = .ok lowered) :
    ∃ tag header codes, lowered = ⟨.namedData tag.owner,
        SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩ ∧
      Header values source id node instantiation tag header codes ∧ ids.length = instantiation.payloadTypes.length ∧
      ListRel (Argument values (fun budget source scope id reasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy body budget context source scope id reasonAt)
        fuel source scope reasonAt) (ids.zip instantiation.payloadTypes) codes := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) context childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form, readPolicy, bind, Except.bind, pure, Except.pure] at accepted
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error error => simp [read] at accepted
      | ok pair =>
        rcases pair with ⟨other, type⟩
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        simp only [read, form, leafPolicy] at accepted
        unfold SourceCoreCompatibleDataExpressions.leafLowerer at accepted
        simp only [read, bind, Except.bind, form] at accepted
        obtain ⟨tag, header, codes, codeEq, receipt, count, arguments⟩ := constructor_of_lower found form accepted
        refine ⟨tag, header, codes, codeEq, receipt, count, ?_⟩
        generalize inputsEq : ids.zip instantiation.payloadTypes = inputs at arguments ⊢
        clear codeEq receipt inputsEq
        induction arguments with
        | nil => exact .nil
        | cons head tail ih => exact .cons ⟨head.projected, by simpa only [Nat.min_self] using head.generated⟩ ih
  · simp [owner, bind, Except.bind] at accepted

theorem child_certificates
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {certificate : ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source sourceContext ids types)
    (generated : ListRel (Argument values (fun budget source scope id reasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget context source scope id reasonAt)
      fuel source scope reasonAt) (ids.zip types) codes)
    (extract : ∀ id, id ∈ ids → ∀ node code,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok code →
      certificate id code) :
    Nodes source ids types codes ∧ ∀ id code, (id, code) ∈ ids.zip codes →
      certificate id code := by
  induction ids generalizing types codes with
  | nil => cases typed; cases generated; exact ⟨.nil, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      cases generated with
      | @cons _ _ code codes first rest =>
        obtain ⟨node, contains, sourceType⟩ := head.stored_type
        have found := lookupExpression?_complete unique contains
        have child := extract id (by simp) node code found (sourceType ▸ head) first.generated
        obtain ⟨nodes, children⟩ := ih tail rest (fun id member => extract id (by simp [member]))
        refine ⟨.cons ⟨node, found, sourceType⟩ nodes, ?_⟩
        intro other otherCode member
        rcases List.mem_cons.mp member with same | remaining
        · cases same; exact child
        · exact children other otherCode remaining

private theorem child_trees
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context} {readFuel : Nat}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source sourceContext ids types)
    (generated : ListRel (Argument values (fun budget source scope id reasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget context source scope id reasonAt)
      fuel source scope reasonAt) (ids.zip types) codes)
    (extract : ∀ id, id ∈ ids → ∀ node code,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok code →
      Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id code) :
    Nodes source ids types codes ∧ ∀ id code, (id, code) ∈ ids.zip codes →
      Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id code := by
  exact child_certificates unique typed generated extract

/-- Independent source instantiation validity is consumed at each stored
constructor occurrence; native representations do not supply this law. -/
theorem tree_of_functions_with_literals
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    (literals : GenericExpressionMeaning.Certificate)
    (literalFactory : CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt literals)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree.WithLiterals (fuel := readFuel) (values := values) (source := source)
      (context := sourceContext) (solved := context.solvedRequirements) (reasonAt := reasonAt) literals scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
  | fragment syntaxTree =>
    refine (fun ⟨tree, sites⟩ => ⟨_, Tree.LiteralSites.fragment tree sites⟩) (CompatibleExpressionConditionals.tree_of_functions_with_literals literals literalFactory unique declarations ?_ ?_ syntaxTree found typed accepted)
    · exact ⟨fun id child => policyFor.special id (.fragment child), fun id child => policyFor.read id (.fragment child), policyFor.lower, policyFor.leaf⟩
    · exact fun id node child => coercions id node (.fragment child)
  | @constructor id original instantiation ids originalFound form children ih =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨tag, header, codes, rfl, receipt, count, arguments⟩ := constructor_of_functions originalFound form
        (policyFor.special _ (.constructor originalFound form children))
        (policyFor.read _ (.constructor originalFound form children)) policyFor.leaf accepted
      obtain ⟨admissible, argumentsTyped, sourceType⟩ := constructor_source_types unique originalFound form receipt.metadata.coercions typed
      obtain ⟨nodes, childReceipts⟩ := child_certificates unique argumentsTyped arguments
        (fun id member node code found typed generated => ih id member found typed generated)
      let childTrees := fun id code (member : (id, code) ∈ ids.zip codes) => (childReceipts id code member).choose
      exact ⟨_, .constructor receipt form (constructorValid _ _ _ _ (.constructor originalFound form children) originalFound form admissible) count nodes childTrees (fun id code member => (childReceipts id code member).choose_spec)⟩

/-- Original tree-only API, projected from the single supported extraction. -/
theorem tree_of_functions_with_validity
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  exact (tree_of_functions_with_literals
    (fun _ id lowered => CompatibleExpressionLiterals.Certificate context.solvedRequirements source id lowered)
    CompatibleExpressionProducts.LiteralFactory.ordinary unique declarations constructorValid policyFor coercions syntaxTree found typed accepted).choose

/-- Compatibility with the former false residual scope. -/
theorem tree_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_functions_with_validity (policy := policy) (body := body) (readFuel := readFuel)
    (context := context) (values := values) (source := source) (scope := scope) (reasonAt := reasonAt)
    (sourceContext := sourceContext) (unique := unique) (declarations := declarations)
    (constructorValid := CompatibleExpressionInstantiationLaws.ConstructorLaw.of_closed closed residual)
    (policyFor := policyFor) (coercions := coercions) (id := id) (syntaxTree := syntaxTree) (node := node)
    (found := found) (typed := typed) (fuel := fuel) (lowered := lowered) (accepted := accepted)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualConstructors
/-! The actual contextual dispatcher supplies the ordinary recursive-constructor policy.
Static occurrence metadata excludes local specialization and output coercions.
The final receipt contains no child lowering or runtime execution hypothesis. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
open Core Frontend SourceInference

/-- Metadata for the ordinary fragment in this source view. Conditions apply
only to occurrences admitting the finite grammar, not arbitrary source forms. -/
structure Ordinary (source : TypedSource) (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceSpecialization.SpecializationKey) : Prop where
  requirements : ∀ id node, Syntax source id → source.lookupExpression? id = some node →
    node.requirements = CompatibleExpressionLiterals.owned node.form
  coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = []
  notInitializer : ∀ id, Syntax source id → locals.bindings.find?
    (fun binding => decide (binding.caller = owner ∧ binding.initializer = id)) = none
  localBinder : ∀ id node name binder, Syntax source id → source.lookupExpression? id = some node →
    node.form = .reference name (.local binder) →
    locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false

private theorem contextualSource_fragment
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    (ordinary : Ordinary source locals owner) (syntaxTree : Syntax source id) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  cases syntaxTree with
  | fragment child =>
    cases child with
    | primitive syntaxTree =>
      cases syntaxTree with
      | product syntaxTree =>
        cases syntaxTree with
        | @literal _ literalNode found atomic =>
          generalize form : literalNode.form = shape at atomic
          cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
        | read found form =>
          have localBinder := ordinary.localBinder _ _ _ _ (.fragment (.primitive (.product (.read found form)))) found form
          simp only [SourceCoreGeneralFunctions.contextualSource, found, form, localBinder, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
        | group found form child => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
        | pair found form first second => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
      | unary found form child | binary found form first second | group found form child | pair found form first second =>
        simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
    | unary found form child | binary found form first second | group found form child | pair found form first second | conditional found form _ _ _ =>
      simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

  | constructor found form _ =>
    simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem evidence_fragment (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (requirements : node.requirements = CompatibleExpressionLiterals.owned node.form) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (CompatibleExpressionLiterals.owned node.form) := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    change (if (CompatibleExpressionLiterals.owned node.form).length < 0 then none else
      if CompatibleExpressionLiterals.owned node.form = (CompatibleExpressionLiterals.owned node.form).take
          ((CompatibleExpressionLiterals.owned node.form).length - 0) ++ [] then
        some ((CompatibleExpressionLiterals.owned node.form).take ((CompatibleExpressionLiterals.owned node.form).length - 0)) else none) = _
    simp
  cases syntaxTree with
  | fragment child =>
    cases child with
    | primitive syntaxTree =>
      cases syntaxTree with
      | product syntaxTree =>
        cases syntaxTree with
        | @literal _ literalNode originalFound atomic =>
          have same := Option.some.inj (originalFound.symm.trans found)
          subst node
          generalize form : literalNode.form = shape at atomic
          cases atomic <;> simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
            CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
        | read originalFound form | group originalFound form _ | pair originalFound form _ _ =>
          have same := Option.some.inj (originalFound.symm.trans found)
          subst node
          simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
            CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
      | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ =>
        have same := Option.some.inj (originalFound.symm.trans found)
        subst node
        simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
          CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
    | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ | conditional originalFound form _ _ _ =>
      have same := Option.some.inj (originalFound.symm.trans found)
      subst node
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
        CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

  | constructor originalFound form _ =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
      CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

private theorem fragment_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : Syntax source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases syntaxTree with
  | fragment child =>
    cases child with
    | primitive syntaxTree =>
      cases syntaxTree with
      | product child => cases child <;> exact ⟨_, by assumption⟩
      | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ => exact ⟨_, found⟩
    | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ | conditional found _ _ _ _ => exact ⟨_, found⟩

  | constructor found _ _ => exact ⟨_, found⟩

private theorem context_bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Complete ordinary primitive trees are extracted from the production
contextual traversal, at root or full specialized parent context. -/
theorem tree_of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context}
    (ordinary : Ordinary source locals context.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine tree_of_functions unique declarations closed residual ?_ ordinary.coercions syntaxTree found typed accepted
      refine ⟨?_, ?_, lowerPolicy, leafPolicy⟩
      · intro childId childTree child budget
        obtain ⟨childNode, childFound⟩ := fragment_has_node childTree
        dsimp only
        rw [contextualSource_fragment program context.plan locals context.owner (some prepared) ordinary childTree]
        simp only [childFound, ordinary.notInitializer _ childTree, Option.filter]
        rw [evidence_fragment program _ prepared.caller context child budget scope reasonAt _ childTree childFound
          (ordinary.requirements _ _ childTree childFound) (ordinary.coercions _ _ childTree childFound)]
        cases childForm : childNode.form <;> simp only [childForm]
        case reference name resolution =>
          cases resolution <;> simp only
          case «local» binder =>
            rw [ordinary.localBinder _ _ _ _ childTree childFound childForm]
            rfl
      · intro childId childTree
        change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner (some prepared) source childId
          representation.expressions.readExpression viewed childId) = _
        rw [contextualSource_fragment program context.plan locals context.owner (some prepared) ordinary childTree]
        simp only [bind, Except.bind, readPolicy]
    | none =>
      dsimp only at accepted
      obtain ⟨caller, selected, generated⟩ := context_bind_accepted accepted
      refine tree_of_functions unique declarations closed residual ?_ ordinary.coercions syntaxTree found typed generated
      refine ⟨?_, ?_, lowerPolicy, leafPolicy⟩
      · intro childId childTree child budget
        obtain ⟨childNode, childFound⟩ := fragment_has_node childTree
        dsimp only
        rw [contextualSource_fragment program context.plan locals context.owner none ordinary childTree]
        simp only [bind, Except.bind, pure, Except.pure, childFound, ordinary.notInitializer _ childTree, Option.filter]
        rw [evidence_fragment program _ caller context child budget scope reasonAt _ childTree childFound
          (ordinary.requirements _ _ childTree childFound) (ordinary.coercions _ _ childTree childFound)]
        cases childForm : childNode.form <;> simp only [childForm]
        case reference name resolution =>
          cases resolution <;> simp only
          case «local» binder =>
            rw [ordinary.localBinder _ _ _ _ childTree childFound childForm]
            rfl
      · intro childId childTree
        change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner none source childId
          representation.expressions.readExpression viewed childId) = _
        rw [contextualSource_fragment program context.plan locals context.owner none ordinary childTree]
        simp only [bind, Except.bind, readPolicy]

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberLayouts
/-! Independent uniform-field typing fixes original field views. Compiler rows
may erase staging in their native types, but raw source types are aligned by
the retained source substitution and catalog membership instead. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
open Core Frontend SourceInference DataPatternValues CompatibleConstructorMetadata
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Child := SourceCoreFunctions.ExpressionLowerer
abbrev Branch := SourceCoreCompatibleDataPlaces.MemberBranch

/-- A source-only property of the canonical metadata rows, with no evaluation
or native type equality premise. -/
def FieldViews (signature : ProgramDataSignature) (arguments : List TypeSystem.Ty)
    (index : Nat) (field : TypeSystem.Ty) : Prop :=
  ∀ constructor ∈ signature.constructors, ∃ actual,
    (constructor.payloadTypes.map (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip arguments)))[index]? = some actual ∧
      SourceCoreRawMetadata.runtimeType actual = SourceCoreRawMetadata.runtimeType field

theorem field_views {checked : SourceCoreCompatibleCatalog.Checked} {context : SourceSemantics.Context}
    (signatures : context.signatures = checked.signatures)
    {base field : TypeSystem.Ty} {index : Nat} {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType base) = some (signature.id, arguments))
    (selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
    (typed : UniformMemberProjection context base index field) : FieldViews signature arguments index field := by
  cases typed with
  | @intro _ _ dataType substitution member exact baseEq _ _ _ uniform _ =>
    rw [baseEq, runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal] at nominal
    obtain ⟨sameId, sameArguments⟩ := Prod.mk.inj (Option.some.inj nominal)
    have selectedMember : dataType ∈ checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) :=
      List.mem_filter.mpr ⟨signatures ▸ member, by simpa using sameId⟩
    rw [selected] at selectedMember
    have sameSignature : dataType = signature := List.mem_singleton.mp selectedMember
    subst dataType
    rw [← sameArguments]
    intro constructor member
    have found := uniform constructor member
    have lists :
        (constructor.payloadTypes.map
          (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip ((SourceSemantics.ParameterSubstitution.orderedArguments substitution signature.parameters).map
            SourceCoreRawMetadata.runtimeType)))).map SourceCoreRawMetadata.runtimeType =
        (constructor.payloadTypes.map substitution.apply).map SourceCoreRawMetadata.runtimeType := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro type _
      exact CompatiblePlaceKeyTyping.canonical_substitution_view exact type
    have same : ((constructor.payloadTypes.map
        (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip ((SourceSemantics.ParameterSubstitution.orderedArguments substitution signature.parameters).map
          SourceCoreRawMetadata.runtimeType))))[index]?).map SourceCoreRawMetadata.runtimeType = some (SourceCoreRawMetadata.runtimeType field) := by
      rw [← List.getElem?_map, lists, List.getElem?_map, found]
      rfl
    cases actualAt : (constructor.payloadTypes.map
        (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip ((SourceSemantics.ParameterSubstitution.orderedArguments substitution signature.parameters).map
          SourceCoreRawMetadata.runtimeType))))[index]? with
    | none => simp [actualAt] at same
    | some actual =>
      simp only [actualAt, Option.map_some, Option.some.injEq] at same
      exact ⟨actual, rfl, same⟩

def branchCode (index : Nat) (branch : Branch) : Expr :=
  LanguageResult.success (SourceCoreDataExpressions.projectPacked index branch.payloadTypes (.second (.var 0)))

/-- Exact expression-member row. Raw field equality is provided separately by
`FieldViews`; the compiler only checks its projected native type. -/
structure Row (checked : SourceCoreCompatibleCatalog.Checked) (site : SourceCoreElaboration.ErrorSite)
    (root : TypeSystem.Ty) (substitution : TypeSystem.ParameterSubstitution)
    (identity : DataTypeId) (index : Nat) (result : Ty)
    (input : ProgramDataConstructorSignature × Nat) (branch : Branch) : Prop where
  authenticated : checked.resolveConstructor
    ⟨input.1.id, substitution, input.1.payloadTypes.map substitution.apply, root⟩ = .ok branch.constructor
  position : branch.constructor = ⟨identity, input.2⟩
  field : ∃ actual, (input.1.payloadTypes.map substitution.apply)[index]? = some actual ∧
    SourceCoreCompatibleDataExpressions.projectType checked site actual = .ok result
  payloads : (input.1.payloadTypes.map substitution.apply).mapM
    (SourceCoreCompatibleDataExpressions.projectType checked site) = .ok branch.payloadTypes

theorem row_member {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (rows : ListRel relation inputs outputs) {input : α} (member : input ∈ inputs) :
    ∃ output, relation input output := by
  induction rows with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, head⟩
    · exact ih member

theorem rows_certificate {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {root field : TypeSystem.Ty} {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty}
    {identity : DataTypeId} {index : Nat} {result : Ty} {branches : List Branch}
    (identityFound : checked.catalog.identity? root = some identity)
    (projected : SourceCoreCompatibleDataExpressions.projectType checked site field = .ok result)
    (views : FieldViews signature arguments index field)
    (rows : ListRel (Row checked site root (signature.parameters.zip arguments) identity index result)
      signature.constructors.zipIdx branches) :
    CompatibleMemberCertificates.Certificate checked site root field signature arguments index identity branches result := by
  refine ⟨identityFound, projected, ?_⟩
  have convert : ∀ inputs outputs,
      ListRel (Row checked site root (signature.parameters.zip arguments) identity index result) inputs outputs →
      (∀ input ∈ inputs, input.1 ∈ signature.constructors) →
      ListRel (CompatibleMemberCertificates.Row checked site root field (signature.parameters.zip arguments) identity index) inputs outputs := by
    intro inputs outputs related
    induction related with
    | nil => intro _; exact .nil
    | @cons input inputs branch branches row rest ih =>
      intro members
      obtain ⟨actual, found, view⟩ := views input.1 (members input (by simp))
      exact .cons ⟨row.authenticated, row.position, ⟨actual, found, view⟩, row.payloads⟩
        (ih (fun item member => members item (by simp [member])))
  apply convert _ _ rows
  intro input member
  obtain ⟨constructor, position⟩ := input
  exact List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp member)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberSource
/-! Independent member-expression traces, including the exact base failure
and invalid projection rules. Authenticated static layouts exclude invalid
shapes and positions only after the base's meaning has been established. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
open Core Frontend SourceInference CompatibleExpressionPrimitives CompatiblePayload GeneralHeap DataPatternValues

inductive Layout (checked : SourceCoreCompatibleCatalog.Checked) (site : SourceCoreElaboration.ErrorSite)
    (base field : TypeSystem.Ty) (index : Nat) (identity : DataTypeId) (branches : List Expr) (result : Ty) : Prop where
  | intro {signature arguments infos}
      (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType base) = some (signature.id, arguments))
      (selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
      (certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType base)
        field signature arguments index identity infos result)
      (generated : branches = infos.map (branchCode index)) : Layout checked site base field index identity branches result

private theorem source_constructor {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {owner arguments}, SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType sourceType) = some (owner, arguments) →
      ∃ metadata payloads, source = .constructed metadata payloads := by
  induction related using CompatiblePayload.ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | function | proxy | mappingValue => intro _ _ impossible; cases impossible
  | constructed => intro _ _ _; exact ⟨_, _, rfl⟩
  | compatible same _ ih => intro _ _ view; exact ih (by rw [← same]; exact view)
  | nil | cons | empty | entry | absent | present => trivial

/-- Row selection authenticates both the original source field view and the
actual projected payload expression. This statement has no evaluation input. -/
theorem Layout.select {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {site : SourceCoreElaboration.ErrorSite}
    {base field : TypeSystem.Ty} {index : Nat} {identity : DataTypeId} {branches : List Expr} {result : Ty}
    (layout : Layout checked site base field index identity branches result)
    {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world base source value type) :
    ∃ metadata sources tag header payloads types child native,
      source = .constructed metadata sources ∧
      value = .constructed tag (.pair (.word header) (packValues payloads)) ∧
      tag.owner = identity ∧
      branches[tag.index]? = some (LanguageResult.success (SourceCoreDataExpressions.projectPacked index types (.second (.var 0)))) ∧
      types.length = payloads.length ∧ payloads[index]? = some native ∧
      Dynamic.ValueAt sources index child ∧ ValueRep checked registry functions mapping world field child native result := by
  cases layout with
  | intro nominal selected certificate generated =>
    obtain ⟨metadata, sources, rfl⟩ := source_constructor related nominal
    obtain ⟨tag, header, payloads, types, rfl, typeEq, fields⟩ := constructor_fields related rfl
    obtain ⟨owner, branch, actual, child, native, branchAt, tagEq, typesEq, sourceAt, view, coreAt, selectedAt, nativeAt, childRelated⟩ :=
      certificate.select nominal selected fields
    refine ⟨metadata, sources, tag, header, payloads, types, child, native, rfl, rfl, owner, ?_, ?_, nativeAt, selectedAt,
      .compatible view.symm childRelated⟩
    · simp only [generated, List.getElem?_map, branchAt, Option.map_some, branchCode, typesEq]
    · exact fields.payloads.length.2.2.symm.trans fields.payloads.length.2.1

inductive SourceMember (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap) (base : ExpressionId)
    (index : Nat) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {metadata arguments selected after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base (.constructed metadata arguments) after)
      (field : Dynamic.ValueAt arguments index selected) : SourceMember program context evidence source environment before base index (.value selected) after
  | failure {reason after}
      (baseTrace : Dynamic.ExpressionFaults program context evidence source environment before base reason after) :
      SourceMember program context evidence source environment before base index (.fault reason) after
  | shape {value after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base value after)
      (invalid : ¬ Dynamic.ConstructedValue value) : SourceMember program context evidence source environment before base index (.fault .invalidProjection) after
  | position {metadata arguments after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base (.constructed metadata arguments) after)
      (missing : Dynamic.ValueIndexMissing arguments index) : SourceMember program context evidence source environment before base index (.fault .invalidProjection) after

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id base : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome} {name : String} {index : Nat}

theorem member_inv (metadata : Metadata checked source id node type)
    (form : node.form = .member base name index) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    SourceMember program context evidence source environment before base index outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | member _ base field => exact .value base field
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | memberBase _ base => exact .failure base
    | memberShape _ base invalid => exact .shape base invalid
    | memberIndex _ base missing => exact .position base missing

theorem member_intro (metadata : Metadata checked source id node type)
    (form : node.form = .member base name index)
    (trace : SourceMember program context evidence source environment before base index outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | value base field =>
    apply Dynamic.ExpressionEvaluatesOutcome.value
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]; exact .member rfl base field
    · rw [metadata.coercions]; exact .nil
  | failure base =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .memberBase rfl base
  | shape base invalid =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .memberShape rfl base invalid
  | position base missing =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .memberIndex rfl base missing

theorem member_source_types
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .member base name index) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ baseType, ExpressionHasType source context base baseType ∧ UniformMemberProjection context baseType index node.type := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | member baseTyped projection => exact ⟨_, baseTyped, projection⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberTree
/-! Finite member chains over the already certified constructor expression
fragment. Every child certificate is structural; no execution is stored. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
open Core Frontend SourceInference CompatibleExpressionReads

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | fragment {id} (tree : CompatibleExpressionConstructors.Syntax source id) : Syntax source id
  | member {id node base name index} (found : source.lookupExpression? id = some node)
      (form : node.form = .member base name index) (child : Syntax source base) : Syntax source id

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | fragment {id lowered}
      (tree : CompatibleExpressionConstructors.Tree fuel values source context solved reasonAt scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | member {id node base baseNode name index identity branches result child}
      (metadata : Metadata values.checked source id node result)
      (baseMetadata : Metadata values.checked source base baseNode child.type)
      (form : node.form = .member base name index)
      (layout : Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result)
      (childTree : Tree fuel values source context solved reasonAt scope base child) :
      Tree fuel values source context solved reasonAt scope id
        ⟨result, SourceCoreDataExpressions.member identity result branches child.expression⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxyMeaning
/-! Ordinary proxy expressions retain their raw inner type, including staging
annotations inside it. A registered Word header carries that metadata while
the native constructor uses its checked nominal layout. Both heaps are unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives

variable {values : ValuesContext} {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
  {inner : TypeSystem.Ty} {owner : DataTypeId} {header : Word}

/-- A leaf has the registered native type under any actual ambient suffix. -/
theorem Header.hasType (receipt : Header values source id node inner owner header)
    (ambient : AmbientDefinitions values.checked.catalog.definitions) (context : Core.Context) :
    HasType context (LanguageResult.success (.construct ⟨owner, 0⟩ (.word header)))
      (LanguageResult.resultType (.namedData owner)) ambient.definitions :=
  .inRight .word (.construct (ambient.basePrefix.constructor_lookup receipt.registered) .word)

theorem Header.source_evaluates (receipt : Header values source id node inner owner header)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id (.proxy inner) heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound receipt.metadata.found)
  · rw [receipt.form, receipt.metadata.requirements, receipt.metadata.coercions]
    exact .proxy rfl
  · rw [receipt.metadata.coercions]; exact .nil

theorem Header.source_outcome (receipt : Header values source id node inner owner header)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    outcome = .value (.proxy inner) ∧ after = before := by
  cases trace with
  | value evaluation =>
    have raw := evaluation_raw unique (lookupExpression?_sound receipt.metadata.found)
      (by intros; simp [receipt.form]) receipt.metadata.coercions evaluation
    rw [receipt.form] at raw
    cases raw
    exact ⟨rfl, rfl⟩
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound receipt.metadata.found)
      (by intros; simp [receipt.form]) receipt.metadata.coercions failed
    rw [receipt.form] at raw
    cases raw

theorem Header.represents (receipt : Header values source id node inner owner header)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (extension : SourceCoreRawMetadata.Extends values.registry registry)
    (mapping : LocationMap) (world : StoreTyping) :
    ValueRep values.checked registry functions mapping world node.type (.proxy inner)
      (.constructed ⟨owner, 0⟩ (.word header)) (.namedData owner) := by
  rw [receipt.sourceType]
  exact .proxy (receipt.original.extend extension) receipt.identity receipt.registered

theorem Header.native_evaluates (_receipt : Header values source id node inner owner header)
    (environment : Environment) (store : Store) (ξ : Renaming) :
    Evaluates environment store
      ((LanguageResult.success (.construct ⟨owner, 0⟩ (.word header))).rename ξ)
      (.inRight .word (.constructed ⟨owner, 0⟩ (.word header))) store := .inRight (.construct .word)

/-- Accepted proxy certificates supply their whole expression meaning. No
child semantics, source typing inference or runtime metadata resolver is used. -/
theorem preserves {values : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (extension : SourceCoreRawMetadata.Extends values.registry registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (unique : NodeOccurrencesUnique source) (faults : FunctionCalls.FaultRep) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source) faults := by
  intro scope id lowered certificate node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees actualTyped trace
  cases certificate with
  | @proxy other inner owner header receipt =>
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst other
    obtain ⟨rfl, rfl⟩ := receipt.source_outcome unique trace
    exact ⟨_, store, mapping, world, receipt.native_evaluates actual store ξ,
      .value (receipt.represents functions extension mapping world), heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩

/-- Every completed proxy evaluation returns the registered raw header and
constructs its independent source trace, with both stores preserved. -/
theorem reflects {values : ValuesContext} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (extension : SourceCoreRawMetadata.Extends values.registry registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (faults : FunctionCalls.FaultRep) :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source) faults := by
  intro scope id lowered certificate node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
  cases certificate with
  | @proxy other inner owner header receipt =>
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst other
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic (receipt.native_evaluates actual store ξ) evaluated
    exact ⟨.value (.proxy inner), before, mapping, world,
      .value (receipt.source_evaluates program context evidence environment before),
      .value (receipt.represents functions extension mapping world), heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.IntegerBitNotSnapshot
/-! Integer bit-not at the retained IR boundary. The declarative snapshot rule
agrees with the already executable unary primitive and ordinary Core modifier.
This does not broaden the source checker's Word-only compound admission. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.IntegerBitNotSnapshot
open Core Frontend SourceInference GeneralHeap DataEquality CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces

theorem preserves_type {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {current : Option Dynamic.Value} {result : Dynamic.Value}
    (typed : Dynamic.OptionalValueHasType context heap current .integer)
    (applies : Dynamic.BitNotSnapshot current result) : Dynamic.ValueHasType context heap result .integer := by
  cases applies with
  | word => cases typed with | some typed => cases typed
  | integer _ => exact .integer _

theorem native_success (value : Int) {environment : Environment} {snapshot rhs : Expr}
    (selected : Selects environment snapshot (.inRight .unit (.integer value)))
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (store : Store) (invalid : Word) :
    Dynamic.BitNotSnapshot (some (.integer value)) (.integer (~~~value)) ∧
      Evaluates environment store (modified .integer operator true snapshot rhs invalid)
        (.inRight .word (.integer (~~~value))) store ∧
      ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot (.integer value) := by
  obtain ⟨_, evaluated, valid⟩ := DataPlaceModifier.integer_bitNot_primitive value selected operator store invalid
  exact ⟨.integer value, evaluated, valid⟩

/-- Every completed generated modifier run returns the independent Integer
snapshot result and keeps the store unchanged. No source runtime is imported. -/
theorem native_reflects (value : Int) {environment : Environment} {snapshot rhs : Expr}
    (selected : Selects environment snapshot (.inRight .unit (.integer value)))
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) {store after : Store} (invalid : Word) {result : Value}
    (completed : Evaluates environment store (modified .integer operator true snapshot rhs invalid) result after) :
    result = .inRight .word (.integer (~~~value)) ∧ after = store ∧
      Dynamic.BitNotSnapshot (some (.integer value)) (.integer (~~~value)) := by
  obtain ⟨applies, evaluated, _⟩ := native_success value selected operator store invalid
  exact ⟨(evaluation_deterministic completed evaluated).1, (evaluation_deterministic completed evaluated).2, applies⟩

theorem compatible_success {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}

    {sourceType : TypeSystem.Ty} {type : Ty} {source : Dynamic.Value} {value : Value}
    (profile : SourceCoreRawMetadata.runtimeType sourceType = .integer)
    (represented : ValueRep checked registry functions mapping world sourceType source value type)
    {environment : Environment} {snapshot rhs : Expr}
    (selected : Selects environment snapshot (.inRight .unit value))
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (store : Store) (invalid : Word) :
    ∃ result native, ValueRep checked registry functions mapping world sourceType result native type ∧
      Dynamic.BitNotSnapshot (some source) result ∧
      Evaluates environment store (modified type operator true snapshot rhs invalid) (.inRight .word native) store ∧
      ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot source := by
  obtain ⟨integer, rfl, rfl, rfl⟩ := CompatibleRawScalarFields.integer_fields represented profile
  obtain ⟨applies, evaluated, valid⟩ := native_success integer selected operator store invalid
  exact ⟨_, _, .compatible (actual := .integer) profile (.integer (~~~integer)), applies, evaluated, valid⟩

/-- The newly admitted dynamic constructor closes an ordinary source snapshot
write. The retained place is Integer typed, without claiming checker admission. -/
theorem source_assignment (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (id : Resolved.LocalId) (value : Int) :
    Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      [(id, ⟨0⟩)] ⟨[⟨.integer, some (.integer value), none⟩]⟩ ⟨id, [], .integer⟩
      (.integer (~~~value)) ⟨[⟨.integer, some (.integer (~~~value)), none⟩]⟩ := by
  apply Dynamic.SourcePlaceSnapshotUpdate.intro
    (selectedHeap := ⟨[⟨.integer, some (.integer value), none⟩]⟩)
    (target := ⟨⟨0⟩, .integer, .integer, [], some (.integer value)⟩)
  · exact Dynamic.SourcePlaceResolves.intro (place := ⟨id, [], .integer⟩)
      (before := ⟨[⟨.integer, some (.integer value), none⟩]⟩)
      (after := ⟨[⟨.integer, some (.integer value), none⟩]⟩)
      .head (.intro .head) .nil (.intro .head) .initialized .nil
  · exact .intro (.intro .head) rfl .initialized (.leaf (.integer value))
      (DataPlaceCommitReflection.source_writes (.intro .head) (.integer (~~~value)))

end Solcore.SourceSemantics.CoreLowering.IntegerBitNotSnapshot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorNativeTyping
/-! Registered constructor headers and the existing ordered packing tree close
native typing for recursive constructors with scalar children. The exact raw
metadata word is retained; no child-code typing callback is required. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorNativeTyping
open Core Frontend SourceInference
open CompatibleExpressionScalarNativeTyping

theorem packed_type (codes : List SourceCoreBasic.LoweredExpr) :
    (SourceCoreCalls.packArguments codes).type = SourceCoreCompatibleCatalog.packTypes (codes.map (·.type)) := by
  induction codes with
  | nil => rfl
  | cons head rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      simp only [SourceCoreCalls.packArguments, SourceCoreCompatibleCatalog.packTypes, List.map_cons]
      exact congrArg (Ty.product head.type) ih

/-- The same ordered static sequence types zero, one and many arguments. Its
packing shape and inserted payload slots are the production helper's shape. -/
theorem packed_native {definitions : DataEnvironment} {nativeContext : Core.Context}
    {source : TypedSource} {certificates : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificates scope ids types codes)
    (children : ∀ id lowered, certificates scope id lowered → NativeTyping definitions nativeContext lowered) :
    NativeTyping definitions nativeContext (SourceCoreCalls.packArguments codes) := by
  induction tree with
  | nil => exact ⟨.unit, LanguageResult.success_hasType .unit⟩
  | single _ receipt => exact children _ _ receipt
  | cons _ receipt _ rest =>
    have first := children _ _ receipt
    exact ⟨.product first.1 rest.1, LocalSequence.pair_hasType first.1 rest.1 first.2 rest.2⟩

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope) (administrative : Core.Context)

include visibleTypes in
theorem constructors_native
    (tree : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact conditionals_native visibleTypes administrative child
  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children ih =>
    have sequence := CompatibleExpressionConstructors.sequence_of_nodes
      (scope := scope)
      (certificate := fun _ _ code => NativeTyping values.checked.catalog.definitions
        (SourceCoreLocalCell.coreContext scope ++ administrative) code) count nodes ih
    obtain ⟨packedWF, packedTyped⟩ := packed_native sequence (fun _ _ typed => typed)
    have registered := receipt.registered
    rw [← packed_type codes] at registered
    obtain ⟨_, ownerRegistered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner registered
    exact ⟨.namedData ownerRegistered, SourceCoreCompatibleDataExpressions.construct_hasType header registered packedTyped⟩

include visibleTypes in
theorem constructors_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := constructors_native visibleTypes administrative tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

include visibleTypes in
/-- The real contextual constructor traversal determines the tree and every
ordered child receipt. Source typing and visible scope annotations stay static
inputs, independently of native layout and metadata erasure. -/
theorem contextual_native
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment}
    (ordinary : CompatibleExpressionConstructors.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (syntaxTree : CompatibleExpressionConstructors.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  exact constructors_native_at visibleTypes administrative extension
    (CompatibleExpressionConstructors.tree_of_contextual ordinary unique closed residual declarations syntaxTree found sourceTyped
      readPolicy lowerPolicy leafPolicy accepted)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorNativeTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NativeExpressionRenamingSupport
/-! Reflection of free-slot bounds follows the actual renamed syntax, including
each binder. It does not transport runtime captures or infer source authority. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NativeExpressionRenamingSupport
open Core NativeExpressionContextSupport

def ReflectsBound (mapping : Renaming) (source target : Nat) : Prop :=
  ∀ index, mapping index < target → index < source

theorem ReflectsBound.lift {mapping : Renaming} {source target : Nat}
    (reflects : ReflectsBound mapping source target) :
    ReflectsBound mapping.lift (source + 1) (target + 1) := by
  intro index bound
  cases index with
  | zero => omega
  | succ index =>
    simp only [Renaming.lift] at bound
    have := reflects index (by omega)
    omega

mutual
  theorem reflects : ∀ (code : Expr) {mapping : Renaming} {source target : Nat},
      ReflectsBound mapping source target → supported (code.rename mapping) target = true →
      supported code source = true
    | .unit, _, _, _, _, _ | .bool _, _, _, _, _, _
    | .word _, _, _, _, _, _ | .integer _, _, _, _, _, _ => rfl
    | .var index, _, _, _, bound, support => by
      simp only [Expr.rename, supported, decide_eq_true_eq] at support ⊢
      exact bound index support
    | .pair a b, _, _, _, bound, support
    | .apply a b, _, _, _, bound, support
    | .storeCell a b, _, _, _, bound, support
    | .binary _ a b, _, _, _, bound, support => by
      simp only [Expr.rename, supported, Bool.and_eq_true] at support ⊢
      exact ⟨reflects a bound support.1, reflects b bound support.2⟩
    | .first a, _, _, _, bound, support | .second a, _, _, _, bound, support
    | .inLeft _ a, _, _, _, bound, support | .inRight _ a, _, _, _, bound, support
    | .newCell _ a, _, _, _, bound, support | .loadCell a, _, _, _, bound, support
    | .construct _ a, _, _, _, bound, support | .unary _ a, _, _, _, bound, support =>
      reflects a bound support
    | .lambda _ _ body, _, _, _, bound, support => reflects body bound.lift support
    | .letE a b, _, _, _, bound, support => by
      simp only [Expr.rename, supported, Bool.and_eq_true] at support ⊢
      exact ⟨reflects a bound support.1, reflects b bound.lift support.2⟩
    | .caseE a b c, _, _, _, bound, support => by
      simp only [Expr.rename, supported, Bool.and_eq_true] at support ⊢
      exact ⟨⟨reflects a bound support.1.1, reflects b bound.lift support.1.2⟩,
        reflects c bound.lift support.2⟩
    | .ifE a b c, _, _, _, bound, support
    | .ternary _ a b c, _, _, _, bound, support => by
      simp only [Expr.rename, supported, Bool.and_eq_true] at support ⊢
      exact ⟨⟨reflects a bound support.1.1, reflects b bound support.1.2⟩,
        reflects c bound support.2⟩
    | .matchData _ _ value branches, _, _, _, bound, support => by
      simp only [Expr.rename, supported, Bool.and_eq_true] at support ⊢
      exact ⟨reflects value bound support.1, branches_reflect branches bound support.2⟩

  theorem branches_reflect : ∀ (branches : List Expr) {mapping : Renaming} {source target : Nat},
      ReflectsBound mapping source target →
      branchesSupported (Expr.renameList branches mapping.lift) target = true →
      branchesSupported branches source = true
    | [], _, _, _, _, _ => rfl
    | head :: tail, _, _, _, bound, support => by
      simp only [Expr.renameList, branchesSupported, Bool.and_eq_true] at support ⊢
      exact ⟨reflects head bound.lift support.1, branches_reflect tail bound support.2⟩
end

theorem shift (code : Expr) (count bound : Nat)
    (support : supported (code.rename (fun index => index + count)) (bound + count) = true) :
    supported code bound = true :=
  reflects code (by intro index smaller; dsimp at smaller; omega) support

end Solcore.SourceSemantics.CoreLowering.NativeExpressionRenamingSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualProducts
/-! The actual contextual dispatcher supplies the ordinary product-tree policy.
Static occurrence metadata excludes local specialization and output coercions.
The final receipt contains no child lowering or runtime execution hypothesis. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
open Core Frontend SourceInference

/-- Metadata for the ordinary fragment in this source view. Conditions apply
only to occurrences admitting the finite grammar, not arbitrary source forms. -/
structure Ordinary (source : TypedSource) (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceSpecialization.SpecializationKey) : Prop where
  requirements : ∀ id node, Syntax source id → source.lookupExpression? id = some node →
    node.requirements = CompatibleExpressionLiterals.owned node.form
  coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = []
  notInitializer : ∀ id, Syntax source id → locals.bindings.find?
    (fun binding => decide (binding.caller = owner ∧ binding.initializer = id)) = none
  localBinder : ∀ id node name binder, Syntax source id → source.lookupExpression? id = some node →
    node.form = .reference name (.local binder) →
    locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false

private theorem contextualSource_fragment
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    (ordinary : Ordinary source locals owner) (syntaxTree : Syntax source id) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  cases syntaxTree with
  | @literal _ literalNode found atomic =>
    generalize form : literalNode.form = shape at atomic
    cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
  | read found form =>
    have localBinder := ordinary.localBinder _ _ _ _ (.read found form) found form
    simp only [SourceCoreGeneralFunctions.contextualSource, found, form, localBinder, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
  | group found form child => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
  | pair found form first second => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem evidence_fragment (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (requirements : node.requirements = CompatibleExpressionLiterals.owned node.form) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (CompatibleExpressionLiterals.owned node.form) := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    change (if (CompatibleExpressionLiterals.owned node.form).length < 0 then none else
      if CompatibleExpressionLiterals.owned node.form = (CompatibleExpressionLiterals.owned node.form).take
          ((CompatibleExpressionLiterals.owned node.form).length - 0) ++ [] then
        some ((CompatibleExpressionLiterals.owned node.form).take ((CompatibleExpressionLiterals.owned node.form).length - 0)) else none) = _
    simp
  cases syntaxTree with
  | @literal _ literalNode originalFound atomic =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    generalize form : literalNode.form = shape at atomic
    cases atomic <;> simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
      CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
  | read originalFound form | group originalFound form _ | pair originalFound form _ _ =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
      CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

private theorem fragment_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : Syntax source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases syntaxTree <;> exact ⟨_, by assumption⟩

private theorem context_bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Complete ordinary product trees are extracted from the production
contextual traversal, at root or full specialized parent context. -/
theorem tree_of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context}
    (ordinary : Ordinary source locals context.owner)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine tree_of_functions unique declarations ?_ ordinary.coercions syntaxTree found typed accepted
      refine ⟨?_, ?_, lowerPolicy, leafPolicy⟩
      · intro childId childTree child budget
        obtain ⟨childNode, childFound⟩ := fragment_has_node childTree
        dsimp only
        rw [contextualSource_fragment program context.plan locals context.owner (some prepared) ordinary childTree]
        simp only [childFound, ordinary.notInitializer _ childTree, Option.filter]
        rw [evidence_fragment program _ prepared.caller context child budget scope reasonAt _ childTree childFound
          (ordinary.requirements _ _ childTree childFound) (ordinary.coercions _ _ childTree childFound)]
        cases childForm : childNode.form <;> simp only [childForm]
        case reference name resolution =>
          cases resolution <;> simp only
          case «local» binder =>
            rw [ordinary.localBinder _ _ _ _ childTree childFound childForm]
            rfl
      · intro childId childTree
        change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner (some prepared) source childId
          representation.expressions.readExpression viewed childId) = _
        rw [contextualSource_fragment program context.plan locals context.owner (some prepared) ordinary childTree]
        simp only [bind, Except.bind, readPolicy]
    | none =>
      dsimp only at accepted
      obtain ⟨caller, selected, generated⟩ := context_bind_accepted accepted
      refine tree_of_functions unique declarations ?_ ordinary.coercions syntaxTree found typed generated
      refine ⟨?_, ?_, lowerPolicy, leafPolicy⟩
      · intro childId childTree child budget
        obtain ⟨childNode, childFound⟩ := fragment_has_node childTree
        dsimp only
        rw [contextualSource_fragment program context.plan locals context.owner none ordinary childTree]
        simp only [bind, Except.bind, pure, Except.pure, childFound, ordinary.notInitializer _ childTree, Option.filter]
        rw [evidence_fragment program _ caller context child budget scope reasonAt _ childTree childFound
          (ordinary.requirements _ _ childTree childFound) (ordinary.coercions _ _ childTree childFound)]
        cases childForm : childNode.form <;> simp only [childForm]
        case reference name resolution =>
          cases resolution <;> simp only
          case «local» binder =>
            rw [ordinary.localBinder _ _ _ _ childTree childFound childForm]
            rfl
      · intro childId childTree
        change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner none source childId
          representation.expressions.readExpression viewed childId) = _
        rw [contextualSource_fragment program context.plan locals context.owner none ordinary childTree]
        simp only [bind, Except.bind, readPolicy]

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
end
