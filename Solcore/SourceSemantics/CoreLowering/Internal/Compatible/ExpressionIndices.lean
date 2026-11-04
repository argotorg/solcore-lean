import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.GeneralExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions

/-!
# Compatible expressions: indices and members

Index lookup, execution and fault policies, and member meaning.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberMeaning
/-! Exact member selection after the real child evaluation, with arbitrary
ambient closures and stores. Static layout authentication excludes invalid
source projections; success and base failure preserve the child's heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
open Core Frontend SourceInference CompatibleExpressionReads GeneralHeap ReadOnly DataPatternValues CompatiblePayload

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : Scope}

/-- Static leaf support indexes the existing tree and its exact children.
It contains only leaf membership, with no execution or heap law. -/
inductive Tree.LiteralSites (literals : GenericExpressionMeaning.Certificate) :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Tree fuel values source context solved reasonAt scope id lowered → Prop where
  | fragment {id lowered}
      (tree : CompatibleExpressionConstructors.Tree fuel values source context solved reasonAt scope id lowered)
      (treeSites : CompatibleExpressionConstructors.Tree.LiteralSites literals tree) :
      LiteralSites literals (Tree.fragment (scope := scope) tree)
  | member {id node base baseNode name index identity branches result child}
      (metadata : Metadata values.checked source id node result)
      (baseMetadata : Metadata values.checked source base baseNode child.type)
      (form : node.form = .member base name index)
      (layout : Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result)
      (childTree : Tree fuel values source context solved reasonAt scope base child)
      (childTreeSites : Tree.LiteralSites literals childTree) :
      LiteralSites literals (Tree.member (scope := scope) metadata baseMetadata form layout childTree)

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
  | member metadata baseMetadata form layout childTree childTreeIH => exact .member metadata baseMetadata form layout childTree childTreeIH

private theorem projectPacked_rename (types : List Ty) (index : Nat) (bundle : Expr) (ξ : Renaming) :
    (SourceCoreDataExpressions.projectPacked index types bundle).rename ξ =
      SourceCoreDataExpressions.projectPacked index types (bundle.rename ξ) := by
  induction types generalizing index bundle with
  | nil => rfl
  | cons type types ih => cases types with
    | nil => rfl
    | cons next rest =>
      by_cases zero : index = 0
      · simp [SourceCoreDataExpressions.projectPacked, zero, Expr.rename]
      · simp only [SourceCoreDataExpressions.projectPacked, zero, ↓reduceIte]
        exact ih (index - 1) (.second bundle)

private theorem branchCode_rename (index : Nat) (branch : Branch) (ξ : Renaming) :
    (branchCode index branch).rename ξ.lift.lift = branchCode index branch := by
  simp [branchCode, LanguageResult.success, Expr.rename, projectPacked_rename, Renaming.lift]

theorem member_rename {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {base field : TypeSystem.Ty} {index : Nat} {identity : DataTypeId} {branches : List Expr} {result : Ty}
    (layout : Layout checked site base field index identity branches result) (child : Expr) (ξ : Renaming) :
    (SourceCoreDataExpressions.member identity result branches child).rename ξ =
      SourceCoreDataExpressions.member identity result branches (child.rename ξ) := by
  cases layout with
  | @intro signature arguments infos nominal selected certificate generated =>
    simp only [SourceCoreDataExpressions.member, LanguageResult.bind, Expr.rename, Renaming.lift]
    have branchesEq : Expr.renameList branches ξ.lift.lift = branches := by
      rw [generated]
      clear certificate generated
      induction infos with
      | nil => rfl
      | cons branch rest ih => simp only [List.map_cons, Expr.renameList, branchCode_rename, ih]
    rw [branchesEq]

theorem member_success {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {site : SourceCoreElaboration.ErrorSite}
    {base field : TypeSystem.Ty} {index : Nat} {identity : DataTypeId} {branches : List Expr} {result : Ty}
    (layout : Layout checked site base field index identity branches result)
    {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : CompatiblePayload.ValueRep checked registry functions mapping world base source value type)
    {environment : Environment} {before after : Store} {child : Expr}
    (evaluated : Evaluates environment before child (.inRight .word value) after) :
    ∃ metadata sources selected native,
      source = .constructed metadata sources ∧ Dynamic.ValueAt sources index selected ∧
      CompatiblePayload.ValueRep checked registry functions mapping world field selected native result ∧
      Evaluates environment before (SourceCoreDataExpressions.member identity result branches child)
        (.inRight .word native) after := by
  obtain ⟨metadata, sources, tag, header, payloads, types, selected, native, sourceEq, rfl,
    owner, branchAt, count, nativeAt, sourceAt, represented⟩ := layout.select related
  refine ⟨metadata, sources, selected, native, sourceEq, sourceAt, represented, ?_⟩
  apply SourceCoreDataExpressions.member_evaluates evaluated owner branchAt
  exact .inRight ((projectPacked_selects (.second (.var rfl)) count index nativeAt).evaluates after)

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
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {literals : GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include extension unique in
theorem preserves_with_literals_and_post
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (constructorJoins : ScalarConstructorFaultPostContracts.Joins post listPost values program context evidence source)
    (memberJoins : ScalarMemberFaultPostContracts.Joins post values program context evidence source)
    (literalMeaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults post)
    (readMeaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults post) :
    ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults post := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | fragment child treeSites => exact CompatibleExpressionConstructors.preserves_with_literals_and_post (fuel := fuel) (reasonAt := reasonAt) functions extension program evidence unique sequenceJoins ordinaryJoins constructorJoins literalMeaning readMeaning ⟨child, treeSites⟩
  | @member id node base baseNode name index identity branches result child metadata baseMetadata form layout childTree childTreeSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after environments heaps locals agrees trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have raw := member_inv metadata form unique trace
    cases raw with
    | value childTrace selected =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees (.value childTrace)
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
        ih baseMetadata.found environments heaps locals agrees (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact LanguageResult.bind_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          ScalarMemberFaultPostContracts.base_fault_outcome memberJoins
            metadata baseMetadata form layout childTrace retained⟩
    | shape childTrace invalid =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, _⟩ := member_success layout payload evaluated
        subst_vars
        exact False.elim (invalid .intro)
    | position childTrace missing =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, selected, _⟩ := member_success layout payload evaluated
        cases shape
        exact False.elim (missing_excludes missing selected)

include extension in
theorem reflects_with_literals_and_post
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (constructorJoins : ScalarConstructorFaultPostContracts.Joins post listPost values program context evidence source)
    (memberJoins : ScalarMemberFaultPostContracts.Joins post values program context evidence source)
    (literalMeaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults post)
    (readMeaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults post) :
    ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults post := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | fragment child treeSites => exact CompatibleExpressionConstructors.reflects_with_literals_and_post (fuel := fuel) (reasonAt := reasonAt) functions extension program evidence sequenceJoins ordinaryJoins constructorJoins literalMeaning readMeaning ⟨child, treeSites⟩
  | @member id node base baseNode name index identity branches result child metadata baseMetadata form layout childTree childTreeSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [member_rename layout] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure result baseEvaluation (body := .matchData identity (LanguageResult.resultType result) (.var 0) branches)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.failure failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata,
            ScalarMemberFaultPostContracts.base_fault_outcome memberJoins
              metadata baseMetadata form layout failed retained⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees baseEvaluation
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, selected, native, shape, sourceAt, related, expected⟩ := member_success layout payload baseEvaluation
        subst_vars
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.value childTrace sourceAt), .value related,
            finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩

include extension unique uninitialized in
theorem preserves_with_literals
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
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
      (ExpressionFailurePostContracts.Preserves.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Preserves.of_trivial
        (certificate := CompatibleExpressionReads.LoweredRead fuel values source context reasonAt)
        (by
          intro scope id lowered receipt
          exact CompatibleExpressionReads.loweredRead_preserves functions extension program context evidence reasonAt uninitialized unique receipt)))

include extension contextValid unique uninitialized in
theorem preserves :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact preserves_with_literals functions extension program evidence unique uninitialized
    (CompatibleExpressionLiterals.preserves functions program context evidence contextValid unique faults) ⟨tree, tree.literalSites⟩


include extension uninitialized in
theorem reflects_with_literals
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
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
      (ExpressionFailurePostContracts.Reflects.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Reflects.of_trivial
        (certificate := CompatibleExpressionReads.LoweredRead fuel values source context reasonAt)
        (by
          intro scope id lowered receipt
          exact CompatibleExpressionReads.loweredRead_reflects functions extension program context evidence reasonAt uninitialized receipt)))

include extension contextValid uninitialized in
theorem reflects :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact reflects_with_literals functions extension program evidence uninitialized
    (CompatibleExpressionLiterals.reflects functions program context evidence contextValid source faults) ⟨tree, tree.literalSites⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberCertificates
/-! Successful expression-member generation yields every native branch and
its catalog receipt. Independent source projection supplies raw field views;
no native representation equality is treated as source-type equality. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
open Core Frontend SourceInference DataPatternValues CompatibleExpressionReads
open CompatibleEncoding (bind_ok mapError_ok)

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked

private theorem read_projected {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readExpression checked source id = .ok (node, type)) :
    SourceCoreCompatibleDataExpressions.projectType checked (.occurrence id.occurrence) node.type = .ok type := by
  have metadata := metadata_of_read accepted
  simp only [SourceCoreCompatibleDataExpressions.readExpression, metadata.owner, ne_eq, not_true_eq_false,
    ↓reduceIte, metadata.found, metadata.requirements, metadata.coercions, List.isEmpty_nil, Bool.true_eq_false,
    bind, Except.bind, pure, Except.pure] at accepted
  cases projected : SourceCoreCompatibleDataExpressions.projectType checked (.occurrence id.occurrence) node.type with
  | error error => simp [projected] at accepted
  | ok native => simp only [projected, Except.ok.injEq, Prod.mk.injEq, true_and] at accepted; subst type; rfl

private theorem row_of_accepted {values : ValuesContext} {node : ExpressionNode} {root : TypeSystem.Ty}
    {substitution : TypeSystem.ParameterSubstitution} {identity : DataTypeId} {index : Nat} {result : Ty}
    {input : ProgramDataConstructorSignature × Nat} {code : Expr}
    (accepted : (do
      let payloadTypes := input.1.payloadTypes.map substitution.apply
      let instantiation : DataConstructorInstantiation := ⟨input.1.id, substitution, payloadTypes, root⟩
      let resolved ← (values.checked.resolveConstructor instantiation).mapError (fun _ => SourceCoreBasic.Error.unsupportedExpression node.id node.form)
      unless resolved.owner = identity && resolved.index = input.2 do throw (SourceCoreBasic.Error.unsupportedExpression node.id node.form)
      let selected ← match payloadTypes[index]? with
        | some selected => SourceCoreCompatibleDataExpressions.projectType values.checked (.occurrence node.id.occurrence) selected
        | none => throw (SourceCoreBasic.Error.unsupportedExpression node.id node.form)
      SourceCoreBasic.ensureType (.occurrence node.id.occurrence) result selected
      let payloads ← payloadTypes.mapM (SourceCoreCompatibleDataExpressions.projectType values.checked (.occurrence node.id.occurrence))
      pure (LanguageResult.success (SourceCoreDataExpressions.projectPacked index payloads (.second (.var 0))))) = Except.ok code) :
    ∃ info, code = branchCode index info ∧ Row values.checked (.occurrence node.id.occurrence) root substitution identity index result input info := by
  obtain ⟨tag, resolved, accepted⟩ := bind_ok accepted
  have resolved := mapError_ok resolved
  by_cases valid : tag.owner = identity ∧ tag.index = input.2
  · simp only [valid.1, valid.2, decide_true, Bool.and_self, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases fieldAt : (input.1.payloadTypes.map substitution.apply)[index]? with
    | none => simp [fieldAt, throw] at accepted
    | some field =>
      simp only [fieldAt] at accepted
      obtain ⟨native, projected, accepted⟩ := bind_ok accepted
      obtain ⟨success, ensured, accepted⟩ := bind_ok accepted
      cases success
      have same := ensureType_ok ensured
      have projectedResult : SourceCoreCompatibleDataExpressions.projectType values.checked (.occurrence node.id.occurrence) field = .ok result := by
        rw [same]; exact projected
      cases payloads : (input.1.payloadTypes.map substitution.apply).mapM
          (SourceCoreCompatibleDataExpressions.projectType values.checked (.occurrence node.id.occurrence)) with
      | error error => simp only [payloads] at accepted; cases accepted
      | ok types =>
        simp only [payloads, pure, Except.pure, bind, Except.bind] at accepted
        cases accepted
        exact ⟨⟨tag, types⟩, rfl, resolved, by cases tag; simp_all, ⟨field, fieldAt, projectedResult⟩, payloads⟩
  · simp [valid, Bool.and_eq_true, throw, bind, Except.bind] at accepted

private theorem rows_of_mapM {values : ValuesContext} {node : ExpressionNode} {root : TypeSystem.Ty}
    {substitution : TypeSystem.ParameterSubstitution} {identity : DataTypeId} {index : Nat} {result : Ty}
    {inputs : List (ProgramDataConstructorSignature × Nat)} {codes : List Expr}
    {action : ProgramDataConstructorSignature × Nat → Except SourceCoreBasic.Error Expr}
    (accepted : inputs.mapM action = .ok codes)
    (row : ∀ input code, action input = .ok code → ∃ info, code = branchCode index info ∧
      Row values.checked (.occurrence node.id.occurrence) root substitution identity index result input info) :
    ∃ infos, codes = infos.map (branchCode index) ∧
      ListRel (Row values.checked (.occurrence node.id.occurrence) root substitution identity index result) inputs infos := by
  induction inputs generalizing codes with
  | nil => simp at accepted; subst codes; exact ⟨[], rfl, .nil⟩
  | cons input tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, produced, accepted⟩ := bind_ok accepted
    obtain ⟨rest, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    obtain ⟨info, rfl, firstRow⟩ := row input first produced
    obtain ⟨infos, rfl, restRows⟩ := ih remaining
    exact ⟨info :: infos, rfl, .cons firstRow restRows⟩

theorem layout_of_accepted {values : ValuesContext} {node : ExpressionNode} {base : TypeSystem.Ty}
    {context : SourceSemantics.Context} {index : Nat} {result : Ty} {identity : DataTypeId} {branches : List Expr}
    (signatures : context.signatures = values.checked.signatures)
    (projection : UniformMemberProjection context base index node.type)
    (projected : SourceCoreCompatibleDataExpressions.projectType values.checked (.occurrence node.id.occurrence) node.type = .ok result)
    (accepted : SourceCoreCompatibleDataExpressions.memberBranches values node base result index = .ok (identity, branches)) :
    Layout values.checked (.occurrence node.id.occurrence) base node.type index identity branches result := by
  unfold SourceCoreCompatibleDataExpressions.memberBranches at accepted
  cases nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType base) with
  | none => simp [nominal, throw, bind, Except.bind] at accepted
  | some pair =>
    rcases pair with ⟨declaration, arguments⟩
    simp only [nominal, pure, Except.pure, bind, Except.bind] at accepted
    cases selected : values.checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) with
    | nil => simp [selected, throw] at accepted
    | cons signature rest => cases rest with
      | cons => simp [selected, throw] at accepted
      | nil =>
        simp only [selected, bind, Except.bind] at accepted
        have member : signature ∈ values.checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) := by rw [selected]; simp
        have signatureId : signature.id = declaration := by simpa using (List.mem_filter.mp member).2
        subst declaration
        by_cases valid : signature.parameters.length = arguments.length ∧ signature.constructors ≠ []
        · simp only [valid.1, decide_true, List.isEmpty_eq_false_iff.mpr valid.2, Bool.not_false, Bool.and_self, ↓reduceIte,
            pure, Except.pure, bind, Except.bind] at accepted
          cases identityFound : values.checked.catalog.identity? (SourceCoreRawMetadata.runtimeType base) with
          | none => simp [identityFound, throw] at accepted
          | some native =>
            simp only [identityFound, pure, Except.pure, bind, Except.bind] at accepted
            obtain ⟨codes, produced, accepted⟩ := bind_ok accepted
            cases accepted
            obtain ⟨infos, generated, rows⟩ := rows_of_mapM produced (fun _ _ generated => row_of_accepted generated)
            exact .intro nominal selected
              (rows_certificate identityFound projected (field_views signatures nominal selected projection) rows) generated
        · simp [valid, Bool.and_eq_true, throw] at accepted

/-- Actual child compilation equations, rather than semantic premises. -/
theorem member_of_lower
    {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource} {scope : Scope}
    {id base : ExpressionId} {node baseNode : ExpressionNode} {name : String} {index : Nat}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context}
    (signatures : context.signatures = values.checked.signatures)
    (found : source.lookupExpression? id = some node) (baseFound : source.lookupExpression? base = some baseNode)
    (form : node.form = .member base name index)
    (projection : UniformMemberProjection context baseNode.type index node.type)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id reasonAt = .ok lowered) :
    ∃ identity branches result code,
      lowered = ⟨result, SourceCoreDataExpressions.member identity result branches code.expression⟩ ∧
      Metadata values.checked source id node result ∧ Metadata values.checked source base baseNode code.type ∧
      Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result ∧
      child fuel source scope base reasonAt = .ok code := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨baseRead, baseAccepted, accepted⟩ := bind_ok accepted
  rcases baseRead with ⟨actualBase, baseType⟩
  have baseMetadata := metadata_of_read baseAccepted
  have same := Option.some.inj (baseMetadata.found.symm.trans baseFound)
  subst actualBase
  obtain ⟨layout, generated, accepted⟩ := bind_ok accepted
  rcases layout with ⟨identity, branches⟩
  obtain ⟨success, baseEnsured, accepted⟩ := bind_ok accepted
  cases success
  obtain ⟨code, compiled, accepted⟩ := bind_ok accepted
  obtain ⟨success, childEnsured, accepted⟩ := bind_ok accepted
  cases success
  cases accepted
  have same : baseType = code.type := ensureType_ok childEnsured
  subst baseType
  have layout := layout_of_accepted signatures projection (by
    simpa only [(lookupExpression?_sound found).2] using read_projected readAccepted) generated
  exact ⟨identity, branches, type, code, rfl, metadata, baseMetadata,
    (lookupExpression?_sound found).2 ▸ layout, compiled⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberExtraction
/-! The actual compatible member branch supplies its static tree. Independent
source typing supplies uniform raw fields; child semantics follows from the
tree and is never a hypothesis of accepted-code extraction. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
open Core Frontend SourceInference CompatibleExpressionReads

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

theorem member_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {id base : ExpressionId} {node baseNode : ExpressionNode} {name : String} {index : Nat}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr} {sourceContext : SourceSemantics.Context}
    (signatures : sourceContext.signatures = values.checked.signatures)
    (found : source.lookupExpression? id = some node) (baseFound : source.lookupExpression? base = some baseNode)
    (form : node.form = .member base name index)
    (projection : UniformMemberProjection sourceContext baseNode.type index node.type)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) context source scope id reasonAt = .ok lowered) :
    ∃ identity branches result code,
      lowered = ⟨result, SourceCoreDataExpressions.member identity result branches code.expression⟩ ∧
      Metadata values.checked source id node result ∧ Metadata values.checked source base baseNode code.type ∧
      Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope base reasonAt = .ok code := by
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
        have metadata := metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        simp only [read, form, leafPolicy] at accepted
        unfold SourceCoreCompatibleDataExpressions.leafLowerer at accepted
        simp only [read, bind, Except.bind, form] at accepted
        obtain ⟨identity, branches, result, code, output, metadata, baseMetadata, layout, generated⟩ :=
          member_of_lower signatures found baseFound form projection accepted
        exact ⟨identity, branches, result, code, output, metadata, baseMetadata, layout,
          by simpa only [Nat.min_self] using generated⟩
  · simp [owner, bind, Except.bind] at accepted

theorem tree_of_functions_with_literals
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    (literals : GenericExpressionMeaning.Certificate)
    (literalFactory : CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt literals)
    (unique : NodeOccurrencesUnique source)
    (declarations : ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
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
    refine (fun ⟨tree, sites⟩ => ⟨_, Tree.LiteralSites.fragment tree sites⟩) (CompatibleExpressionConstructors.tree_of_functions_with_literals literals literalFactory unique declarations (constructorValid.restrict (fun _ child => .fragment child)) ?_ ?_ syntaxTree found typed accepted)
    · exact ⟨fun id child => policyFor.special id (.fragment child), fun id child => policyFor.read id (.fragment child), policyFor.lower, policyFor.leaf⟩
    · exact fun id node child => coercions id node (.fragment child)
  | @member id original base name index originalFound form child ih =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨baseType, baseTyped, projection⟩ := member_source_types unique originalFound form
        (coercions _ _ (.member originalFound form child) originalFound) typed
      obtain ⟨baseNode, contains, sourceType⟩ := baseTyped.stored_type
      have baseFound := lookupExpression?_complete unique contains
      rw [← sourceType] at baseTyped projection
      obtain ⟨identity, branches, result, code, rfl, metadata, baseMetadata, layout, generated⟩ :=
        member_of_functions signatures originalFound baseFound form projection
          (policyFor.special _ (.member originalFound form child))
          (policyFor.read _ (.member originalFound form child)) policyFor.leaf accepted
      obtain ⟨acceptedChild1, acceptedChild1Sites⟩ := ih baseFound baseTyped generated
      exact ⟨_, .member metadata baseMetadata form layout acceptedChild1 acceptedChild1Sites⟩

/-- Original tree-only API, projected from the single supported extraction. -/
theorem tree_of_functions_with_validity
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
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
    CompatibleExpressionProducts.LiteralFactory.ordinary unique declarations signatures constructorValid policyFor coercions syntaxTree found typed accepted).choose

/-- Compatibility with the former false residual scope. -/
theorem tree_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
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
    (sourceContext := sourceContext) (unique := unique) (declarations := declarations) (signatures := signatures)
    (constructorValid := CompatibleExpressionInstantiationLaws.ConstructorLaw.of_closed closed residual)
    (policyFor := policyFor) (coercions := coercions) (id := id) (syntaxTree := syntaxTree) (node := node)
    (found := found) (typed := typed) (fuel := fuel) (lowered := lowered) (accepted := accepted)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualMembers
/-! The actual contextual dispatcher supplies the ordinary recursive-member policy.
Static occurrence metadata excludes local specialization and output coercions.
The final receipt contains no child lowering or runtime execution hypothesis. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
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
  | fragment old =>
    cases old with
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
              have localBinder := ordinary.localBinder _ _ _ _ (.fragment (.fragment (.primitive (.product (.read found form))))) found form
              simp only [SourceCoreGeneralFunctions.contextualSource, found, form, localBinder, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
            | group found form child => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
            | pair found form first second => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
          | unary found form child | binary found form first second | group found form child | pair found form first second =>
            simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
        | unary found form child | binary found form first second | group found form child | pair found form first second | conditional found form _ _ _ =>
          simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

      | constructor found form _ =>
        simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
  | member found form _ =>
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
  | fragment old =>
    cases old with
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
  | member originalFound form _ =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
      CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

private theorem fragment_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : Syntax source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases syntaxTree with
  | fragment old =>
    cases old with
      | fragment child =>
        cases child with
        | primitive syntaxTree =>
          cases syntaxTree with
          | product child => cases child <;> exact ⟨_, by assumption⟩
          | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ => exact ⟨_, found⟩
        | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ | conditional found _ _ _ _ => exact ⟨_, found⟩

      | constructor found _ _ => exact ⟨_, found⟩
  | member found _ _ => exact ⟨_, found⟩

private theorem context_bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Finite member trees are extracted from the production
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
    (sourceSignatures : sourceContext.signatures = values.checked.signatures)
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
      refine tree_of_functions unique declarations sourceSignatures closed residual ?_ ordinary.coercions syntaxTree found typed accepted
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
      refine tree_of_functions unique declarations sourceSignatures closed residual ?_ ordinary.coercions syntaxTree found typed generated
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

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexLookup
/-! Scalar-key index helpers use the real generated comparator. No callable
identity law is needed for Bool, Word, or Integer keys. Administrative closures
are typed using the full actual environment and actual ambient definitions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend CompatiblePayload CompatibleMapping CompatibleEquality DataEquality
open GeneralHeap ReadOnly CompatibleExpressionPrimitives

inductive Scalar : Ty → Prop where
  | bool : Scalar .bool
  | word : Scalar .word
  | integer : Scalar .integer

private def noIdentities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem noIdentities_faithful : IdentityFaithful noIdentities :=
  ⟨fun impossible => False.elim impossible, fun impossible => False.elim impossible⟩

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

theorem Scalar.observation {type : Ty} (scalar : Scalar type)
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    Observation checked.catalog registry noIdentities type source value := by
  cases scalar with
  | bool => obtain ⟨value, rfl, rfl⟩ := bool_fields related; exact .bool value
  | word => obtain ⟨value, rfl, rfl⟩ := word_fields related; exact .word value
  | integer => obtain ⟨value, rfl, rfl⟩ := integer_fields related; exact .integer value

private theorem scalar_entries (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {keyType valueType : Ty} (scalar : Scalar keyType) (projected : keyType = prepared.type)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)} {entries : OrderedMapping.Entries}
    (related : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType) :
    CoreLowering.OrderedMapping.EntriesRel (CompatibleMappingComparison.KeyRep prepared registry noIdentities)
      (Payload registry functions mapping world sourceValue valueType) sources entries := by
  subst keyType
  induction sources generalizing entries with
  | nil => cases related; exact .nil
  | cons head tail ih => cases related with
    | entry key value rest => exact .cons (scalar.observation key) value (ih rest)

/-- Total finite lookup from scalar key receipts, using actual prepared code. -/
theorem lookup_meaning (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {layout : Core.OrderedMapping.Layout} (scalar : Scalar layout.keyType) (keyType : layout.keyType = prepared.type)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (missingBase : Word) (mappingExpression keyExpression : Expr)
    (mappingSelected : Selects environment mappingExpression (Transport.carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) :
    ∃ result, ReadResult checked registry functions mapping world sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      Evaluates environment store (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression mappingExpression keyExpression) result
        (Transport.lookupStore prepared layout environment store header fallback entries key) := by
  obtain ⟨equal, correct⟩ := CompatibleMappingComparison.exists_predicate_correct prepared registry noIdentities_faithful
  have fullCorrect : CoreLowering.OrderedMapping.KeyEqualityCorrect (Payload registry functions mapping world sourceKey layout.keyType) equal := by
    refine ⟨fun left right => correct.equivalent ?_ ?_⟩
    · simpa only [keyType] using scalar.observation left
    · simpa only [keyType] using scalar.observation right
  have observed : CompatibleMappingComparison.KeyRep prepared registry noIdentities sourceLookup key := by
    simpa only [keyType] using scalar.observation keyRep
  have evaluated := Transport.lookup_evaluates prepared layout keyType noIdentities_faithful equal correct observed
    (scalar_entries prepared scalar keyType fields.stored) environment store missingBase header fallback
    mappingExpression keyExpression mappingSelected keySelected
  obtain ⟨found, sourceLookup⟩ := lookup_total sourceLookup sources
  cases sourceLookup with
  | found found =>
    obtain ⟨value, located, represented⟩ := lookup_preserves fullCorrect keyRep fields.stored found
    exact ⟨_, .found found represented, by simpa only [located, SourceCoreMappingWithDefault.selectedValue, Option.or] using evaluated⟩
  | absent absent =>
    have missing := CoreLowering.OrderedMapping.absent_related fullCorrect keyRep (entries_related fields.stored) absent
    rw [missing] at evaluated
    cases fields.default with
    | absent noDefault projected wf => exact ⟨_, .missing absent noDefault, evaluated⟩
    | present defaulted represented => exact ⟨_, .default absent defaulted represented, evaluated⟩

theorem extend_read_result {sourceValue : TypeSystem.Ty} {sourceLookup : Dynamic.Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {type : Ty} {missingBase header : Word} {result : Value}
    (related : ReadResult checked registry functions mapping world sourceValue sourceLookup sources type missingBase header result)
    {futureWorld : StoreTyping} (extension : WorldExtends world futureWorld) :
    ReadResult checked registry functions mapping futureWorld sourceValue sourceLookup sources type missingBase header result := by
  cases related with
  | found selected represented => exact .found selected (represented.extend (.refl _) (.refl _) extension)
  | default absent defaulted represented => exact .default absent defaulted (represented.extend (.refl _) (.refl _) extension)
  | missing absent unavailable => exact .missing absent unavailable

private theorem closed_hasType {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) (context : Core.Context) : HasType context expression type definitions := by
  have extended := typed.rename (mapping := Renaming.id) (target := context) (by intro index type found; cases found)
  simpa using extended

/-- Comparator closure allocations preserve the source heap and every existing
administrative cell. The captured actual slots must all be typed. -/
theorem lookup_preserves_heap (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {layout : Core.OrderedMapping.Layout} (scalar : Scalar layout.keyType) (keyType : layout.keyType = prepared.type)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    {environment : Environment} {context : Core.Context} {heap : Dynamic.Heap} {store : Store}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world heap store)
    (missingBase : Word) :
    ∃ result finalStore futureWorld,
      ReadResult checked registry functions mapping futureWorld sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      Evaluates (key :: Transport.carrier header fallback layout entries :: environment) store
        (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression (.var 1) (.var 0)) result finalStore ∧
      CompatibleAmbientHeap.HeapRepresents checked registry functions mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore := by
  obtain ⟨result, meaning, evaluated⟩ := lookup_meaning prepared scalar keyType fields keyRep
    (key :: Transport.carrier header fallback layout entries :: environment) store missingBase (.var 1) (.var 0) (.var rfl) (.var rfl)
  have nativeTyped := fields.represents.runtime_hasType
  have actualTyped := RuntimeEnvironmentHasTypes.cons keyRep.runtime_hasType (.cons nativeTyped environmentTyped)
  have helperTyped : HasType (layout.keyType :: SourceCoreMappingWithDefault.type layout :: context)
      (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression (.var 1) (.var 0))
      (LanguageResult.resultType layout.valueType) ambient.definitions := by
    apply SourceCoreMappingWithDefault.lookup_hasType missingBase (fields.registered.extend_definitions ambient.basePrefix)
    · simpa only [Core.OrderedMapping.Layout.comparisonType, SourceCoreCompatibleDataEquality.comparatorType, SourceCoreDataEquality.comparatorType, keyType] using closed_hasType (prepared.typed.extend_definitions ambient.basePrefix) _
    · exact .var rfl
    · exact .var rfl
  obtain ⟨suffix, appended, _⟩ := Transport.lookupStore_extension prepared layout
    (key :: Transport.carrier header fallback layout entries :: environment) store header fallback entries key
  obtain ⟨futureWorld, extension, futureHeaps, resultTyped, unchanged⟩ :=
    DataMappingHeap.evaluation_preserves_frame heaps actualTyped helperTyped evaluated appended
  exact ⟨result, _, futureWorld, extend_read_result meaning extension, evaluated, futureHeaps, extension, unchanged⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexSource
/-! Independent index traces retain base-before-key evaluation, exact raw
mapping headers and default availability. The scalar restriction is static;
it does not identify source metadata using equal native representations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMapping
open CompatibleExpressionReads CompatibleExpressionPrimitives

inductive SourceScalar : TypeSystem.Ty → Prop where
  | bool : SourceScalar .bool
  | word : SourceScalar .word
  | integer : SourceScalar .integer

theorem SourceScalar.projected {checked : SourceCoreCompatibleCatalog.Checked} {sourceType : TypeSystem.Ty} {type : Ty}
    (scalar : SourceScalar sourceType) (projected : checked.catalog.project sourceType = .ok type) : Scalar type := by
  cases scalar <;> cases projected
  · exact .bool
  · exact .word
  · exact .integer

theorem source_mapping {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world expected source value type) :
    ∀ {key result}, SourceCoreRawMetadata.runtimeType expected = .mapping key result →
      ∃ sourceKey sourceValue sources, source = .mapping sourceKey sourceValue sources := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | function | proxy => intro _ _ impossible; cases impossible
  | constructed metadata =>
    intro key result view
    have facts := CompatibleConstructorMetadata.facts metadata.authenticated
    cases facts with
    | mk signature constructor arguments _ _ _ _ _ resultType =>
      rw [resultType, CompatibleConstructorMetadata.runtimeType_nominal] at view
      have impossible := congrArg SourceCoreDataCatalog.nominalParts view
      simp only [DataPatternAuthenticity.nominalParts_nominal, SourceCoreDataCatalog.nominalParts, reduceCtorEq] at impossible
  | mappingValue => intro _ _ _; exact ⟨_, _, _, rfl⟩
  | compatible same _ ih => intro _ _ view; exact ih (by rw [← same]; exact view)
  | nil | cons | empty | entry | absent | present => trivial

inductive SourceIndex (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap) (base key : ExpressionId) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | found {sourceKey sourceValue entries lookup value middle after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key lookup after)
      (located : Dynamic.MappingLookup lookup entries value) :
      SourceIndex program context evidence source environment before base key (.value value) after
  | default {sourceKey sourceValue entries lookup value middle after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key lookup after)
      (absent : Dynamic.MappingAbsent lookup entries) (defaulted : Dynamic.DefaultValue sourceValue value) :
      SourceIndex program context evidence source environment before base key (.value value) after
  | baseFailure {reason after}
      (failed : Dynamic.ExpressionFaults program context evidence source environment before base reason after) :
      SourceIndex program context evidence source environment before base key (.fault reason) after
  | keyFailure {baseValue reason middle after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseValue middle)
      (failed : Dynamic.ExpressionFaults program context evidence source environment middle key reason after) :
      SourceIndex program context evidence source environment before base key (.fault reason) after
  | shape {baseValue lookup middle after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseValue middle)
      (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key lookup after)
      (invalid : ¬ Dynamic.MappingValue baseValue) :
      SourceIndex program context evidence source environment before base key (.fault .invalidProjection) after
  | keyType {sourceKey sourceValue entries lookup actual middle after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key lookup after)
      (typed : Dynamic.ValueRuntimeType lookup actual)
      (mismatch : Dynamic.runtimeType actual ≠ Dynamic.runtimeType sourceKey) :
      SourceIndex program context evidence source environment before base key (.fault (.typeMismatch sourceKey (Dynamic.runtimeType actual))) after
  | unavailable {sourceKey sourceValue entries lookup middle after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key lookup after)
      (typed : Dynamic.ValueRuntimeTypeMatches lookup sourceKey)
      (absent : Dynamic.MappingAbsent lookup entries) (missing : ¬ Dynamic.Defaultable sourceValue) :
      SourceIndex program context evidence source environment before base key (.fault (.missingMappingDefault sourceValue)) after

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id base key : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome}

theorem index_inv (metadata : CompatibleExpressionReads.Metadata checked source id node type)
    (form : node.form = .index base key) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    SourceIndex program context evidence source environment before base key outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | indexFound _ base key found => exact .found base key found
    | indexDefault _ base key absent defaulted => exact .default base key absent defaulted
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | indexBase _ failed => exact .baseFailure failed
    | indexKey _ base failed => exact .keyFailure base failed
    | indexShape _ base key shape => exact .shape base key shape
    | indexKeyType _ base key typed mismatch => exact .keyType base key typed mismatch
    | indexDefaultUnavailable _ base key typed absent missing => exact .unavailable base key typed absent missing

theorem index_intro (metadata : CompatibleExpressionReads.Metadata checked source id node type) (form : node.form = .index base key)
    (trace : SourceIndex program context evidence source environment before base key outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | found base key found =>
    apply Dynamic.ExpressionEvaluatesOutcome.value; apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]; exact .indexFound rfl base key found
    · rw [metadata.coercions]; exact .nil
  | default base key absent defaulted =>
    apply Dynamic.ExpressionEvaluatesOutcome.value; apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]; exact .indexDefault rfl base key absent defaulted
    · rw [metadata.coercions]; exact .nil
  | baseFailure failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault; apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]; exact .indexBase rfl failed
  | keyFailure base failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault; apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]; exact .indexKey rfl base failed
  | shape base key shape =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault; apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]; exact .indexShape rfl base key shape
  | keyType base key typed mismatch =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault; apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]; exact .indexKeyType rfl base key typed mismatch
  | unavailable base key typed absent missing =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault; apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]; exact .indexDefaultUnavailable rfl base key typed absent missing

theorem index_source_types (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .index base key) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ keyType, ExpressionHasType source context base (.mapping keyType node.type) ∧ ExpressionHasType source context key keyType := by
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
    | index baseTyped keyTyped => exact ⟨_, baseTyped, keyTyped⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexCertificates
/-! Successful index lowering retains the real prepared comparator and exact
child compilation equations. These static receipts contain no child execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference CompatibleExpressionReads CompatibleMapping
open CompatibleEncoding (bind_ok mapError_ok)
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Child := SourceCoreFunctions.ExpressionLowerer

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked

structure Header (values : ValuesContext) (source : TypedSource) (id base : ExpressionId)
    (node baseNode : ExpressionNode) (layout : Core.OrderedMapping.Layout)
    (comparison : SourceCoreCompatibleDataEquality.Prepared values.checked)
    (first second : SourceCoreBasic.LoweredExpr) : Prop where
  metadata : CompatibleExpressionReads.Metadata values.checked source id node layout.valueType
  baseMetadata : CompatibleExpressionReads.Metadata values.checked source base baseNode first.type
  baseType : first.type = SourceCoreMappingWithDefault.type layout
  keyType : second.type = layout.keyType
  registered : layout.Registered values.checked.catalog.definitions
  comparisonType : layout.keyType = comparison.type
  generated : ∃ key value budget,
    SourceCoreRawMetadata.runtimeType baseNode.type = .mapping key value ∧
    values.checked.catalog.mappingLayout key value = .ok layout ∧
    SourceCoreCompatibleDataEquality.prepare budget values.checked key = .ok comparison

theorem index_of_lower {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource} {scope : Scope}
    {id base key : ExpressionId} {node baseNode : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (baseFound : source.lookupExpression? base = some baseNode)
    (form : node.form = .index base key)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id reasonAt = .ok lowered) :
    ∃ layout comparison first second,
      lowered = ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)⟩ ∧
      Header values source id base node baseNode layout comparison first second ∧
      child fuel source scope base reasonAt = .ok first ∧ child fuel source scope key reasonAt = .ok second := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨baseRead, baseAccepted, accepted⟩ := bind_ok accepted
  rcases baseRead with ⟨actualBase, baseType⟩
  have baseMetadata := metadata_of_read baseAccepted
  have same := Option.some.inj (baseMetadata.found.symm.trans baseFound)
  subst actualBase
  cases mappingType : SourceCoreRawMetadata.runtimeType baseNode.type <;>
    simp only [mappingType, pure, Except.pure, bind, Except.bind] at accepted
  all_goals try cases accepted
  rename_i sourceKey sourceValue
  obtain ⟨layout, selected, accepted⟩ := bind_ok accepted
  have selected := mapError_ok selected
  obtain ⟨success, resultEnsured, accepted⟩ := bind_ok accepted
  cases success
  have resultType := ensureType_ok resultEnsured
  obtain ⟨success, baseEnsured, accepted⟩ := bind_ok accepted
  cases success
  have baseTypeEq : baseType = SourceCoreMappingWithDefault.type layout := ensureType_ok baseEnsured
  obtain ⟨first, firstGenerated, accepted⟩ := bind_ok accepted
  obtain ⟨second, secondGenerated, accepted⟩ := bind_ok accepted
  obtain ⟨success, firstEnsured, accepted⟩ := bind_ok accepted
  cases success
  have firstType : baseType = first.type := ensureType_ok firstEnsured
  obtain ⟨success, secondEnsured, accepted⟩ := bind_ok accepted
  cases success
  have secondType := ensureType_ok secondEnsured
  obtain ⟨comparison, comparisonGenerated, accepted⟩ := bind_ok accepted
  have comparisonGenerated := mapError_ok comparisonGenerated
  cases accepted
  have facts := CompatibleEncoding.mappingLayout_facts selected
  have comparisonProjection := comparison.projection
  rw [comparison_sourceType comparisonGenerated] at comparisonProjection
  refine ⟨layout, comparison, first, second, ?_, ?_, firstGenerated, secondGenerated⟩
  · cases resultType; rfl
  · exact ⟨resultType ▸ metadata, firstType ▸ baseMetadata, firstType.symm.trans baseTypeEq,
      secondType.symm, facts.2.2.2, Except.ok.inj (facts.2.1.symm.trans comparisonProjection),
      ⟨sourceKey, sourceValue, fuel, mappingType, selected, comparisonGenerated⟩⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexFaultPolicies
/-! The unavailable mapping branch retains its actual raw Fields,
metadata header and Source runtime views. Source index occurrence membership
is supplied by the real upper Tree constructor, not recovered from layout. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMapping

/-- This receipt is constructed only at the actual unavailable lookup branch.
It keeps the whole raw mapping representation and exact absent key. -/
structure MissingWitness {values : ValuesContext} {source : TypedSource}
    {id base : ExpressionId} {node baseNode keyNode : ExpressionNode}
    {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping)
    (baseSource keySource : Dynamic.Value) (baseValue : Value)
    (rawKey rawValue : TypeSystem.Ty) (sources : List (Dynamic.Value × Dynamic.Value))
    (tag : Word) (entries : Core.OrderedMapping.Entries) (fallback : Option Value) : Prop where
  contains : ContainsExpression source id node
  baseContains : ContainsExpression source base baseNode
  sourceType : baseNode.type = .mapping keyNode.type node.type
  baseShape : baseSource = .mapping rawKey rawValue sources
  nativeShape : baseValue = Transport.carrier tag fallback layout entries
  keyView : SourceCoreRawMetadata.runtimeType keyNode.type = SourceCoreRawMetadata.runtimeType rawKey
  valueView : SourceCoreRawMetadata.runtimeType node.type = SourceCoreRawMetadata.runtimeType rawValue
  fields : Fields values.checked registry functions mapping world rawKey rawValue sources tag layout entries fallback
  keyTyped : Dynamic.ValueRuntimeTypeMatches keySource rawKey
  absent : Dynamic.MappingAbsent keySource sources
  unavailable : ¬ Dynamic.Defaultable rawValue

/-- This policy is called with the Fields extracted from the actual represented
mapping. It asks for no relation on unrelated registered mapping types. -/
def MissingPolicy {values : ValuesContext} {source : TypedSource}
    {id base : ExpressionId} {node baseNode keyNode : ExpressionNode}
    {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping)
    (baseSource keySource : Dynamic.Value) (baseValue : Value)
    (reason : Word) (faults : Dynamic.SemanticFault → Word → Prop) : Prop :=
  ∀ rawKey rawValue sources tag entries fallback,
    MissingWitness (keyNode := keyNode) (registry := registry) header functions mapping world baseSource keySource baseValue
      rawKey rawValue sources tag entries fallback →
    faults (.missingMappingDefault rawValue) (reason.add tag)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexTree
/-! Index chains over the certified member fragment. Original scalar key
metadata and raw mapping result types remain explicit static facts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | fragment {id} (tree : CompatibleExpressionMembers.Syntax source id) : Syntax source id
  | index {id node base key keyNode} (found : source.lookupExpression? id = some node)
      (form : node.form = .index base key) (keyFound : source.lookupExpression? key = some keyNode)
      (scalar : SourceScalar keyNode.type) (first : Syntax source base) (second : Syntax source key) : Syntax source id

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | fragment {id lowered}
      (tree : CompatibleExpressionMembers.Tree fuel values source context solved reasonAt scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | index {id node base key baseNode keyNode layout comparison first second}
      (header : Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (scalar : SourceScalar keyNode.type)
      (firstTree : Tree fuel values source context solved reasonAt scope base first)
      (secondTree : Tree fuel values source context solved reasonAt scope key second) :
      Tree fuel values source context solved reasonAt scope id
        ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)⟩

theorem Header.scalar {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type) (scalar : SourceScalar keyNode.type) : Scalar layout.keyType := by
  obtain ⟨key, value, fuel, view, selected, generated⟩ := header.generated
  rw [sourceType] at view
  have shape : SourceCoreRawMetadata.runtimeType keyNode.type = key := (TypeSystem.Ty.mapping.inj view).1
  have projected := (CompatibleEncoding.mappingLayout_facts selected).2.1
  rw [← shape, SourceCoreCompatibleCatalog.Catalog.project_runtimeType] at projected
  exact scalar.projected projected

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexExecution
/-! Exact index helper syntax and scalar source key guards. The native helper
may allocate administrative closures; all payload metadata remains source-owned. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping
open CompatibleExpressionPrimitives

private theorem lift_weaken (expression : Expr) (ξ : Renaming) :
    (expression.weakenAt 0).rename ξ.lift = (expression.rename ξ).weakenAt 0 := by
  rw [← Expr.rename_insertion, Expr.rename_comp, Renaming.lift_comp_insertion_zero,
    ← Expr.rename_comp, Expr.rename_insertion]

private theorem lookup_rename {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleDataEquality.Prepared checked) {layout : Core.OrderedMapping.Layout}
    (registered : layout.Registered checked.catalog.definitions) (keyType : layout.keyType = prepared.type)
    (reason : Word) (ξ : Renaming) :
    (SourceCoreMappingWithDefault.lookup layout reason prepared.expression (.var 1) (.var 0)).rename ξ.lift.lift =
      SourceCoreMappingWithDefault.lookup layout reason prepared.expression (.var 1) (.var 0) := by
  have comparator := prepared.typed.rename (mapping := Renaming.id)
    (target := [layout.keyType, SourceCoreMappingWithDefault.type layout]) (by intro index type found; cases found)
  simp only [Expr.rename_id] at comparator
  have typed : HasType [layout.keyType, SourceCoreMappingWithDefault.type layout]
      (SourceCoreMappingWithDefault.lookup layout reason prepared.expression (.var 1) (.var 0))
      (LanguageResult.resultType layout.valueType) checked.catalog.definitions := by
    apply SourceCoreMappingWithDefault.lookup_hasType reason registered
    · simpa only [Core.OrderedMapping.Layout.comparisonType, SourceCoreCompatibleDataEquality.comparatorType,
        SourceCoreDataEquality.comparatorType, keyType] using comparator
    · exact .var rfl
    · exact .var rfl
  have same := CoreProof.typed_rename_agree typed (left := ξ.lift.lift) (right := Renaming.id) (by
    intro index bound
    have small : index < 2 := bound
    cases index with
    | zero => rfl
    | succ index => cases index with
      | zero => rfl
      | succ index => omega)
  simpa only [Expr.rename_id] using same

theorem index_rename {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleDataEquality.Prepared checked) {layout : Core.OrderedMapping.Layout}
    (registered : layout.Registered checked.catalog.definitions) (keyType : layout.keyType = prepared.type)
    (base key : Expr) (reason : Word) (ξ : Renaming) :
    (SourceCoreCompatibleDataExpressions.index layout prepared.expression base key reason).rename ξ =
      SourceCoreCompatibleDataExpressions.index layout prepared.expression (base.rename ξ) (key.rename ξ) reason := by
  simp only [SourceCoreCompatibleDataExpressions.index, CompatibleMapping.Transport.expression_weaken,
    LanguageResult.bind, Expr.rename, Renaming.lift, lift_weaken]
  exact congrArg (Expr.caseE (base.rename ξ) (.inLeft layout.valueType (.var 0)))
    (congrArg (Expr.caseE ((key.rename ξ).weakenAt 0) (.inLeft layout.valueType (.var 0)))
      (lookup_rename prepared registered keyType reason ξ))

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

theorem SourceScalar.runtime_matches {expected raw : TypeSystem.Ty} (scalar : SourceScalar expected)
    {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world expected source value type)
    (view : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType raw) :
    Dynamic.ValueRuntimeTypeMatches source raw := by
  have projected := related.projection
  cases scalar with
  | bool =>
    cases projected
    obtain ⟨value, rfl, rfl⟩ := bool_fields related
    exact .intro (.bool value) (by simpa only [runtimeType_agrees_metadata] using view)
  | word =>
    cases projected
    obtain ⟨value, rfl, rfl⟩ := word_fields related
    exact .intro (.word value) (by simpa only [runtimeType_agrees_metadata] using view)
  | integer =>
    cases projected
    obtain ⟨value, rfl, rfl⟩ := integer_fields related
    exact .intro (.integer value) (by simpa only [runtimeType_agrees_metadata] using view)

theorem Header.mapping_fields {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {sourceKey sourceValue : TypeSystem.Ty} {entries : List (Dynamic.Value × Dynamic.Value)} {value : Value}
    (represented : ValueRep values.checked registry functions mapping world baseNode.type
      (.mapping sourceKey sourceValue entries) value first.type) :
    ∃ tag nativeEntries fallback,
      value = Transport.carrier tag fallback layout nativeEntries ∧
      SourceCoreRawMetadata.runtimeType keyNode.type = SourceCoreRawMetadata.runtimeType sourceKey ∧
      SourceCoreRawMetadata.runtimeType node.type = SourceCoreRawMetadata.runtimeType sourceValue ∧
      Fields values.checked registry functions mapping world sourceKey sourceValue entries tag layout nativeEntries fallback := by
  obtain ⟨tag, actual, nativeEntries, fallback, valueEq, typeEq, view, fields⟩ := CompatibleMapping.mapping_fields represented rfl
  have same := registered_layout_eq fields.registered header.registered (typeEq.symm.trans header.baseType)
  subst actual
  rw [sourceType] at view
  have views := TypeSystem.Ty.mapping.inj view
  exact ⟨tag, nativeEntries, fallback, valueEq, views.1, views.2, fields⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexTerminal
/-! The source decision after successful base and key effects is compared with
the real ordered mapping helper. Missing defaults retain the raw source type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping

inductive Terminal (base key : Dynamic.Value) : Dynamic.ExpressionOutcome → Prop where
  | found {sourceKey sourceValue entries value} (shape : base = .mapping sourceKey sourceValue entries)
      (located : Dynamic.MappingLookup key entries value) : Terminal base key (.value value)
  | default {sourceKey sourceValue entries value} (shape : base = .mapping sourceKey sourceValue entries)
      (absent : Dynamic.MappingAbsent key entries) (defaulted : Dynamic.DefaultValue sourceValue value) : Terminal base key (.value value)
  | shape (invalid : ¬ Dynamic.MappingValue base) : Terminal base key (.fault .invalidProjection)
  | keyType {sourceKey sourceValue entries actual} (shape : base = .mapping sourceKey sourceValue entries)
      (typed : Dynamic.ValueRuntimeType key actual) (mismatch : Dynamic.runtimeType actual ≠ Dynamic.runtimeType sourceKey) :
      Terminal base key (.fault (.typeMismatch sourceKey (Dynamic.runtimeType actual)))
  | unavailable {sourceKey sourceValue entries} (shape : base = .mapping sourceKey sourceValue entries)
      (typed : Dynamic.ValueRuntimeTypeMatches key sourceKey) (absent : Dynamic.MappingAbsent key entries)
      (missing : ¬ Dynamic.Defaultable sourceValue) : Terminal base key (.fault (.missingMappingDefault sourceValue))

theorem Terminal.functional {sourceKey sourceValue : TypeSystem.Ty} {entries : List (Dynamic.Value × Dynamic.Value)}
    {key : Dynamic.Value} {first second : Dynamic.ExpressionOutcome}
    (typed : Dynamic.ValueRuntimeTypeMatches key sourceKey)
    (left : Terminal (.mapping sourceKey sourceValue entries) key first)
    (right : Terminal (.mapping sourceKey sourceValue entries) key second) : first = second := by
  have mismatchImpossible : ∀ {actual}, Dynamic.ValueRuntimeType key actual →
      Dynamic.runtimeType actual ≠ Dynamic.runtimeType sourceKey → False := by
    intro actual actualTyped mismatch
    cases typed with
    | intro expected same => exact mismatch (actualTyped.functional expected ▸ same)
  cases left with
  | found shape found =>
    cases shape
    cases right with
    | found shape other => cases shape; exact congrArg Dynamic.ExpressionOutcome.value (found.functional other)
    | default shape absent _ | unavailable shape _ absent _ => cases shape; exact (absent.excludes_lookup found).elim
    | shape invalid => exact (invalid .intro).elim
    | keyType shape actual mismatch => cases shape; exact (mismatchImpossible actual mismatch).elim
  | default shape absent defaulted =>
    cases shape
    cases right with
    | found shape found => cases shape; exact (absent.excludes_lookup found).elim
    | default shape _ other => cases shape; exact congrArg Dynamic.ExpressionOutcome.value (defaulted.functional other)
    | unavailable shape _ _ missing => cases shape; exact (missing defaulted.defaultable).elim
    | shape invalid => exact (invalid .intro).elim
    | keyType shape actual mismatch => cases shape; exact (mismatchImpossible actual mismatch).elim
  | unavailable shape _ absent missing =>
    cases shape
    cases right with
    | found shape found => cases shape; exact (absent.excludes_lookup found).elim
    | default shape _ defaulted => cases shape; exact (missing defaulted.defaultable).elim
    | unavailable shape _ _ _ => cases shape; rfl
    | shape invalid => exact (invalid .intro).elim
    | keyType shape actual mismatch => cases shape; exact (mismatchImpossible actual mismatch).elim
  | shape invalid => exact (invalid .intro).elim
  | keyType shape actual mismatch => cases shape; exact (mismatchImpossible actual mismatch).elim

theorem SourceIndex.split {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {base key : ExpressionId}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : SourceIndex program context evidence source environment before base key outcome after) :
    (∃ reason, outcome = .fault reason ∧ Dynamic.ExpressionFaults program context evidence source environment before base reason after) ∨
    (∃ baseValue middle, Dynamic.ExpressionEvaluates program context evidence source environment before base baseValue middle ∧
      ((∃ reason, outcome = .fault reason ∧ Dynamic.ExpressionFaults program context evidence source environment middle key reason after) ∨
       (∃ keyValue, Dynamic.ExpressionEvaluates program context evidence source environment middle key keyValue after ∧ Terminal baseValue keyValue outcome))) := by
  cases trace with
  | baseFailure failed => exact .inl ⟨_, rfl, failed⟩
  | keyFailure base failed => exact .inr ⟨_, _, base, .inl ⟨_, rfl, failed⟩⟩
  | found base key found => exact .inr ⟨_, _, base, .inr ⟨_, key, .found rfl found⟩⟩
  | default base key absent defaulted => exact .inr ⟨_, _, base, .inr ⟨_, key, .default rfl absent defaulted⟩⟩
  | shape base key invalid => exact .inr ⟨_, _, base, .inr ⟨_, key, .shape invalid⟩⟩
  | keyType base key typed mismatch => exact .inr ⟨_, _, base, .inr ⟨_, key, .keyType rfl typed mismatch⟩⟩
  | unavailable base key typed absent missing => exact .inr ⟨_, _, base, .inr ⟨_, key, .unavailable rfl typed absent missing⟩⟩

theorem Terminal.trace {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before middle after : Dynamic.Heap} {base key : ExpressionId}
    {baseValue keyValue : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseValue middle)
    (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key keyValue after)
    (terminal : Terminal baseValue keyValue outcome) :
    SourceIndex program context evidence source environment before base key outcome after := by
  cases terminal with
  | found shape found => cases shape; exact .found baseTrace keyTrace found
  | default shape absent defaulted => cases shape; exact .default baseTrace keyTrace absent defaulted
  | shape invalid => exact .shape baseTrace keyTrace invalid
  | keyType shape typed mismatch => cases shape; exact .keyType baseTrace keyTrace typed mismatch
  | unavailable shape typed absent missing => cases shape; exact .unavailable baseTrace keyTrace typed absent missing

/-- The final helper creates a source decision and typed administrative suffix.
The key guard follows retained raw types and the explicit scalar source profile. -/
theorem Header.finish_with_diagnostics {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type) (scalar : SourceScalar keyNode.type)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {baseSource keySource : Dynamic.Value} {baseValue keyValue : Value}
    (baseRep : ValueRep values.checked registry functions mapping world baseNode.type baseSource baseValue first.type)
    (keyRep : ValueRep values.checked registry functions mapping world keyNode.type keySource keyValue second.type)
    {environment : Environment} {context : Core.Context} {heap : Dynamic.Heap} {store : Store}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (reason : Word) {faults : FunctionCalls.FaultRep}
    (missing : MissingPolicy (keyNode := keyNode) (registry := registry) header functions mapping world
      baseSource keySource baseValue reason faults) :
    ∃ outcome result finalStore futureWorld,
      Terminal baseSource keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result ∧
      Evaluates (keyValue :: baseValue :: environment) store
        (SourceCoreMappingWithDefault.lookup layout reason comparison.expression (.var 1) (.var 0)) result finalStore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      (∀ other, Terminal baseSource keySource other → other = outcome) := by
  obtain ⟨rawKey, rawValue, sources, rfl⟩ := source_mapping baseRep (by rw [sourceType]; rfl)
  obtain ⟨tag, nativeEntries, fallback, rfl, keyView, valueView, fields⟩ := header.mapping_fields sourceType baseRep
  have keyTyped := scalar.runtime_matches keyRep keyView
  have nativeKey : Payload registry functions mapping world rawKey layout.keyType keySource keyValue :=
    .compatible keyView.symm (header.keyType ▸ keyRep)
  obtain ⟨result, finalStore, futureWorld, resultMeaning, evaluated, finalHeaps, worlds, frame⟩ :=
    lookup_preserves_heap comparison (header.scalar sourceType scalar) header.comparisonType fields nativeKey environmentTyped heaps reason
  have outcome : ∃ outcome, Terminal (.mapping rawKey rawValue sources) keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result := by
    cases resultMeaning with
    | found located represented => exact ⟨_, .found rfl located, .value (.compatible valueView represented)⟩
    | default absent defaulted represented => exact ⟨_, .default rfl absent defaulted, .value (.compatible valueView represented)⟩
    | missing absent unavailable => exact ⟨_, .unavailable rfl keyTyped absent unavailable, .fault (missing rawKey rawValue sources tag nativeEntries fallback
        ⟨lookupExpression?_sound header.metadata.found, lookupExpression?_sound header.baseMetadata.found,
          sourceType, rfl, rfl, keyView, valueView, fields, keyTyped, absent, unavailable⟩)⟩
  obtain ⟨outcome, terminal, represented⟩ := outcome
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, evaluated, finalHeaps, worlds, frame,
    fun _ other => other.functional keyTyped terminal⟩

/-- The original uniform inclusion supplies the policy at its actual witness. -/
theorem Header.finish {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type) (scalar : SourceScalar keyNode.type)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {baseSource keySource : Dynamic.Value} {baseValue keyValue : Value}
    (baseRep : ValueRep values.checked registry functions mapping world baseNode.type baseSource baseValue first.type)
    (keyRep : ValueRep values.checked registry functions mapping world keyNode.type keySource keyValue second.type)
    {environment : Environment} {context : Core.Context} {heap : Dynamic.Heap} {store : Store}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (reason : Word) {faults : FunctionCalls.FaultRep}
    (missing : ∀ key value tag, MetadataRep registry (.mapping key value) tag → faults (.missingMappingDefault value) (reason.add tag)) :
    ∃ outcome result finalStore futureWorld,
      Terminal baseSource keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result ∧
      Evaluates (keyValue :: baseValue :: environment) store
        (SourceCoreMappingWithDefault.lookup layout reason comparison.expression (.var 1) (.var 0)) result finalStore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      (∀ other, Terminal baseSource keySource other → other = outcome) := by
  exact header.finish_with_diagnostics sourceType scalar baseRep keyRep environmentTyped heaps reason
    (fun _ _ _ _ _ _ witness => missing _ _ _ witness.fields.metadata)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberNativeTyping
/-! Factory nominal coverage and authenticated emitted rows type the complete
member match. Raw field views determine projection; no native branch typing or
child typing callback is assumed for the recursive member grammar. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberNativeTyping
open Core Frontend SourceInference CompatibleExpressionReads
open CompatibleExpressionMembers CompatibleExpressionScalarNativeTyping
open CompatibleCatalogNominalCoverage
open DataPatternValues
open CompatibleEncoding (bind_ok)

theorem projectPacked_native {definitions : DataEnvironment} {context : Core.Context}
    {types : List Ty} {index : Nat} {type : Ty} {bundle : Expr}
    (found : types[index]? = some type)
    (typed : HasType context bundle (SourceCoreCompatibleCatalog.packTypes types) definitions) :
    HasType context (SourceCoreDataExpressions.projectPacked index types bundle) type definitions := by
  induction types generalizing index bundle with
  | nil => cases found
  | cons head rest ih =>
    cases rest with
    | nil =>
      cases index with
      | zero => cases found; exact typed
      | succ index => simp at found
    | cons next tail =>
      cases index with
      | zero => cases found; exact .first typed
      | succ index =>
        simpa [SourceCoreDataExpressions.projectPacked] using ih (by simpa using found) (HasType.second typed)

private theorem mapM_at {α β ε : Type} {inputs : List α} {outputs : List β}
    {action : α → Except ε β} (accepted : inputs.mapM action = .ok outputs)
    {index : Nat} {input : α} (found : inputs[index]? = some input) :
    ∃ output, outputs[index]? = some output ∧ action input = .ok output := by
  induction inputs generalizing outputs index with
  | nil => cases found
  | cons head rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, produced, accepted⟩ := bind_ok accepted
    obtain ⟨tail, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    cases index with
    | zero => cases found; exact ⟨first, rfl, produced⟩
    | succ index => exact ih remaining found

private theorem projected_list {checked : SourceCoreCompatibleCatalog.Checked}
    {site : SourceCoreElaboration.ErrorSite} {inputs : List TypeSystem.Ty} {outputs : List Ty}
    (accepted : inputs.mapM (SourceCoreCompatibleDataExpressions.projectType checked site) = .ok outputs) :
    inputs.mapM checked.catalog.project = .ok outputs := by
  induction inputs generalizing outputs with
  | nil => simpa using accepted
  | cons head rest ih =>
    rw [List.mapM_cons] at accepted ⊢
    obtain ⟨first, produced, accepted⟩ := bind_ok accepted
    obtain ⟨tail, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    simp [projectType_of_accepted produced, ih remaining, bind, Except.bind, pure, Except.pure]

private theorem relation_at {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (related : ListRel relation inputs outputs) {index : Nat} {output : β}
    (found : outputs[index]? = some output) : ∃ input, inputs[index]? = some input ∧ relation input output := by
  induction related generalizing index with
  | nil => cases found
  | cons head tail ih =>
    cases index with
    | zero => cases found; exact ⟨_, rfl, head⟩
    | succ index => exact ih found

private theorem relation_length {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (related : ListRel relation inputs outputs) : outputs.length = inputs.length := by
  induction related with
  | nil => rfl
  | cons head tail ih => simpa using ih

private theorem branches_native {definitions : DataEnvironment} {context : Core.Context}
    {payloads : List Ty} {branches : List Expr} {result : Ty}
    (count : branches.length = payloads.length)
    (typed : ∀ (index : Nat) payload branch, payloads[index]? = some payload → branches[index]? = some branch →
      HasType (payload :: context) branch result definitions) :
    BranchesHaveType context result payloads branches definitions := by
  induction payloads generalizing branches with
  | nil =>
    cases branches with
    | nil => exact .nil
    | cons => simp at count
  | cons payload rest ih =>
    cases branches with
    | nil => simp at count
    | cons branch tail =>
      exact .cons (typed 0 payload branch rfl rfl)
        (ih (by simpa using count) (fun index payload branch found generated => typed (index + 1) payload branch found generated))

theorem nominal_project {catalog : SourceCoreCompatibleCatalog.Catalog} {type : TypeSystem.Ty}
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty} {identity : DataTypeId}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (found : catalog.identity? type = some identity) : catalog.project type = .ok (.namedData identity) := by
  cases type <;> try simp [SourceCoreDataCatalog.nominalParts] at nominal
  · rename_i constructor
    cases constructor <;> simp_all [SourceCoreDataCatalog.nominalParts, SourceCoreCompatibleCatalog.Catalog.project]
  · simp [SourceCoreCompatibleCatalog.Catalog.project, found]

private theorem row_native {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {root field : TypeSystem.Ty} {substitution : TypeSystem.ParameterSubstitution}
    {identity : DataTypeId} {index : Nat} {input : ProgramDataConstructorSignature × Nat} {branch : Branch} {result : Ty}
    (row : CompatibleMemberCertificates.Row checked site root field substitution identity index input branch)
    (fieldProjected : SourceCoreCompatibleDataExpressions.projectType checked site field = .ok result) :
    checked.catalog.definitions.lookupConstructorPayloadType? branch.constructor =
        some (.product .word (SourceCoreCompatibleCatalog.packTypes branch.payloadTypes)) ∧
      branch.payloadTypes[index]? = some result := by
  obtain ⟨_, actualTypes, projected, registered⟩ := CompatibleEncoding.resolveConstructor_facts row.authenticated
  have payloads := projected_list row.payloads
  have same := Except.ok.inj (projected.symm.trans payloads)
  subst actualTypes
  obtain ⟨actual, found, view⟩ := row.fieldLookup
  obtain ⟨native, nativeAt, actualProjected⟩ := mapM_at payloads found
  have compatible := CompatibleEncoding.project_compatible (catalog := checked.catalog) view
  have resultProjected := projectType_of_accepted fieldProjected
  rw [compatible, resultProjected] at actualProjected
  cases actualProjected
  exact ⟨registered, nativeAt⟩

theorem layout_native_at {definitions : DataEnvironment}
    {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {base field : TypeSystem.Ty} {index : Nat} {identity : DataTypeId} {branches : List Expr} {result : Ty}
    (extension : checked.catalog.definitions.Extends definitions)
    (layout : Layout checked site base field index identity branches result)
    (shaped : Shapes checked.signatures checked.catalog) (complete : Complete checked.catalog)
    {context : Core.Context} {child : Expr}
    (childTyped : HasType context child (LanguageResult.resultType (.namedData identity)) definitions) :
    HasType context (SourceCoreDataExpressions.member identity result branches child)
      (LanguageResult.resultType result) definitions := by
  cases layout with
  | @intro signature arguments infos nominal selected certificate generated =>
    obtain ⟨entry, entryAt, _⟩ := identity_entry certificate.identityLookup
    cases stored : entry.definition with
    | none =>
      have present := complete entry (List.mem_of_getElem? entryAt)
      simp [stored] at present
    | some definition =>
      have registered : checked.catalog.definitions.lookupDataType? identity = some definition := by
        simp [DataEnvironment.lookupDataType?, SourceCoreCompatibleCatalog.Catalog.definitions, List.getElem?_map, entryAt, stored]
      obtain ⟨_, _, _, count⟩ := shaped.nominal_coverage complete
        (by simpa [SourceCoreRawMetadata.runtimeType_idempotent] using nominal) selected certificate.identityLookup registered
      apply SourceCoreDataExpressions.member_hasType (extension.data_lookup registered)
        ((projectType_wellFormed certificate.projectedField).extend_definitions extension) childTyped
      apply branches_native
      · rw [generated, List.length_map, relation_length certificate.rows, List.length_zipIdx, count]
      · intro position payload code payloadAt codeAt
        rw [generated, List.getElem?_map] at codeAt
        cases branchAt : infos[position]? with
        | none => simp [branchAt] at codeAt
        | some branch =>
          simp only [branchAt, Option.map_some, Option.some.injEq] at codeAt
          subst code
          obtain ⟨input, inputAt, row⟩ := relation_at certificate.rows branchAt
          have positionEq : input.2 = position := by
            rw [List.getElem?_zipIdx] at inputAt
            cases constructorAt : signature.constructors[position]? with
            | none => simp [constructorAt] at inputAt
            | some constructor => simp only [constructorAt, Option.map_some, Option.some.injEq] at inputAt; cases inputAt; simp
          obtain ⟨payloadLookup, fieldAt⟩ := row_native row certificate.projectedField
          simp only [row.position, positionEq, DataEnvironment.lookupConstructorPayloadType?, registered,
            bind, Option.bind, payloadAt] at payloadLookup
          have payloadEq := Option.some.inj payloadLookup
          subst payload
          exact LanguageResult.success_hasType (projectPacked_native fieldAt (HasType.second (HasType.var rfl)))

theorem layout_native {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {base field : TypeSystem.Ty} {index : Nat} {identity : DataTypeId} {branches : List Expr} {result : Ty}
    (layout : Layout checked site base field index identity branches result)
    (shaped : Shapes checked.signatures checked.catalog) (complete : Complete checked.catalog)
    {context : Core.Context} {child : Expr}
    (childTyped : HasType context child (LanguageResult.resultType (.namedData identity)) checked.catalog.definitions) :
    HasType context (SourceCoreDataExpressions.member identity result branches child)
      (LanguageResult.resultType result) checked.catalog.definitions :=
  layout_native_at (.refl _) layout shaped complete childTyped

theorem child_type {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {base field : TypeSystem.Ty} {index : Nat} {identity : DataTypeId} {branches : List Expr} {result native : Ty}
    (layout : Layout checked site base field index identity branches result)
    (projected : checked.catalog.project base = .ok native) : native = .namedData identity := by
  cases layout with
  | intro nominal selected certificate generated =>
    have named := nominal_project nominal certificate.identityLookup
    rw [SourceCoreCompatibleCatalog.Catalog.project_runtimeType] at named
    exact Except.ok.inj (projected.symm.trans named)

theorem result_wellFormed {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {base field : TypeSystem.Ty} {index : Nat} {identity : DataTypeId} {branches : List Expr} {result : Ty}
    (layout : Layout checked site base field index identity branches result) :
    result.WellFormed checked.catalog.definitions := by
  cases layout with
  | intro nominal selected certificate generated => exact projectType_wellFormed certificate.projectedField

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (shaped : Shapes values.checked.signatures values.checked.catalog) (complete : Complete values.checked.catalog)
  (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope) (administrative : Core.Context)

include shaped complete visibleTypes in
theorem members_native
    (tree : CompatibleExpressionMembers.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact CompatibleExpressionConstructorNativeTyping.constructors_native visibleTypes administrative child
  | member metadata baseMetadata form layout childTree ih =>
    have childType := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← childType]; exact ih.2)⟩

include shaped complete visibleTypes in
theorem members_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionMembers.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := members_native shaped complete visibleTypes administrative tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

include visibleTypes in
theorem contextual_native
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment}
    (ordinary : CompatibleExpressionMembers.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionMembers.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  have shaped := prepare_shapes registered
  rw [← SourceCoreCompatibleCatalog.prepare_signatures registered] at shaped
  exact members_native_at shaped (prepare_complete registered) visibleTypes administrative extension
    (CompatibleExpressionMembers.tree_of_contextual ordinary unique closed residual declarations sourceSignatures syntaxTree found sourceTyped
      readPolicy lowerPolicy leafPolicy accepted)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberNativeTyping
end
