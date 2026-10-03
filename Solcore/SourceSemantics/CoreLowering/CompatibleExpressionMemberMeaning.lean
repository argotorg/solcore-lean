import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberTree

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

include extension unique uninitialized in
theorem preserves_with_literals
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | fragment child treeSites => exact CompatibleExpressionConstructors.preserves_with_literals functions extension program evidence unique uninitialized literalMeaning ⟨child, treeSites⟩
  | @member id node base baseNode name index identity branches result child metadata baseMetadata form layout childTree childTreeSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after environments heaps locals agrees trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have raw := member_inv metadata form unique trace
    cases raw with
    | value childTrace selected =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, sourceChild, native, shape, sourceAt, related, completed⟩ := member_success layout payload evaluated
        cases shape
        have same := at_functional sourceAt selected
        subst sourceChild
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact completed,
          .value related, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | failure childTrace =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact LanguageResult.bind_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
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
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | fragment child treeSites => exact CompatibleExpressionConstructors.reflects_with_literals functions extension program evidence uninitialized literalMeaning ⟨child, treeSites⟩
  | @member id node base baseNode name index identity branches result child metadata baseMetadata form layout childTree childTreeSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [member_rename layout] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure result baseEvaluation (body := .matchData identity (LanguageResult.resultType result) (.var 0) branches)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.failure failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees baseEvaluation
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, selected, native, shape, sourceAt, related, expected⟩ := member_success layout payload baseEvaluation
        subst_vars
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.value childTrace sourceAt), .value related,
            finalHeaps, maps, worlds, frame, heapMetadata⟩

include extension contextValid uninitialized in
theorem reflects :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact reflects_with_literals functions extension program evidence uninitialized
    (CompatibleExpressionLiterals.reflects functions program context evidence contextValid source faults) ⟨tree, tree.literalSites⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
