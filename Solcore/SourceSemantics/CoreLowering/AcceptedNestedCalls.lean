import Solcore.SourceSemantics.CoreLowering.AcceptedCalls

/-!
# Accepted bodies: direct calls inside expressions

Extends the expression closure of named-row bodies to direct calls at every
expression position: inside operators, conditionals, groups and pairs, and as
the arguments of other direct calls. Closes a family of such rows by one strong
induction on the grade.

Main declarations:
- `CellAwareInvocationAcceptedNestedTrees.Nested`, the sites, and
  `CellAwareInvocationAcceptedNestedTrees.NestedTree`, their receipt trees;
- `CellAwareInvocationAcceptedNestedTrees.of_nested`, the receipt tree from the
  compiler's acceptance;
- `CellAwareInvocationAcceptedNestedBounds.preserves_nested_tree` and
  `CellAwareInvocationAcceptedNestedBounds.reflects_nested_tree`, their meaning;
- `CellAwareInvocationAcceptedNestedExpressions.ClosedNested` and
  `CellAwareInvocationAcceptedNestedExpressions.expressions`, the closure, with
  `CellAwareInvocationAcceptedNestedExpressions.closedNested_of_closedCalls` for
  rows whose calls are at expression roots;
- `CellAwareInvocationAcceptedCallFamily.Row`,
  `CellAwareInvocationAcceptedCallFamily.preserves` and
  `CellAwareInvocationAcceptedCallFamily.reflects`, the family closure;
- `CellAwareInvocationAcceptedNestedCheck.nodes?` and
  `CellAwareInvocationAcceptedNestedCheck.closedNested`, a finite check of the
  nested sites on an actually compiled row.
-/

section
/-! Direct calls inside the expressions of named-row bodies. `Nested` closes
the first subset's forms and direct calls under one another: every operand,
branch and pair element, and every argument of a direct call, is again a
`Nested` site. `NestedTree` keeps the first subset's receipts at its forms and
the direct-call receipts of `CellAwareInvocationAcceptedCallTrees.CallTree` at
its calls. A call's argument receipts are indexed by the pairs of the
arguments and their lowered codes: a receipt tree cannot be the certificate of
the head's argument sequence (`DataExpressionSequence.Tree`) inside its own
definition, so the bounds rebuild that sequence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedTrees
open Core Frontend SourceInference DataPatternValues
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareNamedExpressionSyntax (Site)
open CellAwareInvocationAcceptedExpressionTrees (Subset)
open CellAwareInvocationAcceptedCallTrees (CallSubset)
open CellAwareInvocationAcceptedDirectSites (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt Monomorphic)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port)

/-- Sites of the nested closure: the first subset's forms with nested
children, and direct calls with nested arguments whose instantiation the
caller's family admits. -/
inductive Nested {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (called : DeclarationInstantiation → Prop) : ExpressionId → Prop where
  | literal {id} (site : Site prepared named source id)
      (atomic : CompatibleExpressionLiterals.Atomic site.node.form) : Nested prepared named source called id
  | read {id name binder} (site : Site prepared named source id)
      (form : site.node.form = .reference name (.local binder)) : Nested prepared named source called id
  | unary {id operator operand} (site : Site prepared named source id)
      (form : site.node.form = .unary operator operand)
      (child : Nested prepared named source called operand) : Nested prepared named source called id
  | binary {id operator left right} (site : Site prepared named source id)
      (form : site.node.form = .binary left operator right)
      (first : Nested prepared named source called left) (second : Nested prepared named source called right) :
      Nested prepared named source called id
  | conditional {id condition thenId elseId} (site : Site prepared named source id)
      (form : site.node.form = .conditional condition thenId elseId)
      (test : Nested prepared named source called condition) (yes : Nested prepared named source called thenId)
      (no : Nested prepared named source called elseId) : Nested prepared named source called id
  | group {id inner} (site : Site prepared named source id) (form : site.node.form = .group inner)
      (child : Nested prepared named source called inner) : Nested prepared named source called id
  | pair {id left right} (site : Site prepared named source id) (form : site.node.form = .tuple [left, right])
      (first : Nested prepared named source called left) (second : Nested prepared named source called right) :
      Nested prepared named source called id
  | call {id callee ids instantiation} (site : DirectSite prepared named source id callee ids instantiation)
      (selected : called instantiation)
      (arguments : ∀ argument ∈ ids, Nested prepared named source called argument) :
      Nested prepared named source called id

/-- Static receipts at nested sites. The forms of the first subset keep the
receipts of `CellAwareInvocationAcceptedExpressionTrees.Tree` with nested
children; a call keeps the compiler's direct-call receipt, the authority of the
selected header and the receipt of every argument at its lowered code. -/
inductive NestedTree (whole : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram)))
    (called : DeclarationInstantiation → Prop) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (solved : List SolvedRequirement) (source : TypedSource)
    (sourceContext : SourceSemantics.Context) (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | plain {id lowered}
      (receipt : CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate readFuel
        (.initial whole.compatible.checked) source sourceContext solved reasonAt scope id lowered) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : CompatibleExpressionPrimitives.Metadata whole.compatible.checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode) (type : node.type = innerNode.type)
      (child : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope inner
        lowered) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : CompatibleExpressionPrimitives.Metadata whole.compatible.checked source id node
        (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (type : node.type = .product leftNode.type rightNode.type)
      (leftChild : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope left
        first)
      (rightChild : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope
        right second) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩
  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : CompatibleExpressionPrimitives.Metadata whole.compatible.checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : CompatibleExpressionPrimitives.UnaryProfile operator operandType resultType core)
      (child : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope operand
        ⟨core.operandType, childCode⟩) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨core.resultType, core.lower childCode⟩
  | binary {id node left right leftNode rightNode operator operandType amountType resultType mode leftCode rightCode}
      (metadata : CompatibleExpressionPrimitives.Metadata whole.compatible.checked source id node
        (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = amountType)
      (outputType : node.type = resultType)
      (profile : CompatibleExpressionPrimitives.BinaryProfile operator operandType amountType resultType mode)
      (first : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope left
        ⟨mode.operandType operator, leftCode⟩)
      (second : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope right
        ⟨mode.operandType operator, rightCode⟩) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨mode.resultType operator, mode.binary operator leftCode rightCode⟩
  | conditional {id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      (metadata : CompatibleExpressionPrimitives.Metadata whole.compatible.checked source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (thenFound : source.lookupExpression? thenId = some thenNode)
      (elseFound : source.lookupExpression? elseId = some elseNode)
      (conditionType : conditionNode.type = .bool)
      (thenType : thenNode.type = node.type) (elseType : elseNode.type = node.type)
      (conditionTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope
        condition ⟨.bool, conditionCode⟩)
      (thenTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope thenId
        ⟨type, thenCode⟩)
      (elseTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope elseId
        ⟨type, elseCode⟩) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨type, LocalControl.choose type conditionCode thenCode elseCode⟩
  | call {policy body fuel id callee ids instantiation lowered}
      (receipt : Receipt policy body fuel compilation (.initial whole.compatible.checked) source scope id callee ids
        instantiation reasonAt lowered)
      (port : Port receipt headers)
      (requirements : receipt.node.requirements = [])
      (monomorphic : Monomorphic instantiation)
      (selected : called instantiation)
      (lengths : ids.length = receipt.codes.length)
      (found : ∀ argument ∈ ids, ∃ node, source.lookupExpression? argument = some node)
      (arguments : ∀ argument ∈ ids.zip receipt.codes,
        NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope argument.1
          argument.2) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered

section Embedding
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {called : DeclarationInstantiation → Prop}

/-- Every first-subset site is a nested site. -/
theorem of_subset {id : ExpressionId} (subset : Subset prepared named source id) :
    Nested prepared named source called id := by
  induction subset with
  | literal site atomic => exact .literal site atomic
  | read site form => exact .read site form
  | unary site form _ child => exact .unary site form child
  | binary site form _ _ first second => exact .binary site form first second
  | conditional site form _ _ _ test yes no => exact .conditional site form test yes no
  | group site form _ child => exact .group site form child
  | pair site form _ _ first second => exact .pair site form first second

/-- Every extended root is a nested site. -/
theorem of_call_subset {id : ExpressionId} (subset : CallSubset prepared named source called id) :
    Nested prepared named source called id := by
  cases subset with
  | subset subset => exact of_subset subset
  | call site selected arguments =>
    exact .call site selected (fun argument member => of_subset (arguments argument member))

/-- A nested site is an expression node of its Source. -/
theorem nested_found {id : ExpressionId} (nested : Nested prepared named source called id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases nested with
  | literal site _ | read site _ | unary site _ _ | binary site _ _ _ | conditional site _ _ _ _
  | group site _ _ | pair site _ _ _ => exact ⟨_, site.found⟩
  | call site _ _ => exact ⟨_, site.found⟩

end Embedding

section Projection
variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))}
  {called : DeclarationInstantiation → Prop} {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {solved : List SolvedRequirement} {source : TypedSource} {sourceContext : SourceSemantics.Context}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {lowered : SourceCoreBasic.LoweredExpr}

/-- Every receipt fixes its native type as the projection of its Source type. -/
theorem projected
    (tree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    whole.compatible.checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | plain receipt => exact CompatibleExpressionPrimitives.Tree.projected (.product receipt.1) found
  | group metadata _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | pair metadata _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | unary metadata _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | binary metadata _ _ _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | conditional metadata _ _ _ _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | call receipt _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans receipt.metadata.found)
    exact receipt.metadata.projected

end Projection

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))}
  {called : DeclarationInstantiation → Prop}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : Compilation whole.indexed named diagnostics code) (rootFuel : Nat)
  {source : TypedSource} {sourceContext : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}

private theorem site_special {id : ExpressionId} (site : Site whole.indexed named source id) :
    ∀ child budget, (match (namedPolicy generation rootFuel).lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context whole.indexed named) child budget source scope id reasonAt) = .ok none :=
  fun child budget => CellAwareNamedExpressionPolicies.special generation site rootFuel child budget scope reasonAt

private theorem direct_special {id callee : ExpressionId} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation} (site : DirectSite whole.indexed named source id callee ids instantiation) :
    ∀ child budget, (match (namedPolicy generation rootFuel).lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context whole.indexed named) child budget source scope id reasonAt) = .ok none :=
  fun child budget => CellAwareInvocationAcceptedDirectSites.special generation site rootFuel child budget scope reasonAt

private theorem plain {id : ExpressionId} (site : Site whole.indexed named source id)
    (syntaxTree : CompatibleExpressionProducts.Syntax source id)
    (empty : site.node.form.references = [])
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id site.node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy generation rootFuel)
      (namedLowerBody generation) fuel (context whole.indexed named) source scope id reasonAt = .ok lowered) :
    NestedTree whole headers called (context whole.indexed named) whole.indexed.fuel
      (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope id lowered := by
  have policy : CompatibleExpressionProducts.PolicyOn (namedPolicy generation rootFuel) (context whole.indexed named)
      whole.indexed.fuel (.initial whole.compatible.checked) source scope reasonAt (fun child => child = id) := {
    special := by intro child same _; subst child; exact site_special generation rootFuel site
    read := by intro child same _; subst child; exact CellAwareNamedExpressionPolicies.read generation site rootFuel
    lower := (GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel).lowerRead
    leaf := (GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel).leafLowerer }
  apply NestedTree.plain
  apply CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions_on unique declarations policy
    ?_ ?_ syntaxTree rfl site.found typed accepted
  · intro parent node child same found member
    subst parent
    have sameNode := Option.some.inj (site.found.symm.trans found)
    subst node
    rw [empty] at member
    cases member
  · intro child node same _ found
    subst child
    have sameNode := Option.some.inj (site.found.symm.trans found)
    exact sameNode ▸ site.coercions

private theorem argument_rel {lower : ExpressionId → Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr}
    {relation : ExpressionId → SourceCoreBasic.LoweredExpr → Prop} :
    ∀ {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr},
      (∀ argument ∈ ids, ∀ {lowered}, lower argument = .ok lowered → relation argument lowered) →
      ids.mapM lower = .ok codes → ListRel relation ids codes := by
  intro ids
  induction ids with
  | nil =>
    intro codes _ generated
    simp at generated
    subst codes
    exact .nil
  | cons argument rest ih =>
    intro codes each generated
    cases head : lower argument with
    | error reason => simp [List.mapM_cons, head, bind, Except.bind] at generated
    | ok lowered =>
      cases tail : rest.mapM lower with
      | error reason => simp [List.mapM_cons, head, tail, bind, Except.bind] at generated
      | ok restCodes =>
        simp only [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at generated
        subst codes
        exact .cons (each argument List.mem_cons_self head)
          (ih (fun other member => each other (List.mem_cons_of_mem _ member)) tail)

/-- A pointwise relation of two lists relates them pair by pair along their
zip, which has every pair. -/
theorem zip_of_rel {α β : Type} {relation : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, ListRel relation xs ys →
      xs.length = ys.length ∧ ∀ pair ∈ xs.zip ys, relation pair.1 pair.2 := by
  intro xs ys related
  induction related with
  | nil => exact ⟨rfl, fun _ member => by cases member⟩
  | cons head _ ih =>
    refine ⟨by simp [ih.1], ?_⟩
    intro pair member
    simp only [List.zip_cons_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact head
    · exact ih.2 pair member

/-- The accepted named compiler yields the nested receipt tree at every nested
site. A call's authority is the input `ports`, as for extended roots. -/
theorem of_nested {id : ExpressionId}
    (nested : Nested whole.indexed named source called id)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (ports : ∀ {fuel : Nat} {callScope : SourceCoreLocalCell.Scope} {callId callee : ExpressionId}
      {ids : List ExpressionId} {instantiation : DeclarationInstantiation} {callCode : SourceCoreBasic.LoweredExpr}
      (receipt : Receipt (namedPolicy generation rootFuel) (namedLowerBody generation) fuel
        (context whole.indexed named) (.initial whole.compatible.checked) source callScope callId callee ids
        instantiation reasonAt callCode),
      Nonempty (Port receipt headers))
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy generation rootFuel)
      (namedLowerBody generation) fuel (context whole.indexed named) source scope id reasonAt = .ok lowered) :
    NestedTree whole headers called (context whole.indexed named) whole.indexed.fuel
      (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope id lowered := by
  induction nested generalizing node fuel lowered with
  | literal site atomic =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    exact plain generation rootFuel site (.literal site.found atomic)
      (by generalize form : site.node.form = actual at atomic ⊢; cases atomic <;> rfl) unique declarations typed
      accepted
  | read site form =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    exact plain generation rootFuel site (.read site.found form)
      (by simp [form, ExpressionForm.references]) unique declarations typed accepted
  | unary site form child ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation)
        (context := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (site_special generation rootFuel site) (CellAwareNamedExpressionPolicies.read generation site rootFuel)
        accepted
      cases step with
      | @unary operator operand childCode otherForm metadata generated inputChecked =>
        obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (form.symm.trans otherForm)
        obtain ⟨childNode, core, childFound, childTyped, profile⟩ :=
          CompatibleExpressionPrimitives.unary_source_types unique site.found form metadata.coercions
            metadata.requirements typed
        have childTree := ih childFound childTyped generated
        have lookupEq : _ = some childNode.type := congrArg (Option.map (·.type)) childFound
        have chosen := CompatibleExpressionConditionals.unary_selected profile (projected childTree childFound)
          lookupEq
        rw [chosen] at metadata inputChecked ⊢
        obtain ⟨childType, native⟩ := childCode
        dsimp only at inputChecked childTree ⊢
        subst childType
        exact .unary metadata form childFound rfl rfl profile childTree
      | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | binary site form first second firstIH secondIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation)
        (context := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (site_special generation rootFuel site) (CellAwareNamedExpressionPolicies.read generation site rootFuel)
        accepted
      cases step with
      | @binary operator left right first second otherForm metadata firstGenerated secondGenerated leftChecked
          rightChecked =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, mode, leftFound, rightFound, leftTyped, rightTyped, profile⟩ :=
          CompatibleExpressionPrimitives.binary_source_types unique site.found form metadata.coercions
            metadata.requirements typed
        have firstTree := firstIH leftFound leftTyped firstGenerated
        have secondTree := secondIH rightFound rightTyped secondGenerated
        have lookupEq : _ = some leftNode.type := congrArg (Option.map (·.type)) leftFound
        have chosen := CompatibleExpressionConditionals.binary_selected profile (projected firstTree leftFound)
          lookupEq
        rw [chosen] at metadata leftChecked rightChecked ⊢
        obtain ⟨firstType, leftCode⟩ := first
        obtain ⟨secondType, rightCode⟩ := second
        dsimp only at leftChecked rightChecked firstTree secondTree ⊢
        subst firstType secondType
        exact .binary metadata form leftFound rightFound rfl rfl rfl profile firstTree secondTree
      | unary otherForm _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | conditional site form test yes no testIH thenIH elseIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation)
        (context := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (site_special generation rootFuel site) (CellAwareNamedExpressionPolicies.read generation site rootFuel)
        accepted
      cases step with
      | conditional otherForm metadata testGenerated thenGenerated elseGenerated =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.conditional.inj (form.symm.trans otherForm)
        obtain ⟨testNode, thenNode, elseNode, testFound, thenFound, elseFound,
            testType, thenType, elseType, testTyped, thenTyped, elseTyped⟩ :=
          CompatibleExpressionConditionals.conditional_source_types unique site.found form site.coercions typed
        exact .conditional metadata form testFound thenFound elseFound testType thenType elseType
          (testIH testFound testTyped testGenerated) (thenIH thenFound thenTyped thenGenerated)
          (elseIH elseFound elseTyped elseGenerated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ =>
        simp [form] at otherForm
  | group site form child ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation)
        (context := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (site_special generation rootFuel site) (CellAwareNamedExpressionPolicies.read generation site rootFuel)
        accepted
      cases step with
      | group otherForm metadata generated =>
        cases ExpressionForm.group.inj (form.symm.trans otherForm)
        obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ :=
          CompatibleExpressionProducts.group_source_types unique site.found form site.coercions typed
        exact .group metadata form innerFound sourceType (ih innerFound childTyped generated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | pair site form first second firstIH secondIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation)
        (context := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (site_special generation rootFuel site) (CellAwareNamedExpressionPolicies.read generation site rootFuel)
        accepted
      cases step with
      | pair otherForm metadata firstGenerated secondGenerated =>
        obtain ⟨rfl, rfl⟩ := by simpa using ExpressionForm.tuple.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, leftFound, rightFound, sourceType, leftTyped, rightTyped⟩ :=
          CompatibleExpressionProducts.pair_source_types unique site.found form site.coercions typed
        exact .pair metadata form leftFound rightFound sourceType
          (firstIH leftFound leftTyped firstGenerated) (secondIH rightFound rightTyped secondGenerated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | @call id callee ids instantiation site selected arguments ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedDirectCallCertificates.of_supported
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation) (fuel := fuel)
        (compilation := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found site.form
        ((site.monomorphic.ordinary _).supported) (direct_special generation rootFuel site)
        (CellAwareInvocationAcceptedDirectSites.read generation site rootFuel) accepted
      obtain ⟨port⟩ := ports receipt
      have nodeEq : receipt.node = site.node := Option.some.inj (receipt.metadata.found.symm.trans site.found)
      obtain ⟨_types, _calleeValid, _application, typing⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique site.found site.form
          site.coercions typed
      have relation := argument_rel
        (relation := fun argument lowered => NestedTree whole headers called (context whole.indexed named)
          whole.indexed.fuel (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope
          argument lowered)
        (fun argument member {lowered} generated => by
          obtain ⟨argumentNode, argumentFound⟩ := nested_found (arguments argument member)
          exact ih argument member argumentFound
            (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member
              argumentFound) generated)
        receipt.generated
      obtain ⟨lengths, each⟩ := zip_of_rel relation
      exact .call receipt port (nodeEq ▸ site.requirements) site.monomorphic selected lengths
        (fun argument member => nested_found (arguments argument member)) each

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedTrees
end

section
/-! Meaning of the nested receipt trees. The first subset's forms use their
existing heads with the meaning of their own children, by structural
recursion on the tree; a call uses the direct-call head, with the meaning of
its argument receipts and its evidence from the call's empty requirements. The
application of each admitted callee header below the grade is the input that
the row lemma supplies. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CellAwareInvocationExpressionBounds
open CellAwareInvocationAcceptedNestedTrees (NestedTree)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds (Point)
open DataPatternValues (ListRel)
universe u

private theorem tree_types {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {stored : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree source certificate scope ids stored codes)
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids types) :
    stored = types := by
  induction tree generalizing types with
  | nil => cases typing; rfl
  | single found _generated =>
    cases typing with
    | cons head tail =>
      cases tail
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact congrArg (fun type => [type]) sourceType
  | cons found _generated tail ih =>
    cases typing with
    | cons head rest =>
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [sourceType, ih rest]

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private def Three (scope : SourceCoreLocalCell.Scope) (test yes no : ExpressionId)
    (a b c : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = test ∧ code = a) ∨ (child = yes ∧ code = b) ∨ (child = no ∧ code = c))

/-- The arguments of one call, each at its lowered code. -/
private def Arguments (scope : SourceCoreLocalCell.Scope) (ids : List ExpressionId)
    (codes : List SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ (child, code) ∈ ids.zip codes

private theorem rel_of_zip {α β : Type} {relation : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length → (∀ pair ∈ xs.zip ys, relation pair.1 pair.2) →
      ListRel relation xs ys
  | [], [], _, _ => .nil
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | x :: xs, y :: ys, lengths, each =>
    .cons (each (x, y) (by rw [List.zip_cons_cons]; exact List.mem_cons_self))
      (rel_of_zip (by simpa using lengths)
        (fun pair member => each pair (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ member)))

private theorem arguments_rel {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {codes : List SourceCoreBasic.LoweredExpr} (lengths : ids.length = codes.length)
    (found : ∀ argument ∈ ids, ∃ node, source.lookupExpression? argument = some node) :
    ListRel (fun id code => ∃ node, source.lookupExpression? id = some node ∧ Arguments scope ids codes scope id code)
      ids codes :=
  rel_of_zip lengths fun pair member => by
    obtain ⟨node, nodeFound⟩ := found pair.1 (List.of_mem_zip member).1
    exact ⟨node, nodeFound, rfl, member⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : OwnedKey keys) {compilation : SourceCoreFunctions.Context}
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun current => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix current.scope current.canonical) callerProtocol)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (cache : ∀ {current}, callerProtocol.State current →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled current.mapping current.store)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (faults : RecursiveStageMeaning.FaultRep)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, faults (.semantic (.uninitializedLocation location)) (reasonAt id))
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram)
    registry)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  {called : DeclarationInstantiation → Prop}

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues (model := valueModel) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include callerBridge keyPhysical cache extension sameLedger uninitialized selectedBodies wellFormed runtime covers in
/-- Every nested receipt tree preserves its staged Source execution at every
grade, given the application of every admitted callee header below the
grade. -/
theorem preserves_nested_tree [RecursiveStageMeaning.FaultTokens faults] {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : NestedTree compiled headers called compilation readFuel solved invocation.source context reasonAt scope id
      lowered) :
    ∀ size, (∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
        (keys := keys) valueModel registry faults header size) →
    PreservesAt (attachment := attachment) callerBridge.forgetSlots context valueModel index registry invocation
      (Point scope id lowered) faults size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  induction tree with
  | plain receipt =>
    intro size _ current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationReadProductBounds.preserves callerBridge.forgetSlots functions extension
      GeneralizedLocalDescriptorHeap.ordinary_cells sameLedger runtime.requirements faults
      (semanticFaults := fun reason token => faults (.semantic reason) token) uninitialized
      (fun _ _ proof => proof) unique size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope inner lowered) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationGroups.group_preserves callerBridge.forgetSlots unique size children size (Nat.le_refl _)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope left right first second) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; intro _; exact leftIH childSize below ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; intro _; exact rightIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationPairBounds.pair_preserves callerBridge.forgetSlots unique (product_values functions) size
      children size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope operand ⟨core.operandType, childCode⟩) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.preserves_at_selected callerBridge.forgetSlots functions size size
      (Nat.le_refl _) unique selectedBodies runtime covers children
      (.unary metadata form childFound inputType outputType operatorProfile ⟨rfl, rfl, rfl⟩)
  | @binary id node left right leftNode rightNode operator operandType amountType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH
      rightIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩)
        faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; intro _; exact leftIH childSize below ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; intro _; exact rightIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.preserves_at_selected callerBridge.forgetSlots functions size size
      (Nat.le_refl _) unique selectedBodies runtime covers children
      (.binary metadata form leftFound rightFound leftType rightType outputType operatorProfile
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; intro _; exact testIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; intro _; exact yesIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; intro _; exact noIH childSize below ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.preserves_at_selected callerBridge.forgetSlots functions size size
      (Nat.le_refl _) unique selectedBodies runtime covers children
      (.conditional metadata form testFound yesFound noFound testType yesType noType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩)
  | @call policy body fuel id callee ids instantiation lowered receipt port requirements monomorphic selected
      lengths found arguments ih =>
    intro size applications current child code point node nodeFound typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace
    obtain ⟨currentEq, childEq, codeEq⟩ := point
    subst current child code
    cases Option.some.inj (nodeFound.symm.trans receipt.metadata.found)
    obtain ⟨_sourceTypes, _calleeValid, application, typing⟩ :=
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
        receipt.form receipt.metadata.coercions typed
    have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types receipt port.toReady
      wellFormed runtime.signatures application
    obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children
      (arguments_rel (source := invocation.source) (scope := scope) lengths found)
    have stored := tree_types sequence unique typing
    have ordered := rows.1 ▸ stored ▸ sequence
    have childMeaning : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Arguments scope ids receipt.codes) faults size := by
      intro smaller less current argument argumentCode member _
      obtain ⟨currentEq, member⟩ := member
      subst current
      exact ih (argument, argumentCode) member smaller
        (fun header headerMember headerAdmitted below belowLess =>
          applications header headerMember headerAdmitted below (Nat.lt_trans belowLess less))
        ⟨rfl, rfl, rfl⟩
    have evidenceAt := CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence receipt port
      (monomorphic.ordinary _) requirements context invocation.evidence
    exact CellAwareInvocationAcceptedDirectCalls.preserves owner receipt port evidenceAt callerBridge keyPhysical cache
      valueModel index registry faults unique wellFormed runtime covers size ordered childMeaning
      (applications port.header port.member (port.metadata ▸ selected)) ⟨rfl, rfl, rfl⟩ nodeFound typed
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace

include callerBridge keyPhysical cache extension sameLedger uninitialized selectedBodies wellFormed runtime covers in
/-- Native completion of every nested receipt tree reconstructs its staged
Source execution, given the native application of every admitted callee
header below the grade. -/
theorem reflects_nested_tree [RecursiveStageMeaning.FaultTokens faults] {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : NestedTree compiled headers called compilation readFuel solved invocation.source context reasonAt scope id
      lowered) :
    ∀ size, (∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
        (keys := keys) valueModel registry faults header size) →
    ReflectsAt (attachment := attachment) callerBridge.forgetSlots context valueModel index registry invocation
      (Point scope id lowered) faults size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  induction tree with
  | plain receipt =>
    intro size _ current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationReadProductBounds.reflects callerBridge.forgetSlots functions extension
      GeneralizedLocalDescriptorHeap.ordinary_cells sameLedger runtime.requirements faults
      (semanticFaults := fun reason token => faults (.semantic reason) token) uninitialized
      (fun _ _ proof => proof) unique size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    intro size applications current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationGroups.group_reflects callerBridge.forgetSlots unique size (ih size applications)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope left right first second) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; intro _; exact leftIH childSize below ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; intro _; exact rightIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationPairBounds.pair_reflects callerBridge.forgetSlots unique (product_values functions) size
      children size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope operand ⟨core.operandType, childCode⟩) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.reflects_at_selected callerBridge.forgetSlots functions size size
      (Nat.le_refl _) unique selectedBodies runtime covers children
      (.unary metadata form childFound inputType outputType operatorProfile ⟨rfl, rfl, rfl⟩)
  | @binary id node left right leftNode rightNode operator operandType amountType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH
      rightIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩)
        faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; intro _; exact leftIH childSize below ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; intro _; exact rightIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.reflects_at_selected callerBridge.forgetSlots functions size size
      (Nat.le_refl _) unique selectedBodies runtime covers children
      (.binary metadata form leftFound rightFound leftType rightType outputType operatorProfile
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; intro _; exact testIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; intro _; exact yesIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; intro _; exact noIH childSize below ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.reflects_at_selected callerBridge.forgetSlots functions size size
      (Nat.le_refl _) unique selectedBodies runtime covers children
      (.conditional metadata form testFound yesFound noFound testType yesType noType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩)
  | @call policy body fuel id callee ids instantiation lowered receipt port requirements monomorphic selected
      lengths found arguments ih =>
    intro size applications current child code point node nodeFound typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed
    obtain ⟨currentEq, childEq, codeEq⟩ := point
    subst current child code
    cases Option.some.inj (nodeFound.symm.trans receipt.metadata.found)
    obtain ⟨_sourceTypes, _calleeValid, application, typing⟩ :=
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
        receipt.form receipt.metadata.coercions typed
    have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types receipt port.toReady
      wellFormed runtime.signatures application
    obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children
      (arguments_rel (source := invocation.source) (scope := scope) lengths found)
    have stored := tree_types sequence unique typing
    have ordered := rows.1 ▸ stored ▸ sequence
    have childMeaning : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Arguments scope ids receipt.codes) faults size := by
      intro smaller less current argument argumentCode member _
      obtain ⟨currentEq, member⟩ := member
      subst current
      exact ih (argument, argumentCode) member smaller
        (fun header headerMember headerAdmitted below belowLess =>
          applications header headerMember headerAdmitted below (Nat.lt_trans belowLess less))
        ⟨rfl, rfl, rfl⟩
    have evidenceAt := CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence receipt port
      (monomorphic.ordinary _) requirements context invocation.evidence
    exact CellAwareInvocationAcceptedDirectCalls.reflects owner receipt port evidenceAt callerBridge keyPhysical cache
      valueModel index registry faults unique wellFormed runtime covers size ordered childMeaning
      (applications port.header port.member (port.metadata ▸ selected)) ⟨rfl, rfl, rfl⟩ nodeFound typed
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedBounds
end

section
/-! The expression closure with direct calls at every expression position of a
named-row body. `ClosedNested` states that every expression the compiler
accepts for the body is a nested site. The receipt tree of each accepted
expression is extracted from the compiler's own acceptance and closed by the
nested bounds; the inputs are the call authority of the body's call receipts
and the application of every admitted callee header below the budget, as for
`CellAwareInvocationAcceptedCallExpressions`. A row whose accepted expressions
are extended roots is closed in this sense too (`closedNested_of_closedCalls`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CellAwareInvocationAcceptedTerminals (children)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)
open CellAwareInvocationAcceptedNestedTrees (Nested)
open CellAwareInvocationAcceptedCallExpressions (ClosedCalls Ports)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (Key whole (Program.ofChecked whole.sourceProgram))}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
    .ok named.specialized)
  (called : DeclarationInstantiation → Prop)

/-- The nested sites as a predicate on the actual accepted receipts of the
named row. -/
def Accepted (fuel : Nat) : GenericExpressionMeaning.Certificate :=
  fun scope expression lowered => children (rowIndex generation record) fuel scope expression lowered ∧
    Nested whole.indexed named (CallableIndexedNamedGeneration.source named) called expression

/-- Every expression the compiler accepts for the named row, at any fuel and
scope, is a nested site. -/
def ClosedNested : Prop :=
  ∀ fuel scope expression lowered, children (rowIndex generation record) fuel scope expression lowered →
    Nested whole.indexed named (CallableIndexedNamedGeneration.source named) called expression

/-- A row whose accepted expressions are extended roots is closed with nested
calls. -/
theorem closedNested_of_closedCalls (closed : ClosedCalls generation record called) :
    ClosedNested generation record called :=
  fun fuel scope expression lowered accepted =>
    CellAwareInvocationAcceptedNestedTrees.of_call_subset (closed fuel scope expression lowered accepted)

variable {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (owner : OwnedKey keys) (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

private theorem reads_lowered {fuel : Nat} {context : SourceSemantics.Context}
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults) :
    ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead fuel
        (SourceCoreCompatibleValues.Context.initial whole.compatible.checked)
        invocation.source context (rowIndex generation record).reasonAt scope id lowered →
      ∀ location, faults (.semantic (.uninitializedLocation location))
        ((rowIndex generation record).reasonAt id) := by
  intro scope id lowered receipt location
  obtain ⟨certificate, _type, _binding⟩ := receipt
  exact reads id certificate.node certificate.name certificate.binder
    (sourceEq ▸ certificate.metadata.found) certificate.form location

/-- Every accepted nested site of the named row preserves its staged Source
execution at every grade, given the call authority and the application of
every admitted callee header below the grade. -/
theorem preserves [RecursiveStageMeaning.FaultTokens faults] (fuel : Nat) {context : SourceSemantics.Context}
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram)
      registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context
      (rowIndex generation record).source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (rowIndex generation record).compilation.solvedRequirements)
    (ports : Ports (headers := headers) generation record) (size : Nat)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True) (headers := headers)
        (keys := keys) model registry faults header size) :
    CellAwareInvocationExpressionBounds.PreservesAt (attachment := fun _ _ _ => True)
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots context
      model (rowIndex generation record) registry invocation (Accepted generation record called fuel) faults size := by
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context invocation.source :=
    sourceEq ▸ runtime
  have uninitialized := reads_lowered generation record invocation faults (fuel := whole.indexed.fuel)
    (context := context) sourceEq reads
  intro scope id lowered accepted node found typed mapping world administrative environment canonical
    actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped
    initial admitted authority physical
  obtain ⟨generated, nested⟩ := accepted
  have sourceNamed : invocation.source = CallableIndexedNamedGeneration.source named := sourceEq
  change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
  | succ rootFuel =>
    rw [GeneralizedLocalInitializerCompilation.named_contextual generation record] at generated
    have unique := sourceRuntime.graph.nodeOccurrencesUnique
    rw [sourceNamed] at unique found typed
    have tree := CellAwareInvocationAcceptedNestedTrees.of_nested (headers := headers) generation rootFuel nested
      unique physical.declarations ports found typed generated
    rw [← sourceNamed] at tree found typed
    exact CellAwareInvocationAcceptedNestedBounds.preserves_nested_tree (attachment := fun _ _ _ => True)
      (compilation := CallableIndexedNamedGeneration.context whole.indexed named) owner
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations) keyPhysical
      (fun state => state.physical) functions extension sameLedger faults uninitialized selectedBodies wellFormed
      sourceRuntime covers tree size applications ⟨rfl, rfl, rfl⟩ found typed environments heaps locals agrees
      actualTyped initial admitted authority physical

/-- Every completed native run of an accepted nested site reconstructs an
independent Source grade, outcome and reached heap. -/
theorem reflects [RecursiveStageMeaning.FaultTokens faults] (fuel : Nat) {context : SourceSemantics.Context}
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram)
      registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context
      (rowIndex generation record).source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (rowIndex generation record).compilation.solvedRequirements)
    (ports : Ports (headers := headers) generation record) (size : Nat)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True) (headers := headers)
        (keys := keys) model registry faults header size) :
    CellAwareInvocationExpressionBounds.ReflectsAt (attachment := fun _ _ _ => True)
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots context
      model (rowIndex generation record) registry invocation (Accepted generation record called fuel) faults size := by
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context invocation.source :=
    sourceEq ▸ runtime
  have uninitialized := reads_lowered generation record invocation faults (fuel := whole.indexed.fuel)
    (context := context) sourceEq reads
  intro scope id lowered accepted node found typed mapping world administrative environment canonical
    actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped
    initial admitted authority physical
  obtain ⟨generated, nested⟩ := accepted
  have sourceNamed : invocation.source = CallableIndexedNamedGeneration.source named := sourceEq
  change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
  | succ rootFuel =>
    rw [GeneralizedLocalInitializerCompilation.named_contextual generation record] at generated
    have unique := sourceRuntime.graph.nodeOccurrencesUnique
    rw [sourceNamed] at unique found typed
    have tree := CellAwareInvocationAcceptedNestedTrees.of_nested (headers := headers) generation rootFuel nested
      unique physical.declarations ports found typed generated
    rw [← sourceNamed] at tree found typed
    exact CellAwareInvocationAcceptedNestedBounds.reflects_nested_tree (attachment := fun _ _ _ => True)
      (compilation := CallableIndexedNamedGeneration.context whole.indexed named) owner
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations) keyPhysical
      (fun state => state.physical) functions extension sameLedger faults uninitialized selectedBodies wellFormed
      sourceRuntime covers tree size applications ⟨rfl, rfl, rfl⟩ found typed environments heaps locals agrees
      actualTyped initial admitted authority physical

/-- A named row whose accepted expressions are all nested sites discharges the
accepted-expression input of the statement closure on the slot-retaining
protocol at a budget, given the call authority and the application of every
admitted callee header below the budget. -/
theorem expressions [RecursiveStageMeaning.FaultTokens faults] (closed : ClosedNested generation record called)
    (budget : Nat)
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram)
      registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    (ports : Ports (headers := headers) generation record)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True) (headers := headers)
        (keys := keys) model registry faults header budget ∧
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True) (headers := headers)
        (keys := keys) model registry faults header budget) :
    CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True) (receiving := receiving)
      (functions := functions)
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
      (rowIndex generation record) registry invocation faults budget := by
  intro fuel context runtime covers sameLedger
  refine ⟨?_, ?_⟩
  · intro size smaller scope id lowered generated
    exact preserves generation record called owner keyPhysical registry invocation faults fuel sourceEq extension
      reads selectedBodies wellFormed runtime covers sameLedger ports size
      (fun header member admitted below less => (applications header member admitted).1 below
        (Nat.lt_trans less smaller))
      ⟨generated, closed fuel scope id lowered generated⟩
  · intro size smaller scope id lowered generated
    exact reflects generation record called owner keyPhysical registry invocation faults fuel sourceEq extension
      reads selectedBodies wellFormed runtime covers sameLedger ports size
      (fun header member admitted below less => (applications header member admitted).2 below
        (Nat.lt_trans less smaller))
      ⟨generated, closed fuel scope id lowered generated⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedExpressions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallFamily
/-! The size induction across bodies for direct calls. A family of rows is
given by the instantiations it admits (`called`): every catalog header with an
admitted instantiation has the receipts of a named row whose accepted
expressions are nested sites calling only admitted instantiations (`Row`).
One strong induction on the grade gives the accepted-expression meaning of
every family body on the slot-retaining protocol: at a call of a given grade
the direct-call head needs the callee's application below that grade, and the
row lemma gives it from the callee body's expressions below it. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallFamily
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (Key whole (Program.ofChecked whole.sourceProgram))}

/-- The receipts of one family row, as the public named root takes them, with
the nested closure and call authority of its body and its own registry
scope. -/
structure Row (called : DeclarationInstantiation → Prop)
    (header : Header whole (Program.ofChecked whole.sourceProgram)) where
  named : SourceCoreGeneralFunctions.Function
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  code : Expr
  generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code
  record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized
  sameNamed : header.named = named
  sameLayouts : header.layouts = whole.indexed.layouts
  sameGlobals : header.globals = whole.indexed.base.globals.length
  sameBindings : header.bindings = named.inputs
  sameBody : header.body = generation.body
  sameSolved : header.solved = named.specialized.function.solvedRequirements
  projection : whole.compatible.checked.catalog.project header.function.resultType = .ok named.signature.resultType
  issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics
  assignments : ∃ first, SourceCoreAssignmentFaultSites.prepare (CallableIndexedNamedGeneration.source named) first =
    .ok generation.own.assignments
  body : AcceptedNamedBodyFlow.Body (rowIndex generation record).policy (rowIndex generation record).fuel
    (rowIndex generation record).compilerSource (rowIndex generation record).scope
    (rowIndex generation record).statements (rowIndex generation record).result
    (rowIndex generation record).reasonAt (rowIndex generation record).fellThrough
    (rowIndex generation record).escaped (rowIndex generation record).body
  covered : CellAwareInvocationAcceptedFlow.Covered (rowIndex generation record).source header.function.resultType
    (CellAwareInvocationAcceptedMatches.Admitted (rowIndex generation record))
    (CellAwareInvocationAcceptedInputs.Generalized (attachment := fun _ _ _ => True) (rowIndex generation record))
    body.tree
  native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext (rowIndex generation record).scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
    (rowIndex generation record).body nativeType whole.indexed.layouts.definitions
  issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key)
  closed : CellAwareInvocationAcceptedNestedExpressions.ClosedNested generation record called
  ports : CellAwareInvocationAcceptedCallExpressions.Ports (headers := headers) generation record
  bodyScope : Staging.Recursive.Scope
  bodySelected : (SelectedCompilationPhysicalProgramSupport.stages whole).Closure header.function bodyScope

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (support : SelectedCompilationNamedSupport.Support whole)
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  {called : DeclarationInstantiation → Prop}
  (rows : ∀ header, header ∈ headers → called header.instantiation → Row (headers := headers) called header)

local notation "rootFunctions" =>
  CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" =>
  CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry rootFunctions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private theorem row_source {header : Header whole (Program.ofChecked whole.sourceProgram)}
    (row : Row (headers := headers) called header) {child : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function child) :
    child.source = (rowIndex row.generation row.record).source := by
  show child.source = CallableIndexedNamedGeneration.source row.named
  rw [← row.sameNamed]
  exact ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source

include support in
private theorem row_unique {header : Header whole (Program.ofChecked whole.sourceProgram)}
    (row : Row (headers := headers) called header) :
    NodeOccurrencesUnique (CallableIndexedNamedGeneration.source row.named) := by
  obtain ⟨_facts, certificate⟩ := support.certified header
  have functionUnique : NodeOccurrencesUnique header.function.source := by
    rw [header.frame.source]
    exact certificate.graph_closed.wellFormed.nodeOccurrencesUnique
  rw [← row.sameNamed]
  simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using functionUnique

include profile receiver support artifact checked wellFormed rows in
/-- Every family body has its accepted-expression meaning on the
slot-retaining protocol at every grade, for every owner key with physical
locations and every registry scope of its function. -/
theorem expressions (size : Nat) :
    ∀ header (member : header ∈ headers) (admitted : called header.instantiation) (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (rowIndex (rows header member admitted).generation (rows header member admitted).record) stages child faults
        size := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree whole receiver)
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro header member admitted owner keyPhysical child selected
    have applications : ∀ callee, callee ∈ headers → called callee.instantiation →
        CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True)
          (headers := headers) (keys := keys) model stages faults callee size ∧
        CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True)
          (headers := headers) (keys := keys) model stages faults callee size := by
      intro callee calleeMember calleeAdmitted
      let row := rows callee calleeMember calleeAdmitted
      refine ⟨fun smaller less => ?_, fun smaller less => ?_⟩
      · exact CellAwareInvocationAcceptedNamedApplication.preserves profile receiver callee row.generation row.record
          row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
          support row.issued row.assignments artifact checked row.body row.covered row.native wellFormed smaller
          (fun calleeOwner calleeKey _ calleeSelected =>
            ih smaller less callee calleeMember calleeAdmitted calleeOwner calleeKey calleeSelected)
      · exact CellAwareInvocationAcceptedNamedApplication.reflects profile receiver callee row.generation row.record
          row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
          support row.issued row.assignments artifact checked row.body row.covered row.native smaller row.bodySelected
          (fun calleeOwner calleeKey _ calleeSelected =>
            ih smaller less callee calleeMember calleeAdmitted calleeOwner calleeKey calleeSelected)
    let row := rows header member admitted
    exact CellAwareInvocationAcceptedNestedExpressions.expressions row.generation row.record called owner keyPhysical
      stages child faults row.closed size (row_source row selected) completion.result.extension
      (CellAwareInvocationAcceptedNamedInvocation.reads row.generation row.record row.issuer receiver
        (row_unique support row))
      support.registryBodies wellFormed row.ports applications

include profile receiver support artifact checked wellFormed rows in
/-- The direct-call head's application input holds for every admitted header
at every Source grade. -/
theorem preserves (header : Header whole (Program.ofChecked whole.sourceProgram)) (member : header ∈ headers)
    (admitted : called header.instantiation) (size : Nat) :
    CellAwareInvocationAcceptedDirectCalls.PreservesAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size :=
  let row := rows header member admitted
  CellAwareInvocationAcceptedNamedApplication.preserves profile receiver header row.generation row.record
    row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
    support row.issued row.assignments artifact checked row.body row.covered row.native wellFormed size
    (fun owner keyPhysical _ selected =>
      expressions profile receiver support artifact checked wellFormed rows size header member admitted owner
        keyPhysical selected)

include profile receiver support artifact checked wellFormed rows in
/-- The direct-call head's native application input holds for every admitted
header at every native grade. -/
theorem reflects (header : Header whole (Program.ofChecked whole.sourceProgram)) (member : header ∈ headers)
    (admitted : called header.instantiation) (size : Nat) :
    CellAwareInvocationAcceptedDirectCalls.ReflectsAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size :=
  let row := rows header member admitted
  CellAwareInvocationAcceptedNamedApplication.reflects profile receiver header row.generation row.record
    row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
    support row.issued row.assignments artifact checked row.body row.covered row.native size row.bodySelected
    (fun owner keyPhysical _ selected =>
      expressions profile receiver support artifact checked wellFormed rows size header member admitted owner
        keyPhysical selected)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallFamily
end

section
/-! A finite check of the nested sites, as
`CellAwareInvocationAcceptedCallSubsetCheck` checks the extended roots. It
reads only a row's Source nodes, the prepared local inventory, the row's
evidence assumptions and the plan's reference edges, so it runs on an actually
compiled program. Its result is a proof that every expression node of the row
is a nested site or a declaration reference that the plan records no reference
edge for; the compiler cannot lower such a reference on its own, so
`closedNested` turns the check into `ClosedNested`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedCheck
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareNamedExpressionSyntax (Site site?)
open CellAwareInvocationAcceptedNestedTrees (Nested)
open CellAwareInvocationAcceptedDirectSites (DirectSite)
open CellAwareInvocationAcceptedCallSubsetCheck (ReferenceSite directSite? referenceSite?)

private def all? {P : ExpressionId → Prop} (check : (id : ExpressionId) → Option (PLift (P id))) :
    (ids : List ExpressionId) → Option (PLift (∀ argument ∈ ids, P argument))
  | [] => some ⟨by intro argument member; cases member⟩
  | id :: rest => do
    let ⟨head⟩ ← check id
    let ⟨tail⟩ ← all? check rest
    pure ⟨by
      intro argument member
      rcases List.mem_cons.mp member with same | member
      · subst same
        exact head
      · exact tail argument member⟩

/-- Proof-producing recognition of one nested site and its children. -/
def nested? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (called : DeclarationInstantiation → Prop) [DecidablePred called] :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (Nested prepared named source called id))
  | 0, _ => none
  | fuel + 1, id =>
    match site? prepared named source id with
    | some site =>
      match form : site.node.form with
      | .integerLiteral literal resolution => some ⟨.literal site (form ▸ .integer literal resolution)⟩
      | .reference name (.builtinBoolean value) => some ⟨.literal site (form ▸ .bool name value)⟩
      | .literal literal => some ⟨.literal site (form ▸ .word literal)⟩
      | .tuple [] => some ⟨.literal site (form ▸ .unit)⟩
      | .reference _name (.local _binder) => some ⟨.read site form⟩
      | .unary _operator operand => do
        let ⟨child⟩ ← nested? prepared named source called fuel operand
        pure ⟨.unary site form child⟩
      | .binary left _operator right => do
        let ⟨first⟩ ← nested? prepared named source called fuel left
        let ⟨second⟩ ← nested? prepared named source called fuel right
        pure ⟨.binary site form first second⟩
      | .conditional condition thenId elseId => do
        let ⟨test⟩ ← nested? prepared named source called fuel condition
        let ⟨yes⟩ ← nested? prepared named source called fuel thenId
        let ⟨no⟩ ← nested? prepared named source called fuel elseId
        pure ⟨.conditional site form test yes no⟩
      | .group inner => do
        let ⟨child⟩ ← nested? prepared named source called fuel inner
        pure ⟨.group site form child⟩
      | .tuple [left, right] => do
        let ⟨first⟩ ← nested? prepared named source called fuel left
        let ⟨second⟩ ← nested? prepared named source called fuel right
        pure ⟨.pair site form first second⟩
      | _ => none
    | none =>
      match directSite? prepared named source id with
      | none => none
      | some ⟨_callee, ids, instantiation, site⟩ =>
        if selected : called instantiation then
          match all? (nested? prepared named source called fuel) ids with
          | some ⟨arguments⟩ => some ⟨.call site selected arguments⟩
          | none => none
        else none

/-- An expression node of the check: a nested site, or a reference site. -/
def Checked {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) (called : DeclarationInstantiation → Prop)
    (id : ExpressionId) : Prop :=
  Nested prepared named source called id ∨ Nonempty (ReferenceSite prepared named source id)

private def checkedNode? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (called : DeclarationInstantiation → Prop) [DecidablePred called] (fuel : Nat) (id : ExpressionId) :
    Option (PLift (Checked prepared named source called id)) :=
  match nested? prepared named source called fuel id with
  | some ⟨nested⟩ => some ⟨.inl nested⟩
  | none =>
    match referenceSite? prepared named source id with
    | some site => some ⟨.inr ⟨site⟩⟩
    | none => none

private def sweep? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (called : DeclarationInstantiation → Prop) [DecidablePred called] (fuel : Nat) :
    (nodes : List Node) →
      Option (PLift (∀ node, Node.expression node ∈ nodes → Checked prepared named source called node.id))
  | [] => some ⟨by intro node member; cases member⟩
  | .expression node :: rest => do
    let ⟨head⟩ ← checkedNode? prepared named source called fuel node.id
    let ⟨tail⟩ ← sweep? prepared named source called fuel rest
    pure ⟨by
      intro other member
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact head
      · exact tail other member⟩
  | .statement _ :: rest => do
    let ⟨tail⟩ ← sweep? prepared named source called fuel rest
    pure ⟨by
      intro other member
      rcases List.mem_cons.mp member with same | member
      · cases same
      · exact tail other member⟩

/-- Every expression node of the Source is a nested site or a reference site.
The fuel bounds the depth of the expression graph, which the node count
bounds. -/
def nodes? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (called : DeclarationInstantiation → Prop) [DecidablePred called] :
    Option (PLift (∀ id node, source.lookupExpression? id = some node →
      Checked prepared named source called id)) := do
  let ⟨all⟩ ← sweep? prepared named source called (source.nodes.length + 1) source.nodes
  pure ⟨by
    intro id node found
    obtain ⟨member, same⟩ := lookupExpression?_sound found
    exact same ▸ all node member⟩

/-- `Nested` depends on its row only through the row's key and its empty
assumptions. -/
theorem transport {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {source : TypedSource} {first second : SourceCoreGeneralFunctions.Function}
    (keyEq : first.signature.key = second.signature.key) (assumptions : second.specialized.assumptions = [])
    {called : DeclarationInstantiation → Prop} {id : ExpressionId}
    (nested : Nested prepared first source called id) : Nested prepared second source called id := by
  induction nested with
  | literal site atomic => exact .literal (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) atomic
  | read site form => exact .read (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form
  | unary site form _ child =>
    exact .unary (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form child
  | binary site form _ _ left right =>
    exact .binary (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form left right
  | conditional site form _ _ _ test yes no =>
    exact .conditional (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form test yes no
  | group site form _ child =>
    exact .group (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form child
  | pair site form _ _ left right =>
    exact .pair (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form left right
  | call site selected _ arguments =>
    exact .call (CellAwareInvocationAcceptedCallSubsetCheck.transportDirect keyEq assumptions site) selected
      arguments

/-- A named row whose every expression node is a nested site or a reference
site has every accepted expression a nested site. -/
theorem closedNested {whole : SourceCoreUnifiedCompilation.Compiled} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
      .ok named.specialized)
    {called : DeclarationInstantiation → Prop}
    (nodes : ∀ id node, (CallableIndexedNamedGeneration.source named).lookupExpression? id = some node →
      Checked whole.indexed named (CallableIndexedNamedGeneration.source named) called id) :
    CellAwareInvocationAcceptedNestedExpressions.ClosedNested generation record called := by
  intro fuel scope expression lowered generated
  obtain ⟨node, found⟩ := CellAwareInvocationAcceptedExpressions.found_of_children
    (ActualBodyInvocation.Index.named generation record :
      ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView) generated
  rcases nodes expression node found with nested | rejected
  · exact nested
  · obtain ⟨site⟩ := rejected
    exfalso
    change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
    cases fuel with
    | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
    | succ rootFuel =>
      rw [GeneralizedLocalInitializerCompilation.named_contextual generation record] at generated
      exact CellAwareInvocationAcceptedCallSubsetCheck.reference_rejected generation site rootFuel generated

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedCheck
end
