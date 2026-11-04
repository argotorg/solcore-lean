import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeExpressions
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicOutputSelections
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalBody
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements

/-!
# Cell-aware materialized expressions

Generalized reads, groups and products of materialized bodies: certificates, syntax, collectors, bounds and meaning, with their positive output provenance.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedOutput
/-! Positive materialized provenance survives products, actual output selection
and later heap growth. A public handle never supplies this provenance alone. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedOutput
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open GeneralizedLocalMaterializedAssociation
open RecursiveNamedPublicFunctionHistory (Entry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

inductive ValueAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) (location : Core.Location) :
    Dynamic.Value → Core.Value → Prop where
  | function {function native bindings parameter result}
      (association : Association compiled mapping world function native bindings parameter result)
      (framed : association.AtFrame location) :
      ValueAt compiled mapping world location (.closure function) native
  | product {left right first second}
      (leftValue : ValueAt compiled mapping world location left first)
      (rightValue : ValueAt compiled mapping world location right second) :
      ValueAt compiled mapping world location (.product left right) (.pair first second)

variable {mapping nextMap : LocationMap} {world nextWorld : StoreTyping} {location : Core.Location}
  {source : Dynamic.Value} {native : Core.Value}

theorem ValueAt.extend (value : ValueAt compiled mapping world location source native)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    ValueAt compiled nextMap nextWorld location source native := by
  induction value with
  | function association framed =>
      exact .function (association.extend maps worlds) (by cases association; exact framed)
  | product left right ihLeft ihRight => exact .product ihLeft ihRight

theorem of_read {outcome : Staging.Recursive.Outcome} {value : Core.Value}
    (strong : CellAwareScopeGeneralizedReadBounds.StrongResult (compiled := compiled)
      mapping world location outcome value) (success : outcome = .value source) :
    ∃ payload, value = .inRight .word payload ∧ ValueAt compiled mapping world location source payload := by
  obtain ⟨function, payload, bindings, parameter, result, sourceEq, valueEq, association, framed⟩ := strong source success
  exact ⟨payload, valueEq, sourceEq ▸ .function association framed⟩

theorem ValueAt.callable (value : ValueAt compiled mapping world location source native)
    {context : SourceSemantics.Context} {heap : Dynamic.Heap} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap source (.function parameter result)) :
    ∃ function bindings parameterCore resultCore, source = .closure function ∧
      ∃ association : Association compiled mapping world function native bindings parameterCore resultCore,
        association.AtFrame location := by
  cases value with
  | function association framed => exact ⟨_, _, _, _, rfl, association, framed⟩
  | product left right => cases typed

/-- The complete selected list retains the exact Source/native leaf pairing. -/
def EntriesAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) (location : Core.Location) (entries : List Entry) : Prop :=
  ∀ entry ∈ entries, ValueAt compiled mapping world location entry.source entry.native

theorem selected {sourceType : TypeSystem.Ty} {publicValue : SourceCorePublicValues.Value}
    {selection : RecursiveNamedPublicOutputSelections.Selection sourceType publicValue}
    {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (receipt : RecursiveNamedPublicOutputSelections.Selected selection source native type fuel entries)
    (value : ValueAt compiled mapping world location source native) :
    EntriesAt compiled mapping world location entries := by
  induction receipt with
  | skip => intro entry member; cases member
  | function =>
      intro entry member
      cases List.mem_singleton.mp member
      exact value
  | product left right ihLeft ihRight =>
      cases value with
      | product first second =>
          intro entry member
          rcases List.mem_append.mp member with inLeft | inRight
          · exact ihLeft first entry inLeft
          · exact ihRight second entry inRight

theorem EntriesAt.extend {entries : List Entry}
    (entriesAt : EntriesAt compiled mapping world location entries)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    EntriesAt compiled nextMap nextWorld location entries :=
  fun entry member => (entriesAt entry member).extend maps worlds

theorem EntriesAt.append {first second : List Entry}
    (left : EntriesAt compiled mapping world location first)
    (right : EntriesAt compiled mapping world location second) :
    EntriesAt compiled mapping world location (first ++ second) := by
  intro entry member
  rcases List.mem_append.mp member with inLeft | inRight
  · exact left entry inLeft
  · exact right entry inRight

/-- Success retains positive function leaves; failures carry no output leaf. -/
def OutcomeAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) (location : Core.Location)
    (outcome : Staging.Recursive.Outcome) (native : Core.Value) : Prop :=
  ∀ source, outcome = .value source →
    ∃ payload, native = .inRight .word payload ∧ ValueAt compiled mapping world location source payload

theorem OutcomeAt.fault {failure : Staging.Recursive.Failure} {native : Core.Value} :
    OutcomeAt compiled mapping world location (.fault failure) native := by
  intro source impossible
  cases impossible

theorem OutcomeAt.extend {outcome : Staging.Recursive.Outcome}
    (output : OutcomeAt compiled mapping world location outcome native)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    OutcomeAt compiled nextMap nextWorld location outcome native := by
  intro source same
  obtain ⟨payload, nativeEq, value⟩ := output source same
  exact ⟨payload, nativeEq, value.extend maps worlds⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedOutput
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedRetainedEntries
/-! Each retained exported function keeps its own immutable owner and actual
materialized compiler association. Different factories may share one history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedRetainedEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Key OwnedKey)
open RecursiveNamedPublicFunctionHistory (Entry)
open GeneralizedLocalMaterializedAssociation
open CellAwareMaterializedOutput (ValueAt EntriesAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping nextMap : LocationMap} {world nextWorld : StoreTyping}

def EntryAt (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (mapping : LocationMap) (world : StoreTyping) (entry : Entry) : Prop :=
  ∃ owner : OwnedKey keys,
    ValueAt compiled mapping world owner.key.frameLocation entry.source entry.native

def Retained (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (mapping : LocationMap) (world : StoreTyping) (entries : List Entry) : Prop :=
  ∀ entry ∈ entries, EntryAt keys mapping world entry

theorem EntryAt.extend {entry : Entry} (retained : EntryAt keys mapping world entry)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    EntryAt keys nextMap nextWorld entry := by
  obtain ⟨owner, value⟩ := retained
  exact ⟨owner, value.extend maps worlds⟩

theorem Retained.extend {entries : List Entry} (retained : Retained keys mapping world entries)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    Retained keys nextMap nextWorld entries :=
  fun entry member => (retained entry member).extend maps worlds

theorem Retained.nil : Retained keys mapping world [] := by
  intro entry member
  cases member

theorem Retained.of_selected {entries : List Entry} (owner : OwnedKey keys)
    (selected : EntriesAt compiled mapping world owner.key.frameLocation entries) :
    Retained keys mapping world entries :=
  fun entry member => ⟨owner, selected entry member⟩

theorem Retained.append {first second : List Entry}
    (left : Retained keys mapping world first) (right : Retained keys mapping world second) :
    Retained keys mapping world (first ++ second) := by
  intro entry member
  rcases List.mem_append.mp member with inLeft | inRight
  · exact left entry inLeft
  · exact right entry inRight

theorem EntryAt.association {entry : Entry} (retained : EntryAt keys mapping world entry)
    {function : Dynamic.Closure} (sourceEq : entry.source = .closure function) :
    ∃ (owner : OwnedKey keys), ∃ bindings parameter result,
      ∃ association : Association compiled mapping world function entry.native bindings parameter result,
        association.AtFrame owner.key.frameLocation := by
  obtain ⟨owner, value⟩ := retained
  rw [sourceEq] at value
  cases value with
  | function association framed => exact ⟨owner, _, _, _, association, framed⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedRetainedEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionCertificates
/-! The compiler tree retains actual generalized read wrappers, transparent
groups and ordered product children. Its static receipts contain no assumed
execution or dynamic result. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionCertificates
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

inductive Tree {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) (rootFuel : Nat)
    (source : TypedSource) (sourceContext : SourceSemantics.Context) (reasonAt : ExpressionId → Word)
    (scope : SourceCoreLocalCell.Scope) : ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | generalized {id lowered}
      (receipt : GeneralizedLocalNamedReadCompilation.Certificate prepared named source scope id reasonAt lowered)
      (recipe : GeneralizedLocalNamedRecipeCompilation.Receipt receipt) :
      Tree compiled rootFuel source sourceContext reasonAt scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode) (type : node.type = innerNode.type)
      (child : Tree compiled rootFuel source sourceContext reasonAt scope inner lowered) :
      Tree compiled rootFuel source sourceContext reasonAt scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (type : node.type = .product leftNode.type rightNode.type)
      (leftChild : Tree compiled rootFuel source sourceContext reasonAt scope left first)
      (rightChild : Tree compiled rootFuel source sourceContext reasonAt scope right second) :
      Tree compiled rootFuel source sourceContext reasonAt scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩

theorem Tree.ordinary {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    {compiled : Compilation prepared named diagnostics code} {rootFuel : Nat}
    {source : TypedSource} {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree compiled rootFuel source sourceContext reasonAt scope id lowered) :
    CellAwareNamedExpressionCertificates.Tree compiled rootFuel source sourceContext reasonAt scope id lowered := by
  induction tree with
  | generalized receipt recipe => exact .generalized receipt recipe
  | group metadata form found type _ child => exact .group metadata form found type child
  | pair metadata form leftFound rightFound type _ _ left right =>
    exact .pair metadata form leftFound rightFound type left right

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionSyntax
/-! Actual factory output syntax whose leaves are specialized generalized
reads. The scanner retains every original observation and ordered child. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionSyntax
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareNamedExpressionSyntax (Site site?)

inductive Syntax {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) : ExpressionId → Prop where
  | generalized {id} (observed : GeneralizedLocalNamedReadCompilation.Observations prepared named source id)
      (recipe : GeneralizedLocalNamedRecipeCompilation.Observations prepared named source id) :
      Syntax prepared named source id
  | group {id inner} (site : Site prepared named source id) (form : site.node.form = .group inner)
      (child : Syntax prepared named source inner) : Syntax prepared named source id
  | pair {id left right} (site : Site prepared named source id) (form : site.node.form = .tuple [left, right])
      (first : Syntax prepared named source left) (second : Syntax prepared named source right) :
      Syntax prepared named source id

def syntax? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (Syntax prepared named source id))
  | 0, _ => none
  | fuel + 1, id =>
    match GeneralizedLocalNamedReadCompilation.observations? prepared named source id with
    | some observed => do
      let recipe ← GeneralizedLocalNamedRecipeCompilation.observations? prepared named source id
      pure ⟨.generalized observed recipe⟩
    | none => do
      let site ← site? prepared named source id
      match form : site.node.form with
      | .group inner => do
        let ⟨child⟩ ← syntax? prepared named source fuel inner
        pure ⟨.group site form child⟩
      | .tuple [left, right] => do
        let ⟨first⟩ ← syntax? prepared named source fuel left
        let ⟨second⟩ ← syntax? prepared named source fuel right
        pure ⟨.pair site form first second⟩
      | _ => none

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionSyntax
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionCollectors
/-! Accepted named expression compilation yields the mixed tree recursively.
Original Source typing selects each physical child; no child execution is an
input to this extraction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionCollectors
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareNamedExpressionSyntax (Site)
open CellAwareMaterializedExpressionCertificates (Tree)
open CompatibleEncoding (bind_ok)



variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code) (rootFuel : Nat)
  {source : TypedSource} {sourceContext : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}

private theorem special {id : ExpressionId} (site : Site prepared named source id) :
    ∀ child budget, (match (namedPolicy compiled rootFuel).lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context prepared named) child budget source scope id reasonAt) = .ok none :=
  fun child budget => CellAwareNamedExpressionPolicies.special compiled site rootFuel child budget scope reasonAt

/-- The actual root callback remains fixed while each recursive child uses
its true smaller compiler budget. -/
theorem of_policy {id : ExpressionId}
    (syntaxTree : CellAwareMaterializedExpressionSyntax.Syntax prepared named source id)
    (unique : NodeOccurrencesUnique source)
    (_declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) fuel (context prepared named) source scope id reasonAt = .ok lowered) :
    Tree compiled rootFuel source sourceContext reasonAt scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
  | generalized observed recipe =>
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨receipt⟩ := GeneralizedLocalNamedReadCompilation.of_policy compiled observed accepted
      obtain ⟨recipe⟩ := GeneralizedLocalNamedRecipeCompilation.of_certificate recipe receipt
      exact .generalized receipt recipe
  | group site form child ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (context := context prepared named) (values := .initial checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel) accepted
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
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (context := context prepared named) (values := .initial checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel) accepted
      cases step with
      | pair otherForm metadata firstGenerated secondGenerated =>
        obtain ⟨rfl, rfl⟩ := by simpa using ExpressionForm.tuple.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, leftFound, rightFound, sourceType, leftTyped, rightTyped⟩ :=
          CompatibleExpressionProducts.pair_source_types unique site.found form site.coercions typed
        exact .pair metadata form leftFound rightFound sourceType
          (firstIH leftFound leftTyped firstGenerated) (secondIH rightFound rightTyped secondGenerated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedBodyProducer
/-! The bounded named profile fills every terminal compiler receipt from its
actual accepted expression action. Its public construction has no expression
certificate callback. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedBodyProducer
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}

abbrev Profile (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (expected : TypeSystem.Ty) :=
  CellAwareNamedBodySupport.Profile prepared named statements
    (CellAwareMaterializedExpressionSyntax.Syntax prepared named (source named)) expected

def profile? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (expected : TypeSystem.Ty) :
    Option (Profile prepared named statements expected) :=
  CellAwareNamedBodySupport.profile? prepared named statements
    (CellAwareMaterializedExpressionSyntax.syntax? prepared named (source named) prepared.fuel) expected

def Certificate (compiled : Compilation prepared named diagnostics code)
    (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => ∃ rootFuel,
    CellAwareMaterializedExpressionCertificates.Tree compiled rootFuel (source named) sourceContext
      (diagnostics.reasonAt named.signature.key) scope id lowered

theorem Certificate.ordinary {compiled : Compilation prepared named diagnostics code}
    {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate compiled sourceContext scope id lowered) :
    CellAwareNamedBodyProducer.Certificate compiled sourceContext scope id lowered := by
  obtain ⟨fuel, tree⟩ := receipt
  exact ⟨fuel, tree.ordinary⟩

theorem expression (compiled : Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (syntaxTree : CellAwareMaterializedExpressionSyntax.Syntax prepared named (source named) id)
    (unique : NodeOccurrencesUnique (source named))
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext)
    (found : (source named).lookupExpression? id = some node)
    (typed : ExpressionHasType (source named) sourceContext id node.type)
    (accepted : (CellAwareNamedBodySupport.policy compiled).lowerExpression fuel (source named)
      scope id (diagnostics.reasonAt named.signature.key) = .ok lowered) :
    Certificate compiled sourceContext scope id lowered := by
  change SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
    prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
    diagnostics (context prepared named) prepared.base.callableContext none none fuel
    (source named) scope id (diagnostics.reasonAt named.signature.key) = .ok lowered at accepted
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [GeneralizedLocalInitializerCompilation.named_contextual compiled record] at accepted
    exact ⟨fuel, CellAwareMaterializedExpressionCollectors.of_policy compiled fuel syntaxTree unique
      declarations found typed accepted⟩

theorem of_compilation (compiled : Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {expected : TypeSystem.Ty} (profile : Profile prepared named compiled.statements expected)
    (unique : NodeOccurrencesUnique (source named))
    {control : ControlContext} (result : control.returnType = expected)
    {sourceContext final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType (source named) control sourceContext compiled.statements final facts)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named)
      (CellAwareNamedBodySupport.scope named) sourceContext)
    {administrative : Core.Context} {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (CellAwareNamedBodySupport.scope named) ++ administrative)
      compiled.body nativeType prepared.layouts.definitions) :
    Nonempty (CellAwareNamedBodySupport.Body compiled (Certificate compiled) administrative sourceContext expected) := by
  apply CellAwareNamedBodySupport.of_compilation compiled record profile ?_ unique result typed declarations nativeTyped
  intro childContext childScope fuel id node lowered childDeclarations syntaxTree found childTyped accepted _ _
  exact expression compiled record syntaxTree unique childDeclarations found childTyped accepted

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedBodyProducer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedScopeBounds
/-! Internal terminal-child bounds retain exact declaration authority and
return a concrete effect on every stored generalized row. Actual expression
proofs discharge these bounds; the public theorem does not assume them. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedScopeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (certificate : GenericExpressionMeaning.Certificate) (faults : RecursiveStageMeaning.FaultRep)

/-- Source size is the grade of the genuine staged trace. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
    Staging.Recursive.Size.Expression program registry size invocation context environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      CellAwareMaterializedOutput.OutcomeAt compiled finalMap finalWorld owner.key.frameLocation outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt bridge context model named registry invocation certificate faults size

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedScopeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedPairBounds
/-! Ordered pair children transport actual generalized lexical authority. Their
concrete effects compose across both successful and failing evaluations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedPairBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareMaterializedScopeBounds
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CompatibleExpressionProducts (Metadata)
open CallableIndexedOwnedPreparedStagedPairBounds (Pair ProductValues)
universe u

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- A payload model may combine two represented values at the same reached
heap/world. This is a representation constructor, with no execution input. -/
private inductive SourceChildren (size : Nat) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (left right : ExpressionId) :
    Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | leftFault {childSize after failure}
      (smaller : childSize < size)
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context
        environment before left (.fault failure) after) :
      SourceChildren size environment before left right (.fault failure) after
  | rightFault {firstSize secondSize middle after value failure}
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size)
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context
        environment before left (.value value) middle)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context
        environment middle right (.fault failure) after) :
      SourceChildren size environment before left right (.fault failure) after
  | values {firstSize secondSize middle after leftValue rightValue}
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size)
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context
        environment before left (.value leftValue) middle)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context
        environment middle right (.value rightValue) after) :
      SourceChildren size environment before left right (.value (.product leftValue rightValue)) after

private theorem source_children
    {id left right : ExpressionId} {node : ExpressionNode}
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .tuple [left, right])
    (trace : Staging.Recursive.Size.Expression program registry size invocation context
      environment before id outcome after) :
    SourceChildren (program := program) (registry := registry) (invocation := invocation)
      (context := context) size environment before left right outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm requirements},
      Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .tuple [left, right] := by
    intro actualForm requirements occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | generalizedLocal contains localForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _ =>
      cases same_node contains
      rw [form] at localForm
      cases localForm
  | pair occurrence first second =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .values (Staging.Recursive.Size.child_lt_stepSize (by simp))
          (Staging.Recursive.Size.child_lt_stepSize (by simp)) first second
  | pairLeftFault occurrence child =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .leftFault (Staging.Recursive.Size.child_lt_stepSize (by simp)) child
  | pairRightFault occurrence first second =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .rightFault (Staging.Recursive.Size.child_lt_stepSize (by simp))
          (Staging.Recursive.Size.child_lt_stepSize (by simp)) first second
  | tupleValue occurrence sequence packed =>
      cases ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases sequence with
      | cons first rest =>
          cases rest with
          | cons second tail =>
              cases tail
              cases packed with
              | cons last =>
                  cases last
                  exact .values (by simp [Staging.Recursive.Size.stepSize]; omega)
                    (by simp [Staging.Recursive.Size.stepSize]; omega) first second
  | tupleFault occurrence sequence =>
      cases ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases sequence with
      | headFault first =>
          exact .leftFault (by simp [Staging.Recursive.Size.stepSize]; omega) first
      | tailFault first rest =>
          cases rest with
          | headFault second =>
              exact .rightFault (by simp [Staging.Recursive.Size.stepSize]; omega)
                (by simp [Staging.Recursive.Size.stepSize]; omega) first second
          | tailFault _ rest => cases rest
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _
  | group occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _
  | applied occurrence _ _ _ _ _ _ => cases occurrence_form occurrence

private theorem child_typing
    {id left right : ExpressionId} {node leftNode rightNode : ExpressionNode} {type : Ty}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .tuple [left, right])
    (leftFound : invocation.source.lookupExpression? left = some leftNode)
    (rightFound : invocation.source.lookupExpression? right = some rightNode)
    (unique : NodeOccurrencesUnique invocation.source)
    (typed : ExpressionHasType invocation.source context id node.type) :
    ExpressionHasType invocation.source context left leftNode.type ∧
      ExpressionHasType invocation.source context right rightNode.type := by
  obtain ⟨first, second, firstFound, secondFound, _sourceType, firstTyped, secondTyped⟩ :=
    CompatibleExpressionProducts.pair_source_types unique metadata.found form metadata.coercions typed
  cases Option.some.inj (firstFound.symm.trans leftFound)
  cases Option.some.inj (secondFound.symm.trans rightFound)
  exact ⟨firstTyped, secondTyped⟩

/-- Two genuine Source children are executed in their actual successive heaps.
Either failure keeps its original scoped representation and exact endpoint. -/
theorem pair_preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (products : ProductValues (model := model)) (budget : Nat)
    (childMeaning : PreservesBelow bridge context model named registry invocation children faults budget) :
    ∀ size, size ≤ budget → PreservesAt bridge context model named registry invocation
      (Pair checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  cases certified with
  | actual metadata form leftFound rightFound sourceType firstChild secondChild =>
      cases Option.some.inj (found.symm.trans metadata.found)
      obtain ⟨firstTyped, secondTyped⟩ := child_typing metadata form leftFound rightFound unique typed
      have parts := source_children unique metadata.found form trace
      cases parts with
      | leftFault smaller first =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, strong, finalHeaps,
              maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le smaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame first
          cases represented with
          | fault matched =>
              refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, CellAwareMaterializedOutput.OutcomeAt.fault, finalHeaps,
                maps, worlds, frame, heapMetadata, effect, reached, related, post.at_fault_type⟩
              rw [DataExpressionSequence.pair_rename]
              exact LocalSequence.pair_left_failure _ _ evaluated
      | rightFault firstSmaller secondSmaller first second =>
          obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, firstStrong, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le firstSmaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame first
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, secondStrong, finalHeaps,
                  maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
                childMeaning _ (Nat.lt_of_lt_of_le secondSmaller within) secondChild rightFound secondTyped
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix agrees _) (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame second
              cases represented with
              | fault matched =>
                  refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, CellAwareMaterializedOutput.OutcomeAt.fault, finalHeaps,
                    firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                    firstMetadata.trans heapMetadata, firstEffect.trans effect, reached, callerProtocol.trans firstRelated related,
                    post.at_fault_type⟩
                  rw [DataExpressionSequence.pair_rename]
                  rw [rename_prefix] at secondEval
                  exact LocalSequence.pair_right_failure _ _ firstEval secondEval
      | values firstSmaller secondSmaller first second =>
          obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, firstStrong, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le firstSmaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame first
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, secondStrong, finalHeaps,
                  maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
                childMeaning _ (Nat.lt_of_lt_of_le secondSmaller within) secondChild rightFound secondTyped
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix agrees _) (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame second
              cases represented with
              | @value lastSource lastCoreValue lastPayload =>
                  refine ⟨.inRight .word (.pair coreValue lastCoreValue), finalStore, finalMap, finalWorld, ?_, ?_, ?_, finalHeaps,
                    firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                    firstMetadata.trans heapMetadata, firstEffect.trans effect, reached, callerProtocol.trans firstRelated related, ?_⟩
                  · rw [DataExpressionSequence.pair_rename]
                    rw [rename_prefix] at secondEval
                    exact LocalSequence.pair_success _ _ firstEval secondEval
                  · exact .value (sourceType ▸ products (model.extend payload maps worlds) lastPayload)
                  · intro source same
                    cases same
                    obtain ⟨firstPayload, firstEq, firstAt⟩ := firstStrong _ rfl
                    obtain ⟨secondPayload, secondEq, secondAt⟩ := secondStrong _ rfl
                    cases (Core.Value.inRight.inj firstEq).2
                    cases (Core.Value.inRight.inj secondEq).2
                    exact ⟨_, rfl, .product (firstAt.extend maps worlds) secondAt⟩
                  · refine ⟨post.rows, ?_⟩
                    intro value same
                    cases same
                    refine ⟨?_, post.at_value.2.heap⟩
                    rw [sourceType]
                    exact .product (firstPost.at_value.1.mono heapMetadata) post.at_value.1

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedPairBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedGroupBounds
/-! Group composition carries the actual generalized lexical authority and
returns the child effect unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedGroupBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CompatibleExpressionPrimitives (Metadata)
open CallableIndexedOwnedPreparedStagedGroupBounds (Group)
universe u

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

private theorem source_group_inv
    {id inner : ExpressionId} {node : ExpressionNode}
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .group inner)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context
      environment before id outcome after) :
    ∃ childSize, size = Staging.Recursive.Size.stepSize [childSize] ∧
      Staging.Recursive.Size.Expression program registry childSize invocation context
        environment before inner outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm requirements},
      Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .group inner := by
    intro actualForm requirements occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | atomicFault contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | generalizedLocal contains localForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _ =>
      cases same_node contains
      rw [form] at localForm
      cases localForm
  | group occurrence child =>
      cases ExpressionForm.group.inj (occurrence_form occurrence)
      exact ⟨_, rfl, child⟩
  | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _
  | applied occurrence _ _ _ _ _ _ => cases occurrence_form occurrence

private theorem child_typed
    {id inner : ExpressionId} {node innerNode : ExpressionNode} {type : Ty}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .group inner)
    (innerFound : invocation.source.lookupExpression? inner = some innerNode)
    (unique : NodeOccurrencesUnique invocation.source)
    (typed : ExpressionHasType invocation.source context id node.type) :
    ExpressionHasType invocation.source context inner innerNode.type := by
  obtain ⟨actualNode, found, _sourceType, child⟩ :=
    CompatibleExpressionProducts.group_source_types unique metadata.found form metadata.coercions typed
  have same := Option.some.inj (found.symm.trans innerFound)
  cases same
  exact child

/-- The Source group rule adds one genuine step above its executed child.
The child theorem carries either fault tag and the exact reached state. -/
theorem group_preserves
    (unique : NodeOccurrencesUnique invocation.source) (budget : Nat)
    (childMeaning : CellAwareMaterializedScopeBounds.PreservesBelow
      bridge context model named registry invocation children faults budget) :
    ∀ size, size ≤ budget → CellAwareMaterializedScopeBounds.PreservesAt
      bridge context model named registry invocation (Group checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  cases certified with
  | actual metadata form innerFound sourceType child =>
      have same := Option.some.inj (found.symm.trans metadata.found)
      cases same
      obtain ⟨childSize, sizeEq, childTrace⟩ := source_group_inv unique metadata.found form trace
      have smaller : childSize < budget := by
        rw [sizeEq] at within
        exact Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, strong, finalHeaps,
          maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
        childMeaning childSize smaller child innerFound
          (child_typed metadata form innerFound unique typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childTrace
      refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, strong, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, ?_⟩
      · simpa only [sourceType] using represented
      · simpa only [sourceType] using post


end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedGroupBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedReadProjection
/-! Ordinary expression composition projects the actual generalized-read
post while indirect application retains its stronger materialization witness. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedReadProjection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

def Certificate : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  ∃ reasonAt,
    ∃ certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named invocation.source scope id reasonAt lowered,
      Nonempty (GeneralizedLocalNamedRecipeCompilation.Receipt certificate)

theorem preserves {size : Nat}
    (meaning : CellAwareScopeGeneralizedReadBounds.PreservesAt bridge context model named registry invocation faults size) :
    CellAwareMaterializedScopeBounds.PreservesAt bridge context model named registry invocation
      (Certificate (compiled := compiled) named invocation) faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees typed initial admitted authority physical owner ownerFrame trace
  obtain ⟨reasonAt, certificate, ⟨recipe⟩⟩ := certified
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, strong, rest⟩ :=
    meaning certificate recipe found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, fun source same => CellAwareMaterializedOutput.of_read strong same, rest⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedReadProjection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionTreeBounds
/-! Structural recursion on the genuine named compiler tree fills every child
expression. Generalized reads and products retain positive materialized leaves; no whole-expression meaning is stored in a certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareMaterializedScopeBounds
open CallableIndexedNamedGeneration (Compilation)
open GeneralizedLocalInitializerCompilation (namedPolicy)
open CellAwareMaterializedExpressionCertificates (Tree)
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
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word}
  (unique : NodeOccurrencesUnique invocation.source)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private theorem product_values : CallableIndexedOwnedPreparedStagedPairBounds.ProductValues (model := valueModel) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include unique in
theorem preserves_tree
    (generalized : ∀ size, CellAwareScopeGeneralizedReadBounds.PreservesAt bridge context valueModel named stages invocation callFaults size)
    {rootFuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree generation rootFuel invocation.source context reasonAt scope id lowered)
    (size : Nat) :
    PreservesAt bridge context valueModel named stages invocation (Point scope id lowered) callFaults size := by
  induction tree generalizing size with
  | generalized receipt recipe =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareMaterializedReadProjection.preserves bridge context valueModel named stages invocation callFaults
      (generalized size) ⟨reasonAt, receipt, ⟨recipe⟩⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    have children : PreservesBelow bridge context valueModel named stages invocation (Point scope inner lowered) callFaults size :=
      fun childSize _smaller => ih childSize
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareMaterializedGroupBounds.group_preserves bridge unique size children size (Nat.le_refl _)
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
    exact CellAwareMaterializedPairBounds.pair_preserves bridge unique (product_values profile) size children size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionMeaning
/-! The actual compiler certificate supplies meaning and positive output
provenance for generalized reads, groups and products. The body consumer
receives no expression execution law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (covers : invocation.evidence.Covers context)

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include sourceEq runtime selectedBodies covers in
/-- Every accepted expression in the bounded compiler profile preserves its
original Source execution, including reached mixed cells and public failures. -/
theorem preserves_selected (size : Nat) :
    CellAwareMaterializedScopeBounds.PreservesAt bridge context model named stages invocation
      (CellAwareMaterializedBodyProducer.Certificate generation context) callFaults size := by
  intro scope id lowered certificate node
  obtain ⟨rootFuel, tree⟩ := certificate
  rw [← sourceEq] at tree
  have catalog : SignatureCatalogWellFormed context.signatures := runtime.signatures.symm ▸ selectedBodies.signatures
  exact CellAwareMaterializedExpressionTreeBounds.preserves_tree (bodyRegistry := bodyRegistry)
    (semanticFaults := semanticFaults) generation bridge profile runtime.graph.nodeOccurrencesUnique
    (CellAwareNamedGeneralizedReadBounds.preserves bridge profile runtime.graph.nodeOccurrencesUnique
      runtime.requirements.idsUnique covers catalog) tree size ⟨rfl, rfl, rfl⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include sourceEq runtime wellFormed covers in
theorem preserves (size : Nat) :
    CellAwareMaterializedScopeBounds.PreservesAt bridge context model named stages invocation
      (CellAwareMaterializedBodyProducer.Certificate generation context) callFaults size := by
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (sourceEq := sourceEq) (runtime := runtime) (covers := covers) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedFlowOutput
/-! The original lexical return envelope preserves the concrete Source/native
materialized payload. The function footer removes only that envelope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedFlowOutput
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CellAwareMaterializedOutput

def FlowAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) (location : Core.Location)
    (outcome : Staging.Recursive.BodyOutcome) (native : Core.Value) : Prop :=
  ∀ source, outcome = .returned source →
    ∃ payload, native = LocalLoop.returnedValue payload ∧ ValueAt compiled mapping world location source payload

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap}
  {world : StoreTyping} {location : Core.Location} {native : Value}

theorem FlowAt.returned {source : Dynamic.Value}
    (value : ValueAt compiled mapping world location source native) :
    FlowAt compiled mapping world location (.returned source) (LocalLoop.returnedValue native) := by
  intro other same
  cases same
  exact ⟨native, rfl, value⟩

theorem FlowAt.fault {failure : Staging.Recursive.Failure} :
    FlowAt compiled mapping world location (.fault failure) native := by
  intro source impossible
  cases impossible

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedFlowOutput
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedTerminalStatements
/-! Actual terminal statement composition over the same mixed heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedTerminalStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control ResultRepresents)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Terminal
variable {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Head invocation expression statements)
  (certified : certificate scope expression lowered)
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (sameLocation : owner.key.frameLocation = physical.location)

include head certified found sourceTyped environments heaps locals agrees typed admitted authority physical sameLocation in
/-- The real parent step gives a strict expression grade. The expression IH
runs once and the existing return helper preserves its exact endpoint. -/
theorem preserves (budget : Nat)
    (children : CellAwareMaterializedScopeBounds.PreservesBelow
      bridge context model named registry invocation certificate faults budget)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      CellAwareMaterializedFlowOutput.FlowAt compiled finalMap finalWorld owner.key.frameLocation (control outcome) value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have strict : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize)
      (children := [childSize]) (by simp)) within
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, output, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    children childSize strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
  refine ⟨head.trace child, ?_⟩
  cases represented with
  | value payload =>
    obtain ⟨raw, same, positive⟩ := output _ rfl
    cases same
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
      .returned payload, CellAwareMaterializedFlowOutput.FlowAt.returned positive, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  | fault matched =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
      .fault matched, CellAwareMaterializedFlowOutput.FlowAt.fault, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩

end Terminal

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedTerminalStatements
end
