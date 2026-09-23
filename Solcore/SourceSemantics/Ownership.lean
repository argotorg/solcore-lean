import Solcore.SourceSemantics.Requirements

/-!
Whole-source ownership of stable local and requirement identities.

The typed occurrence graph contains several mirrors of the same evidence
identity.  This module counts only primary owners: expression requirement
lists, pattern requirement lists, and assignment requirement lists.  Coercion
steps, literal metadata, and match-level concatenations are checked by their
local judgments rather than counted a second time.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend.SourceInference

/-- Binder identities introduced by a flat pattern instruction stream. -/
def patternInstructionBinderIds
    (instructions : List MatchPatternInstruction) : List Resolved.LocalId :=
  instructions.filterMap fun instruction =>
    match instruction with
    | .binder binder => some binder.id
    | _ => none

/-- Binder identities introduced by a resolved pattern root and its children. -/
def patternBinderIds (pattern : TypedMatchPattern) : List Resolved.LocalId :=
  match pattern.resolution with
  | .wildcard | .integerLiteral .. => []
  | .binder binder => [binder.id]
  | .constructor _ arguments | .tuple arguments =>
      patternInstructionBinderIds arguments

/-- Local definitions retained directly by a `for` header item. -/
def forItemDefinedLocalIds : ForItemForm → List Resolved.LocalId
  | .letDecl binder _ => [binder.id]
  | .expression _ | .assignValue .. | .assignBitNot _ => []

/-- Primary assignment-owned evidence in one `for` header item. -/
def forItemPrimaryRequirementIds : ForItemForm → List RequirementId
  | .assignValue assignment _ _ | .assignBitNot assignment =>
      assignment.requirements
  | .letDecl .. | .expression _ => []

/-- Local definitions owned directly by one expression form. -/
def expressionDefinedLocalIds : ExpressionForm → List Resolved.LocalId
  | .lambda parameters _ _ => parameters.map (fun binder => binder.id)
  | _ => []

/-- Local definitions owned directly by one statement form. -/
def statementDefinedLocalIds : StatementForm → List Resolved.LocalId
  | .letDecl binder _ => [binder.id]
  | .matchWith resolution =>
      resolution.hiddenScrutinee ::
        resolution.cases.flatMap fun matchCase =>
          patternBinderIds matchCase.pattern
  | .forLoop initializer _ post _ =>
      initializer.flatMap forItemDefinedLocalIds ++
        post.flatMap forItemDefinedLocalIds
  | _ => []

/-- Stable locals defined anywhere in a typed source, with inputs first and
then node-table order. -/
def definedLocalIds (source : TypedSource) : List Resolved.LocalId :=
  source.inputs.map (fun binder => binder.id) ++ source.nodes.flatMap fun node =>
    match node with
    | .expression expression => expressionDefinedLocalIds expression.form
    | .statement statement => statementDefinedLocalIds statement.form

/-- Primary evidence owners retained directly by one statement form. -/
def statementPrimaryRequirementIds : StatementForm → List RequirementId
  | .assignValue assignment _ _ | .assignBitNot assignment =>
      assignment.requirements
  | .matchWith resolution =>
      resolution.cases.flatMap fun matchCase => matchCase.pattern.requirements
  | .forLoop initializer _ post _ =>
      initializer.flatMap forItemPrimaryRequirementIds ++
        post.flatMap forItemPrimaryRequirementIds
  | _ => []

/-- Every primary evidence owner in node-table order. -/
def primaryRequirementIds (source : TypedSource) : List RequirementId :=
  source.nodes.flatMap fun node =>
    match node with
    | .expression expression => expression.requirements
    | .statement statement => statementPrimaryRequirementIds statement.form

/-- Every local definition has a globally unique stable identity owned by the
declaration represented by this source. -/
structure LocalIdentityOwnership (source : TypedSource) : Prop where
  unique : (definedLocalIds source).Nodup
  owned : ∀ id, id ∈ definedLocalIds source → id.owner = source.owner

/-- Primary source occurrences own the solved ledger exactly once. -/
structure RequirementOwnership (context : Context) (source : TypedSource) : Prop where
  primary_unique : (primaryRequirementIds source).Nodup
  ledger_exact : (primaryRequirementIds source).Perm
    (context.solvedRequirements.map fun requirement => requirement.id)

namespace RequirementOwnership

theorem ledger_ids_unique
    {context : Context} {source : TypedSource}
    (ownership : RequirementOwnership context source) :
    RequirementIdsUnique context := by
  unfold RequirementIdsUnique
  exact ownership.ledger_exact.nodup_iff.mp ownership.primary_unique

theorem primary_mem_iff_ledger
    {context : Context} {source : TypedSource}
    (ownership : RequirementOwnership context source)
    (id : RequirementId) :
    id ∈ primaryRequirementIds source ↔
      id ∈ context.solvedRequirements.map (fun requirement => requirement.id) :=
  ownership.ledger_exact.mem_iff

end RequirementOwnership

end Solcore.SourceSemantics
