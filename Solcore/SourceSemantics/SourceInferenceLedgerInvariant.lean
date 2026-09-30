import Solcore.SourceSemantics.SourceInferenceSoundness

/-!
Import-neutral contracts for the operational ledger invariants threaded by
the mutually recursive source-inference soundness proof.  Keeping only the
state predicates and function-indexed propositions here lets expression and
statement preservation steps live in disjoint downstream modules.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Canonical requirement allocation and local-scheme template tracking at
one recursive inference boundary.  `pending` contains templates already
allocated into binders whose owning statement node has not yet been recorded.
Expression and ordinary statement boundaries preserve an arbitrary ambient
suffix; `for`-header traversal extends it until the enclosing loop node is
recorded. -/
structure RecursiveLedgerInvariant (state : State)
    (pending : List RequirementId) : Prop where
  requirements : state.RequirementsWellFormed
  templates : TemplateTracking state pending

def InferExprFuelLedgerPreservation (fuel : Nat) : Prop :=
  ∀ {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option Ty}
    {initial final : State} {inferred : InferredExpression}
    {pending : List RequirementId},
    Detail.inferExprFuel fuel context expression expected initial =
        .ok (inferred, final) →
    RecursiveLedgerInvariant initial pending →
    RecursiveLedgerInvariant final pending

def InferConstructorApplicationFuelLedgerPreservation (fuel : Nat) : Prop :=
  ∀ {context : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty}
    {initial final : State} {inferred : InferredExpression}
    {pending : List RequirementId},
    Detail.inferConstructorApplicationFuel fuel context source id
        instantiation arguments expected initial = .ok (inferred, final) →
    RecursiveLedgerInvariant initial pending →
    RecursiveLedgerInvariant final pending

def InferConstructorArgumentsFuelLedgerPreservation (fuel : Nat) : Prop :=
  ∀ {context : Frontend.SourceInference.Context}
    {arguments : List Syntax.Expr} {expected : List Ty}
    {initial final : State} {inferred : List InferredExpression}
    {pending : List RequirementId},
    Detail.inferConstructorArgumentsFuel fuel context arguments expected
        initial = .ok (inferred, final) →
    RecursiveLedgerInvariant initial pending →
    RecursiveLedgerInvariant final pending

def InferStatementsFuelLedgerPreservation (fuel : Nat) : Prop :=
  ∀ {context : Frontend.SourceInference.Context}
    {statements : List Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.BlockResult}
    {pending : List RequirementId},
    Detail.inferStatementsFuel fuel context statements expectedReturn initial =
        .ok result →
    RecursiveLedgerInvariant initial pending →
    RecursiveLedgerInvariant result.state pending

def InferStatementFuelLedgerPreservation (fuel : Nat) : Prop :=
  ∀ {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {pending : List RequirementId},
    Detail.inferStatementFuel fuel context statement expectedReturn initial =
        .ok result →
    RecursiveLedgerInvariant initial pending →
    RecursiveLedgerInvariant result.state pending

def InferForItemsFuelLedgerPreservation (fuel : Nat) : Prop :=
  ∀ {context : Frontend.SourceInference.Context}
    {items : List Syntax.ForItem} {initial : State}
    {result : Detail.InferredForItems} {pending : List RequirementId},
    Detail.inferForItemsFuel fuel context items initial = .ok result →
    RecursiveLedgerInvariant initial pending →
    RecursiveLedgerInvariant result.state
      (pending ++ result.items.flatMap ForItemForm.localSchemeTemplateIds)

def InferForItemFuelLedgerPreservation (fuel : Nat) : Prop :=
  ∀ {context : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {initial final : State}
    {inferred : ForItemForm} {pending : List RequirementId},
    Detail.inferForItemFuel fuel context item initial =
        .ok (inferred, final) →
    RecursiveLedgerInvariant initial pending →
    RecursiveLedgerInvariant final
      (pending ++ inferred.localSchemeTemplateIds)

def InferPlaceFuelLedgerPreservation (fuel : Nat) : Prop :=
  ∀ {context : Frontend.SourceInference.Context}
    {target : Syntax.Expr} {initial final : State}
    {place : PlaceResolution} {pending : List RequirementId},
    Detail.inferPlaceFuel fuel context target initial = .ok (place, final) →
    RecursiveLedgerInvariant initial pending →
    RecursiveLedgerInvariant final pending

def InferAssignedValueFuelLedgerPreservation (fuel : Nat) : Prop :=
  ∀ {context : Frontend.SourceInference.Context}
    {target value : Syntax.Expr} {operator : Syntax.ValueAssignOp}
    {initial final : State} {assignment : AssignmentResolution}
    {inferred : InferredExpression} {pending : List RequirementId},
    Detail.inferAssignedValueFuel fuel context target operator value initial =
        .ok (assignment, inferred, final) →
    RecursiveLedgerInvariant initial pending →
    RecursiveLedgerInvariant final pending

def InferExprsFuelLedgerPreservation (fuel : Nat) : Prop :=
  ∀ {context : Frontend.SourceInference.Context}
    {expressions : List Syntax.Expr} {initial final : State}
    {inferred : List InferredExpression} {pending : List RequirementId},
    Detail.inferExprsFuel fuel context expressions initial =
        .ok (inferred, final) →
    RecursiveLedgerInvariant initial pending →
    RecursiveLedgerInvariant final pending

def InferMatchCasesFuelLedgerPreservation (fuel : Nat) : Prop :=
  ∀ {context : Frontend.SourceInference.Context}
    {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {initial : State} {result : Detail.MatchCasesResult}
    {pending : List RequirementId},
    Detail.inferMatchCasesFuel fuel context scrutineeType expectedReturn
        outerScope cases initial = .ok result →
    RecursiveLedgerInvariant initial pending →
    RecursiveLedgerInvariant result.state pending

end Solcore.SourceSemantics.SourceInferenceSoundness
