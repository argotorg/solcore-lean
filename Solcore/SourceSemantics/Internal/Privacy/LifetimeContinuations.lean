import Solcore.SourceSemantics.Internal.Privacy.SelectedInference
import Solcore.SourceSemantics.Ownership
import Solcore.Frontend.SourceInference.Internal.LocalReadScopes
import Solcore.SourceSemantics.Internal.Execution.CallGraph

/-!
# Continuations of generalization lifetimes

A lifetime keeps its computation through the next inference call, and newly created events lift
through expressions and operators.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimes
/-! Generalization lifetimes retain actual initialized statement or header
computations. Their privacy is indexed by the reached state and the output
types of the containing computation, including after the binder leaves scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

inductive GeneralizationComputation :
    SourceInference.Context → State → State → InferredExpression → TypedBinder → Prop where
  | statement {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {initial : State} {result : Detail.StatementResult}
      (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result) :
      GeneralizationComputation context initial receipt.ready receipt.value receipt.binding.1
  | header {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial : State} {result : ForItemForm × State}
      (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result) :
      GeneralizationComputation context initial receipt.ready receipt.value receipt.binding.1

structure RetainedGeneralization (whole : TypedSource) (finalSubstitution : Substitution)
    (binder : TypedBinder) (initializer : ExpressionId) where
  context : SourceInference.Context
  entry : State
  readyState : State
  value : InferredExpression
  valueId : value.id = initializer
  computation : GeneralizationComputation context entry readyState value binder
  ready : readyState.InferenceReady
  extension : finalSubstitution.SemanticallyExtends readyState.inference.substitution
  retained : ({binder, initializer := .expression initializer} : InitializedLetBinding) ∈
    initializedLetBindings whole
  binderRetained : binder ∈ whole.initializedLetBinders

structure GeneralizationLifetime
    {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    (event : RetainedGeneralization whole finalSubstitution binder initializer)
    (entryNext : Nat) (state : State) (outputs : List Ty) : Prop where
  createdAfter : entryNext ≤ event.entry.inference.next
  allocated : ∀ q ∈ binder.scheme.quantified, event.entry.inference.next ≤ q.index
  bound : ∀ q ∈ binder.scheme.quantified, q.index < state.inference.next
  transport : SafeTransport binder.scheme.quantified event.readyState state
  live : LiveBindersSafe binder.scheme.quantified state
  values : ∀ type ∈ outputs, Safe binder.scheme.quantified state type
  older : ∀ type, type.VariablesBelow entryNext → Safe binder.scheme.quantified state type
  newRows : ∀ requirement ∈ state.requirements, requirement ∉ event.readyState.requirements →
    PredicateSafe binder.scheme.quantified state requirement.predicate

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {entryNext : Nat} {before after : State} {outputs : List Ty}

/-- This composition only moves an already produced event. New events in the
second call must be supplied separately by that call's actual traversal. -/
theorem append
    (lifetime : GeneralizationLifetime event entryNext before outputs)
    (next : before.inference.next ≤ after.inference.next)
    (transport : SafeTransport binder.scheme.quantified before after)
    (live : LiveBindersSafe binder.scheme.quantified after)
    {newOutputs : List Ty}
    (values : ∀ type ∈ newOutputs, Safe binder.scheme.quantified after type)
    (newRows : ∀ requirement ∈ after.requirements, requirement ∉ before.requirements →
      PredicateSafe binder.scheme.quantified after requirement.predicate) :
    GeneralizationLifetime event entryNext after (outputs ++ newOutputs) where
  createdAfter := lifetime.createdAfter
  allocated := lifetime.allocated
  bound := fun q member => Nat.lt_of_lt_of_le (lifetime.bound q member) next
  transport := lifetime.transport.trans transport
  live
  values := by
    intro type member
    rcases List.mem_append.mp member with old | fresh
    · exact transport type (lifetime.values type old)
    · exact values type fresh
  older := fun type below => transport type (lifetime.older type below)
  newRows := new_requirements_trans lifetime.newRows newRows transport

theorem weaken_entry (lifetime : GeneralizationLifetime event entryNext before outputs)
    {earlier : Nat} (bound : earlier ≤ entryNext) :
    GeneralizationLifetime event earlier before outputs :=
  { lifetime with
    createdAfter := Nat.le_trans bound lifetime.createdAfter
    older := fun type below => lifetime.older type (below.weaken bound) }

theorem restrict_outputs (lifetime : GeneralizationLifetime event entryNext before outputs)
    {selected : List Ty} (subset : selected ⊆ outputs) :
    GeneralizationLifetime event entryNext before selected :=
  { lifetime with values := fun type member => lifetime.values type (subset member) }

/-- Sequential declarations cannot reuse a quantified variable which was
already allocated before the later initializer began. -/
theorem excludes_earlier (lifetime : GeneralizationLifetime event entryNext before outputs)
    {q : TypeVarId} (earlier : q.index < entryNext) : q ∉ binder.scheme.quantified := by
  intro quantified
  exact Nat.not_lt_of_ge (Nat.le_trans lifetime.createdAfter (lifetime.allocated q quantified)) earlier

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeContinuation
/-! Existing events survive the actual next inference call. Newly created
events are handled by the recursive traversal of that call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

structure LifetimeInferenceContext (context : SourceInference.Context) : Prop where
  catalog : SignatureCatalogWellFormed context.signatures
  formation : ProgramSignatureFormationValidated context.signatures
  canonical : ∀ signature ∈ context.signatures.functions,
    signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
      (Ty.productMany signature.returnTypes)

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {entryNext : Nat} {state : State} {outputs : List Ty}
    {fuel : Nat} {context : SourceInference.Context}

theorem inferExpr
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {source : Syntax.Expr} {expected : Option Ty} {result : InferredExpression × State}
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : inferExprFuel fuel context source expected state = .ok result) :
    GeneralizationLifetime event entryNext result.2 (outputs ++ [result.1.type]) := by
  have privacy := inferExprFuel_private binder.scheme.quantified fuel context source expected state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical
    expectedBelow expectedSafe result accepted
  have progress := inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical expectedBelow accepted
  exact lifetime.append progress.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem inferExprs
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {sources : List Syntax.Expr} {result : List InferredExpression × State}
    (accepted : inferExprsFuel fuel context sources state = .ok result) :
    GeneralizationLifetime event entryNext result.2 (outputs ++ result.1.map (·.type)) := by
  have privacy := inferExprsFuel_private binder.scheme.quantified fuel context sources state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical result accepted
  have progress := inferExprsFuel_inferenceProperties ready catalog.formation catalog.canonical accepted
  refine lifetime.append progress.1.next_le privacy.1 privacy.2.2.1 ?_ privacy.2.2.2
  intro type member
  obtain ⟨expression, present, rfl⟩ := List.mem_map.mp member
  exact privacy.2.1 expression present

theorem inferStatement
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {source : Syntax.Statement} {expected : Ty} {result : StatementResult}
    (expectedBelow : expected.VariablesBelow state.inference.next)
    (expectedSafe : Safe binder.scheme.quantified state expected)
    (accepted : inferStatementFuel fuel context source expected state = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.type]) := by
  have privacy := inferStatementFuel_private binder.scheme.quantified fuel context source expected state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical
    expectedBelow expectedSafe result accepted
  have progress := inferStatementFuel_inferenceProperties ready catalog.formation catalog.canonical expectedBelow accepted
  exact lifetime.append progress.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem inferStatements
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {sources : List Syntax.Statement} {expected : Ty} {result : BlockResult}
    (expectedBelow : expected.VariablesBelow state.inference.next)
    (expectedSafe : Safe binder.scheme.quantified state expected)
    (accepted : inferStatementsFuel fuel context sources expected state = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.type]) := by
  have privacy := inferStatementsFuel_private binder.scheme.quantified fuel context sources expected state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical
    expectedBelow expectedSafe result accepted
  have progress := inferStatementsFuel_inferenceProperties ready catalog.formation catalog.canonical expectedBelow accepted
  exact lifetime.append progress.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem inferForItem
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {source : Syntax.ForItem} {result : ForItemForm × State}
    (accepted : inferForItemFuel fuel context source state = .ok result) :
    GeneralizationLifetime event entryNext result.2 outputs := by
  have privacy := inferForItemFuel_private binder.scheme.quantified fuel context source state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical result accepted
  have progress := inferForItemFuel_inferenceProperties ready catalog.formation catalog.canonical accepted
  simpa only [List.append_nil] using lifetime.append (newOutputs := [])
    progress.1.next_le privacy.1 privacy.2.1 (by simp) privacy.2.2

theorem inferForItems
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {sources : List Syntax.ForItem} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context sources state = .ok result) :
    GeneralizationLifetime event entryNext result.state outputs := by
  have privacy := inferForItemsFuel_private binder.scheme.quantified fuel context sources state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical result accepted
  have progress := inferForItemsFuel_inferenceProperties ready catalog.formation catalog.canonical accepted
  simpa only [List.append_nil] using lifetime.append (newOutputs := [])
    progress.1.next_le privacy.1 privacy.2.1 (by simp) privacy.2.2

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeExpressionSteps
/-! Lift a newly created event through real expression and list continuations.
These steps use accepted child and parent computations; the privacy of an
arbitrary continuation is never an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem recordExpression
    {entryNext : Nat} {state : State} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {start : Option Nat} {result : InferredExpression × State}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (typeBelow : type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (typeSafe : Safe binder.scheme.quantified state type)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : recordExpressionWithExpected context source id type form requirements
      expected state start = .ok result) :
    GeneralizationLifetime event entryNext result.2 (outputs ++ [result.1.type]) := by
  have privacy := recordExpressionWithExpected_private catalog ready typeBelow
    expectedBelow typeSafe expectedSafe lifetime.live accepted
  have properties := recordExpressionWithExpected_inferenceProperties ready typeBelow
    expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem group
    {fuel : Nat} {context : SourceInference.Context}
    {source inner : Syntax.Expr} {expected : Option Ty} {initial allocated : State}
    {id : ExpressionId} {child final : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .group inner)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (childAccepted : inferExprFuel fuel context inner expected allocated = .ok child)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have childProperties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical
    (fun type member => sameNext ▸ expectedBelow type member) childAccepted
  have recorded : recordExpressionWithExpected context source id child.1.type
      (.group child.1.id) [] expected child.2 = .ok final := by
    simpa only [inferExprFuel, allocation, form, childAccepted, bind, Except.bind] using accepted
  have result := lifetime.recordExpression catalog.catalog childProperties.2.1
    childProperties.2.2
    (fun type member => (sameNext ▸ expectedBelow type member).weaken childProperties.1.next_le)
    (lifetime.values _ (List.mem_singleton_self _))
    (fun type member => lifetime.older type (sameNext ▸ expectedBelow type member)) recorded
  have finalLifetime := result.restrict_outputs (selected := [final.1.type])
    (by intro type member; exact List.mem_append_right _ member)
  simpa only [sameNext] using finalLifetime

theorem tuple
    {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Expr} {elements : Syntax.DelimitedList Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {child : List InferredExpression × State} {final : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .tuple elements)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (childAccepted : inferExprsFuel fuel context elements.elements allocated = .ok child)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.2
      (child.1.map (·.type))) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have childProperties := inferExprsFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical childAccepted
  have typeBelow : (Ty.productMany (child.1.map (·.type))).VariablesBelow child.2.inference.next := by
    apply Ty.variablesBelow_productMany
    intro type member
    obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
    exact childProperties.2.2 value present
  have recorded : recordExpressionWithExpected context source id
      (Ty.productMany (child.1.map (·.type))) (.tuple (child.1.map (·.id)))
      [] expected child.2 = .ok final := by
    simpa only [inferExprFuel, allocation, form, childAccepted, bind, Except.bind] using accepted
  have result := lifetime.recordExpression catalog.catalog childProperties.2.1 typeBelow
    (fun type member => (sameNext ▸ expectedBelow type member).weaken childProperties.1.next_le)
    (safe_productMany _ _ _ lifetime.values)
    (fun type member => lifetime.older type (sameNext ▸ expectedBelow type member)) recorded
  have finalLifetime := result.restrict_outputs (selected := [final.1.type])
    (by intro type member; exact List.mem_append_right _ member)
  simpa only [sameNext] using finalLifetime

theorem expressions_head
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {sources : List Syntax.Expr} {initial : State}
    {head : InferredExpression × State} {tail result : List InferredExpression × State}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (headAccepted : inferExprFuel fuel context source none initial = .ok head)
    (tailAccepted : inferExprsFuel fuel context sources head.2 = .ok tail)
    (accepted : inferExprsFuel (fuel + 1) context (source :: sources) initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next head.2 [head.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 (result.1.map (·.type)) := by
  have headProperties := inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical
    (by simp) headAccepted
  have headWellFormed := (inferExprFuel_direct_progress headAccepted).wellFormed wellFormed
  have after := lifetime.inferExprs headProperties.2.1 headWellFormed catalog tailAccepted
  have resultEq : (head.1 :: tail.1, tail.2) = result := by
    simpa only [inferExprsFuel, headAccepted, tailAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  simpa only [List.map_cons, List.singleton_append] using after

theorem expressions_tail
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {sources : List Syntax.Expr} {initial : State}
    {head : InferredExpression × State} {tail result : List InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (headAccepted : inferExprFuel fuel context source none initial = .ok head)
    (tailAccepted : inferExprsFuel fuel context sources head.2 = .ok tail)
    (accepted : inferExprsFuel (fuel + 1) context (source :: sources) initial = .ok result)
    (lifetime : GeneralizationLifetime event head.2.inference.next tail.2 (tail.1.map (·.type))) :
    GeneralizationLifetime event initial.inference.next result.2 (result.1.map (·.type)) := by
  have headProperties := inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical
    (by simp) headAccepted
  have resultEq : (head.1 :: tail.1, tail.2) = result := by
    simpa only [inferExprsFuel, headAccepted, tailAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  have tailLifetime := lifetime.weaken_entry headProperties.1.next_le
  refine { tailLifetime with values := ?_ }
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · exact lifetime.older _ headProperties.2.2
  · exact lifetime.values _ member

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeOperatorSteps
/-! Actual operator and selected-call suffixes preserve a generalization
created by a child. Each step uses the accepted compiler computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {entryNext : Nat} {state : State} {outputs : List Ty}

theorem unaryOperator
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {context : SourceInference.Context} {operator : Syntax.UnaryOp} {operand : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {result : OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (operandBelow : operand.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (operandSafe : Safe binder.scheme.quantified state operand)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : inferUnaryOperator context operator operand expected integerLiterals state = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.type]) := by
  have privacy := inferUnaryOperator_private catalog ready operandBelow expectedBelow
    operandSafe expectedSafe lifetime.live accepted
  have properties := inferUnaryOperator_inferenceProperties ready operandBelow expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem binaryOperator
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {context : SourceInference.Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {result : OperatorInferenceResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (leftSafe : Safe binder.scheme.quantified state left)
    (rightSafe : Safe binder.scheme.quantified state right)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.type]) := by
  have privacy := inferBinaryOperator_private catalog ready leftBelow rightBelow expectedBelow
    leftSafe rightSafe expectedSafe lifetime.live accepted
  have properties := inferBinaryOperator_inferenceProperties ready leftBelow rightBelow expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem selectCandidate
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {context : SourceInference.Context} {name : String}
    {candidates : List ProgramFunctionSignature} {arguments : List InferredExpression}
    {integerLiterals : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {result : CandidateAttemptResult}
    (catalog : LifetimeInferenceContext context)
    (cataloged : candidates ⊆ context.signatures.functions)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe binder.scheme.quantified state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : selectFunctionCandidateFrom context name candidates arguments integerLiterals
      call expected state = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.result.type]) := by
  have privacy := selectFunctionCandidateFrom_private catalog.catalog cataloged ready lifetime.bound
    argumentsBelow expectedBelow argumentsSafe expectedSafe lifetime.live accepted
  have properties := selectFunctionCandidateFrom_inferenceProperties ready argumentsBelow
    (fun signature member => catalog.formation.function_scheme_body_variablesBelow
      (cataloged member) (catalog.canonical signature (cataloged member)) _) expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem fitExpected
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {context : SourceInference.Context} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (actualBelow : actual.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (actualSafe : Safe binder.scheme.quantified state actual.type)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : withExpected context state actual expected = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.expression.type]) := by
  have privacy := withExpected_private ready actualBelow expectedBelow actualSafe expectedSafe
    lifetime.live accepted
  have properties := withExpected_inferenceProperties ready actualBelow expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1)
    (withExpected_new_requirements_private catalog ready actualSafe expectedSafe accepted)

theorem recordSelectedResult
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : CandidateAttemptResult) (result : InferredExpression)
    (coercions : List CoercionStep)
    (ready : state.InferenceReady)
    (resultBelow : result.type.VariablesBelow state.inference.next)
    (resultSafe : Safe binder.scheme.quantified state result.type) :
    let recorded := recordSelectedCallResult source callee name arguments attempt result coercions state
    GeneralizationLifetime event entryNext recorded.2 (outputs ++ [recorded.1.type]) := by
  dsimp only
  have privacy := recordSelectedCallResult_private source callee name arguments attempt result coercions state
    resultSafe lifetime.live
  have properties := recordSelectedCallResult_inferenceProperties source callee name arguments
    attempt result coercions state ready resultBelow
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1)
    (fun row member fresh => False.elim (fresh (privacy.2.2.2 ▸ member)))

theorem recordSelected
    {attempt : CandidateAttemptResult}
    (lifetime : GeneralizationLifetime event entryNext attempt.state outputs)
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (ready : attempt.state.InferenceReady)
    (resultBelow : attempt.result.type.VariablesBelow attempt.state.inference.next)
    (resultSafe : Safe binder.scheme.quantified attempt.state attempt.result.type) :
    let recorded := recordSelectedCall source callee name arguments attempt
    GeneralizationLifetime event entryNext recorded.2 (outputs ++ [recorded.1.type]) :=
  lifetime.recordSelectedResult source callee name arguments attempt attempt.result []
    ready resultBelow resultSafe

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeCallSuffix
/-! Actual indirect and builtin call suffixes preserve child generalizations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {entryNext : Nat} {state : State} {outputs : List Ty}

theorem applyIndirect
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {context : SourceInference.Context} {call : ExpressionId} {callee : Ty}
    {arguments : List InferredExpression} {expected : Option Ty} {result : IndirectApplicationResult}
    (catalog : SignatureCatalogWellFormed context.signatures) (ready : state.InferenceReady)
    (calleeBelow : callee.VariablesBelow state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (calleeSafe : Safe binder.scheme.quantified state callee)
    (argumentsSafe : ∀ argument ∈ arguments, Safe binder.scheme.quantified state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : applyFunctionType context call callee arguments expected state = .ok result) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.result.type]) := by
  have privacy := applyFunctionType_private catalog ready lifetime.bound calleeBelow argumentsBelow
    expectedBelow calleeSafe argumentsSafe expectedSafe lifetime.live accepted
  have properties := applyFunctionType_inferenceProperties ready calleeBelow argumentsBelow expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1) privacy.2.2.2

theorem recordIndirect
    {application : IndirectApplicationResult}
    (lifetime : GeneralizationLifetime event entryNext application.state outputs)
    (source : Syntax.Expr) (callee : InferredExpression) (arguments : List InferredExpression)
    (ready : application.state.InferenceReady)
    (resultBelow : application.result.type.VariablesBelow application.state.inference.next)
    (resultSafe : Safe binder.scheme.quantified application.state application.result.type) :
    let recorded := recordIndirectCall source callee arguments application
    GeneralizationLifetime event entryNext recorded.2 (outputs ++ [recorded.1.type]) := by
  dsimp only
  have privacy := recordIndirectCall_private source callee arguments application resultSafe lifetime.live
  have properties := recordIndirectCall_inferenceProperties source callee arguments application ready resultBelow
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1)
    (fun row member fresh => False.elim (fresh (privacy.2.2.2 ▸ member)))

theorem recordBuiltin
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {result : InferredExpression × State}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe binder.scheme.quantified state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type)
    (accepted : recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    GeneralizationLifetime event entryNext result.2 (outputs ++ [result.1.type]) := by
  have privacy := recordBuiltinFunctionCall_private argumentsSafe expectedSafe lifetime.live accepted
  have properties := recordBuiltinFunctionCall_inferenceProperties ready argumentsBelow expectedBelow accepted
  exact lifetime.append properties.1.next_le privacy.1 privacy.2.2.1
    (fun type member => (List.mem_singleton.mp member) ▸ privacy.2.1)
    (fun row member fresh => False.elim (fresh (privacy.2.2.2 ▸ member)))

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeUnary
/-! A generalization created while checking a unary operand survives the
actual operator dispatch, candidate selection and result recording. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem unary
    {fuel : Nat} {context : SourceInference.Context}
    {source operand : Syntax.Expr} {operator : Syntax.Located Syntax.UnaryOp}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {child final : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .unary operator operand)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (childAccepted : inferExprFuel fuel context operand none allocated = .ok child)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have childProperties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical
    (by simp) childAccepted
  have lifetime : GeneralizationLifetime event initial.inference.next child.2 [child.1.type] := by
    simpa only [sameNext] using lifetime
  have childExpected : ∀ type ∈ expected, type.VariablesBelow child.2.inference.next :=
    fun type member => (sameNext ▸ expectedBelow type member).weaken childProperties.1.next_le
  have childSafe := lifetime.values child.1.type (List.mem_singleton_self _)
  have expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified child.2 type :=
    fun type member => lifetime.older type (expectedBelow type member)
  obtain ⟨value, state, actualChild, dispatch⟩ :=
    inferExprFuel_success_unary_facts form allocation accepted
  have sameChild := Except.ok.inj (actualChild.symm.trans childAccepted)
  cases sameChild
  have finish (result : OperatorInferenceResult)
      (operatorAccepted : inferUnaryOperator context operator.value value.type expected
        (relevantIntegerLiterals state allocated.integerLiterals.length [value]) state = .ok result)
      (recorded : recordExpressionWithExpected context source id result.type
        (.unary operator.value value.id) result.requirements expected result.state = .ok final) :
      GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
    have operatorLife := lifetime.unaryOperator catalog.catalog childProperties.2.1
      childProperties.2.2 childExpected childSafe expectedSafe operatorAccepted
    have operatorProperties := inferUnaryOperator_inferenceProperties childProperties.2.1
      childProperties.2.2 childExpected operatorAccepted
    have result := operatorLife.recordExpression catalog.catalog operatorProperties.2.1
      operatorProperties.2.2
      (fun type member => (childExpected type member).weaken operatorProperties.1.next_le)
      (operatorLife.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
      (fun type member => operatorLife.older type (expectedBelow type member)) recorded
    exact result.restrict_outputs (by intro type member; exact List.mem_append_right _ member)
  cases dispatch with
  | directFunction _ _ operatorAccepted recorded => exact finish _ operatorAccepted recorded
  | traitMethod _ operatorAccepted recorded => exact finish _ operatorAccepted recorded
  | @selectedFunction name head tail attempt _ lookup selected recorded =>
      have cataloged := functionsNamed_success_subset_catalog lookup
      have argumentsBelow : ∀ argument ∈ [value], argument.type.VariablesBelow state.inference.next := by
        intro argument member
        cases List.mem_singleton.mp member
        exact childProperties.2.2
      have argumentsSafe : ∀ argument ∈ [value], Safe binder.scheme.quantified state argument.type := by
        intro argument member
        cases List.mem_singleton.mp member
        exact childSafe
      have selectedLife := lifetime.selectCandidate catalog cataloged childProperties.2.1
        argumentsBelow childExpected argumentsSafe expectedSafe selected
      have selectedProperties := selectFunctionCandidateFrom_inferenceProperties childProperties.2.1
        argumentsBelow
        (fun signature member => catalog.formation.function_scheme_body_variablesBelow
          (cataloged member) (catalog.canonical signature (cataloged member)) _) childExpected selected
      let callee : Syntax.Expr := {
        span := operator.span
        value := .identifier {span := operator.span, value := name} }
      have recordedLife := selectedLife.recordSelected source callee name [value]
        selectedProperties.2.1 selectedProperties.2.2
        (selectedLife.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
      change recordSelectedCall source callee name [value] attempt = final at recorded
      rw [recorded] at recordedLife
      exact recordedLife.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end
