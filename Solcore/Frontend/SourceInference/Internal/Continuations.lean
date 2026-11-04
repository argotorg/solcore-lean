import Solcore.Frontend.SourceInference.Internal.LocalGeneralization

/-!
# Inference continuations

Statement, match and `for` positions keep their inference calls and continuations.
-/

section
-- leanmerge: from Solcore.Frontend.SourceInference.ForItemInferenceContinuation
/-! Header positions retain their exact initializer call and continuation
through all later header items. The sequence is the executable for-item fold. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.ForItemInferenceContinuation
open TypeSystem Detail

structure Occurrence (fuel : Nat) (context : Context) (source : Syntax.ForItem)
    (initial final : State) (forms : List ForItemForm) where
  entry : State
  result : ForItemForm × State
  accepted : inferForItemFuel fuel context source entry = .ok result
  ready : entry.InferenceReady
  before : initial.InferenceProgress entry
  continuation : result.2.InferenceProgress final
  retained : result.1 ∈ forms

theorem of_position {fuel : Nat} {context : Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems} {index : Nat} {source : Syntax.ForItem}
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : inferForItemsFuel fuel context sources initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (Occurrence fuel context source initial result.state result.items) := by
  induction sources generalizing initial result index with
  | nil => simp at position
  | cons head rest ih =>
      cases headRun : inferForItemFuel fuel context head initial with
      | error error => simp [inferForItemsFuel, headRun, bind, Except.bind] at accepted
      | ok pair =>
          rcases pair with ⟨headForm, headState⟩
          cases tailRun : inferForItemsFuel fuel context rest headState with
          | error error => simp [inferForItemsFuel, headRun, tailRun, bind, Except.bind] at accepted
          | ok tailResult =>
              have headProgress := inferForItemFuel_inferenceProperties ready formation canonical headRun
              have tailProgress := inferForItemsFuel_inferenceProperties headProgress.2 formation canonical tailRun
              have same : result = { items := headForm :: tailResult.items, state := tailResult.state } := by
                simp only [inferForItemsFuel, headRun, tailRun, bind, Except.bind,
                  pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
                exact accepted.symm
              cases same
              cases index with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at position
                  subst source
                  exact ⟨⟨initial, (headForm, headState), headRun, ready,
                    .refl ready.solved, tailProgress.1, List.mem_cons_self⟩⟩
              | succ index =>
                  obtain ⟨found⟩ := ih headProgress.2 tailRun position
                  exact ⟨⟨found.entry, found.result, found.accepted, found.ready,
                    headProgress.1.trans found.before, found.continuation,
                    List.mem_cons_of_mem _ found.retained⟩⟩

theorem Occurrence.initialized {fuel : Nat} {context : Context} {source : Syntax.ForItem}
    {initial final : State} {forms : List ForItemForm}
    (occurrence : Occurrence fuel context source initial final forms)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer))
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    ∃ childFuel, ∃ receipt : LocalHeaderRequirementTiming.Receipt childFuel context source occurrence.entry occurrence.result,
      receipt.ready.InferenceReady ∧ receipt.ready.InferenceProgress final ∧
        .letDecl receipt.binding.1 (some receipt.value.id) ∈ forms := by
  have accepted := occurrence.accepted
  cases fuel with
  | zero => simp [inferForItemFuel] at accepted
  | succ fuel =>
      obtain ⟨receipt⟩ := LocalHeaderRequirementTiming.of_initialized_accepted form accepted
      have inferred := receipt.initializer_inference occurrence.ready formation canonical
      exact ⟨fuel, receipt, inferred.2.1,
        (receipt.continuation inferred.2.1.solved).trans occurrence.continuation,
        receipt.recorded ▸ occurrence.retained⟩

end Solcore.Frontend.SourceInference.ForItemInferenceContinuation
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.ForStatementInferenceContinuation
/-! A for statement's actual condition, body, post sequence and two saved
scopes connect each header to the statement's returned inference state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.ForStatementInferenceContinuation
open TypeSystem Detail

def loopContext (context : Context) : Context :=
  { context with loopDepth := context.loopDepth + 1 }

def node (source : Syntax.Statement) (initial : State) (initializers : InferredForItems)
    (condition : InferredExpression) (body : BlockResult) (post : InferredForItems) : StatementNode :=
  { id := initial.allocateStatementId.1, span := source.span, type := .unit,
    form := .forLoop initializers.items condition.id post.items body.statements }

def finish (source : Syntax.Statement) (initial : State) (initializers : InferredForItems)
    (condition : InferredExpression) (body : BlockResult) (post : InferredForItems) : StatementResult :=
  { id := initial.allocateStatementId.1, type := .unit, hasValue := false, sawReturn := false,
    state := (post.state.restoreLexicalScope initial.allocateStatementId.2.lexicalScope).recordNode
      (.statement (node source initial initializers condition body post)) }

structure Receipt (fuel : Nat) (context : Context) (source : Syntax.Statement)
    (initializers : List Syntax.ForItem) (condition : Syntax.Expr) (post : List Syntax.ForItem)
    (body : Syntax.Located (List Syntax.Statement)) (expected : Ty) (initial : State) (result : StatementResult) where
  initialized : InferredForItems
  test : InferredExpression
  testState : State
  bodyResult : BlockResult
  postResult : InferredForItems
  initialization : inferForItemsFuel fuel context initializers initial.allocateStatementId.2 = .ok initialized
  tested : inferExprFuel fuel context condition (some .bool) initialized.state = .ok (test, testState)
  bodyAccepted : inferStatementsFuel fuel (loopContext context) body.value expected testState = .ok bodyResult
  postAccepted : inferForItemsFuel fuel (loopContext context) post
    (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) = .ok postResult
  completed : result = finish source initial initialized test bodyResult postResult

theorem of_accepted {fuel : Nat} {context : Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expected : Ty} {initial : State} {result : StatementResult}
    {headerSpan : Syntax.SourceSpan}
    (form : source.value = .forLoop headerSpan initializers condition post body)
    (accepted : inferStatementFuel (fuel + 1) context source expected initial = .ok result) :
    Nonempty (Receipt fuel context source initializers condition post body expected initial result) := by
  unfold inferStatementFuel at accepted
  simp only [form, bind, Except.bind] at accepted
  cases initRun : inferForItemsFuel fuel context initializers initial.allocateStatementId.2 with
  | error error => simp [initRun] at accepted
  | ok initialized =>
      cases testRun : inferExprFuel fuel context condition (some .bool) initialized.state with
      | error error => simp [initRun, testRun] at accepted
      | ok pair =>
          rcases pair with ⟨test, testState⟩
          cases bodyRun : inferStatementsFuel fuel (loopContext context) body.value expected testState with
          | error error =>
              simp only [loopContext] at bodyRun
              simp [initRun, testRun, bodyRun] at accepted
          | ok bodyResult =>
              simp only [loopContext] at bodyRun
              cases postRun : inferForItemsFuel fuel (loopContext context) post
                  (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) with
              | error error =>
                  simp only [loopContext] at postRun
                  simp [initRun, testRun, bodyRun, postRun] at accepted
              | ok postResult =>
                  simp only [loopContext] at postRun
                  simp only [initRun, testRun, bodyRun, postRun,
                    pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
                  exact ⟨⟨initialized, test, testState, bodyResult, postResult,
                    initRun, testRun, bodyRun, postRun, accepted.symm⟩⟩

namespace Receipt
variable {fuel : Nat} {context : Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expected : Ty} {initial : State} {result : StatementResult}

theorem inference_eq (receipt : Receipt fuel context source initializers condition post body expected initial result) :
    result.state.inference = receipt.postResult.state.inference :=
  congrArg (fun value : StatementResult => value.state.inference) receipt.completed

theorem recorded (receipt : Receipt fuel context source initializers condition post body expected initial result) :
    .statement (node source initial receipt.initialized receipt.test receipt.bodyResult receipt.postResult) ∈ result.state.nodes := by
  have same := congrArg (fun value : StatementResult => value.state.nodes) receipt.completed
  rw [same]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Initial and post header callers are both ready at their genuine entry;
each actual header return has a continuation to the same final statement. -/
theorem inference (receipt : Receipt fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next) :
    initial.allocateStatementId.2.InferenceReady ∧
      (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope).InferenceReady ∧
      receipt.initialized.state.InferenceProgress result.state ∧
      receipt.postResult.state.InferenceProgress result.state := by
  have allocated := State.InferenceProgress.allocateStatementId initial ready.solved
  have initProperties := inferForItemsFuel_inferenceProperties ready.allocateStatementId
    formation canonical receipt.initialization
  have testProperties := inferExprFuel_inferenceProperties initProperties.2 formation canonical
    (by intro type member; cases Option.some.inj member; simp [Ty.VariablesBelow, Ty.freeVariables, Ty.bool]) receipt.tested
  have bounds := expectedBelow.weaken (allocated.trans (initProperties.1.trans testProperties.1)).next_le
  have bodyProperties := inferStatementsFuel_inferenceProperties (context := loopContext context) testProperties.2.1 formation canonical
    bounds receipt.bodyAccepted
  have restored := State.restoreLexicalScope_inferenceProperties initProperties.2
    (testProperties.1.trans bodyProperties.1)
  have postProperties := inferForItemsFuel_inferenceProperties (context := loopContext context) restored.2 formation canonical receipt.postAccepted
  have last := State.InferenceProgress.of_inference_eq postProperties.2.solved receipt.inference_eq
  exact ⟨ready.allocateStatementId, restored.2, restored.1.trans (postProperties.1.trans last), last⟩

end Receipt
end Solcore.Frontend.SourceInference.ForStatementInferenceContinuation
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.ForHeaderInferenceContinuation
/-! Both positions in a for header retain their actual binder and initializer
through the complete for statement. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.ForStatementInferenceContinuation
open TypeSystem Detail

structure HeaderContinuation (context : Context) (source : Syntax.ForItem)
    (final : State) (statement : StatementNode) where
  childFuel : Nat
  entry : State
  result : ForItemForm × State
  receipt : LocalHeaderRequirementTiming.Receipt childFuel context source entry result
  ready : receipt.ready.InferenceReady
  continuation : receipt.ready.InferenceProgress final
  retained : receipt.binding.1 ∈ statement.form.initializedLetBinders

theorem Receipt.initialized_header {fuel : Nat} {context : Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {expected : Ty} {initial : State} {result : StatementResult}
    (receipt : Receipt fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (isPost : Bool) {index : Nat} {headerSource : Syntax.ForItem}
    (position : (if isPost then post else initializers)[index]? = some headerSource)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : headerSource.value = .letDecl name annotation (some initializer)) :
    Nonempty (HeaderContinuation (if isPost then loopContext context else context) headerSource result.state
      (node source initial receipt.initialized receipt.test receipt.bodyResult receipt.postResult)) := by
  have facts := receipt.inference ready formation canonical expectedBelow
  cases isPost with
  | false =>
      obtain ⟨occurrence⟩ := ForItemInferenceContinuation.of_position facts.1 formation canonical
        receipt.initialization position
      obtain ⟨childFuel, header, childReady, continuation, member⟩ := occurrence.initialized form formation canonical
      refine ⟨⟨childFuel, occurrence.entry, occurrence.result, header, childReady,
        continuation.trans facts.2.2.1, ?_⟩⟩
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨_, member, List.mem_singleton_self _⟩
  | true =>
      obtain ⟨occurrence⟩ := ForItemInferenceContinuation.of_position (context := loopContext context)
        facts.2.1 formation canonical receipt.postAccepted position
      obtain ⟨childFuel, header, childReady, continuation, member⟩ := occurrence.initialized form formation canonical
      refine ⟨⟨childFuel, occurrence.entry, occurrence.result, header, childReady,
        continuation.trans facts.2.2.2, ?_⟩⟩
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨_, member, List.mem_singleton_self _⟩

end Solcore.Frontend.SourceInference.ForStatementInferenceContinuation
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.StatementInferenceContinuation
/-! A source statement at an actual position in an accepted block has its own
successful inference call and a semantic continuation to the block's returned
state. Both sides of the call are derived from the real sequence computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.StatementInferenceContinuation
open TypeSystem Detail

structure Occurrence (context : Context) (source : Syntax.Statement) (expected : Ty)
    (initial final : State) where
  fuel : Nat
  entry : State
  result : StatementResult
  accepted : inferStatementFuel fuel context source expected entry = .ok result
  ready : entry.InferenceReady
  before : initial.InferenceProgress entry
  continuation : result.state.InferenceProgress final
  retained : result.state.nodes <+: final.nodes

/-- The position refers to the original syntax list, including repeated
identical syntax. The witness is obtained by following that list's real calls. -/
theorem of_position_with_bounds {fuel : Nat} {context : Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (ready : initial.InferenceReady)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (position : sources[index]? = some source) :
    ∃ occurrence : Occurrence context source expected initial result.state,
      occurrence.entry.NodesBelowNextOccurrence := by
  induction fuel generalizing sources initial result index with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
      cases sources with
      | nil => simp at position
      | cons head rest =>
          cases headRun : inferStatementFuel fuel context head expected initial with
          | error error => simp [inferStatementsFuel, headRun, bind, Except.bind] at accepted
          | ok headResult =>
              have headProgress := inferStatementFuel_inferenceProperties ready formation canonical expectedBelow headRun
              have headBelow := (inferStatementFuel_occurrenceBoundExtends headRun).nodesBelowNextOccurrence nodesBelow
              cases rest with
              | nil =>
                  have same : result.state = headResult.state := by
                    simp only [inferStatementsFuel, headRun, bind, Except.bind, pure, Pure.pure,
                      Except.pure, Except.ok.injEq] at accepted
                    exact (congrArg BlockResult.state accepted).symm
                  cases index with
                  | zero =>
                      simp only [List.getElem?_cons_zero, Option.some.injEq] at position
                      subst source
                      exact ⟨⟨fuel, initial, headResult, headRun, ready,
                        .refl ready.solved, same.symm ▸ State.InferenceProgress.refl headProgress.2.1.solved,
                        same.symm ▸ List.prefix_refl _⟩, nodesBelow⟩
                  | succ index => simp at position
              | cons next remaining =>
                  cases tailRun : inferStatementsFuel fuel context (next :: remaining) expected headResult.state with
                  | error error => simp [inferStatementsFuel, headRun, tailRun, bind, Except.bind] at accepted
                  | ok tailResult =>
                      have same : result.state = tailResult.state := by
                        simp only [inferStatementsFuel, headRun, tailRun, bind, Except.bind,
                          pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
                        exact (congrArg BlockResult.state accepted).symm
                      have afterExpected := expectedBelow.weaken headProgress.1.next_le
                      cases index with
                      | zero =>
                          simp only [List.getElem?_cons_zero, Option.some.injEq] at position
                          subst source
                          have tailProgress := inferStatementsFuel_inferenceProperties headProgress.2.1
                            formation canonical afterExpected tailRun
                          exact ⟨⟨fuel, initial, headResult, headRun, ready, .refl ready.solved,
                            same.symm ▸ tailProgress.1, same.symm ▸
                              inferStatementsFuel_preserves_nodesPrefix tailRun (List.prefix_refl _) headBelow (Nat.le_refl _)⟩, nodesBelow⟩
                      | succ index =>
                          have restPosition : (next :: remaining)[index]? = some source := position
                          obtain ⟨found, foundBelow⟩ := ih headProgress.2.1 headBelow afterExpected tailRun restPosition
                          exact ⟨⟨found.fuel, found.entry, found.result, found.accepted, found.ready,
                            headProgress.1.trans found.before, same.symm ▸ found.continuation,
                            same.symm ▸ found.retained⟩, foundBelow⟩

theorem of_position {fuel : Nat} {context : Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (ready : initial.InferenceReady)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (Occurrence context source expected initial result.state) := by
  obtain ⟨occurrence, _⟩ := of_position_with_bounds ready nodesBelow formation canonical expectedBelow accepted position
  exact ⟨occurrence⟩

/-- An initialized declaration's actual child return reaches the whole block,
including every later statement. Annotation bounds come from source resolution. -/
theorem Occurrence.initialized {context : Context} {source : Syntax.Statement}
    {expected : Ty} {initial final : State}
    (occurrence : Occurrence context source expected initial final)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer))
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) :
    ∃ childFuel, ∃ receipt : LocalLetRequirementTiming.Receipt childFuel context source occurrence.entry occurrence.result,
      receipt.ready.InferenceReady ∧ receipt.ready.InferenceProgress final := by
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, inferStatementFuel] at accepted
  | succ fuel =>
      rw [fuelEq] at accepted
      obtain ⟨receipt⟩ := LocalLetRequirementTiming.of_initialized_accepted form accepted
      have inferred := receipt.initializer_inference occurrence.ready formation canonical
      exact ⟨fuel, receipt, inferred.2.1,
        (receipt.continuation inferred.2.1.solved).trans occurrence.continuation⟩

end Solcore.Frontend.SourceInference.StatementInferenceContinuation
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.MatchCaseInferenceContinuation
/-! A match arm's actual body call retains the continuation through the later
arms and their lexical restoration. Positions refer to the original syntax. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.MatchCaseInferenceContinuation
open TypeSystem Detail

structure Occurrence (context : Context) (source : Syntax.MatchCase) (expected : Ty)
    (initial final : State) where
  fuel : Nat
  entry : State
  result : BlockResult
  accepted : inferStatementsFuel fuel context source.value.body.value expected entry = .ok result
  ready : entry.InferenceReady
  nodesBelow : entry.NodesBelowNextOccurrence
  expectedBelow : expected.VariablesBelow entry.inference.next
  before : initial.InferenceProgress entry
  continuation : result.state.InferenceProgress final
  retained : result.state.nodes <+: final.nodes

theorem of_position {fuel : Nat} {context : Context} {sources : List Syntax.MatchCase}
    {scrutinee expected : Ty} {initial : State} {result : MatchCasesResult}
    {index : Nat} {source : Syntax.MatchCase}
    (ready : initial.InferenceReady)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (scrutineeBelow : scrutinee.VariablesBelow initial.inference.next)
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (accepted : inferMatchCasesFuel fuel context scrutinee expected initial.lexicalScope sources initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (Occurrence context source expected initial result.state) := by
  induction fuel generalizing sources initial result index with
  | zero => simp [inferMatchCasesFuel] at accepted
  | succ fuel ih =>
      cases sources with
      | nil => simp at position
      | cons head rest =>
          unfold inferMatchCasesFuel at accepted
          simp only [bind, Except.bind] at accepted
          cases patternRun : inferMatchPatternFuel fuel context head.value.pattern scrutinee initial with
          | error error => simp [patternRun] at accepted
          | ok pair =>
              obtain ⟨pattern, patternState⟩ := pair
              simp only [patternRun] at accepted
              cases bodyRun : inferStatementsFuel fuel context head.value.body.value expected patternState with
              | error error => simp [bodyRun] at accepted
              | ok body =>
                  simp only [bodyRun] at accepted
                  cases tailRun : inferMatchCasesFuel fuel context scrutinee expected initial.lexicalScope rest
                      (body.state.restoreLexicalScope initial.lexicalScope) with
                  | error error => simp [tailRun] at accepted
                  | ok tail =>
                      simp only [tailRun, pure, Pure.pure, Except.pure] at accepted
                      injection accepted with same
                      subst result
                      have patternProperties := inferMatchPatternFuel_inferenceProperties ready scrutineeBelow formation patternRun
                      have patternBelow := (inferMatchPatternFuel_occurrenceBoundExtends patternRun).nodesBelowNextOccurrence nodesBelow
                      have expectedAtPattern := expectedBelow.weaken patternProperties.1.next_le
                      have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1
                        formation canonical expectedAtPattern bodyRun
                      have bodyBelow := (inferStatementsFuel_occurrenceBoundExtends bodyRun).nodesBelowNextOccurrence patternBelow
                      have restored := State.restoreLexicalScope_inferenceProperties ready
                        (patternProperties.1.trans bodyProperties.1)
                      have tailProperties := inferMatchCasesFuel_inferenceProperties restored.2 formation canonical
                        (scrutineeBelow.weaken restored.1.next_le) (expectedBelow.weaken restored.1.next_le) rfl tailRun
                      cases index with
                      | zero =>
                          simp only [List.getElem?_cons_zero, Option.some.injEq] at position
                          subst source
                          exact ⟨⟨fuel, patternState, body, bodyRun, patternProperties.2.1,
                            patternBelow, expectedAtPattern, patternProperties.1,
                            (State.InferenceProgress.restoreLexicalScope body.state initial.lexicalScope
                              bodyProperties.2.1.solved).trans tailProperties.1,
                            inferMatchCasesFuel_preserves_nodesPrefix (result := tail) (state := body.state.restoreLexicalScope initial.lexicalScope) tailRun (List.prefix_refl _) bodyBelow (Nat.le_refl _)⟩⟩
                      | succ index =>
                          obtain ⟨found⟩ := ih restored.2 bodyBelow
                            (scrutineeBelow.weaken restored.1.next_le)
                            (expectedBelow.weaken restored.1.next_le) tailRun position
                          exact ⟨⟨found.fuel, found.entry, found.result, found.accepted, found.ready,
                            found.nodesBelow, found.expectedBelow, restored.1.trans found.before,
                            found.continuation, found.retained⟩⟩

end Solcore.Frontend.SourceInference.MatchCaseInferenceContinuation
end
