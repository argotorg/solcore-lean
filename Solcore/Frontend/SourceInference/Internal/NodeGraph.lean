import Solcore.Frontend.SourceInference.Expression
import Solcore.Frontend.SourceInference.Program
import Solcore.Frontend.SourceInference.Internal.StateProperties
import Lean

/-!
# Node graph and fuel agreement

Graph facts of the inference node table, and agreement of inference results across fuel.
-/

section
-- leanmerge: from Solcore.Frontend.SourceInference.PatternFuelAgreement
/-! Increasing the structural inference budget preserves each successful
pattern result, including its complete state and ordered instructions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.Frontend.SourceInference.Detail
open TypeSystem

private def Stable {α : Type} (action : Nat → Except Error α) (fuel : Nat) : Prop :=
  ∀ extra result, action fuel = .ok result → action (fuel + extra) = .ok result

private theorem pattern_stable (context : Context) :
    (∀ fuel pattern expected seen state,
      Stable (fun budget => inferMatchPatternFlatFuel budget context pattern expected seen state) fuel) ∧
    (∀ fuel patterns expected seen state,
      Stable (fun budget => inferMatchPatternsFlatFuel budget context patterns expected seen state) fuel) := by
  apply inferMatchPatternFlatFuel.mutual_induct context
    (motive1 := fun fuel pattern expected seen state =>
      Stable (fun fuel => inferMatchPatternFlatFuel fuel context pattern expected seen state) fuel)
    (motive2 := fun fuel patterns expected seen state =>
      Stable (fun fuel => inferMatchPatternsFlatFuel fuel context patterns expected seen state) fuel)
  all_goals
    intros
    unfold Stable at *
    intro extra result accepted
    simp_all only [Nat.succ_add, inferMatchPatternFlatFuel, inferMatchPatternsFlatFuel,
      bind, Except.bind]
    repeat' first | split at accepted
    all_goals try cases accepted
    all_goals try simp_all [pure, Except.pure]
    all_goals grind

theorem inferMatchPatternFlatFuel_success_mono {fuel : Nat} {context : Context}
    {pattern : Syntax.Pattern} {expected : Ty} {seen : List String} {state : State} {result : InferredPattern}
    (accepted : inferMatchPatternFlatFuel fuel context pattern expected seen state = .ok result)
    (extra : Nat) : inferMatchPatternFlatFuel (fuel + extra) context pattern expected seen state = .ok result :=
  (pattern_stable context).1 fuel pattern expected seen state extra result accepted

theorem inferMatchPatternsFlatFuel_success_mono {fuel : Nat} {context : Context}
    {patterns : List Syntax.Pattern} {expected : List Ty} {seen : List String} {state : State} {result : InferredPatterns}
    (accepted : inferMatchPatternsFlatFuel fuel context patterns expected seen state = .ok result)
    (extra : Nat) : inferMatchPatternsFlatFuel (fuel + extra) context patterns expected seen state = .ok result :=
  (pattern_stable context).2 fuel patterns expected seen state extra result accepted

theorem inferMatchPatternFuel_success_mono {fuel : Nat} {context : Context}
    {pattern : Syntax.Pattern} {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (accepted : inferMatchPatternFuel fuel context pattern expected state = .ok result)
    (extra : Nat) : inferMatchPatternFuel (fuel + extra) context pattern expected state = .ok result := by
  unfold inferMatchPatternFuel at accepted ⊢
  cases selected : inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [selected, bind, Except.bind] at accepted
  | ok output =>
    have same := inferMatchPatternFlatFuel_success_mono selected extra
    simpa only [selected, same, bind, Except.bind] using accepted

end Solcore.Frontend.SourceInference.Detail
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.ExpressionFuelAgreement
/-! Successful structural inference keeps the complete result when its
recursion budget increases. All original state and metadata remain exact. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
namespace Solcore.Frontend.SourceInference.Detail
open TypeSystem

private theorem inference_stable :
    (∀ fuel context expression expected state, Stable (fun budget => inferExprFuel budget context expression expected state) fuel) ∧
    (∀ fuel context source id instantiation arguments expected state, Stable (fun budget => inferConstructorApplicationFuel budget context source id instantiation arguments expected state) fuel) ∧
    (∀ fuel context sources expected state, Stable (fun budget => inferConstructorArgumentsFuel budget context sources expected state) fuel) ∧
    (∀ fuel context statements expectedReturn state, Stable (fun budget => inferStatementsFuel budget context statements expectedReturn state) fuel) ∧
    (∀ fuel context statement expectedReturn state, Stable (fun budget => inferStatementFuel budget context statement expectedReturn state) fuel) ∧
    (∀ fuel context items state, Stable (fun budget => inferForItemsFuel budget context items state) fuel) ∧
    (∀ fuel context item state, Stable (fun budget => inferForItemFuel budget context item state) fuel) ∧
    (∀ fuel context target state, Stable (fun budget => inferPlaceFuel budget context target state) fuel) ∧
    (∀ fuel context target operator value state, Stable (fun budget => inferAssignedValueFuel budget context target operator value state) fuel) ∧
    (∀ fuel context expressions state, Stable (fun budget => inferExprsFuel budget context expressions state) fuel) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state, Stable (fun budget => inferMatchCasesFuel budget context scrutineeType expectedReturn outerScope cases state) fuel) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      Stable (fun budget => inferExprFuel budget context expression expected state) fuel)
    (motive2 := fun fuel context source id instantiation arguments expected state =>
      Stable (fun budget => inferConstructorApplicationFuel budget context source id instantiation arguments expected state) fuel)
    (motive3 := fun fuel context sources expected state =>
      Stable (fun budget => inferConstructorArgumentsFuel budget context sources expected state) fuel)
    (motive4 := fun fuel context statements expectedReturn state =>
      Stable (fun budget => inferStatementsFuel budget context statements expectedReturn state) fuel)
    (motive5 := fun fuel context statement expectedReturn state =>
      Stable (fun budget => inferStatementFuel budget context statement expectedReturn state) fuel)
    (motive6 := fun fuel context items state =>
      Stable (fun budget => inferForItemsFuel budget context items state) fuel)
    (motive7 := fun fuel context item state =>
      Stable (fun budget => inferForItemFuel budget context item state) fuel)
    (motive8 := fun fuel context target state =>
      Stable (fun budget => inferPlaceFuel budget context target state) fuel)
    (motive9 := fun fuel context target operator value state =>
      Stable (fun budget => inferAssignedValueFuel budget context target operator value state) fuel)
    (motive10 := fun fuel context expressions state =>
      Stable (fun budget => inferExprsFuel budget context expressions state) fuel)
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope cases state =>
      Stable (fun budget => inferMatchCasesFuel budget context scrutineeType expectedReturn outerScope cases state) fuel)
  case case23 =>
    intro fuel context source id instantiation arguments expected state arity children
    unfold Stable at *
    intro extra result accepted
    unfold inferConstructorApplicationFuel at accepted ⊢
    simp only [arity, ↓reduceIte] at accepted ⊢
    simp_all [bind, Except.bind, pure, Except.pure]
    repeat' first | split at accepted
    all_goals try contradiction
    all_goals grind
  case case44 =>
    intro context statement expectedReturn state fuel id allocated allocation
      scrutinees arms form sources many casesInduction defaultInduction expressionsInduction
    have casesByType := fun type state =>
      casesInduction ⟨state.allocateExpressionId.fst, type⟩ state
    clear casesInduction
    unfold Stable at *
    intro extra result accepted
    simp only [Nat.succ_add] at *
    unfold inferStatementFuel at accepted ⊢
    simp_all [bind, Except.bind, pure, Except.pure]
    repeat' first | split at accepted
    all_goals try cases accepted
    all_goals try simp_all
    all_goals grind
  case case70 =>
    intro fuel context target operator value state placeInduction valueInduction
    unfold Stable at *
    intro extra result accepted
    unfold inferAssignedValueFuel at accepted ⊢
    cases found : inferPlaceFuel fuel context target state with
    | error error => simp [found, bind, Except.bind] at accepted
    | ok output =>
        have larger := placeInduction extra output found
        have valueAtTarget := valueInduction output.1
        clear valueInduction
        simp only [found, larger, bind, Except.bind] at accepted ⊢
        cases operator <;> simp_all [pure, Except.pure]
        all_goals repeat' first | split at accepted
        all_goals try cases accepted
        all_goals grind
  all_goals
    intros
    unfold Stable at *
    intro extra result accepted
    simp only [Nat.succ_add] at *
    first
      | unfold inferExprFuel at accepted ⊢
      | unfold inferConstructorApplicationFuel at accepted ⊢
      | unfold inferConstructorArgumentsFuel at accepted ⊢
      | unfold inferStatementsFuel at accepted ⊢
      | unfold inferStatementFuel at accepted ⊢
      | unfold inferForItemsFuel at accepted ⊢
      | unfold inferForItemFuel at accepted ⊢
      | unfold inferPlaceFuel at accepted ⊢
      | unfold inferAssignedValueFuel at accepted ⊢
      | unfold inferExprsFuel at accepted ⊢
      | unfold inferMatchCasesFuel at accepted ⊢
    simp_all [bind, Except.bind, pure, Except.pure]
    repeat' first | split at accepted
    all_goals try cases accepted
    all_goals try simp_all
    all_goals grind [inferMatchPatternFuel_success_mono]

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferExprFuel_success_mono
    {fuel : Nat} {context : Context}
    {expression : Syntax.Expr}
    {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (accepted : inferExprFuel fuel context expression expected state = .ok result)
    (extra : Nat) :
    inferExprFuel (fuel + extra) context expression expected state = .ok result :=
  inference_stable.1 fuel context expression expected state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferConstructorApplicationFuel_success_mono
    {fuel : Nat} {context : Context}
    {source : Syntax.Expr}
    {id : ExpressionId}
    {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr}
    {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (accepted : inferConstructorApplicationFuel fuel context source id instantiation arguments expected state = .ok result)
    (extra : Nat) :
    inferConstructorApplicationFuel (fuel + extra) context source id instantiation arguments expected state = .ok result :=
  inference_stable.2.1 fuel context source id instantiation arguments expected state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferConstructorArgumentsFuel_success_mono
    {fuel : Nat} {context : Context}
    {sources : List Syntax.Expr}
    {expected : List Ty}
    {state : State} {result : List InferredExpression × State}
    (accepted : inferConstructorArgumentsFuel fuel context sources expected state = .ok result)
    (extra : Nat) :
    inferConstructorArgumentsFuel (fuel + extra) context sources expected state = .ok result :=
  inference_stable.2.2.1 fuel context sources expected state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferStatementsFuel_success_mono
    {fuel : Nat} {context : Context}
    {statements : List Syntax.Statement}
    {expectedReturn : Ty}
    {state : State} {result : BlockResult}
    (accepted : inferStatementsFuel fuel context statements expectedReturn state = .ok result)
    (extra : Nat) :
    inferStatementsFuel (fuel + extra) context statements expectedReturn state = .ok result :=
  inference_stable.2.2.2.1 fuel context statements expectedReturn state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferStatementFuel_success_mono
    {fuel : Nat} {context : Context}
    {statement : Syntax.Statement}
    {expectedReturn : Ty}
    {state : State} {result : StatementResult}
    (accepted : inferStatementFuel fuel context statement expectedReturn state = .ok result)
    (extra : Nat) :
    inferStatementFuel (fuel + extra) context statement expectedReturn state = .ok result :=
  inference_stable.2.2.2.2.1 fuel context statement expectedReturn state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferForItemsFuel_success_mono
    {fuel : Nat} {context : Context}
    {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (accepted : inferForItemsFuel fuel context items state = .ok result)
    (extra : Nat) :
    inferForItemsFuel (fuel + extra) context items state = .ok result :=
  inference_stable.2.2.2.2.2.1 fuel context items state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferForItemFuel_success_mono
    {fuel : Nat} {context : Context}
    {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (accepted : inferForItemFuel fuel context item state = .ok result)
    (extra : Nat) :
    inferForItemFuel (fuel + extra) context item state = .ok result :=
  inference_stable.2.2.2.2.2.2.1 fuel context item state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferPlaceFuel_success_mono
    {fuel : Nat} {context : Context}
    {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (accepted : inferPlaceFuel fuel context target state = .ok result)
    (extra : Nat) :
    inferPlaceFuel (fuel + extra) context target state = .ok result :=
  inference_stable.2.2.2.2.2.2.2.1 fuel context target state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferAssignedValueFuel_success_mono
    {fuel : Nat} {context : Context}
    {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp}
    {value : Syntax.Expr}
    {state : State} {result : AssignmentResolution × InferredExpression × State}
    (accepted : inferAssignedValueFuel fuel context target operator value state = .ok result)
    (extra : Nat) :
    inferAssignedValueFuel (fuel + extra) context target operator value state = .ok result :=
  inference_stable.2.2.2.2.2.2.2.2.1 fuel context target operator value state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferExprsFuel_success_mono
    {fuel : Nat} {context : Context}
    {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (accepted : inferExprsFuel fuel context expressions state = .ok result)
    (extra : Nat) :
    inferExprsFuel (fuel + extra) context expressions state = .ok result :=
  inference_stable.2.2.2.2.2.2.2.2.2.1 fuel context expressions state extra result accepted

/-- A successful traversal has the exact same result at every larger budget. -/
theorem inferMatchCasesFuel_success_mono
    {fuel : Nat} {context : Context}
    {scrutineeType : Ty}
    {expectedReturn : Ty}
    {outerScope : LexicalScope}
    {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (accepted : inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope cases state = .ok result)
    (extra : Nat) :
    inferMatchCasesFuel (fuel + extra) context scrutineeType expectedReturn outerScope cases state = .ok result :=
  inference_stable.2.2.2.2.2.2.2.2.2.2 fuel context scrutineeType expectedReturn outerScope cases state extra result accepted

/-- Two successful budgets retain exactly the same statement body and state. -/
theorem inferStatementsFuel_success_unique_fuel
    {firstFuel secondFuel : Nat} {context : Context}
    {statements : List Syntax.Statement} {expectedReturn : Ty} {state : State}
    {first second : BlockResult}
    (firstAccepted : inferStatementsFuel firstFuel context statements expectedReturn state = .ok first)
    (secondAccepted : inferStatementsFuel secondFuel context statements expectedReturn state = .ok second) :
    first = second := by
  have firstLarger := inferStatementsFuel_success_mono firstAccepted secondFuel
  have secondLarger := inferStatementsFuel_success_mono secondAccepted firstFuel
  rw [Nat.add_comm secondFuel firstFuel] at secondLarger
  exact Except.ok.inj (firstLarger.symm.trans secondLarger)

end Solcore.Frontend.SourceInference.Detail
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.FunctionFuelAgreement
/-! Successful checks of the same original function retain the complete same
checked function, even when their structural inference budgets differ. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference

/-- Equality includes the typed body, substitutions, and solved requirements. -/
theorem checkFunctionBody_success_unique_fuel
    {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature} {firstFuel secondFuel : Nat}
    {first second : CheckedFunction}
    (firstAccepted : checkFunctionBody environment signatures signature firstFuel = .ok first)
    (secondAccepted : checkFunctionBody environment signatures signature secondFuel = .ok second) :
    first = second := by
  obtain ⟨firstDeclaration, firstBody, firstState, firstResult, firstFound,
    firstInferred, firstUnified, firstFinalized, firstExact⟩ :=
    checkFunctionBody_success_witness firstAccepted
  obtain ⟨secondDeclaration, secondBody, secondState, secondResult, secondFound,
    secondInferred, secondUnified, secondFinalized, secondExact⟩ :=
    checkFunctionBody_success_witness secondAccepted
  have declarationEq := Option.some.inj (firstFound.symm.trans secondFound)
  subst secondDeclaration
  have bodyEq := Detail.inferStatementsFuel_success_unique_fuel
    firstInferred secondInferred
  subst secondBody
  have stateEq := Except.ok.inj (firstUnified.symm.trans secondUnified)
  subst secondState
  have resultEq := Except.ok.inj (firstFinalized.symm.trans secondFinalized)
  subst secondResult
  exact firstExact.trans secondExact.symm

end Solcore.Frontend.SourceInference
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.NodeShapeProperties
/-! Inference may attach coercion metadata to existing expressions. Their
identities and syntax, including child edges and local targets, stay fixed. -/
set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

def SameNodeShape : Node → Node → Prop
  | .expression before, .expression after => before.id = after.id ∧ before.form = after.form
  | .statement before, .statement after => before.id = after.id ∧ before.form = after.form
  | _, _ => False

def NodeShapesPreserved (before after : List Node) : Prop :=
  ∀ node ∈ before, ∃ current ∈ after, SameNodeShape node current

namespace SameNodeShape

theorem refl (node : Node) : SameNodeShape node node := by
  cases node <;> exact ⟨rfl, rfl⟩

theorem trans {before middle after : Node}
    (first : SameNodeShape before middle) (second : SameNodeShape middle after) :
    SameNodeShape before after := by
  cases before <;> cases middle <;> cases after <;>
    simp only [SameNodeShape] at first second ⊢
  all_goals first
  | contradiction
  | exact ⟨first.1.trans second.1, first.2.trans second.2⟩

theorem id {before after : Node} (same : SameNodeShape before after) :
    before.id = after.id := by
  cases before <;> cases after <;> simp only [SameNodeShape] at same
  all_goals first
  | contradiction
  | exact congrArg NodeId.expression same.1
  | exact congrArg NodeId.statement same.1

theorem references {before after : Node} (same : SameNodeShape before after) :
    before.references = after.references := by
  cases before <;> cases after <;> simp only [SameNodeShape] at same
  all_goals first
  | contradiction
  | exact congrArg ExpressionForm.references same.2
  | exact congrArg StatementForm.references same.2

end SameNodeShape

namespace NodeShapesPreserved

theorem refl (nodes : List Node) : NodeShapesPreserved nodes nodes :=
  fun node member => ⟨node, member, .refl node⟩

theorem trans {before middle after : List Node}
    (first : NodeShapesPreserved before middle)
    (second : NodeShapesPreserved middle after) : NodeShapesPreserved before after := by
  intro node member
  obtain ⟨current, present, firstShape⟩ := first node member
  obtain ⟨later, retained, secondShape⟩ := second current present
  exact ⟨later, retained, firstShape.trans secondShape⟩

theorem of_eq {before after : List Node} (same : after = before) :
    NodeShapesPreserved before after := same ▸ refl before

theorem recordNode (state : State) (node : Node) :
    NodeShapesPreserved state.nodes (state.recordNode node).nodes := by
  intro previous member
  exact ⟨previous, List.mem_append_left _ member, .refl previous⟩

theorem modifyExpressionNode (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode)
    (form : ∀ node, (modify node).form = node.form) :
    NodeShapesPreserved state.nodes (state.modifyExpressionNode id modify).nodes := by
  intro node member
  unfold State.modifyExpressionNode
  refine ⟨_, List.mem_map.mpr ⟨node, member, rfl⟩, ?_⟩
  cases node with
  | statement node => exact ⟨rfl, rfl⟩
  | expression node =>
      dsimp
      split
      · rename_i selected
        exact ⟨selected, (form node).symm⟩
      · exact ⟨rfl, rfl⟩

theorem attachExpressionCoercions (state : State)
    (entries : List Detail.ExpressionCoercions) :
    NodeShapesPreserved state.nodes (Detail.attachExpressionCoercions state entries).nodes := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact refl _
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      exact (modifyExpressionNode state entry.expression
        (fun node => Detail.appendExpressionCoercions node entry.coercions)
        (fun _ => rfl)).trans (ih _)

end NodeShapesPreserved
end Solcore.Frontend.SourceInference
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.NodeGraphProperties
/-!
Graph facts for the actual inference node table.  A completed node may only
refer to identities already in that table.  Coercion attachment changes
payloads but preserves both identities and child edges.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

def NodeIdsPresent (references : List NodeId) (nodes : List Node) : Prop :=
  references ⊆ nodes.map Node.id

def NodesClosed (nodes : List Node) : Prop :=
  ∀ node ∈ nodes, NodeIdsPresent node.references nodes

structure NodeGraphProgress (before after : State) : Prop where
  ids : NodeIdsPresent (before.nodes.map Node.id) after.nodes
  closed : NodesClosed before.nodes → NodesClosed after.nodes
  shapes : NodeShapesPreserved before.nodes after.nodes

namespace NodeIdsPresent

theorem nil (nodes : List Node) : NodeIdsPresent [] nodes := by
  simp [NodeIdsPresent]

theorem append {left right : List NodeId} {nodes : List Node}
    (first : NodeIdsPresent left nodes) (second : NodeIdsPresent right nodes) :
    NodeIdsPresent (left ++ right) nodes := by
  intro id member
  rcases List.mem_append.mp member with member | member
  · exact first member
  · exact second member

theorem cons {head : NodeId} {tail : List NodeId} {nodes : List Node}
    (first : NodeIdsPresent [head] nodes) (rest : NodeIdsPresent tail nodes) :
    NodeIdsPresent (head :: tail) nodes :=
  append first rest

theorem transport {references : List NodeId} {before after : State}
    (present : NodeIdsPresent references before.nodes)
    (progress : NodeGraphProgress before after) :
    NodeIdsPresent references after.nodes :=
  fun _ member => progress.ids (present member)

end NodeIdsPresent

namespace NodesClosed

theorem nil : NodesClosed [] := by
  simp [NodesClosed]

theorem record {nodes : List Node} (closed : NodesClosed nodes) (node : Node)
    (children : NodeIdsPresent node.references nodes) :
    NodesClosed (nodes ++ [node]) := by
  intro current member child reference
  rcases List.mem_append.mp member with old | fresh
  · exact List.mem_map.mpr (by
      rcases List.mem_map.mp (closed current old reference) with ⟨prior, priorMem, eq⟩
      exact ⟨prior, List.mem_append_left _ priorMem, eq⟩)
  · have eq : current = node := List.mem_singleton.mp fresh
    subst current
    rcases List.mem_map.mp (children reference) with ⟨prior, priorMem, eq⟩
    exact List.mem_map.mpr ⟨prior, List.mem_append_left _ priorMem, eq⟩

end NodesClosed

namespace NodeGraphProgress

theorem refl (state : State) : NodeGraphProgress state state :=
  ⟨fun _ member => member, fun closed => closed, .refl _⟩

theorem of_nodes_eq {before after : State} (eq : after.nodes = before.nodes) :
    NodeGraphProgress before after := by
  constructor
  · rw [eq]
    exact fun _ member => member
  · rw [eq]
    exact fun closed => closed
  · exact NodeShapesPreserved.of_eq eq

theorem trans {first middle last : State}
    (left : NodeGraphProgress first middle)
    (right : NodeGraphProgress middle last) :
    NodeGraphProgress first last :=
  ⟨fun _ member => right.ids (left.ids member),
    fun closed => right.closed (left.closed closed),
    left.shapes.trans right.shapes⟩

theorem recordNode (state : State) (node : Node)
    (children : NodeIdsPresent node.references state.nodes) :
    NodeGraphProgress state (state.recordNode node) := by
  constructor
  · intro id member
    simpa only [State.recordNode_nodes, List.map_append, List.map_cons,
      List.map_nil] using
      List.mem_append_left [node.id] member
  · exact fun closed => closed.record node children
  · exact NodeShapesPreserved.recordNode state node

theorem recordNode_present (state : State) (node : Node) :
    NodeIdsPresent [node.id] (state.recordNode node).nodes := by
  intro id member
  have eq := List.mem_singleton.mp member
  subst id
  simp [State.recordNode]

theorem modifyExpressionNode (state : State) (id : ExpressionId)
    (modify : ExpressionNode → ExpressionNode)
    (form : ∀ node, (modify node).form = node.form) :
    NodeGraphProgress state (state.modifyExpressionNode id modify) := by
  have ids : (state.modifyExpressionNode id modify).nodes.map Node.id =
      state.nodes.map Node.id := by
    simp only [State.modifyExpressionNode, List.map_map]
    apply List.map_congr_left
    intro node member
    cases node with
    | statement node => rfl
    | expression node =>
        dsimp
        split
        · rename_i eq
          simp [Node.id, eq]
        · rfl
  constructor
  · rw [NodeIdsPresent, ids]
    exact fun _ member => member
  · intro closed node member child reference
    rw [State.modifyExpressionNode] at member
    rcases List.mem_map.mp member with ⟨prior, priorMem, eq⟩
    have refs : node.references = prior.references := by
      rw [← eq]
      cases prior with
      | statement prior => rfl
      | expression prior =>
          dsimp
          split
          · simp [Node.references, form]
          · rfl
    rw [ids]
    exact closed prior priorMem (by simpa only [refs] using reference)
  · exact NodeShapesPreserved.modifyExpressionNode state id modify form

theorem attachExpressionCoercions (state : State)
    (entries : List Detail.ExpressionCoercions) :
    NodeGraphProgress state (Detail.attachExpressionCoercions state entries) := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact refl state
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      exact (modifyExpressionNode state entry.expression
        (fun node => Detail.appendExpressionCoercions node entry.coercions)
        (fun _ => rfl)).trans (ih _)

end NodeGraphProgress

/-- The richer internal result projects to the established allocation law.
The returned references are real nodes of the resulting table. -/
structure OccurrenceGraphResult (before after : State)
    (references : List NodeId) : Prop where
  bound : before.OccurrenceBoundExtends after
  graph : NodeGraphProgress before after
  returned : NodeIdsPresent references after.nodes

theorem OccurrenceGraphResult.of_bound_nodes {before after : State}
    {references : List NodeId} (bound : before.OccurrenceBoundExtends after)
    (nodes : NodeGraphProgress before after ∧
      NodeIdsPresent references after.nodes) :
    OccurrenceGraphResult before after references :=
  ⟨bound, nodes.1, nodes.2⟩

class ReturnedNodeReferences (alpha : Type) where
  references : alpha → List NodeId

instance : ReturnedNodeReferences (InferredExpression × State) :=
  ⟨fun result => [.expression result.1.id]⟩

instance : ReturnedNodeReferences (List InferredExpression × State) :=
  ⟨fun result => result.1.map (fun expression => .expression expression.id)⟩

instance : ReturnedNodeReferences Detail.StatementResult :=
  ⟨fun result => [.statement result.id]⟩

instance : ReturnedNodeReferences Detail.BlockResult :=
  ⟨fun result => result.statements.map NodeId.statement⟩

instance : ReturnedNodeReferences Detail.InferredForItems :=
  ⟨fun result => result.items.flatMap ForItemForm.references⟩

instance : ReturnedNodeReferences (ForItemForm × State) :=
  ⟨fun result => result.1.references⟩

instance : ReturnedNodeReferences (PlaceResolution × State) :=
  ⟨fun result => result.1.references⟩

instance : ReturnedNodeReferences
    (AssignmentResolution × InferredExpression × State) :=
  ⟨fun result => result.1.references ++ [.expression result.2.1.id]⟩

instance : ReturnedNodeReferences Detail.MatchCasesResult :=
  ⟨fun result => result.cases.flatMap TypedMatchCase.references⟩



end Solcore.Frontend.SourceInference
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.NodeGraphAutomation
set_option autoImplicit false
namespace Solcore.Frontend.SourceInference

theorem NodeIdsPresent.trans {references : List NodeId} {middle final : List Node}
    (first : NodeIdsPresent references middle)
    (next : NodeIdsPresent (middle.map Node.id) final) :
    NodeIdsPresent references final :=
  fun _ member => next (first member)

theorem NodeGraphProgress.trans_nodes {first left right final : State}
    (a : NodeGraphProgress first left) (b : NodeGraphProgress right final)
    (same : left.nodes = right.nodes) :
    NodeGraphProgress first final :=
  a.trans ((NodeGraphProgress.of_nodes_eq same.symm).trans b)

namespace NodeGraphProof

open Lean Meta Elab Tactic

private def endsInState (type : Expr) : MetaM Bool :=
  repeatM (fun type => do
    let type ← whnf type
    if type.isConstOf ``State then return .inr true
    if type.isAppOf ``Prod then return .inl type.getAppArgs[1]!
    return .inr false) type

/-- Expose actual result tuples even when their local names are inaccessible.
This only eliminates product constructors, preserving all call equations. -/
elab "occurrence_split_state_pairs" : tactic => do
  repeat
    let candidate? ← withMainContext do
      for decl in (← getLCtx) do
        let type ← whnf decl.type
        if type.isAppOf ``Prod && (← endsInState type) then
          return some decl.fvarId
      return none
    let some candidate := candidate? | break
    let goals ← (← getMainGoal).cases candidate
    replaceMainGoal (goals.toList.map (·.mvarId))

elab "occurrence_singleton_inputs" : tactic => withMainContext do
  let locals := (← getLCtx).decls.toArray.filterMap id
  for left in locals do
    for right in locals do
      let saved ← saveState
      try
        withoutRecover do
          unless left.type.isAppOf ``Eq && right.type.isAppOf ``Eq do
            throwError "Not equations"
          let leftArgs := left.type.getAppArgs
          let rightArgs := right.type.getAppArgs
          unless leftArgs[2]!.isAppOf ``List.cons && rightArgs[2]!.isAppOf ``List.cons do
            throwError "Not singleton inputs"
          let leftList := leftArgs[2]!.getAppArgs
          let rightList := rightArgs[2]!.getAppArgs
          unless leftList[2]!.isAppOf ``List.nil && rightList[2]!.isAppOf ``List.nil do
            throwError "Not singleton inputs"
          if ← isDefEq leftList[1]! rightList[1]! then throwError "Same source"
          unless ← isDefEq leftArgs[1]! rightArgs[1]! do throwError "Different input list"
          let equalLists ← mkEqTrans (← mkEqSymm left.toExpr) right.toExpr
          let equalHeads ← mkAppM ``And.left #[← mkAppM ``List.cons.inj #[equalLists]]
          let (_, next) ← (← getMainGoal).note `actual_source_eq equalHeads
          setGoals [next]
      catch _ => saved.restore
  evalTactic (← `(tactic| subst_vars))
private def conjunctionEquations (proof type : Expr) : MetaM (Array Expr) :=
  repeatM (fun (pending, equations) => do
    match pending with
    | [] => return .inr equations
    | (proof, type?) :: rest =>
      let type ← match type? with
        | some type => pure type
        | none => inferType proof
      let type ← whnf type
      if type.isAppOf ``Eq then return .inl (rest, equations.push proof)
      if type.isAppOf ``And then
        let left ← mkAppM ``And.left #[proof]
        let right ← mkAppM ``And.right #[proof]
        -- Visit the left branch first and infer each child's type when reached.
        return .inl ((left, none) :: (right, none) :: rest, equations)
      return .inl (rest, equations)) ([(proof, some type)], #[])

elab "occurrence_split_conjunctions" : tactic => withMainContext do
  let locals := (← getLCtx).decls.toArray.filterMap id
  for decl in locals do
    if (← whnf decl.type).isAppOf ``And then
      for proof in (← conjunctionEquations decl.toExpr decl.type) do
        let (_, next) ← (← getMainGoal).note `actual_pair_eq proof
        setGoals [next]

/-- Retain the original bound-only proof inside the strengthened mutual
induction.  This tactic builds only projections of actual induction hypotheses. -/
elab "occurrence_bound_ihs" : tactic => withMainContext do
  let declarations := (← getLCtx).decls.toList.filterMap id
  for decl in declarations do
    unless decl.isImplementationDetail do
      let proof? ← forallTelescopeReducing decl.type fun args terminal => do
        let terminal ← whnf terminal
        unless terminal.isAppOf ``OccurrenceGraphResult do return none
        let result ← mkAppM ``OccurrenceGraphResult.bound #[mkAppN decl.toExpr args]
        return some (← mkLambdaFVars args result)
      if let some proof := proof? then
        let (_, goal) ← (← getMainGoal).note decl.userName proof
        replaceMainGoal [goal]

/-- Instantiate strengthened induction hypotheses at successful calls already
present in the current branch.  Every argument is checked by the kernel. -/
elab "occurrence_graph_ihs" : tactic => withMainContext do
  let locals := (← getLCtx).decls.toArray.filterMap id
  for hypothesis in locals do
    for equation in locals do
      let saved ← saveState
      let goal ← getMainGoal
      try
        withoutRecover do
          unless equation.type.isAppOf ``Eq do throwError "Not an equation"
          let (arguments, _, terminal) ← forallMetaTelescopeReducing hypothesis.type
          unless (← whnf terminal).isAppOf ``OccurrenceGraphResult do
            throwError "Not a graph induction hypothesis"
          let mut matched := false
          for argument in arguments do
            let type ← whnf (← inferType argument)
            if type.isAppOf ``Eq then
              if ← isDefEq type equation.type then
                argument.mvarId!.assign equation.toExpr
                matched := true
          unless matched do throwError "No matching successful call"
          -- A preceding result can occur only through its state projection.
          -- Recover that quantified record from an actual local result.
          for argument in arguments do
            let value ← instantiateMVars argument
            if value.hasExprMVar then
              let type ← instantiateMVars (← inferType value)
              unless ← isProp type do
                for candidate in locals do
                  let prior ← saveState
                  if (← isDefEq type candidate.type) &&
                      (← isDefEq value candidate.toExpr) then
                    break
                  else
                    prior.restore
          for argument in arguments do
            unless ← argument.mvarId!.isAssigned do
              let type ← instantiateMVars (← inferType argument)
              if ← isProp type then
                try argument.mvarId!.assumption catch _ =>
                  try argument.mvarId!.refl catch _ =>
                    setGoals [argument.mvarId!]
                    let allocator := mkIdent
                      `Solcore.Frontend.SourceInference.State.allocateExpressionId_index_lt_nextOccurrence
                    let fresh := mkIdent
                      `Solcore.Frontend.SourceInference.Detail.freshDataConstructorInstantiation_nextOccurrence
                    evalTactic (← `(tactic| first | omega | grind [$allocator:ident, $fresh:ident]))
          let proof ← instantiateMVars (mkAppN hypothesis.toExpr arguments)
          if proof.hasExprMVar then throwError "Undetermined induction inputs"
          let (_, next) ← goal.note `graph_ih proof
          setGoals [next]
          for projection in [``OccurrenceGraphResult.bound,
              ``OccurrenceGraphResult.graph, ``OccurrenceGraphResult.returned] do
            let fact ← mkAppM projection #[proof]
            let (_, next) ← (← getMainGoal).note `graph_fact fact
            setGoals [next]
      catch _ => saved.restore

elab "occurrence_state_facts" "[" names:ident,* "]" : tactic => withMainContext do
  let locals := (← getLCtx).decls.toArray.filterMap id
  for name in names.getElems do
    for equation in locals do
      let saved ← saveState
      let goal ← getMainGoal
      try
        withoutRecover do
          let theoremProof ← elabTerm name none
          unless equation.type.isAppOf ``Eq do throwError "Not an equation"
          let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType theoremProof)
          let mut matched := false
          for argument in arguments do
            let type ← whnf (← inferType argument)
            if type.isAppOf ``Eq then
              if ← isDefEq type equation.type then
                argument.mvarId!.assign equation.toExpr
                matched := true
          unless matched do throwError "No matching successful call"
          for argument in arguments do
            unless ← argument.mvarId!.isAssigned do
              let type ← instantiateMVars (← inferType argument)
              if ← isProp type then
                try argument.mvarId!.assumption catch _ => argument.mvarId!.refl
          let proof ← instantiateMVars (mkAppN theoremProof arguments)
          if proof.hasExprMVar then throwError "Undetermined primitive inputs"
          if (← whnf (← inferType proof)).isAppOf ``NodeGraphProgress then
            let (_, next) ← goal.note `primitive_graph proof
            setGoals [next]
          else
            let (_, next) ← goal.note `occurrence_state proof
            setGoals [next]
            let eq ← if (← whnf (← inferType proof)).isAppOf ``And then
              mkAppM ``And.left #[proof] else pure proof
            let eqType ← inferType eq
            let sides := eqType.getAppArgs
            let after ← match sides[1]! with
              | .app (.const name _) state =>
                  if name == ``State.nodes then pure state else throwError "Not a node table"
              | .proj _ _ state => pure state
              | _ => throwError "Not a node table"
            let before ← match sides[2]! with
              | .app (.const name _) state =>
                  if name == ``State.nodes then pure state else throwError "Not a node table"
              | .proj _ _ state => pure state
              | _ => throwError "Not a node table"
            let graph ← mkAppOptM ``NodeGraphProgress.of_nodes_eq
              #[some before, some after, some eq]
            if graph.hasExprMVar then throwError "Undetermined state graph"
            let (_, next) ← (← getMainGoal).note `primitive_graph graph
            setGoals [next]
      catch _ => saved.restore

end NodeGraphProof
end Solcore.Frontend.SourceInference
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.NodeGraphRecorderAutomation
set_option autoImplicit false

namespace Solcore.Frontend.SourceInference.Detail.NodeGraphProof

open Lean Meta Elab Tactic

private def recorders : List Name :=
  [``recordExpression, ``recordExpressionWithExpected,
    ``recordSelectedCallResult, ``recordSelectedCall,
    ``recordIndirectCall, ``recordBuiltinFunctionCall, ``State.recordNode]

private def recorderCalls (e : Expr) : Array Expr :=
  let found := if e.getAppFn.isConst && recorders.contains e.getAppFn.constName! &&
      !e.hasLooseBVars then #[e] else #[]
  found ++ match e with
    | .app f a => recorderCalls f ++ recorderCalls a
    | .lam _ t b _ | .forallE _ t b _ => recorderCalls t ++ recorderCalls b
    | .letE _ t v b _ => recorderCalls t ++ recorderCalls v ++ recorderCalls b
    | .mdata _ b | .proj _ _ b => recorderCalls b
    | _ => #[]

/-- Specialize existing recorder lemmas at the actual call.  Unsatisfied
reference premises remain implications, never added assumptions. -/
elab "occurrence_recorder_facts" "[" names:ident,* "]" : tactic => withMainContext do
  let locals := (← getLCtx).decls.toArray.filterMap id
  let mut calls := recorderCalls (← getMainTarget)
  for decl in locals do
    calls := calls ++ recorderCalls decl.type
  let mut completeCalls : Array Expr := #[]
  for call in calls do
    unless completeCalls.contains call do
      unless (← whnf (← inferType call)).isForall do
        completeCalls := completeCalls.push call
  for name in names.getElems do
    for call in completeCalls do
      let saved ← saveState
      let goal ← getMainGoal
      try
        withoutRecover do
          let theoremProof ← elabTerm name none
          let (args, _, terminal) ← forallMetaTelescope (← inferType theoremProof)
          let patterns := recorderCalls terminal
          let mut matched := false
          for pattern in patterns do
            if pattern.getAppFn == call.getAppFn &&
                pattern.getAppNumArgs == call.getAppNumArgs then
              let trial ← saveState
              if ← isDefEq pattern call then
                matched := true
                break
              else
                trial.restore
          -- Except recorders occur in their actual acceptance premise.
          for arg in args do
            let type ← whnf (← inferType arg)
            if type.isAppOf ``Eq then
              for decl in locals do
                let trial ← saveState
                if (← isDefEq type.getAppArgs[1]! call) &&
                    (← isDefEq type decl.type) then
                  arg.mvarId!.assign decl.toExpr
                  matched := true
                  break
                else
                  trial.restore
          unless matched do throwError "No actual recorder matched"
          for arg in args do
            unless ← arg.mvarId!.isAssigned do
              let type ← instantiateMVars (← inferType arg)
              unless ← isProp type do
                throwError "Undetermined recorder input"
          let proof ← instantiateMVars (mkAppN theoremProof args)
          let proof := (← abstractMVars proof false).expr
          if proof.hasExprMVar then throwError "Undetermined recorder proof"
          let (_, next) ← goal.note `recorder_graph proof
          setGoals [next]
      catch _ => saved.restore

private def terms (e : Expr) : Array Expr :=
  #[e] ++ match e with
    | .app f a => terms f ++ terms a
    | .lam _ t b _ | .forallE _ t b _ => terms t ++ terms b
    | .letE _ t v b _ => terms t ++ terms v ++ terms b
    | .mdata _ b | .proj _ _ b => terms b
    | _ => #[]

/-- Supply only definitionally equal node tables.  State updates which touch
unrelated fields do not need to be unfolded by the graph-composition solver. -/
elab "occurrence_equal_node_tables" : tactic => withMainContext do
  let locals := (← getLCtx).decls.toArray.filterMap id
  let mut candidates := terms (← getMainTarget)
  for decl in locals do
    candidates := candidates ++ terms decl.type
  let mut states : Array Expr := #[]
  let mut seen : Std.HashSet Expr := {}
  for candidate in candidates do
    unless candidate.hasLooseBVars || candidate.hasExprMVar || seen.contains candidate do
      seen := seen.insert candidate
      try
        if ← isDefEq (← inferType candidate) (mkConst ``State) then
          states := states.push candidate
      catch _ => pure ()
  for before in states do
    for after in states do
      let left ← mkAppM ``State.nodes #[before]
      let right ← mkAppM ``State.nodes #[after]
      if ← withTransparency .all (isDefEq left right) then
        let eq ← mkEqRefl left
        let fact ← mkAppOptM ``NodeGraphProgress.of_nodes_eq
          #[some before, some after, some eq]
        let (_, next) ← (← getMainGoal).note `equal_nodes_graph fact
        setGoals [next]

end Solcore.Frontend.SourceInference.Detail.NodeGraphProof
end
