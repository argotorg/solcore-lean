import Solcore.Frontend.SourceInference.NodeGraphProperties
import Lean

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
