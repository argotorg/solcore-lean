import Solcore.Frontend.SourceInference.NodeGraphAutomation

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
