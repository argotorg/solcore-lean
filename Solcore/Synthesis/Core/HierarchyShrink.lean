import Solcore.Synthesis.Core.HierarchyPlan
import Solcore.Synthesis.Core.TraitShrink

/-! Reductions of trait hierarchy plans: removing a use, a base method, the
subclass's own method or its name, an impl nothing needs or a declaration
nothing refers to, reducing a receiver's or an argument's nesting, calling
more directly, and removing or simplifying builder values. The caller seals
each candidate by admission, the full Core checker and a strictly smaller
measure. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Hierarchies

open Solcore.Synthesis.Core.Enums (Decl)
open Solcore.Synthesis.Core.Traits (Inst Val Builder Head)

private def total (values : List Nat) : Nat := values.foldl (· + ·) 0

def Call.weight : Call → Nat
  | .direct => 0
  | .sub => 1
  | .top | .value | .function => 2

def Sub.weight : Sub → Nat
  | .marker => 0
  | .mix => 1
  | .shadow => 2

def Builder.size (builder : Builder) : Nat := total (builder.trees.map Traits.Val.size)

def Use.size (use : Use) : Nat :=
  1 + use.call.weight + use.type.nodes + Builder.size use.builder +
    total (use.arguments.map fun argument => argument.type.nodes + Builder.size argument.builder)

def SubImpl.size (impl : SubImpl) : Nat := 1 + impl.steps.length

def Plan.size (plan : Plan) : Nat :=
  total (plan.decls.map Enums.Decl.size) + (if plan.unary then 1 else 0) + (if plan.binary then 1 else 0) +
    total (plan.impls.map Traits.Impl.size) + plan.sub.weight + total (plan.subImpls.map SubImpl.size) +
    plan.tops.length + plan.helpers.length + total (plan.uses.map Use.size)

/-- The helpers the uses need, keeping their drawn operators and constants;
a helper a reduced call newly needs adds 0. -/
def Plan.normalize (plan : Plan) : Plan :=
  let helpers := (neededHelpers plan.uses).map fun (call, method) =>
    (plan.helperOf? call method).getD {call, method, op := .add, constant := 0}
  {plan with helpers}

private def dedup {α : Type} [BEq α] (values : List α) : List α :=
  values.foldl (fun kept value => if kept.contains value then kept else kept ++ [value]) []

private def closure (decls : List Decl) (heads : List Head) : List Head :=
  Traits.headsClosure decls (decls.length + 4) (dedup heads)

/-- The chain's impls the `top` uses need. -/
def Plan.neededTops (plan : Plan) : List Head :=
  dedup (plan.uses.flatMap fun use => if use.call == .top then Traits.instHeads use.type else [])

/-- The subclass's impls: those a subclass bound or method needs and those
under a kept chain impl, closed under the fields when it has a method. -/
def Plan.neededSubs (plan : Plan) : List Head :=
  let heads := plan.tops ++ plan.uses.flatMap fun use =>
    if use.call != .direct || use.method == .mix then Traits.instHeads use.type else []
  if plan.sub.method then closure plan.decls heads else dedup heads

/-- The base trait's impls: every receiver's and argument's heads and those
under a kept subclass impl, closed under the fields. -/
def Plan.neededFolds (plan : Plan) : List Head :=
  closure plan.decls (plan.subImpls.map (·.head) ++ plan.uses.flatMap fun use =>
    Traits.instHeads use.type ++ use.arguments.flatMap fun argument => Traits.instHeads argument.type)

def callReductions (use : Use) : List Use :=
  (if use.call != .direct then [{use with call := .direct}] else []) ++
    (if use.method != .mix && (use.call == .top || use.call == .value || use.call == .function) then
      [{use with call := .sub}] else [])

def argumentReductions (decls : List Decl) (argument : Argument) : List Argument :=
  (Traits.nestingReductions decls (maximumDepth + 2) argument.type).map (fun (type, map) =>
      {type, builder := {argument.builder with trees := argument.builder.trees.map map}}) ++
    (Traits.builderReductions argument.builder).map fun builder => {argument with builder}

def useReductions (decls : List Decl) (use : Use) : List Use :=
  (Traits.nestingReductions decls (maximumDepth + 2) use.type).map (fun (type, map) =>
      {use with type, builder := {use.builder with trees := use.builder.trees.map map}}) ++
    callReductions use ++
    (Traits.builderReductions use.builder).map (fun builder => {use with builder}) ++
    (List.range use.arguments.length).flatMap fun index =>
      (argumentReductions decls (use.arguments.getD index default)).map fun argument =>
        {use with arguments := use.arguments.set index argument}

private def shiftHead (decl : Nat) : Head → Head
  | .decl index => .decl (if index > decl then index - 1 else index)
  | head => head

/-- Declaration `decl` and its impls removed when no use, argument or other
declaration refers to it. -/
def removeDecl (plan : Plan) (decl : Nat) : Option Plan :=
  let fieldTypes := plan.decls.flatMap fun target => target.constructors.flatMap id
  if fieldTypes.any (Enums.Ty.mentions decl) ||
      plan.uses.any (fun use => use.type.mentions decl || use.arguments.any (·.type.mentions decl)) then none
  else
    let decls := (plan.decls.eraseIdx decl).map fun target =>
      {target with constructors := target.constructors.map (·.map (Enums.Ty.shiftAfter decl))}
    let impls := (plan.impls.filter (·.head != .decl decl)).map fun impl => {impl with head := shiftHead decl impl.head}
    let subImpls := (plan.subImpls.filter (·.head != .decl decl)).map fun impl =>
      {impl with head := shiftHead decl impl.head}
    let tops := (plan.tops.filter (· != .decl decl)).map (shiftHead decl)
    let shiftArgument := fun (argument : Argument) => {argument with type := argument.type.shiftAfter decl}
    let uses := plan.uses.map fun (use : Use) =>
      {use with type := use.type.shiftAfter decl, arguments := use.arguments.map shiftArgument}
    some {plan with decls, impls, subImpls, tops, uses}

def planReductions (plan : Plan) : List Plan :=
  let removeUses := if plan.uses.length > 1 then
      (List.range plan.uses.length).map fun index => {plan with uses := plan.uses.eraseIdx index}
    else []
  let removeMethods :=
    (if plan.unary && plan.binary && !plan.sub.method && plan.uses.all (·.method == .binary) then
      [{plan with unary := false, impls := plan.impls.map fun impl => {impl with unary := []}}] else []) ++
    (if plan.unary && plan.binary && plan.uses.all (·.method != .binary) then
      [{plan with binary := false, impls := plan.impls.map fun impl =>
        {impl with binary := [], mismatch := [], form := .nested}}] else [])
  let reduceSub :=
    (if plan.sub == .shadow then [{plan with sub := .mix}] else []) ++
    (if plan.sub.method && plan.uses.all (·.method != .mix) then
      [{plan with sub := .marker, subImpls := plan.subImpls.map fun impl => {impl with steps := []}}] else [])
  let tops := plan.neededTops
  let subs := plan.neededSubs
  let folds := plan.neededFolds
  let removeImpls :=
    (plan.tops.filter (!tops.contains ·)).map (fun head => {plan with tops := plan.tops.filter (· != head)}) ++
    (plan.subImpls.filter (!subs.contains ·.head)).map (fun impl =>
      {plan with subImpls := plan.subImpls.filter (·.head != impl.head)}) ++
    (plan.impls.filter (!folds.contains ·.head)).map fun impl =>
      {plan with impls := plan.impls.filter (·.head != impl.head)}
  let reduceUses := (List.range plan.uses.length).flatMap fun index =>
    (useReductions plan.decls (plan.uses.getD index default)).map fun use =>
      {plan with uses := plan.uses.set index use}
  let removeDecls := (List.range plan.decls.length).filterMap (removeDecl plan)
  removeUses ++ removeMethods ++ reduceSub ++ removeImpls ++ reduceUses ++ removeDecls

end Solcore.Synthesis.Core.Hierarchies
