import Solcore.Synthesis.Core.TraitPlan
import Solcore.Synthesis.Core.EnumShrink

/-! Reductions of trait plans: removing a use, a method, an impl no use
reaches or a declaration nothing refers to, reducing an instance type's
nesting, calling directly, and removing or simplifying builder values. The
caller seals each candidate by admission, the full Core checker and a
strictly smaller measure. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Traits

open Solcore.Synthesis.Core.Enums (Decl LeafOp Form valueFuel)

private def total (values : List Nat) : Nat := values.foldl (· + ·) 0

/-- A leaf with a constant weighs more than the input itself. -/
def Val.size : Val → Nat
  | .leaf .input _ => 1
  | .leaf _ _ => 2
  | .ctor0 _ _ => 1
  | .tuple left right | .ctor2 _ left right _ => 1 + left.size + right.size
  | .inl value | .inr value | .ctor1 _ value _ => 1 + value.size

def Call.weight : Call → Nat
  | .direct => 0
  | .generic => 1
  | .lifted => 2

def Use.size (use : Use) : Nat := 1 + use.call.weight + use.type.nodes + total (use.builder.trees.map Val.size)

def Impl.size (impl : Impl) : Nat := 1 + impl.unary.length + impl.binary.length + impl.mismatch.length

def Plan.size (plan : Plan) : Nat :=
  total (plan.decls.map Enums.Decl.size) + (if plan.unary then 1 else 0) + (if plan.binary then 1 else 0) +
    total (plan.impls.map Impl.size) + plan.helpers.length + total (plan.uses.map Use.size)

/-- The helpers the uses need, keeping their drawn operators and constants;
a helper a reduced call newly needs adds 0. -/
def Plan.normalize (plan : Plan) : Plan :=
  let helpers := (neededHelpers plan.uses).map fun (call, method) =>
    (plan.helpers.find? fun helper => helper.call == call && helper.method == method).getD
      {call, method, op := .add, constant := 0}
  {plan with helpers}

private def dedup {α : Type} [BEq α] (values : List α) : List α :=
  values.foldl (fun kept value => if kept.contains value then kept else kept ++ [value]) []

/-- The impls the uses reach, closed under the declarations' field types. -/
def headsClosure (decls : List Decl) : Nat → List Head → List Head
  | 0, heads => heads
  | fuel + 1, heads =>
      let more := heads.flatMap fun head => match head with
        | .decl index => (decls[index]?.map fun decl => decl.constructors.flatten.flatMap fieldHeads).getD []
        | _ => []
      let next := dedup (heads ++ more)
      if next.length = heads.length then heads else headsClosure decls fuel next

def Plan.neededHeads (plan : Plan) : List Head :=
  headsClosure plan.decls (plan.decls.length + 4)
    (dedup (plan.uses.flatMap fun use => instHeads use.type ++ (if use.call == .lifted then [.tuple] else [])))

/-- The smallest value of a type: the first side or constructor, with input
leaves. -/
def minimalVal (decls : List Decl) : Nat → Inst → Val
  | 0, _ => .leaf .input 0
  | _ + 1, .word => .leaf .input 0
  | fuel + 1, .tuple left right => .tuple (minimalVal decls fuel left) (minimalVal decls fuel right)
  | fuel + 1, .sum left _ => .inl (minimalVal decls fuel left)
  | fuel + 1, type => match constructorsOf decls type with
      | some constructors => match constructors.headD [] with
          | [] => .ctor0 0 .qualified
          | [field] => .ctor1 0 (minimalVal decls fuel field) .qualified
          | first :: second :: _ => .ctor2 0 (minimalVal decls fuel first) (minimalVal decls fuel second) .qualified
      | none => .leaf .input 0

private def declIndex? : Inst → Option Nat
  | .enum index | .applied index _ => some index
  | _ => none

/-- A value at an old type rewritten at a new type that replaces some of its
nodes: replaced Words become `sc_x`, other mismatches the smallest value. -/
def rewriteVal (decls : List Decl) : Nat → Inst → Inst → Val → Val
  | 0, new, _, _ => minimalVal decls valueFuel new
  | fuel + 1, new, old, value =>
      if new == old then value
      else match new, old, value with
        | .word, _, _ => .leaf .input 0
        | .tuple left right, .tuple oldLeft oldRight, .tuple first second =>
            .tuple (rewriteVal decls fuel left oldLeft first) (rewriteVal decls fuel right oldRight second)
        | .sum left _, .sum oldLeft _, .inl inner => .inl (rewriteVal decls fuel left oldLeft inner)
        | .sum _ right, .sum _ oldRight, .inr inner => .inr (rewriteVal decls fuel right oldRight inner)
        | _, _, _ =>
            match declIndex? new, declIndex? old, constructorsOf decls new, constructorsOf decls old, value.constructor? with
            | some target, some source, some news, some olds, some (index, fields, form) =>
                if target != source then minimalVal decls valueFuel new
                else
                  let rewritten := ((news.getD index []).zip ((olds.getD index []).zip fields)).map
                    fun (newType, oldType, field) => rewriteVal decls fuel newType oldType field
                  match rewritten with
                  | [] => .ctor0 index form
                  | [field] => .ctor1 index field form
                  | first :: second :: _ => .ctor2 index first second form
            | _, _, _, _, _ => minimalVal decls valueFuel new

/-- One node of a type replaced by a Word, or a tuple or sum by one of its
components, or a generic declaration by its argument, with each value mapped
to the new type. -/
def nestingReductions (decls : List Decl) : Nat → Inst → List (Inst × (Val → Val))
  | 0, _ => []
  | fuel + 1, type =>
      let toWord : Inst × (Val → Val) := (.word, fun _ => .leaf .input 0)
      let here : List (Inst × (Val → Val)) := match type with
        | .word => []
        | .tuple left right => [toWord,
            (left, fun value => match value with
              | .tuple first _ => first
              | _ => minimalVal decls valueFuel left),
            (right, fun value => match value with
              | .tuple _ second => second
              | _ => minimalVal decls valueFuel right)]
        | .sum left right => [toWord,
            (left, fun value => match value with
              | .inl inner => inner
              | _ => minimalVal decls valueFuel left),
            (right, fun value => match value with
              | .inr inner => inner
              | _ => minimalVal decls valueFuel right)]
        | .enum _ => [toWord]
        | .applied _ argument => [toWord, (argument, fun _ => minimalVal decls valueFuel argument)]
      let inner : List (Inst × (Val → Val)) := match type with
        | .tuple left right =>
            ((nestingReductions decls fuel left).map fun (reduced, map) => (Inst.tuple reduced right, fun value =>
              match value with
              | .tuple first second => .tuple (map first) second
              | _ => minimalVal decls valueFuel (.tuple reduced right))) ++
            ((nestingReductions decls fuel right).map fun (reduced, map) => (Inst.tuple left reduced, fun value =>
              match value with
              | .tuple first second => .tuple first (map second)
              | _ => minimalVal decls valueFuel (.tuple left reduced)))
        | .sum left right =>
            ((nestingReductions decls fuel left).map fun (reduced, map) => (Inst.sum reduced right, fun value =>
              match value with
              | .inl first => .inl (map first)
              | other => other)) ++
            ((nestingReductions decls fuel right).map fun (reduced, map) => (Inst.sum left reduced, fun value =>
              match value with
              | .inr second => .inr (map second)
              | other => other))
        | .applied index argument =>
            (nestingReductions decls fuel argument).map fun (reduced, _) =>
              let new := Inst.applied index reduced
              (new, rewriteVal decls valueFuel new type)
        | _ => []
      here ++ inner

def leafSimplifications : Val → List Val
  | .leaf .input _ => []
  | .leaf _ _ => [.leaf .input 0]
  | .ctor0 _ _ => []
  | .tuple left right => (leafSimplifications left).map (Val.tuple · right) ++
      (leafSimplifications right).map (Val.tuple left ·)
  | .inl value => (leafSimplifications value).map .inl
  | .inr value => (leafSimplifications value).map .inr
  | .ctor1 index field form => (leafSimplifications field).map (Val.ctor1 index · form)
  | .ctor2 index first second form => (leafSimplifications first).map (Val.ctor2 index · second form) ++
      (leafSimplifications second).map (Val.ctor2 index first · form)

def builderReductions (builder : Builder) : List Builder :=
  (if builder.trees.length > 1 then
    (List.range builder.trees.length).map fun index => {builder with trees := builder.trees.eraseIdx index}
   else []) ++
  (List.range builder.trees.length).flatMap fun index =>
    (leafSimplifications (builder.trees.getD index default)).map fun tree => {builder with trees := builder.trees.set index tree}

def useReductions (decls : List Decl) (use : Use) : List Use :=
  (nestingReductions decls (maximumDepth + 2) use.type).map (fun (type, map) =>
      {use with type, builder := {use.builder with trees := use.builder.trees.map map}}) ++
    (match use.call with
      | .lifted => [{use with call := .generic}]
      | .generic => [{use with call := .direct}]
      | .direct => []) ++
    (builderReductions use.builder).map fun builder => {use with builder}

def Inst.mentions (decl : Nat) : Inst → Bool
  | .word => false
  | .tuple left right | .sum left right => left.mentions decl || right.mentions decl
  | .enum index => index = decl
  | .applied index argument => index = decl || argument.mentions decl

def Inst.shiftAfter (decl : Nat) : Inst → Inst
  | .word => .word
  | .tuple left right => .tuple (left.shiftAfter decl) (right.shiftAfter decl)
  | .sum left right => .sum (left.shiftAfter decl) (right.shiftAfter decl)
  | .enum index => .enum (if index > decl then index - 1 else index)
  | .applied index argument => .applied (if index > decl then index - 1 else index) (argument.shiftAfter decl)

/-- Declaration `decl` and its impl removed when no use or other declaration
refers to it. -/
def removeDecl (plan : Plan) (decl : Nat) : Option Plan :=
  let fieldTypes := plan.decls.flatMap fun target => target.constructors.flatMap id
  if fieldTypes.any (Enums.Ty.mentions decl) || plan.uses.any (·.type.mentions decl) then none
  else
    let decls := (plan.decls.eraseIdx decl).map fun target =>
      {target with constructors := target.constructors.map (·.map (Enums.Ty.shiftAfter decl))}
    let impls := (plan.impls.filter (·.head != .decl decl)).map fun impl => match impl.head with
      | .decl index => {impl with head := .decl (if index > decl then index - 1 else index)}
      | _ => impl
    let uses := plan.uses.map fun use => {use with type := use.type.shiftAfter decl}
    some {plan with decls, impls, uses}

def planReductions (plan : Plan) : List Plan :=
  let removeUses := if plan.uses.length > 1 then
      (List.range plan.uses.length).map fun index => {plan with uses := plan.uses.eraseIdx index}
    else []
  let removeMethods :=
    (if plan.unary && plan.binary && plan.uses.all (·.method == .binary) then
      [{plan with unary := false, impls := plan.impls.map fun impl => {impl with unary := []}}] else []) ++
    (if plan.unary && plan.binary && plan.uses.all (·.method == .unary) then
      [{plan with binary := false, impls := plan.impls.map fun impl =>
        {impl with binary := [], mismatch := [], form := .nested}}] else [])
  let needed := plan.neededHeads
  let removeImpls := (plan.impls.filter fun impl => !needed.contains impl.head).map fun impl =>
    {plan with impls := plan.impls.filter (·.head != impl.head)}
  let reduceUses := (List.range plan.uses.length).flatMap fun index =>
    (useReductions plan.decls (plan.uses.getD index default)).map fun use =>
      {plan with uses := plan.uses.set index use}
  let removeDecls := (List.range plan.decls.length).filterMap (removeDecl plan)
  removeUses ++ removeMethods ++ removeImpls ++ reduceUses ++ removeDecls

end Solcore.Synthesis.Core.Traits
