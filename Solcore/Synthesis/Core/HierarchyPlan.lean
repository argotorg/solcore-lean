import Solcore.Synthesis.Core.TraitPlan

/-! Trait hierarchies over the trait of `runtime-traits`, and the plans of the
`runtime-trait-hierarchies` profile: a subclass `Sc_Sub<a> where a: Sc_Fold`,
a marker or with its own method-level generic `sc_mix<u>`, the chain
`Sc_Top<a> where a: Sc_Sub`, and helpers bounded by them that call a
superclass's method directly, as a method value or through a generic
function value. The base trait, its impls, the instance types, values and
builders are `TraitPlan`'s. The original Core reference keeps `TraitPlan`'s
closures of the base trait's methods and adds one closure per receiver and
argument type of the subclass's method that the uses reach, built bottom-up;
a superclass call through a subclass bound applies the superclass instance's
closure. Nothing here reads source text. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Hierarchies

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Synthesis.Core.Enums (Decl Gen draw drawWeighted drawConstant typeFuel)
open Solcore.Synthesis.Core.Traits (Inst Val Builder Step Impl Head FieldTy)

def hierarchyVersion : String := "core-trait-hierarchies-v1"

/-- The subclass trait: a marker, or with its own method-level generic named
`sc_mix`, or named after the superclass's `sc_fold`. -/
inductive Sub where
  | marker
  | mix
  | shadow
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Sub

def name : Sub → String
  | .marker => "marker"
  | .mix => "mix"
  | .shadow => "shadow"

def ofString? : String → Option Sub
  | "marker" => some .marker
  | "mix" => some .mix
  | "shadow" => some .shadow
  | _ => none

def method (sub : Sub) : Bool := sub != .marker

end Sub

/-- The base trait's unary and binary methods, and the subclass's own
method-level generic. -/
inductive Method where
  | unary
  | binary
  | mix
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Method

def name : Method → String
  | .unary => "unary"
  | .binary => "binary"
  | .mix => "mix"

def ofString? : String → Option Method
  | "unary" => some .unary
  | "binary" => some .binary
  | "mix" => some .mix
  | _ => none

def base? : Method → Option Traits.Method
  | .unary => some .unary
  | .binary => some .binary
  | .mix => none

end Method

/-- A call at the closed type, or through a helper: bounded by `Sc_Sub` and
calling the method; bounded by `Sc_Top` and calling it; bounded by `Sc_Sub`
and calling a method value of it; or bounded by `Sc_Sub` and calling a
generic function value of the `sub` helper. -/
inductive Call where
  | direct
  | sub
  | top
  | value
  | function
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Call

def name : Call → String
  | .direct => "direct"
  | .sub => "sub"
  | .top => "top"
  | .value => "value"
  | .function => "function"

def ofString? : String → Option Call
  | "direct" => some .direct
  | "sub" => some .sub
  | "top" => some .top
  | "value" => some .value
  | "function" => some .function
  | _ => none

/-- The subclass's method is called directly, through `Sc_Top` or as a
method value. -/
def admitted : Method → Call → Bool
  | .mix, .sub | .mix, .function => false
  | _, _ => true

end Call

/-- An impl of the subclass trait: one step per constructor for its own
method, none for a marker. -/
structure SubImpl where
  head : Head
  steps : List Step
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A helper for one call form and method, with its operator and constant. -/
structure Helper where
  call : Call
  method : Method
  op : Traits.Op
  constant : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A value of the subclass method's own type parameter. -/
structure Argument where
  type : Inst
  builder : Builder
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A call of one method at a closed receiver type, on the builder's value of
the input; a binary use also on its value of the input plus a shift, and a
use of the subclass's method at each of its two argument types. -/
structure Use where
  method : Method
  call : Call
  type : Inst
  shift : Nat
  builder : Builder
  arguments : List Argument
  deriving Repr, BEq, DecidableEq, Inhabited

structure Plan where
  decls : List Decl
  unary : Bool
  binary : Bool
  impls : List Impl
  sub : Sub
  subImpls : List SubImpl
  tops : List Head
  helpers : List Helper
  uses : List Use
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumUses : Nat := Traits.maximumUses
def maximumDepth : Nat := Traits.maximumDepth
def argumentCount : Nat := 2

/-- The base trait's plan: its declarations, methods and impls. -/
def Plan.base (plan : Plan) : Traits.Plan :=
  {decls := plan.decls, unary := plan.unary, binary := plan.binary, impls := plan.impls, helpers := [], uses := []}

def Plan.presentFold (plan : Plan) (head : Head) : Bool := plan.impls.any (·.head == head)
def Plan.presentSub (plan : Plan) (head : Head) : Bool := plan.subImpls.any (·.head == head)
def Plan.presentTop (plan : Plan) (head : Head) : Bool := plan.tops.contains head

def Plan.subImplOf? (plan : Plan) (head : Head) : Option SubImpl := plan.subImpls.find? (·.head == head)

/-! Admission. -/

/-- The subclass method's operands per arm: a Word and the argument's base
fold at a Word, as a binary method's at every other head. -/
def mixCounts (decls : List Decl) (head : Head) : Option (List Nat) := Traits.operandCounts decls .binary head

def SubImpl.admitted (decls : List Decl) (sub : Sub) (impl : SubImpl) : Bool :=
  match mixCounts decls impl.head with
  | some counts => if sub.method then Traits.stepsAdmitted counts impl.steps else impl.steps.isEmpty
  | none => false

def ordered (heads : List Head) : Bool := (heads.zip heads.tail).all fun (first, second) => first.rank < second.rank

/-- Every impl a declaration's fields resolve to is present. -/
def fieldsPresent (decls : List Decl) (present : Head → Bool) (head : Head) : Bool :=
  match head with
  | .decl index => match decls[index]? with
      | some decl => decl.constructors.all (·.all fun field => (Traits.fieldHeads field).all present)
      | none => false
  | _ => true

/-- The helpers the uses need, in this order; a `function` helper also needs
the `sub` helper of its method. -/
def helperKeys : List (Call × Method) :=
  [(.sub, .unary), (.sub, .binary), (.top, .unary), (.top, .binary), (.value, .unary), (.value, .binary),
   (.function, .unary), (.function, .binary), (.top, .mix), (.value, .mix)]

def neededHelpers (uses : List Use) : List (Call × Method) :=
  helperKeys.filter fun (call, method) => uses.any fun use =>
    use.method == method && (use.call == call || (call == .sub && use.call == .function))

/-- The receiver and argument types lowered in order with one table of sums:
the plan's declarations then the sums', and each use's lowered types. -/
def Plan.lowered (plan : Plan) : List Decl × List (FieldTy × List FieldTy) :=
  let base := plan.decls.length
  let lowerUse := fun (use : Use) => show StateM Traits.Sums (FieldTy × List FieldTy) from do
    let type ← Traits.lowerM base use.type
    let arguments ← use.arguments.mapM fun (argument : Argument) => Traits.lowerM base argument.type
    return (type, arguments)
  let (types, sums) := (plan.uses.mapM lowerUse).run []
  (plan.decls ++ sums.map Traits.sumDecl, types)

def instAdmitted (decls : List Decl) (type : Inst) (builder : Builder) : Bool :=
  type.valid decls && type.depth ≤ maximumDepth && builder.admitted decls type

/-- A use's method, call, shift and arguments; its types' depths, values and
Core types; and the impls its calls need: the base trait's at every head of
its receiver, the subclass's when a subclass bound or method is involved,
the chain's for `top`, and the base trait's at every head of an argument. -/
def Use.admitted (plan : Plan) (decls : List Decl) (lowered : FieldTy × List FieldTy) (use : Use) : Bool :=
  let heads := Traits.instHeads use.type
  let viaSub := use.call != .direct || use.method == .mix
  Call.admitted use.method use.call &&
    (match use.method with
      | .unary => plan.unary && use.shift = 0 && use.arguments.isEmpty
      | .binary => plan.binary && 1 ≤ use.shift && use.shift ≤ 4 && use.arguments.isEmpty
      | .mix => plan.sub.method && use.shift = 0 && use.arguments.length = argumentCount &&
          (match use.arguments with
            | [first, second] => first.type != second.type
            | _ => false)) &&
    instAdmitted plan.decls use.type use.builder &&
    use.arguments.all (fun argument => instAdmitted plan.decls argument.type argument.builder) &&
    heads.all plan.presentFold && (!viaSub || heads.all plan.presentSub) &&
    (use.call != .top || heads.all plan.presentTop) &&
    use.arguments.all (fun argument => (Traits.instHeads argument.type).all plan.presentFold) &&
    Traits.typeAdmitted decls lowered.1 && lowered.2.length = use.arguments.length &&
    lowered.2.all (Traits.typeAdmitted decls)

def Plan.admitted (plan : Plan) : Bool :=
  let (decls, types) := plan.lowered
  0 < plan.decls.length && plan.decls.length ≤ Enums.maximumDecls &&
    plan.decls.zipIdx.all (fun (decl, index) => decl.admitted plan.decls index) &&
    (plan.unary || plan.binary) && (!plan.sub.method || plan.unary) &&
    plan.impls.all (Traits.Impl.admitted plan.decls plan.unary plan.binary) &&
    ordered (plan.impls.map (·.head)) &&
    plan.impls.all (fun impl => fieldsPresent plan.decls plan.presentFold impl.head) &&
    plan.subImpls.all (SubImpl.admitted plan.decls plan.sub) &&
    ordered (plan.subImpls.map (·.head)) &&
    plan.subImpls.all (fun impl => plan.presentFold impl.head &&
      (!plan.sub.method || fieldsPresent plan.decls plan.presentSub impl.head)) &&
    ordered plan.tops && plan.tops.all plan.presentSub &&
    plan.helpers.map (fun helper => (helper.call, helper.method)) == neededHelpers plan.uses &&
    plan.helpers.all (·.constant < 2 ^ 256) &&
    0 < plan.uses.length && plan.uses.length ≤ maximumUses &&
    types.length = plan.uses.length &&
    (plan.uses.zip types).all fun (use, lowered) => use.admitted plan decls lowered

/-! The closures the uses reach. -/

private def dedup {α : Type} [BEq α] (values : List α) : List α :=
  values.foldl (fun kept value => if kept.contains value then kept else kept ++ [value]) []

def visitMix (decls : List Decl) : Nat → FieldTy × FieldTy → List (FieldTy × FieldTy) → List (FieldTy × FieldTy)
  | 0, _, seen => seen
  | fuel + 1, (type, argument), seen =>
      if seen.contains (type, argument) then seen
      else (Traits.children decls type).foldl (fun seen child => visitMix decls fuel (child, argument) seen) seen ++
        [(type, argument)]

/-- The subclass method's closures: each use's receiver at each argument
type, and transitively its components at the same argument, components
first, in the order first reached. -/
def Plan.mixInstances (plan : Plan) : List (FieldTy × FieldTy) :=
  let (decls, types) := plan.lowered
  (plan.uses.zip types).foldl (fun seen (use, (type, arguments)) =>
    if use.method == .mix then
      arguments.foldl (fun seen argument => visitMix decls (typeFuel + 1) (type, argument) seen) seen
    else seen) []

/-- The base trait's closures: each unary or binary use's method at its
receiver, then the unary method at the argument of every subclass closure at
a Word, components first, in the order first reached. -/
def Plan.instances (plan : Plan) : List (FieldTy × Traits.Method) :=
  let (decls, types) := plan.lowered
  let roots := (plan.uses.zip types).filterMap (fun (use, (type, _)) => use.method.base?.map (type, ·)) ++
    plan.mixInstances.filterMap fun (type, argument) => if type == .word then some (argument, .unary) else none
  roots.foldl (fun seen root => Traits.visit decls (typeFuel + 1) root seen) []

/-- A helper closure's instance: the receiver type, and the argument type of
the subclass's method. -/
abbrev HelperKey := Helper × FieldTy × Option FieldTy

def Plan.helperOf? (plan : Plan) (call : Call) (method : Method) : Option Helper :=
  plan.helpers.find? fun helper => helper.call == call && helper.method == method

/-- The helper closures the uses call, first use first; a `function` helper's
`sub` helper comes before it. -/
def Plan.helperInstances (plan : Plan) : List HelperKey :=
  let (_, types) := plan.lowered
  dedup ((plan.uses.zip types).flatMap fun (use, (type, arguments)) =>
    match use.call, plan.helperOf? use.call use.method with
    | .direct, _ | _, none => []
    | .function, some helper => match plan.helperOf? .sub use.method with
        | some sub => [(sub, type, none), (helper, type, none)]
        | none => [(helper, type, none)]
    | _, some helper => if use.method == .mix then arguments.map fun argument => (helper, type, some argument)
        else [(helper, type, none)])

/-! The Core reference. Variables are compiled from absolute levels, as in
`TraitPlan`: the base trait's closures, then the subclass's, the helpers',
the builders' and the entry. -/

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

private def varAt (depth level : Nat) : Expr := .var (depth - 1 - level)

/-- An arm of the subclass method: the method at its bound values at the same
argument, or a constant. -/
def mixLeaf (mixes : List (FieldTy × FieldTy)) (base : Nat) (argument : FieldTy) (yLevel : Nat) (depth : Nat)
    (scope : Enums.Scope) : Traits.Leaf → Expr
  | .unary names step => Traits.stepExpr step (names.map fun name => match Enums.lookupLevel scope name with
      | some (type, level) => match mixes.idxOf? (type, argument) with
          | some index => .apply (.apply (varAt depth (base + index)) (varAt depth level)) (varAt depth yLevel)
          | none => .unit
      | none => .unit)
  | .binary _ _ => .unit
  | .constant value => word value

/-- The subclass method's closure at a receiver and argument type, at
`level`: a Word combines its value with the base fold of the argument, any
other head matches its receiver arm by arm. -/
def mixExpr (plan : Plan) (decls : List Decl) (instances : List (FieldTy × Traits.Method))
    (mixes : List (FieldTy × FieldTy)) (base level : Nat) (type argument : FieldTy) : Expr :=
  let wire := Enums.wireTy decls type
  let argumentWire := Enums.wireTy decls argument
  let depth := level + 2
  match Traits.headOf plan.decls.length type with
  | none => .unit
  | some head => match plan.subImplOf? head, mixCounts plan.decls head with
    | some impl, some counts =>
        let body := match head with
          | .word => match Traits.closureLevel instances argument .unary with
              | some callee => Traits.stepExpr (impl.steps.headD default)
                  [varAt depth level, .apply (varAt depth callee) (varAt depth (level + 1))]
              | none => .unit
          | _ => Enums.armsExpr decls (mixLeaf mixes base argument (level + 1)) [] [(type, level)] depth
              (Traits.unaryRows head counts impl.steps)
        .lambda wire (.function argumentWire .word) (.lambda argumentWire .word body)
    | _, _ => .unit

/-- A helper's closure at one instance: its operator and constant applied to
the base method's closure at the parameter (`sub`, `top` and `value`), to the
`sub` helper's closure (`function`), or to the subclass method's closure at
the receiver and argument. -/
def helperExpr (decls : List Decl) (instances : List (FieldTy × Traits.Method)) (mixes : List (FieldTy × FieldTy))
    (mixBase helperBase : Nat) (helpers : List HelperKey) (level : Nat) (key : HelperKey) : Expr :=
  let (helper, type, argument) := key
  let wire := Enums.wireTy decls type
  let step : Step := {combine := .add, op := helper.op, constant := helper.constant}
  let callee := match helper.method, helper.call, argument with
    | .mix, _, some argument => mixBase + (mixes.idxOf? (type, argument)).getD 0
    | method, .function, _ => helperBase + (helpers.findIdx? fun (other, otherType, _) =>
        other.call == .sub && other.method == method && otherType == type).getD 0
    | .unary, _, _ => (Traits.closureLevel instances type .unary).getD 0
    | _, _, _ => (Traits.closureLevel instances type .binary).getD 0
  match helper.method, argument with
  | .unary, _ =>
      let depth := level + 1
      .lambda wire .word (Traits.stepExpr step [.apply (varAt depth callee) (varAt depth level)])
  | .mix, some argument =>
      let argumentWire := Enums.wireTy decls argument
      let depth := level + 2
      .lambda wire (.function argumentWire .word) (.lambda argumentWire .word
        (Traits.stepExpr step [.apply (.apply (varAt depth callee) (varAt depth level)) (varAt depth (level + 1))]))
  | _, _ =>
      let depth := level + 2
      .lambda wire (.function wire .word) (.lambda wire .word
        (Traits.stepExpr step [.apply (.apply (varAt depth callee) (varAt depth level)) (varAt depth (level + 1))]))

/-- The program: the base trait's closures, the subclass method's closures,
the helper closures and the builders, receivers then arguments, let-bound in
order; then the entry over the input, binding each use's Word in order and
combining them as `r_0 + 3 r_1 + 5 r_2 + …`. A use of the subclass's method
adds its calls at its two arguments. -/
def Plan.expression (plan : Plan) : Expr :=
  let (decls, types) := plan.lowered
  let instances := plan.instances
  let mixes := plan.mixInstances
  let helpers := plan.helperInstances
  let mixBase := instances.length
  let helperBase := mixBase + mixes.length
  let builderBase := helperBase + helpers.length
  let instanceClosures := instances.zipIdx.map fun ((type, method), level) =>
    Traits.instanceExpr plan.base decls instances level type method
  let mixClosures := mixes.zipIdx.map fun ((type, argument), index) =>
    mixExpr plan decls instances mixes mixBase (mixBase + index) type argument
  let helperClosures := helpers.zipIdx.map fun (key, index) =>
    helperExpr decls instances mixes mixBase helperBase helpers (helperBase + index) key
  let builders := (plan.uses.zip types).flatMap fun (use, (type, arguments)) =>
    (type, use.builder) :: (arguments.zip use.arguments).map fun (argumentType, argument) => (argumentType, argument.builder)
  let builderClosures := builders.map fun (type, builder) => Enums.builderExpr decls type builder.lower
  let offsets := (plan.uses.foldl (fun (offsets, next) use => (offsets ++ [next], next + 1 + use.arguments.length))
    (([] : List Nat), 0)).1
  let input := builderBase + builders.length
  let helperLevel := fun (helper : Helper) (type : FieldTy) (argument : Option FieldTy) =>
    helperBase + (helpers.idxOf? (helper, type, argument)).getD 0
  let callExpr := fun (depth : Nat) (((use, (type, arguments)), index) : (Use × FieldTy × List FieldTy) × Nat) =>
    let builder := builderBase + offsets.getD index 0
    let first := Expr.apply (varAt depth builder) (varAt depth input)
    match use.method.base?, plan.helperOf? use.call use.method with
    | some method, helper =>
        let callee := match use.call, helper with
          | .direct, _ | _, none => (Traits.closureLevel instances type method).getD 0
          | _, some helper => helperLevel helper type none
        match method with
        | .unary => Expr.apply (varAt depth callee) first
        | .binary => Expr.apply (.apply (varAt depth callee) first)
            (.apply (varAt depth builder) (.binary .wordAdd (varAt depth input) (word use.shift)))
    | none, helper =>
        let calls := arguments.zipIdx.map fun (argument, position) =>
          let callee := match use.call, helper with
            | .direct, _ | _, none => mixBase + (mixes.idxOf? (type, argument)).getD 0
            | _, some helper => helperLevel helper type (some argument)
          Expr.apply (.apply (varAt depth callee) first)
            (.apply (varAt depth (builder + 1 + position)) (varAt depth input))
        match calls with
        | [] => word 0
        | head :: rest => rest.foldl (fun sum call => .binary .wordAdd sum call) head
  let entry := (plan.uses.zip types).zipIdx.foldr
    (fun call inner => fun depth => Expr.letE (callExpr depth call) (inner (depth + 1)))
    (fun depth => Enums.combine depth (input + 1) plan.uses.length)
  (instanceClosures ++ mixClosures ++ helperClosures ++ builderClosures).foldr (fun closure inner => .letE closure inner)
    (.lambda .word .word (entry (input + 1)))

def Plan.program (plan : Plan) : Program := {
  resultType := .function .word .word, dataDefinitions := [], body := plan.expression}

def Plan.applied (plan : Plan) (input : Word) : Program := {
  resultType := .word, dataDefinitions := [], body := .apply plan.expression (.word input)}

def Plan.nodes (plan : Plan) : Nat := programNodes (plan.applied Word.zero)

/-! Specified shapes, from the plan. -/

def Plan.shapes (plan : Plan) : List (String × List String) :=
  let (_, types) := plan.lowered
  let base := plan.decls.length
  let instances := plan.instances
  let mixes := plan.mixInstances
  let sorted := fun (values : List String) => values.eraseDups.mergeSort (· ≤ ·)
  let binaryForm := fun (head : Head) (label : String) =>
    (plan.base.implOf? head).map fun impl => label ++ ":" ++ impl.form.name
  let receivers := instances.map Prod.fst ++ mixes.map Prod.fst
  [("instances", sorted (instances.map (fun (type, method) => Traits.loweredKind base type ++ ":" ++ method.name) ++
      mixes.map fun (type, _) => Traits.loweredKind base type ++ ":mix")),
   ("calls", sorted (plan.uses.map fun use => use.method.name ++ ":" ++ use.call.name)),
   ("depths", sorted (plan.uses.map fun use => toString use.type.depth)),
   ("arguments", sorted (receivers.filterMap fun type => match type with
      | .applied _ argument => some (Traits.loweredKind base argument)
      | _ => none)),
   ("parameters", sorted (types.flatMap fun (_, arguments) => arguments.map (Traits.loweredKind base))),
   ("forms", sorted (instances.filterMap fun (type, method) =>
      if method != .binary then none
      else match Traits.headOf base type with
        | some .tuple => binaryForm .tuple "tuple"
        | some (.decl index) => binaryForm (.decl index) "enum"
        | _ => none)),
   ("subclass", [plan.sub.name])]

/-! Generation: a SplitMix64 stream with this profile's domain. -/

def domain : UInt64 := 0x7472616974730002

def drawSubImpl (decls : List Decl) (sub : Sub) (head : Head) : Gen SubImpl := do
  let steps ← if sub.method then ((mixCounts decls head).getD []).mapM Traits.drawStep else pure []
  return {head, steps}

/-- A type is the first of four candidates of the drawn depth that differs
from `avoid` and whose Core type fits the type limit, otherwise a Word, or
`(word, word)` when a Word is to be avoided. -/
def drawInst (decls : List Decl) (avoid : Option Inst) : Gen Inst := do
  let depth ← drawWeighted [1, 3, 3, 3]
  let mut found : Option Inst := none
  for _ in List.range 4 do
    let candidate ← Traits.drawExact decls (maximumDepth + 1) depth
    let (lowered, sums) := (Traits.lowerM decls.length candidate).run []
    if found.isNone && avoid != some candidate && Traits.typeAdmitted (decls ++ sums.map Traits.sumDecl) lowered then
      found := some candidate
  return found.getD (if avoid == some .word then .tuple .word .word else .word)

def drawUse (decls : List Decl) (sub : Sub) : Gen Use := do
  let method ← if sub.method then do
      match ← drawWeighted [1, 1, 1] with
      | 0 => pure Method.unary
      | 1 => pure .binary
      | _ => pure .mix
    else do
      let bit ← draw 2
      pure (if bit = 0 then Method.unary else .binary)
  let call ← if method == .mix then do
      match ← drawWeighted [1, 1, 1] with
      | 0 => pure Call.direct
      | 1 => pure .top
      | _ => pure .value
    else do
      match ← draw 5 with
      | 0 => pure Call.direct
      | 1 => pure .sub
      | 2 => pure .top
      | 3 => pure .value
      | _ => pure .function
  let type ← drawInst decls none
  let shift ← if method == .binary then (do let bits ← draw 4; pure (1 + bits)) else pure 0
  let builder ← Traits.drawBuilder decls type
  let arguments ← if method == .mix then do
      let first ← drawInst decls none
      let firstBuilder ← Traits.drawBuilder decls first
      let second ← drawInst decls (some first)
      let secondBuilder ← Traits.drawBuilder decls second
      pure [{type := first, builder := firstBuilder}, {type := second, builder := secondBuilder}]
    else pure []
  return {method, call, type, shift, builder, arguments}

/-- Draws in plan order: declarations, the base trait's impls, the subclass
form and its impls, the helpers, then the uses. -/
def drawPlan : Gen Plan := do
  let decls ← Enums.drawDecls
  let heads := Traits.heads decls
  let impls ← heads.mapM (Traits.drawImpl decls)
  let sub := match ← draw 3 with
    | 0 => Sub.marker
    | 1 => .mix
    | _ => .shadow
  let subImpls ← heads.mapM (drawSubImpl decls sub)
  let mut helpers : List Helper := []
  for (call, method) in helperKeys do
    helpers := helpers ++ [{call, method, op := ← Traits.drawOp, constant := ← drawConstant}]
  let count := 1 + (← draw maximumUses)
  let mut uses : List Use := []
  for _ in List.range count do
    uses := uses ++ [← drawUse decls sub]
  let needed := neededHelpers uses
  return {decls, unary := true, binary := true, impls, sub, subImpls, tops := heads,
          helpers := helpers.filter fun helper => needed.contains (helper.call, helper.method), uses}

def generate (seed : UInt64) : Plan :=
  (drawPlan.run {seed, domain, index := 0}).1

/-- Uses are dropped from the end while the reference exceeds the budget and
more than one remains; helpers no use needs go with them. -/
def Plan.fit (nodes : Nat) (plan : Plan) : Plan := Id.run do
  let mut plan := plan
  for _ in List.range plan.uses.length do
    if plan.nodes > nodes && plan.uses.length > 1 then
      let uses := plan.uses.dropLast
      let needed := neededHelpers uses
      plan := {plan with uses, helpers := plan.helpers.filter fun helper => needed.contains (helper.call, helper.method)}
  return plan

end Solcore.Synthesis.Core.Hierarchies
