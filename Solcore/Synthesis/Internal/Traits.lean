import Solcore.Synthesis.Internal.Enums

/-!
# Profiles: traits and hierarchies

The profiles `runtime-traits` and `runtime-trait-hierarchies`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.TraitPlan
/-! One trait with a unary and a binary method, its impls at Words, tuples,
std sums and the declarations of `EnumData`, and the plans of the
`runtime-traits` profile. The original Core reference has one closure per
instance type and method reachable from the uses, built bottom-up from the
impl at that instance. A std sum is lowered as a plain declaration of two
one-field constructors after the plan's, so every impl's `match` is compiled
by `EnumMatch`. Nothing here reads source text. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Traits

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Synthesis.Core.Enums (Decl LeafOp Form Gen Stream draw drawBits drawWeighted drawConstant typeLimit
  typeFuel valueFuel)

def traitVersion : String := "core-trait-instances-v1"

abbrev FieldTy := Solcore.Synthesis.Core.Enums.Ty
abbrev Op := Solcore.Synthesis.Core.Enums.Op
abbrev Pat := Solcore.Synthesis.Core.Enums.Pat

/-- Instance types: Words, tuples, std sums, plain declarations, and generic
declarations at an instance. -/
inductive Inst where
  | word
  | tuple (left right : Inst)
  | sum (left right : Inst)
  | enum (index : Nat)
  | applied (index : Nat) (argument : Inst)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Inst

def nodes : Inst → Nat
  | .word | .enum _ => 1
  | .tuple left right | .sum left right => 1 + left.nodes + right.nodes
  | .applied _ argument => 1 + argument.nodes

/-- A Word 0, a tuple or sum one more than its deepest component, a plain
declaration 1 and a generic one one more than its argument. -/
def depth : Inst → Nat
  | .word => 0
  | .enum _ => 1
  | .tuple left right | .sum left right => 1 + max left.depth right.depth
  | .applied _ argument => 1 + argument.depth

def kind : Inst → String
  | .word => "word"
  | .tuple _ _ => "tuple"
  | .sum _ _ => "sum"
  | .enum _ => "plain"
  | .applied _ _ => "generic"

/-- A declaration's field type at an instance argument. -/
def ofField (argument : Inst) : FieldTy → Inst
  | .word => .word
  | .param => argument
  | .tuple left right => .tuple (ofField argument left) (ofField argument right)
  | .enum index => .enum index
  | .applied index inner => .applied index (ofField argument inner)

/-- Every declaration reference names a declaration of its kind. -/
def valid (decls : List Decl) : Inst → Bool
  | .word => true
  | .tuple left right | .sum left right => valid decls left && valid decls right
  | .enum index => (decls[index]?.map (!·.generic)).getD false
  | .applied index argument => (decls[index]?.map (·.generic)).getD false && valid decls argument

end Inst

/-- The field types of an instance's constructors: a tuple is one
constructor of two fields, a sum two of one, a declaration its own at the
argument; none for a Word or an invalid reference. -/
def constructorsOf (decls : List Decl) : Inst → Option (List (List Inst))
  | .word => none
  | .tuple left right => some [[left, right]]
  | .sum left right => some [[left], [right]]
  | .enum index => match decls[index]? with
      | some decl => if decl.generic then none else some (decl.constructors.map (·.map (Inst.ofField .word)))
      | none => none
  | .applied index argument => match decls[index]? with
      | some decl => if decl.generic then some (decl.constructors.map (·.map (Inst.ofField argument))) else none
      | none => none

/-! Values. -/

inductive Val where
  | leaf (op : LeafOp) (constant : Nat)
  | tuple (left right : Val)
  | inl (value : Val)
  | inr (value : Val)
  | ctor0 (index : Nat) (form : Form)
  | ctor1 (index : Nat) (field : Val) (form : Form)
  | ctor2 (index : Nat) (first second : Val) (form : Form)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Val

def nodes : Val → Nat
  | .leaf _ _ | .ctor0 _ _ => 1
  | .tuple left right | .ctor2 _ left right _ => 1 + left.nodes + right.nodes
  | .inl value | .inr value | .ctor1 _ value _ => 1 + value.nodes

def constructor? : Val → Option (Nat × List Val × Form)
  | .ctor0 index form => some (index, [], form)
  | .ctor1 index field form => some (index, [field], form)
  | .ctor2 index first second form => some (index, [first, second], form)
  | _ => none

/-- The top constructor: a sum's side or a declaration's constructor. -/
def top : Val → Nat
  | .inr _ => 1
  | .ctor0 index _ | .ctor1 index _ _ | .ctor2 index _ _ _ => index
  | _ => 0

/-- The value as an `EnumData` value: `inl` and `inr` are the two
constructors of a lowered sum. -/
def lower : Val → Enums.Value
  | .leaf op constant => .leaf op constant
  | .tuple left right => .tuple left.lower right.lower
  | .inl value => .ctor1 0 value.lower .qualified
  | .inr value => .ctor1 1 value.lower .qualified
  | .ctor0 index form => .ctor0 index form
  | .ctor1 index field form => .ctor1 index field.lower form
  | .ctor2 index first second form => .ctor2 index first.lower second.lower form

end Val

private def declIndex : Inst → Option Nat
  | .enum index | .applied index _ => some index
  | _ => none

/-- `T.C` always, `.C` in a returned value, `T` for a same-name constructor. -/
def formAdmitted (decls : List Decl) (type : Inst) (index : Nat) (top : Bool) : Form → Bool
  | .qualified => true
  | .dot => top
  | .sameName => index = 0 && (((declIndex type).bind (decls[·]?)).map (·.sameName)).getD false

/-- Values are typed structurally; leaves are canonical, with no constant
for the input itself. -/
def valTyped (decls : List Decl) : Nat → Bool → Inst → Val → Bool
  | 0, _, _, _ => false
  | _ + 1, _, .word, .leaf op constant => constant < 2 ^ 256 && (op != .input || constant = 0)
  | fuel + 1, _, .tuple left right, .tuple first second =>
      valTyped decls fuel false left first && valTyped decls fuel false right second
  | fuel + 1, _, .sum left _, .inl value => valTyped decls fuel false left value
  | fuel + 1, _, .sum _ right, .inr value => valTyped decls fuel false right value
  | fuel + 1, top, type, value => match type, constructorsOf decls type, value.constructor? with
      | .enum _, some constructors, some (index, fields, form)
      | .applied _ _, some constructors, some (index, fields, form) => match constructors[index]? with
          | some types => types.length = fields.length && formAdmitted decls type index top form &&
              (types.zip fields).all fun (fieldType, field) => valTyped decls fuel false fieldType field
          | none => false
      | _, _, _ => false

/-- One to four values selected by the residue `(x + offset) & 3`, as in
`EnumData`. -/
structure Builder where
  offset : Nat
  trees : List Val
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumTrees : Nat := 4

def Builder.admitted (decls : List Decl) (type : Inst) (builder : Builder) : Bool :=
  builder.offset < 4 && 0 < builder.trees.length && builder.trees.length ≤ maximumTrees &&
    builder.trees.all (valTyped decls valueFuel true type)

def Builder.lower (builder : Builder) : Enums.Builder := {offset := builder.offset, trees := builder.trees.map Val.lower}

/-! The trait, its impls and its uses. -/

inductive Method where
  | unary
  | binary
  deriving Repr, BEq, DecidableEq, Inhabited

def Method.name : Method → String
  | .unary => "unary"
  | .binary => "binary"

def Method.ofString? : String → Option Method
  | "unary" => some .unary
  | "binary" => some .binary
  | _ => none

/-- A direct call, a call through a constrained generic function at its
parameter, or through one at the tuple `(t, t)` of its parameter. -/
inductive Call where
  | direct
  | generic
  | lifted
  deriving Repr, BEq, DecidableEq, Inhabited

def Call.name : Call → String
  | .direct => "direct"
  | .generic => "generic"
  | .lifted => "lifted"

def Call.ofString? : String → Option Call
  | "direct" => some .direct
  | "generic" => some .generic
  | "lifted" => some .lifted
  | _ => none

/-- An arm's arithmetic: the operator folding its operands, then the
operator with its constant. An arm with one operand has no fold and one with
none returns its constant; unused operators are `add`. -/
structure Step where
  combine : Op
  op : Op
  constant : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

def Step.admitted (operands : Nat) (step : Step) : Bool :=
  step.constant < 2 ^ 256 && (operands ≥ 2 || step.combine == .add) && (operands ≥ 1 || step.op == .add)

/-- A binary method matches its second argument inside each arm, or both
arguments as two columns. -/
inductive MatchForm where
  | nested
  | columns
  deriving Repr, BEq, DecidableEq, Inhabited

def MatchForm.name : MatchForm → String
  | .nested => "nested"
  | .columns => "columns"

def MatchForm.ofString? : String → Option MatchForm
  | "nested" => some .nested
  | "columns" => some .columns
  | _ => none

inductive Head where
  | word
  | tuple
  | sum
  | decl (index : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def Head.rank : Head → Nat
  | .word => 0
  | .tuple => 1
  | .sum => 2
  | .decl index => 3 + index

/-- An impl: per method one step per constructor, the binary match form and
the binary mismatch constants (two for a sum, one for a declaration). -/
structure Impl where
  head : Head
  unary : List Step
  binary : List Step
  form : MatchForm
  mismatch : List Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A constrained generic function: `generic` or `lifted`, for one method. -/
structure Helper where
  call : Call
  method : Method
  op : Op
  constant : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A call of one method at a closed instance type, on the builder's value of
the input and, for the binary method, of the input plus a shift. -/
structure Use where
  method : Method
  call : Call
  type : Inst
  shift : Nat
  builder : Builder
  deriving Repr, BEq, DecidableEq, Inhabited

structure Plan where
  decls : List Decl
  unary : Bool
  binary : Bool
  impls : List Impl
  helpers : List Helper
  uses : List Use
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumUses : Nat := 6
def maximumDepth : Nat := 3

/-! Admission. -/

/-- Each arm's operands per method: a Word's own value or both values, two
components for a tuple, one side for a sum, a constructor's fields. -/
def operandCounts (decls : List Decl) (method : Method) : Head → Option (List Nat)
  | .word => some [if method == .unary then 1 else 2]
  | .tuple => some [2]
  | .sum => some [1, 1]
  | .decl index => decls[index]?.map (·.constructors.map List.length)

def mismatchCount : Head → Nat
  | .word | .tuple => 0
  | .sum => 2
  | .decl _ => 1

def stepsAdmitted (counts : List Nat) (steps : List Step) : Bool :=
  counts.length = steps.length && (counts.zip steps).all fun (operands, step) => step.admitted operands

def Impl.admitted (decls : List Decl) (unary binary : Bool) (impl : Impl) : Bool :=
  match operandCounts decls .unary impl.head, operandCounts decls .binary impl.head with
  | some unaryCounts, some binaryCounts =>
      (if unary then stepsAdmitted unaryCounts impl.unary else impl.unary.isEmpty) &&
      (if binary then stepsAdmitted binaryCounts impl.binary && impl.mismatch.length = mismatchCount impl.head &&
          impl.mismatch.all (· < 2 ^ 256) &&
          (impl.form == .nested || (match impl.head with
            | .tuple | .decl _ => true
            | _ => false))
       else impl.binary.isEmpty && impl.mismatch.isEmpty && impl.form == .nested)
  | _, _ => false

/-- The impls a declaration field's type resolves to; a parameter resolves
through the impl's constraint. -/
def fieldHeads : FieldTy → List Head
  | .word => [.word]
  | .param => []
  | .tuple left right => .tuple :: fieldHeads left ++ fieldHeads right
  | .enum index => [.decl index]
  | .applied index argument => .decl index :: fieldHeads argument

def instHeads : Inst → List Head
  | .word => [.word]
  | .tuple left right => .tuple :: instHeads left ++ instHeads right
  | .sum left right => .sum :: instHeads left ++ instHeads right
  | .enum index => [.decl index]
  | .applied index argument => .decl index :: instHeads argument

def Plan.present (plan : Plan) (head : Head) : Bool := plan.impls.any (·.head == head)

def Plan.implOf? (plan : Plan) (head : Head) : Option Impl := plan.impls.find? (·.head == head)

/-- The helpers the uses need, in the order generic unary, generic binary,
lifted unary, lifted binary. -/
def helperKeys : List (Call × Method) :=
  [(.generic, .unary), (.generic, .binary), (.lifted, .unary), (.lifted, .binary)]

def neededHelpers (uses : List Use) : List (Call × Method) :=
  helperKeys.filter fun (call, method) => uses.any fun use => use.call == call && use.method == method

/-! Std sums lowered as plain declarations after the plan's. -/

abbrev Sums := List (FieldTy × FieldTy)

def lowerM (base : Nat) : Inst → StateM Sums FieldTy
  | .word => pure .word
  | .tuple left right => do
      let left ← lowerM base left
      let right ← lowerM base right
      return .tuple left right
  | .sum left right => do
      let left ← lowerM base left
      let right ← lowerM base right
      let sums ← get
      match sums.idxOf? (left, right) with
      | some index => return .enum (base + index)
      | none =>
          set (sums ++ [(left, right)])
          return .enum (base + sums.length)
  | .enum index => pure (.enum index)
  | .applied index argument => do return .applied index (← lowerM base argument)

def sumDecl (sum : FieldTy × FieldTy) : Decl := {generic := false, sameName := false, constructors := [[sum.1], [sum.2]]}

/-- The use types lowered in order with one table of sums: the plan's
declarations then the sums', and each use's lowered type. -/
def Plan.lowered (plan : Plan) : List Decl × List FieldTy :=
  let (types, sums) := (plan.uses.mapM fun use => lowerM plan.decls.length use.type).run []
  (plan.decls ++ sums.map sumDecl, types)

/-- The type a use calls its method at: `(t, t)` through a lifted helper. -/
def rootType (use : Use) (type : FieldTy) : FieldTy :=
  if use.call == .lifted then .tuple type type else type

/-- A lowered type's Core type, with fuel exhaustion visible: one more level
of fuel changes an exhausted type, since no closed type's Core type is Unit. -/
def wireChecked (decls : List Decl) (type : FieldTy) : Option Enums.WireTy :=
  let wire := Enums.coreTy decls typeFuel type
  if wire == Enums.coreTy decls (typeFuel + 1) type then some wire else none

def typeAdmitted (decls : List Decl) (type : FieldTy) : Bool :=
  match wireChecked decls type with
  | some wire => Enums.wireTypeNodes wire ≤ typeLimit
  | none => false

def Use.admitted (plan : Plan) (decls : List Decl) (lowered : FieldTy) (use : Use) : Bool :=
  (if use.method == .unary then plan.unary && use.shift = 0 else plan.binary && 1 ≤ use.shift && use.shift ≤ 4) &&
    use.type.valid plan.decls && use.type.depth ≤ maximumDepth && use.builder.admitted plan.decls use.type &&
    (instHeads use.type).all plan.present && (use.call != .lifted || plan.present .tuple) &&
    typeAdmitted decls (rootType use lowered)

def Plan.admitted (plan : Plan) : Bool :=
  let (decls, types) := plan.lowered
  0 < plan.decls.length && plan.decls.length ≤ Enums.maximumDecls &&
    plan.decls.zipIdx.all (fun (decl, index) => decl.admitted plan.decls index) &&
    (plan.unary || plan.binary) &&
    plan.impls.all (Impl.admitted plan.decls plan.unary plan.binary) &&
    (plan.impls.zip plan.impls.tail).all (fun (first, second) => first.head.rank < second.head.rank) &&
    plan.impls.all (fun impl => match impl.head with
      | .decl index => match plan.decls[index]? with
          | some decl => decl.constructors.all (·.all fun field => (fieldHeads field).all plan.present)
          | none => false
      | _ => true) &&
    plan.helpers.map (fun helper => (helper.call, helper.method)) == neededHelpers plan.uses &&
    plan.helpers.all (·.constant < 2 ^ 256) &&
    0 < plan.uses.length && plan.uses.length ≤ maximumUses &&
    types.length = plan.uses.length &&
    (plan.uses.zip types).all fun (use, type) => use.admitted plan decls type

/-! The instances the uses reach. -/

private def dedup {α : Type} [BEq α] (values : List α) : List α :=
  values.foldl (fun kept value => if kept.contains value then kept else kept ++ [value]) []

/-- The instance types an impl's arms call the method at: tuple and sum
components, a declaration's fields at its instance. -/
def children (decls : List Decl) (type : FieldTy) : List FieldTy :=
  dedup ((Enums.constructorsOf decls type).getD []).flatten

def visit (decls : List Decl) : Nat → FieldTy × Method → List (FieldTy × Method) → List (FieldTy × Method)
  | 0, _, seen => seen
  | fuel + 1, (type, method), seen =>
      if seen.contains (type, method) then seen
      else (children decls type).foldl (fun seen child => visit decls fuel (child, method) seen) seen ++
        [(type, method)]

/-- Every instance and method reachable from the uses, components first, in
the order first reached. -/
def Plan.instances (plan : Plan) : List (FieldTy × Method) :=
  let (decls, types) := plan.lowered
  (plan.uses.zip types).foldl (fun seen (use, type) => visit decls (typeFuel + 1) (rootType use type, use.method) seen) []

/-- A lowered type's impl: sums follow the plan's declarations. -/
def headOf (base : Nat) : FieldTy → Option Head
  | .word => some .word
  | .tuple _ _ => some .tuple
  | .enum index => some (if index < base then .decl index else .sum)
  | .applied index _ => some (.decl index)
  | .param => none

/-! The Core reference. Variables are compiled from absolute levels: at depth
`d`, level `l` is de Bruijn index `d - 1 - l`. -/

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

private def varAt (depth level : Nat) : Expr := .var (depth - 1 - level)

def stepExpr (step : Step) : List Expr → Expr
  | [] => word step.constant
  | first :: rest =>
      .binary step.op.binary (rest.foldl (fun folded operand => .binary step.combine.binary folded operand) first)
        (word step.constant)

/-- An arm's result: the method at its bound values' types, or a constant. -/
inductive Leaf where
  | unary (names : List Nat) (step : Step)
  | binary (pairs : List (Nat × Nat)) (step : Step)
  | constant (value : Nat)
  deriving Repr, BEq, Inhabited

def closureLevel (instances : List (FieldTy × Method)) (type : FieldTy) (method : Method) : Option Nat :=
  instances.idxOf? (type, method)

def leafExpr (instances : List (FieldTy × Method)) (depth : Nat) (scope : Enums.Scope) : Leaf → Expr
  | .unary names step => stepExpr step (names.map fun name => match Enums.lookupLevel scope name with
      | some (type, level) => match closureLevel instances type .unary with
          | some callee => .apply (varAt depth callee) (varAt depth level)
          | none => .unit
      | none => .unit)
  | .binary pairs step => stepExpr step (pairs.map fun (first, second) =>
      match Enums.lookupLevel scope first, Enums.lookupLevel scope second with
      | some (type, level), some (_, other) => match closureLevel instances type .binary with
          | some callee => .apply (.apply (varAt depth callee) (varAt depth level)) (varAt depth other)
          | none => .unit
      | _, _ => .unit)
  | .constant value => word value

/-- The pattern of a constructor binding its fields to two names in order. -/
def ctorPat (head : Head) (ctor fields first : Nat) : Pat :=
  match head, fields with
  | .tuple, _ => .tuple (.var first) (.var (first + 1))
  | _, 0 => .ctor0 ctor .qualified
  | _, 1 => .ctor1 ctor (.var first) .qualified
  | _, _ => .ctor2 ctor (.var first) (.var (first + 1)) .qualified

def fieldNames (fields first : Nat) : List Nat := (List.range fields).map (first + ·)

def fieldPairs (fields : Nat) : List (Nat × Nat) := (List.range fields).map fun index => (index, index + 2)

/-- An arm of an outer match: a result, or a match of the second argument. -/
abbrev Outer := Leaf ⊕ List (List Pat × Leaf)

/-- The unary match: one arm per constructor. -/
def unaryRows (head : Head) (counts : List Nat) (steps : List Step) : List (List Pat × Leaf) :=
  (counts.zip steps).zipIdx.map fun ((fields, step), ctor) =>
    ([ctorPat head ctor fields 0], .unary (fieldNames fields 0) step)

/-- The binary match of a sum: each side matches the second argument, its own
side recursing and the other returning a mismatch constant. -/
def sumRows (steps : List Step) (mismatch : List Nat) : List (List Pat × Outer) :=
  [([.ctor1 0 (.var 0) .qualified], .inr [
      ([.ctor1 0 (.var 2) .qualified], .binary [(0, 2)] (steps.getD 0 default)),
      ([.ctor1 1 .wild .qualified], .constant (mismatch.getD 0 0))]),
   ([.ctor1 1 (.var 0) .qualified], .inr [
      ([.ctor1 0 .wild .qualified], .constant (mismatch.getD 1 0)),
      ([.ctor1 1 (.var 2) .qualified], .binary [(0, 2)] (steps.getD 1 default))])]

/-- The nested binary match of a tuple or declaration: the same constructor
recurses on each pair of fields, any other returns the mismatch constant. -/
def nestedRows (head : Head) (counts : List Nat) (steps : List Step) (mismatch : List Nat) :
    List (List Pat × Outer) :=
  (counts.zip steps).zipIdx.map fun ((fields, step), ctor) =>
    let same : List Pat × Leaf := ([ctorPat head ctor fields 2], .binary (fieldPairs fields) step)
    ([ctorPat head ctor fields 0], .inr (match head with
      | .tuple => [same]
      | _ => [same, ([], .constant (mismatch.getD 0 0))]))

/-- The two-column binary match: a row per constructor, then `default` for a
declaration. -/
def columnRows (head : Head) (counts : List Nat) (steps : List Step) (mismatch : List Nat) :
    List (List Pat × Leaf) :=
  (counts.zip steps).zipIdx.map (fun ((fields, step), ctor) =>
    ([ctorPat head ctor fields 0, ctorPat head ctor fields 2], .binary (fieldPairs fields) step)) ++
    (match head with
      | .tuple => []
      | _ => [([], .constant (mismatch.getD 0 0))])

/-- The closure of an instance's method at `level`: its parameters follow the
earlier closures. -/
def instanceExpr (plan : Plan) (decls : List Decl) (instances : List (FieldTy × Method)) (level : Nat)
    (type : FieldTy) (method : Method) : Expr :=
  let wire := Enums.wireTy decls type
  let leaf := leafExpr instances
  match headOf plan.decls.length type with
  | none => .unit
  | some head => match plan.implOf? head, operandCounts plan.decls method head with
    | some impl, some counts => match method with
      | .unary =>
          let body := match head with
            | .word => stepExpr (impl.unary.headD default) [varAt (level + 1) level]
            | _ => Enums.armsExpr decls leaf [] [(type, level)] (level + 1) (unaryRows head counts impl.unary)
          .lambda wire .word body
      | .binary =>
          let depth := level + 2
          let outer := fun (depth : Nat) (scope : Enums.Scope) (body : Outer) => match body with
            | .inl result => leaf depth scope result
            | .inr rows => Enums.armsExpr decls leaf scope [(type, level + 1)] depth rows
          let body := match head, impl.form with
            | .word, _ => stepExpr (impl.binary.headD default) [varAt depth level, varAt depth (level + 1)]
            | .sum, _ => Enums.armsExpr decls outer [] [(type, level)] depth (sumRows impl.binary impl.mismatch)
            | _, .nested => Enums.armsExpr decls outer [] [(type, level)] depth
                (nestedRows head counts impl.binary impl.mismatch)
            | _, .columns => Enums.armsExpr decls leaf [] [(type, level), (type, level + 1)] depth
                (columnRows head counts impl.binary impl.mismatch)
          .lambda wire (.function wire .word) (.lambda wire .word body)
    | _, _ => .unit

/-- A helper's closure at one instance: the method at the parameter, or at
`(x, x)` and `((x, y), (y, x))` when lifted. -/
def helperExpr (decls : List Decl) (instances : List (FieldTy × Method)) (level : Nat) (helper : Helper)
    (type : FieldTy) : Expr :=
  let wire := Enums.wireTy decls type
  let step : Step := {combine := .add, op := helper.op, constant := helper.constant}
  let target := if helper.call == .lifted then Enums.Ty.tuple type type else type
  let callee := (closureLevel instances target helper.method).getD 0
  match helper.method with
  | .unary =>
      let depth := level + 1
      let argument := if helper.call == .lifted then Expr.pair (varAt depth level) (varAt depth level)
        else varAt depth level
      .lambda wire .word (stepExpr step [.apply (varAt depth callee) argument])
  | .binary =>
      let depth := level + 2
      let (first, second) := if helper.call == .lifted then
          (Expr.pair (varAt depth level) (varAt depth (level + 1)), Expr.pair (varAt depth (level + 1)) (varAt depth level))
        else (varAt depth level, varAt depth (level + 1))
      .lambda wire (.function wire .word) (.lambda wire .word
        (stepExpr step [.apply (.apply (varAt depth callee) first) second]))

/-- The helper closures the uses call, by helper and instance, first use first. -/
def Plan.helperInstances (plan : Plan) : List (Helper × FieldTy) :=
  let (_, types) := plan.lowered
  dedup ((plan.uses.zip types).filterMap fun (use, type) =>
    (plan.helpers.find? fun helper => helper.call == use.call && helper.method == use.method).map (·, type))

/-- The program: instance closures, helper closures and builders let-bound in
order, then the entry over the input, binding each use's Word in order and
combining them as `r_0 + 3 r_1 + 5 r_2 + …`. -/
def Plan.expression (plan : Plan) : Expr :=
  let (decls, types) := plan.lowered
  let instances := plan.instances
  let helpers := plan.helperInstances
  let instanceClosures := instances.zipIdx.map fun ((type, method), level) =>
    instanceExpr plan decls instances level type method
  let helperClosures := helpers.zipIdx.map fun ((helper, type), index) =>
    helperExpr decls instances (instances.length + index) helper type
  let builderBase := instances.length + helpers.length
  let builderClosures := (plan.uses.zip types).map fun (use, type) => Enums.builderExpr decls type use.builder.lower
  let input := builderBase + plan.uses.length
  let callExpr := fun (depth : Nat) (((use, type), index) : (Use × FieldTy) × Nat) =>
    let callee := match plan.helpers.find? (fun helper => helper.call == use.call && helper.method == use.method) with
      | some helper => instances.length + (helpers.idxOf? (helper, type)).getD 0
      | none => (closureLevel instances type use.method).getD 0
    let builder := builderBase + index
    let first := Expr.apply (varAt depth builder) (varAt depth input)
    match use.method with
    | .unary => Expr.apply (varAt depth callee) first
    | .binary => Expr.apply (.apply (varAt depth callee) first)
        (.apply (varAt depth builder) (.binary .wordAdd (varAt depth input) (word use.shift)))
  let entry := (plan.uses.zip types).zipIdx.foldr
    (fun call inner => fun depth => Expr.letE (callExpr depth call) (inner (depth + 1)))
    (fun depth => Enums.combine depth (input + 1) plan.uses.length)
  (instanceClosures ++ helperClosures ++ builderClosures).foldr (fun closure inner => .letE closure inner)
    (.lambda .word .word (entry (input + 1)))

def Plan.program (plan : Plan) : Program := {
  resultType := .function .word .word, dataDefinitions := [], body := plan.expression}

def Plan.applied (plan : Plan) (input : Word) : Program := {
  resultType := .word, dataDefinitions := [], body := .apply plan.expression (.word input)}

def Plan.nodes (plan : Plan) : Nat := programNodes (plan.applied Word.zero)

/-! Specified shapes, from the plan. -/

def loweredKind (base : Nat) : FieldTy → String
  | .word => "word"
  | .tuple _ _ => "tuple"
  | .enum index => if index < base then "plain" else "sum"
  | .applied _ _ => "generic"
  | .param => "param"

def Plan.shapes (plan : Plan) : List (String × List String) :=
  let (decls, _) := plan.lowered
  let base := plan.decls.length
  let instances := plan.instances
  let binaryForm := fun (head : Head) (label : String) =>
    (plan.implOf? head).map fun impl => label ++ ":" ++ impl.form.name
  let sorted := fun (values : List String) => values.eraseDups.mergeSort (· ≤ ·)
  let sumOfProduct := instances.any fun (type, method) => method == .binary && (match type with
    | .enum index => base ≤ index && (match Enums.constructorsOf decls type with
        | some [[left], [right]] => (match left, right with
            | .tuple _ _, .tuple _ _ => false
            | .tuple _ _, _ | _, .tuple _ _ => true
            | _, _ => false)
        | _ => false)
    | _ => false)
  [("instances", sorted (instances.map fun (type, method) => loweredKind base type ++ ":" ++ method.name)),
   ("calls", sorted (plan.uses.map fun use => use.method.name ++ ":" ++ use.call.name)),
   ("depths", sorted (plan.uses.map fun use => toString use.type.depth)),
   ("arguments", sorted (instances.filterMap fun (type, _) => match type with
      | .applied _ argument => some (loweredKind base argument)
      | _ => none)),
   ("forms", sorted (instances.filterMap fun (type, method) =>
      if method != .binary then none
      else match headOf base type with
        | some .tuple => binaryForm .tuple "tuple"
        | some (.decl index) => binaryForm (.decl index) "enum"
        | _ => none)),
   ("shapes", if sumOfProduct then ["sum-of-product"] else [])]

/-! Generation: a SplitMix64 stream with this profile's domain. -/

def domain : UInt64 := 0x7472616974730001

def drawOp : Gen Op := return Enums.opOf (← draw 4)

def drawStep (operands : Nat) : Gen Step := do
  let combine ← if operands ≥ 2 then drawOp else pure .add
  let op ← if operands ≥ 1 then drawOp else pure .add
  return {combine, op, constant := ← drawConstant}

def drawImpl (decls : List Decl) (head : Head) : Gen Impl := do
  let unary ← ((operandCounts decls .unary head).getD []).mapM drawStep
  let binary ← ((operandCounts decls .binary head).getD []).mapM drawStep
  let form ← match head with
    | .tuple | .decl _ => do
        let bit ← draw 2
        pure (if bit = 0 then MatchForm.nested else .columns)
    | _ => pure .nested
  let mut mismatch : List Nat := []
  for _ in List.range (mismatchCount head) do
    mismatch := mismatch ++ [← drawConstant]
  return {head, unary, binary, form, mismatch}

/-- An instance type of exactly this depth; fuel bounds the depth. -/
def drawExact (decls : List Decl) : Nat → Nat → Gen Inst
  | 0, _ | _ + 1, 0 => return .word
  | fuel + 1, depth + 1 => do
      let plain := (List.range decls.length).filter fun index => (decls[index]?.map (!·.generic)).getD false
      let generic := (List.range decls.length).filter fun index => (decls[index]?.map (·.generic)).getD false
      match ← drawWeighted [2, 2, if depth = 0 && !plain.isEmpty then 2 else 0, if generic.isEmpty then 0 else 3] with
      | 0 | 1 =>
          let deep ← drawExact decls fuel depth
          let other ← drawExact decls fuel (← draw (depth + 1))
          let (left, right) := if (← draw 2) = 0 then (deep, other) else (other, deep)
          return if (← draw 2) = 0 then .tuple left right else .sum left right
      | 2 => return .enum (plain.getD (← draw plain.length) 0)
      | _ =>
          let index := generic.getD (← draw generic.length) 0
          return .applied index (← drawExact decls fuel depth)

/-- A random leaf, drawn as `EnumData` draws it. -/
def drawLeafVal : Gen Val := do
  match ← Enums.drawLeaf with
  | .leaf op constant => return .leaf op constant
  | _ => return .leaf .input 0

/-- A random value of a closed type; `top` admits the dot form. -/
def drawVal (decls : List Decl) : Nat → Bool → Inst → Gen Val
  | 0, _, _ => return .leaf .input 0
  | _ + 1, _, .word => drawLeafVal
  | fuel + 1, _, .tuple left right =>
      return .tuple (← drawVal decls fuel false left) (← drawVal decls fuel false right)
  | fuel + 1, _, .sum left right => do
      if (← draw 2) = 0 then return .inl (← drawVal decls fuel false left)
      else return .inr (← drawVal decls fuel false right)
  | fuel + 1, top, type => do
      match constructorsOf decls type with
      | some constructors =>
          let index ← draw constructors.length
          let sameName := formAdmitted decls type index top .sameName
          let form := match ← drawWeighted [3, if top then 1 else 0, if sameName then 2 else 0] with
            | 0 => Form.qualified
            | 1 => .dot
            | _ => .sameName
          match constructors.getD index [] with
          | [] => return .ctor0 index form
          | [field] => return .ctor1 index (← drawVal decls fuel false field) form
          | [first, second] =>
              return .ctor2 index (← drawVal decls fuel false first) (← drawVal decls fuel false second) form
          | _ => return .ctor0 index form
      | none => return .leaf .input 0

/-- Each value is the first of four candidates whose top constructor no
earlier value has, or the first candidate. -/
def drawBuilder (decls : List Decl) (type : Inst) : Gen Builder := do
  let offset ← draw 4
  let count := 1 + (← draw maximumTrees)
  let mut trees : List Val := []
  for _ in List.range count do
    let mut first : Option Val := none
    let mut chosen : Option Val := none
    for _ in List.range 4 do
      let candidate ← drawVal decls valueFuel true type
      if first.isNone then first := some candidate
      if chosen.isNone && !(trees.any (·.top == candidate.top)) then chosen := some candidate
    trees := trees ++ [(chosen.orElse fun _ => first).getD (.leaf .input 0)]
  return {offset, trees}

/-- A use type is the first of four candidates of the drawn depth whose
called type fits the type limit, or a Word. -/
def drawUse (decls : List Decl) : Gen Use := do
  let method := if (← draw 2) = 0 then Method.unary else .binary
  let call := match ← drawWeighted [2, 1, 1] with
    | 0 => Call.direct
    | 1 => .generic
    | _ => .lifted
  let depth ← drawWeighted [1, 3, 3, 3]
  let mut found : Option Inst := none
  for _ in List.range 4 do
    let candidate ← drawExact decls (maximumDepth + 1) depth
    let (lowered, sums) := (lowerM decls.length candidate).run []
    let root := if call == .lifted then Enums.Ty.tuple lowered lowered else lowered
    if found.isNone && typeAdmitted (decls ++ sums.map sumDecl) root then found := some candidate
  let type := found.getD .word
  let shift ← if method == .binary then (do let bits ← draw 4; pure (1 + bits)) else pure 0
  return {method, call, type, shift, builder := ← drawBuilder decls type}

def heads (decls : List Decl) : List Head := [.word, .tuple, .sum] ++ (List.range decls.length).map .decl

/-- Draws in plan order: declarations, impls, helpers, then the uses. -/
def drawPlan : Gen Plan := do
  let decls ← Enums.drawDecls
  let impls ← (heads decls).mapM (drawImpl decls)
  let mut helpers : List Helper := []
  for (call, method) in helperKeys do
    helpers := helpers ++ [{call, method, op := ← drawOp, constant := ← drawConstant}]
  let count := 1 + (← draw maximumUses)
  let mut uses : List Use := []
  for _ in List.range count do
    uses := uses ++ [← drawUse decls]
  let needed := neededHelpers uses
  return {decls, unary := true, binary := true, impls,
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

end Solcore.Synthesis.Core.Traits
end

section
-- leanmerge: from Solcore.Synthesis.Core.HierarchyPlan
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
end

section
-- leanmerge: from Solcore.Synthesis.Core.TraitShrink
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
end

section
-- leanmerge: from Solcore.Synthesis.Core.HierarchyShrink
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.TraitEmitter
/-! Source emission of a trait plan: the declarations, the trait `Sc_Fold`
with `sc_fold` and `sc_both`, its impls, the constrained generic helpers,
one builder function per use, and `run`, which calls every use. No emitter
proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Traits

open Solcore.Synthesis.Core.Traits
open Solcore.Synthesis.Source.Enums (enumName constructorName declLines leafText)

def emitterVersion : String := "solcore-source-traits-v1"
def wrapperVersion : String := "solcore-word-traits-contract-v1"

def contractName : String := "SynthesizedTraits"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedTraitsDeploy"]
def runtimePath : List String := ["SynthesizedTraitsDeploy", "SynthesizedTraits"]

def traitName : String := "Sc_Fold"

def methodText : Method → String
  | .unary => "sc_fold"
  | .binary => "sc_both"

def instText : Inst → String
  | .word => "word"
  | .tuple left right => "(" ++ instText left ++ ", " ++ instText right ++ ")"
  | .sum left right => "sum<" ++ instText left ++ ", " ++ instText right ++ ">"
  | .enum index => enumName index
  | .applied index argument => enumName index ++ "<" ++ instText argument ++ ">"

private def indented (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def arguments (texts : List String) : String :=
  if texts.isEmpty then "" else "(" ++ ", ".intercalate texts ++ ")"

private def instIndex : Inst → Nat
  | .enum index | .applied index _ => index
  | _ => 0

def valueText (decls : List Solcore.Synthesis.Core.Enums.Decl) : Nat → Inst → Val → String
  | 0, _, _ => "sc_x"
  | _ + 1, .word, .leaf op constant => leafText op constant
  | fuel + 1, .tuple left right, .tuple first second =>
      "(" ++ valueText decls fuel left first ++ ", " ++ valueText decls fuel right second ++ ")"
  | fuel + 1, .sum left _, .inl value => "inl(" ++ valueText decls fuel left value ++ ")"
  | fuel + 1, .sum _ right, .inr value => "inr(" ++ valueText decls fuel right value ++ ")"
  | fuel + 1, type, value => match constructorsOf decls type, value.constructor? with
      | some constructors, some (ctor, fields, form) =>
          let index := instIndex type
          let name := match form with
            | .qualified => enumName index ++ "." ++ constructorName decls index ctor
            | .dot => "." ++ constructorName decls index ctor
            | .sameName => enumName index
          name ++ arguments (((constructors.getD ctor []).zip fields).map fun (fieldType, field) =>
            valueText decls fuel fieldType field)
      | _, _ => "sc_x"

/-- An arm's result: the operands folded, then the operator and constant. -/
def stepText (step : Step) : List String → String
  | [] => toString step.constant
  | first :: rest =>
      let folded := rest.foldl (fun folded operand => "(" ++ folded ++ " " ++ step.combine.token ++ " " ++ operand ++ ")")
        first
      "(" ++ folded ++ " " ++ step.op.token ++ " " ++ toString step.constant ++ ")"

private def xNames : List String := ["sc_a", "sc_b"]
private def yNames : List String := ["sc_c", "sc_d"]

def unaryCall (name : String) : String := traitName ++ ".sc_fold(" ++ name ++ ")"

def binaryCall (first second : String) : String := traitName ++ ".sc_both(" ++ first ++ ", " ++ second ++ ")"

/-- Constructor `ctor` of an impl's type binding its fields: a tuple's
components, a sum's side, or a declaration's constructor, unqualified when it
is a same-name constructor. -/
def ctorPattern (decls : List Solcore.Synthesis.Core.Enums.Decl) (head : Head) (ctor fields : Nat)
    (names : List String) : String :=
  let bound := names.take fields
  match head with
  | .tuple => "(" ++ ", ".intercalate bound ++ ")"
  | .sum => (if ctor = 0 then "inl" else "inr") ++ arguments bound
  | .decl index =>
      let name := if ctor = 0 && (decls[index]?.map (·.sameName)).getD false then enumName index
        else enumName index ++ "." ++ constructorName decls index ctor
      name ++ arguments bound
  | .word => "_"

def implType (decls : List Solcore.Synthesis.Core.Enums.Decl) : Head → String
  | .word => "word"
  | .tuple => "(f, g)"
  | .sum => "sum<f, g>"
  | .decl index => enumName index ++ (if (decls[index]?.map (·.generic)).getD false then "<a>" else "")

def implHeader (decls : List Solcore.Synthesis.Core.Enums.Decl) : Head → String
  | .word => "impl " ++ traitName ++ "<word> {"
  | .tuple => "impl<f, g> " ++ traitName ++ "<(f, g)> where f: " ++ traitName ++ ", g: " ++ traitName ++ " {"
  | .sum => "impl<f, g> " ++ traitName ++ "<sum<f, g>> where f: " ++ traitName ++ ", g: " ++ traitName ++ " {"
  | .decl index =>
      if (decls[index]?.map (·.generic)).getD false then
        "impl<a> " ++ traitName ++ "<" ++ enumName index ++ "<a>> where a: " ++ traitName ++ " {"
      else "impl " ++ traitName ++ "<" ++ enumName index ++ "> {"

private def arm (indent : Nat) (header : String) (body : List String) : List String :=
  [indented indent ("case " ++ header ++ " {")] ++ body ++ [indented indent "}"]

private def defaultArm (indent : Nat) (value : Nat) : List String :=
  [indented indent "default {", indented (indent + 4) ("return " ++ toString value ++ ";"), indented indent "}"]

private def returned (indent : Nat) (text : String) : String := indented indent ("return " ++ text ++ ";")

def unaryBody (decls : List Solcore.Synthesis.Core.Enums.Decl) (head : Head) (counts : List Nat)
    (steps : List Step) : List String :=
  match head with
  | .word => [returned 8 (stepText (steps.headD default) ["sc_x"])]
  | _ =>
      let names := fun (ctor : Nat) => if head == .sum && ctor = 1 then ["sc_b"] else xNames
      [indented 8 "match (sc_x) {"] ++
        (counts.zip steps).zipIdx.flatMap (fun ((fields, step), ctor) =>
          arm 12 (ctorPattern decls head ctor fields (names ctor))
            [returned 16 (stepText step (((names ctor).take fields).map unaryCall))]) ++
        [indented 8 "}"]

def binaryBody (decls : List Solcore.Synthesis.Core.Enums.Decl) (head : Head) (counts : List Nat) (impl : Impl) :
    List String :=
  let steps := impl.binary
  let pairs := fun (fields : Nat) (left right : List String) =>
    ((left.take fields).zip (right.take fields)).map fun (first, second) => binaryCall first second
  match head, impl.form with
  | .word, _ => [returned 8 (stepText (steps.headD default) ["sc_x", "sc_y"])]
  | .sum, _ =>
      let mismatch := fun (index : Nat) => toString (impl.mismatch.getD index 0)
      [indented 8 "match (sc_x) {"] ++
        arm 12 "inl(sc_a)" ([indented 16 "match (sc_y) {"] ++
          arm 20 "inl(sc_c)" [returned 24 (stepText (steps.getD 0 default) [binaryCall "sc_a" "sc_c"])] ++
          arm 20 "inr(_)" [returned 24 (mismatch 0)] ++ [indented 16 "}"]) ++
        arm 12 "inr(sc_b)" ([indented 16 "match (sc_y) {"] ++
          arm 20 "inl(_)" [returned 24 (mismatch 1)] ++
          arm 20 "inr(sc_d)" [returned 24 (stepText (steps.getD 1 default) [binaryCall "sc_b" "sc_d"])] ++
          [indented 16 "}"]) ++
        [indented 8 "}"]
  | _, .nested =>
      [indented 8 "match (sc_x) {"] ++
        (counts.zip steps).zipIdx.flatMap (fun ((fields, step), ctor) =>
          arm 12 (ctorPattern decls head ctor fields xNames) ([indented 16 "match (sc_y) {"] ++
            arm 20 (ctorPattern decls head ctor fields yNames) [returned 24 (stepText step (pairs fields xNames yNames))] ++
            (if head == .tuple then [] else defaultArm 20 (impl.mismatch.getD 0 0)) ++ [indented 16 "}"])) ++
        [indented 8 "}"]
  | _, .columns =>
      [indented 8 "match (sc_x, sc_y) {"] ++
        (counts.zip steps).zipIdx.flatMap (fun ((fields, step), ctor) =>
          arm 12 ("(" ++ ctorPattern decls head ctor fields xNames ++ ", " ++ ctorPattern decls head ctor fields yNames ++ ")")
            [returned 16 (stepText step (pairs fields xNames yNames))]) ++
        (if head == .tuple then [] else defaultArm 12 (impl.mismatch.getD 0 0)) ++
        [indented 8 "}"]

def implLines (plan : Plan) (impl : Impl) : List String :=
  let decls := plan.decls
  let type := implType decls impl.head
  let unary := match operandCounts decls .unary impl.head with
    | some counts => if plan.unary then
        [indented 4 ("function sc_fold(sc_x: " ++ type ++ ") returns (word) {")] ++
          unaryBody decls impl.head counts impl.unary ++ [indented 4 "}"]
      else []
    | none => []
  let binary := match operandCounts decls .binary impl.head with
    | some counts => if plan.binary then
        [indented 4 ("function sc_both(sc_x: " ++ type ++ ", sc_y: " ++ type ++ ") returns (word) {")] ++
          binaryBody decls impl.head counts impl ++ [indented 4 "}"]
      else []
    | none => []
  [implHeader decls impl.head] ++ unary ++ binary ++ ["}", ""]

def traitLines (plan : Plan) : List String :=
  ["trait " ++ traitName ++ "<a> {"] ++
    (if plan.unary then [indented 4 "function sc_fold(sc_x: a) returns (word);"] else []) ++
    (if plan.binary then [indented 4 "function sc_both(sc_x: a, sc_y: a) returns (word);"] else []) ++
    ["}", ""]

def helperName (call : Call) (method : Method) : String :=
  match call, method with
  | .lifted, .unary => "sc_lift"
  | .lifted, .binary => "sc_lift2"
  | _, .unary => "sc_once"
  | _, .binary => "sc_twice"

def helperLines (helper : Helper) : List String :=
  let step : Step := {combine := .add, op := helper.op, constant := helper.constant}
  let call := match helper.call, helper.method with
    | .lifted, .unary => unaryCall "(sc_x, sc_x)"
    | .lifted, .binary => binaryCall "(sc_x, sc_y)" "(sc_y, sc_x)"
    | _, .unary => unaryCall "sc_x"
    | _, .binary => binaryCall "sc_x" "sc_y"
  let parameters := if helper.method == .unary then "sc_x: t" else "sc_x: t, sc_y: t"
  ["function " ++ helperName helper.call helper.method ++ "<t>(" ++ parameters ++ ") returns (word) where t: " ++
    traitName ++ " {", returned 4 (stepText step [call]), "}", ""]

def builderName (index : Nat) : String := "sc_u" ++ toString index

def builderLines (decls : List Solcore.Synthesis.Core.Enums.Decl) (index : Nat) (use : Use) : List String :=
  let header := "function " ++ builderName index ++ "(sc_x: word) returns (" ++ instText use.type ++ ") {"
  let value := fun (indent : Nat) (tree : Val) =>
    returned indent (valueText decls Solcore.Synthesis.Core.Enums.valueFuel use.type tree)
  match use.builder.trees with
  | [tree] => [header, value 4 tree, "}", ""]
  | trees =>
      let count := trees.length
      [header, indented 4 ("let sc_k: word = ((sc_x + " ++ toString use.builder.offset ++ ") & 3);")] ++
        (trees.take (count - 1)).zipIdx.flatMap (fun (tree, residue) =>
          [indented 4 ("if (sc_k == " ++ toString residue ++ ") {"), value 8 tree, indented 4 "}"]) ++
        [value 4 (trees.getLastD default), "}", ""]

def useText (index : Nat) (use : Use) : String :=
  let first := builderName index ++ "(sc_input)"
  let second := builderName index ++ "((sc_input + " ++ toString use.shift ++ "))"
  let callee := if use.call == .direct then traitName ++ "." ++ methodText use.method
    else helperName use.call use.method
  callee ++ "(" ++ (if use.method == .unary then first else first ++ ", " ++ second) ++ ")"

def runLines (plan : Plan) : List String :=
  let callLines := plan.uses.zipIdx.map fun (use, index) =>
    indented 8 ("let sc_r" ++ toString index ++ ": word = " ++ useText index use ++ ";")
  let combined := (List.range plan.uses.length).foldl (fun accumulated index =>
      if index = 0 then "sc_r0"
      else "(" ++ accumulated ++ " + (sc_r" ++ toString index ++ " * " ++ toString (2 * index + 1) ++ "))") ""
  ["contract " ++ contractName ++ " {",
   indented 4 ("function " ++ methodName ++ "(input: uint256) public returns (uint256) {"),
   indented 8 "let sc_input: word = Typedef.rep(input);"] ++ callLines ++
    [indented 8 ("return uint256(" ++ combined ++ ");"), indented 4 "}", "}"]

def emit (plan : Plan) : Solcore.Synthesis.Source.EmittedProgram :=
  let lines := ["import * from std;", "import * from std.dispatch;", ""] ++
    plan.decls.zipIdx.flatMap (fun (decl, index) => declLines plan.decls index decl) ++
    traitLines plan ++ plan.impls.flatMap (implLines plan) ++ plan.helpers.flatMap helperLines ++
    plan.uses.zipIdx.flatMap (fun (use, index) => builderLines plan.decls index use) ++
    runLines plan
  { source := "\n".intercalate lines ++ "\n", contractName, methodName, methodSignature, deployPath, runtimePath }

end Solcore.Synthesis.Source.Traits
end

section
-- leanmerge: from Solcore.Synthesis.Source.HierarchyEmitter
/-! Source emission of a trait hierarchy plan: the declarations, the base
trait `Sc_Fold` and its impls as `TraitEmitter` emits them, the subclass
`Sc_Sub` and the chain `Sc_Top` with their impls, the helpers, one builder
function per use's receiver and argument, and `run`, which calls every use.
No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Hierarchies

open Solcore.Synthesis.Core.Hierarchies
open Solcore.Synthesis.Core.Traits (Inst Step Head)
open Solcore.Synthesis.Source.Enums (enumName declLines)

abbrev Decl := Solcore.Synthesis.Core.Enums.Decl

def emitterVersion : String := "solcore-source-trait-hierarchies-v1"
def wrapperVersion : String := "solcore-word-trait-hierarchies-contract-v1"

def contractName : String := "SynthesizedTraitHierarchies"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedTraitHierarchiesDeploy"]
def runtimePath : List String := ["SynthesizedTraitHierarchiesDeploy", "SynthesizedTraitHierarchies"]

def baseName : String := Traits.traitName
def subName : String := "Sc_Sub"
def topName : String := "Sc_Top"

/-- The subclass method's name: `sc_fold`, the superclass's, when shadowing. -/
def mixName : Sub → String
  | .shadow => "sc_fold"
  | _ => "sc_mix"

private def indented (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def returned (indent : Nat) (text : String) : String := indented indent ("return " ++ text ++ ";")

private def arm (indent : Nat) (header : String) (body : List String) : List String :=
  [indented indent ("case " ++ header ++ " {")] ++ body ++ [indented indent "}"]

/-- An impl header of a trait at a head, constrained by the same trait. -/
def implHeader (decls : List Decl) (trait : String) : Head → String
  | .word => "impl " ++ trait ++ "<word>"
  | .tuple => "impl<f, g> " ++ trait ++ "<(f, g)> where f: " ++ trait ++ ", g: " ++ trait
  | .sum => "impl<f, g> " ++ trait ++ "<sum<f, g>> where f: " ++ trait ++ ", g: " ++ trait
  | .decl index =>
      if (decls[index]?.map (·.generic)).getD false then
        "impl<a> " ++ trait ++ "<" ++ enumName index ++ "<a>> where a: " ++ trait
      else "impl " ++ trait ++ "<" ++ enumName index ++ ">"

def mixCall (sub : Sub) (receiver argument : String) : String :=
  subName ++ "." ++ mixName sub ++ "(" ++ receiver ++ ", " ++ argument ++ ")"

private def xNames : List String := ["sc_a", "sc_b"]

/-- The subclass method's body at a head: a Word combines `sc_x` with the
base fold of `sc_y`, any other head matches `sc_x` and calls the method at
its bound values. -/
def mixBody (plan : Plan) (head : Head) (counts : List Nat) (steps : List Step) : List String :=
  match head with
  | .word => [returned 8 (Traits.stepText (steps.headD default) ["sc_x", Traits.unaryCall "sc_y"])]
  | _ =>
      let names := fun (ctor : Nat) => if head == .sum && ctor = 1 then ["sc_b"] else xNames
      [indented 8 "match (sc_x) {"] ++
        (counts.zip steps).zipIdx.flatMap (fun ((fields, step), ctor) =>
          arm 12 (Traits.ctorPattern plan.decls head ctor fields (names ctor))
            [returned 16 (Traits.stepText step (((names ctor).take fields).map fun name => mixCall plan.sub name "sc_y"))]) ++
        [indented 8 "}"]

def subImplLines (plan : Plan) (impl : SubImpl) : List String :=
  let header := implHeader plan.decls subName impl.head
  match mixCounts plan.decls impl.head with
  | some counts => if plan.sub.method then
      [header ++ " {", indented 4 ("function " ++ mixName plan.sub ++ "<u>(sc_x: " ++ Traits.implType plan.decls impl.head ++
          ", sc_y: u) returns (word) where u: " ++ baseName ++ " {")] ++
        mixBody plan impl.head counts impl.steps ++ [indented 4 "}", "}", ""]
    else [header ++ " {}", ""]
  | none => []

def topImplLines (plan : Plan) (head : Head) : List String := [implHeader plan.decls topName head ++ " {}", ""]

def hierarchyLines (plan : Plan) : List String :=
  (if plan.sub.method then
    ["trait " ++ subName ++ "<a> where a: " ++ baseName ++ " {",
     indented 4 ("function " ++ mixName plan.sub ++ "<u>(sc_x: a, sc_y: u) returns (word) where u: " ++ baseName ++ ";"),
     "}", ""]
   else ["trait " ++ subName ++ "<a> where a: " ++ baseName ++ " {}", ""]) ++
    ["trait " ++ topName ++ "<a> where a: " ++ subName ++ " {}", ""]

def helperName (call : Call) (method : Method) : String :=
  match call, method with
  | .top, .mix => "sc_mixt"
  | _, .mix => "sc_mixv"
  | .sub, .unary => "sc_up"
  | .sub, _ => "sc_up2"
  | .top, .unary => "sc_top"
  | .top, _ => "sc_top2"
  | .value, .unary => "sc_val"
  | .value, _ => "sc_val2"
  | _, .unary => "sc_fun"
  | _, _ => "sc_fun2"

def helperLines (plan : Plan) (helper : Helper) : List String :=
  let step : Step := {combine := .add, op := helper.op, constant := helper.constant}
  let bound := if helper.call == .top then topName else subName
  let arguments := match helper.method with
    | .unary => "sc_x"
    | _ => "sc_x, sc_y"
  let parameters := match helper.method with
    | .unary => "<t>(sc_x: t)"
    | .binary => "<t>(sc_x: t, sc_y: t)"
    | .mix => "<t, u>(sc_x: t, sc_y: u)"
  let bounds := "t: " ++ bound ++ (if helper.method == .mix then ", u: " ++ baseName else "")
  let target := match helper.method, helper.call with
    | .mix, _ => subName ++ "." ++ mixName plan.sub
    | .unary, .function => "sc_up"
    | _, .function => "sc_up2"
    | .unary, _ => baseName ++ ".sc_fold"
    | _, _ => baseName ++ ".sc_both"
  let header := "function " ++ helperName helper.call helper.method ++ parameters ++ " returns (word) where " ++
    bounds ++ " {"
  let body := match helper.call with
    | .value | .function => [indented 4 ("let sc_f = " ++ target ++ ";"),
        returned 4 (Traits.stepText step ["sc_f(" ++ arguments ++ ")"])]
    | _ => [returned 4 (Traits.stepText step [target ++ "(" ++ arguments ++ ")"])]
  [header] ++ body ++ ["}", ""]

def builderName (prefix_ : String) (index : Nat) : String := prefix_ ++ toString index

/-- A builder returning one of its values, selected by the residue
`(sc_x + offset) & 3` when it has several, as `TraitEmitter`'s. -/
def builderLines (decls : List Decl) (name : String) (type : Inst) (builder : Solcore.Synthesis.Core.Traits.Builder) :
    List String :=
  let header := "function " ++ name ++ "(sc_x: word) returns (" ++ Traits.instText type ++ ") {"
  let value := fun (indent : Nat) (tree : Solcore.Synthesis.Core.Traits.Val) =>
    returned indent (Traits.valueText decls Solcore.Synthesis.Core.Enums.valueFuel type tree)
  match builder.trees with
  | [tree] => [header, value 4 tree, "}", ""]
  | trees =>
      let count := trees.length
      [header, indented 4 ("let sc_k: word = ((sc_x + " ++ toString builder.offset ++ ") & 3);")] ++
        (trees.take (count - 1)).zipIdx.flatMap (fun (tree, residue) =>
          [indented 4 ("if (sc_k == " ++ toString residue ++ ") {"), value 8 tree, indented 4 "}"]) ++
        [value 4 (trees.getLastD default), "}", ""]

def argumentPrefixes : List String := ["sc_v", "sc_w"]

def useBuilderLines (decls : List Decl) (index : Nat) (use : Use) : List String :=
  builderLines decls (builderName "sc_u" index) use.type use.builder ++
    (use.arguments.zip argumentPrefixes).flatMap fun (argument, prefix_) =>
      builderLines decls (builderName prefix_ index) argument.type argument.builder

def useText (plan : Plan) (index : Nat) (use : Use) : String :=
  let first := builderName "sc_u" index ++ "(sc_input)"
  let second := builderName "sc_u" index ++ "((sc_input + " ++ toString use.shift ++ "))"
  let callee := match use.call, use.method with
    | .direct, .unary => baseName ++ ".sc_fold"
    | .direct, .binary => baseName ++ ".sc_both"
    | .direct, .mix => subName ++ "." ++ mixName plan.sub
    | call, method => helperName call method
  match use.method with
  | .unary => callee ++ "(" ++ first ++ ")"
  | .binary => callee ++ "(" ++ first ++ ", " ++ second ++ ")"
  | .mix =>
      let calls := (argumentPrefixes.take use.arguments.length).map fun prefix_ =>
        callee ++ "(" ++ first ++ ", " ++ builderName prefix_ index ++ "(sc_input))"
      "(" ++ " + ".intercalate calls ++ ")"

def runLines (plan : Plan) : List String :=
  let callLines := plan.uses.zipIdx.map fun (use, index) =>
    indented 8 ("let sc_r" ++ toString index ++ ": word = " ++ useText plan index use ++ ";")
  let combined := (List.range plan.uses.length).foldl (fun accumulated index =>
      if index = 0 then "sc_r0"
      else "(" ++ accumulated ++ " + (sc_r" ++ toString index ++ " * " ++ toString (2 * index + 1) ++ "))") ""
  ["contract " ++ contractName ++ " {",
   indented 4 ("function " ++ methodName ++ "(input: uint256) public returns (uint256) {"),
   indented 8 "let sc_input: word = Typedef.rep(input);"] ++ callLines ++
    [indented 8 ("return uint256(" ++ combined ++ ");"), indented 4 "}", "}"]

def emit (plan : Plan) : Solcore.Synthesis.Source.EmittedProgram :=
  let base := plan.base
  let lines := ["import * from std;", "import * from std.dispatch;", ""] ++
    plan.decls.zipIdx.flatMap (fun (decl, index) => declLines plan.decls index decl) ++
    Traits.traitLines base ++ plan.impls.flatMap (Traits.implLines base) ++
    hierarchyLines plan ++ plan.subImpls.flatMap (subImplLines plan) ++ plan.tops.flatMap (topImplLines plan) ++
    plan.helpers.flatMap (helperLines plan) ++
    plan.uses.zipIdx.flatMap (fun (use, index) => useBuilderLines plan.decls index use) ++
    runLines plan
  { source := "\n".intercalate lines ++ "\n", contractName, methodName, methodSignature, deployPath, runtimePath }

end Solcore.Synthesis.Source.Hierarchies
end

section
-- leanmerge: from Solcore.Synthesis.Source.TraitCases
/-! A trait case retains its plan, drawn from the case seed, and the plan's
complete original Core reference at the case input. The reference builds
every instance's closure from the plan, never from the source. Saved
observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Traits
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Traits
open Solcore.Synthesis.Core.Enums (Decl LeafOp Form)

def caseSchema : String := "solcore-lean.semantic-trait-case.v1"
def planSchema : String := "solcore-lean.trait-plan.v1"
def profileVersion : String := "runtime-traits-v1/plan-seed-v1"

/-- The decode bound of a saved reference and the largest node budget. -/
def caseLimit : Nat := 4096
def defaultNodes : Nat := 2048
def minimumNodes : Nat := 256

/-- An admitted plan whose reference passes the full Core checker. The input
is a literal, so the check at zero holds at every input. -/
structure CheckedPlan where private mk ::
  plan : Plan
  admitted : plan.admitted = true
  checked : (plan.applied Word.zero).check = true

namespace CheckedPlan

def ofPlan? (plan : Plan) : Option CheckedPlan :=
  if admitted : plan.admitted = true then
    if checked : (plan.applied Word.zero).check = true then some ⟨plan, admitted, checked⟩ else none
  else none

def program (plan : CheckedPlan) (input : Word) : Wire.Program := plan.plan.applied input

end CheckedPlan

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program := value.plan.program value.input

/-! Plan JSON. Words are decimal strings; every decoder is strict and the
decoded plan must re-encode to the saved JSON. -/

private def wordJson (value : Nat) : Json := toJson (toString value)

def instJson : Inst → Json
  | .word => toJson "word"
  | .tuple left right => Json.mkObj [("tuple", .arr #[instJson left, instJson right])]
  | .sum left right => Json.mkObj [("sum", .arr #[instJson left, instJson right])]
  | .enum index => Json.mkObj [("enum", toJson index)]
  | .applied index argument => Json.mkObj [("enum", toJson index), ("argument", instJson argument)]

private def fieldsJson (form : Form) (index : Nat) (fields : Array Json) : Json :=
  Json.mkObj [("constructor", toJson index), ("form", toJson form.name), ("fields", .arr fields)]

def valJson : Val → Json
  | .leaf op constant => Json.mkObj [("leaf", toJson op.name), ("constant", wordJson constant)]
  | .tuple left right => Json.mkObj [("tuple", .arr #[valJson left, valJson right])]
  | .inl value => Json.mkObj [("inl", valJson value)]
  | .inr value => Json.mkObj [("inr", valJson value)]
  | .ctor0 index form => fieldsJson form index #[]
  | .ctor1 index field form => fieldsJson form index #[valJson field]
  | .ctor2 index first second form => fieldsJson form index #[valJson first, valJson second]

def stepJson (step : Step) : Json := Json.mkObj [
  ("combine", toJson step.combine.name), ("op", toJson step.op.name), ("constant", wordJson step.constant)]

def headJson : Head → Json
  | .word => toJson "word"
  | .tuple => toJson "tuple"
  | .sum => toJson "sum"
  | .decl index => Json.mkObj [("enum", toJson index)]

def implJson (impl : Impl) : Json := Json.mkObj [
  ("head", headJson impl.head), ("unary", .arr (impl.unary.map stepJson).toArray),
  ("binary", .arr (impl.binary.map stepJson).toArray), ("form", toJson impl.form.name),
  ("mismatch", .arr (impl.mismatch.map wordJson).toArray)]

def helperJson (helper : Helper) : Json := Json.mkObj [
  ("call", toJson helper.call.name), ("method", toJson helper.method.name), ("op", toJson helper.op.name),
  ("constant", wordJson helper.constant)]

def builderJson (builder : Traits.Builder) : Json := Json.mkObj [
  ("offset", toJson builder.offset), ("values", .arr (builder.trees.map valJson).toArray)]

def useJson (use : Use) : Json := Json.mkObj [
  ("method", toJson use.method.name), ("call", toJson use.call.name), ("type", instJson use.type),
  ("shift", toJson use.shift), ("builder", builderJson use.builder)]

def methodsJson (plan : Plan) : Json :=
  toJson ((if plan.unary then ["unary"] else []) ++ (if plan.binary then ["binary"] else []))

def planJson (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("declarations", .arr (plan.decls.map Enums.declJson).toArray),
  ("methods", methodsJson plan), ("impls", .arr (plan.impls.map implJson).toArray),
  ("helpers", .arr (plan.helpers.map helperJson).toArray), ("uses", .arr (plan.uses.map useJson).toArray)]

private def decodeFuel : Nat := 64

private def wordOf (json : Json) : Except String Nat := do
  let text ← json.getStr?
  let some value := text.toNat? | throw "trait plan constant is not a decimal Word"
  unless toString value = text && value < 2 ^ 256 do throw "trait plan constant is not a canonical decimal Word"
  return value

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

private def pairOf (json : Json) (key : String) : Except String (Option (Json × Json)) := do
  match json.getObjValAs? (Array Json) key with
  | .ok components =>
      let [left, right] := components.toList | throw "trait plan pairs have two components"
      return some (left, right)
  | .error _ => return none

def instOf : Nat → Json → Except String Inst
  | 0, _ => throw "trait plan type is too deep"
  | fuel + 1, json => do
      if let .ok text := json.getStr? then
        if text = "word" then return .word else throw "unknown trait plan type"
      if let some (left, right) := (← pairOf json "tuple") then return .tuple (← instOf fuel left) (← instOf fuel right)
      if let some (left, right) := (← pairOf json "sum") then return .sum (← instOf fuel left) (← instOf fuel right)
      let index ← json.getObjValAs? Nat "enum"
      match json.getObjVal? "argument" with
      | .ok argument => return .applied index (← instOf fuel argument)
      | .error _ => return .enum index

private def opOf (json : Json) : Except String Traits.Op := do
  let some op := Enums.Op.ofString? (← json.getStr?) | throw "unknown trait plan operation"
  return op

def valOf : Nat → Json → Except String Val
  | 0, _ => throw "trait value is too deep"
  | fuel + 1, json => do
      if let .ok op := json.getObjValAs? String "leaf" then
        let some op := LeafOp.ofString? op | throw "unknown trait value leaf"
        return .leaf op (← wordOf (← json.getObjVal? "constant"))
      if let some (left, right) := (← pairOf json "tuple") then return .tuple (← valOf fuel left) (← valOf fuel right)
      if let .ok value := json.getObjVal? "inl" then return .inl (← valOf fuel value)
      if let .ok value := json.getObjVal? "inr" then return .inr (← valOf fuel value)
      let index ← json.getObjValAs? Nat "constructor"
      let some form := Form.ofString? (← json.getObjValAs? String "form") | throw "unknown constructor form"
      match ← array json "fields" with
      | [] => return .ctor0 index form
      | [field] => return .ctor1 index (← valOf fuel field) form
      | [first, second] => return .ctor2 index (← valOf fuel first) (← valOf fuel second) form
      | _ => throw "trait constructor values have at most two fields"

def stepOf (json : Json) : Except String Step := do
  return {combine := ← opOf (← json.getObjVal? "combine"), op := ← opOf (← json.getObjVal? "op"),
          constant := ← wordOf (← json.getObjVal? "constant")}

def headOfJson (json : Json) : Except String Head := do
  if let .ok text := json.getStr? then
    match text with
    | "word" => return .word
    | "tuple" => return .tuple
    | "sum" => return .sum
    | _ => throw "unknown trait impl head"
  return .decl (← json.getObjValAs? Nat "enum")

def implOf (json : Json) : Except String Impl := do
  let some form := MatchForm.ofString? (← json.getObjValAs? String "form") | throw "unknown trait match form"
  return {head := ← headOfJson (← json.getObjVal? "head"), unary := ← (← array json "unary").mapM stepOf,
          binary := ← (← array json "binary").mapM stepOf, form,
          mismatch := ← (← array json "mismatch").mapM wordOf}

def helperOf (json : Json) : Except String Helper := do
  let some call := Call.ofString? (← json.getObjValAs? String "call") | throw "unknown trait helper call"
  let some method := Method.ofString? (← json.getObjValAs? String "method") | throw "unknown trait method"
  return {call, method, op := ← opOf (← json.getObjVal? "op"), constant := ← wordOf (← json.getObjVal? "constant")}

def builderOf (json : Json) : Except String Traits.Builder := do
  return {offset := ← json.getObjValAs? Nat "offset", trees := ← (← array json "values").mapM (valOf decodeFuel)}

def useOf (json : Json) : Except String Use := do
  let some method := Method.ofString? (← json.getObjValAs? String "method") | throw "unknown trait method"
  let some call := Call.ofString? (← json.getObjValAs? String "call") | throw "unknown trait call form"
  return {method, call, type := ← instOf decodeFuel (← json.getObjVal? "type"),
          shift := ← json.getObjValAs? Nat "shift", builder := ← builderOf (← json.getObjVal? "builder")}

def planOf (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported trait plan schema"
  let methods ← (← array json "methods").mapM fun method => method.getStr?
  return {decls := ← (← array json "declarations").mapM Enums.declOf,
          unary := methods.contains "unary", binary := methods.contains "binary",
          impls := ← (← array json "impls").mapM implOf, helpers := ← (← array json "helpers").mapM helperOf,
          uses := ← (← array json "uses").mapM useOf}

def checkedPlan (json : Json) : Except String CheckedPlan := do
  let plan ← planOf json
  unless plan.admitted do
    throw "trait plan is outside the admitted declarations, impls, helpers, uses and builders"
  let some checked := CheckedPlan.ofPlan? plan | throw "trait reference failed the full Core checker"
  unless json == planJson plan do throw "saved trait plan differs from its canonical checked representation"
  unless plan.nodes ≤ caseLimit do throw "trait reference exceeds the 4,096-node case limit"
  return checked

def shapesJson (plan : Plan) : Json :=
  Json.mkObj (plan.shapes.map fun (dimension, values) => (dimension, toJson values))

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ =>
        [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram) (origin : Json) (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("traitPlan", planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("generatorVersion", toJson traitVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      ("traitShapes", shapesJson plan.plan)]),
    ("contract", Enums.contractJson emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw "trait reference exceeds the 4,096-node case limit"
  return makeCase plan input (emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic trait case schema"
  let plan ← checkedPlan (← json.getObjVal? "traitPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its trait plan's reference and runtime input"
  return ⟨plan, input⟩

/-- A generation filter on the reference, not a claim that this finite bank
covers a plan. -/
def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) := do
  Primitive.boundaryInputs.mapM fun input =>
    match (plan.program input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (plan : CheckedPlan) (fuel : Nat) (acceptance : Acceptance := .profile) :
    Except String Unit := do
  let results ← boundaryResults plan fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all eight boundary inputs returned the same Word"
  acceptance.check Primitive.boundaryInputs results

/-- The seed's plan, its uses dropped from the end while the reference
exceeds the budget. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String CheckedPlan := do
  let plan := (generate seed.toUInt64).fit nodes
  unless plan.nodes ≤ nodes do throw "trait reference exceeds the node budget"
  let some checked := CheckedPlan.ofPlan? plan | throw "trait reference failed admission or the full Core checker"
  return checked

private def generatedOrigin (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson "trait-generated"), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
  ("inputIndex", toJson inputIndex), ("validationFuel", toJson fuel)]

/-- Attempt limits count plans; case limits count individual runtime inputs. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless minimumNodes ≤ nodes && nodes ≤ caseLimit do throw "trait node budget is outside 256 to 4,096"
        let plan ← generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "trait-profile"), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok plan =>
          let emitted := emit plan.plan
          for (input, inputIndex) in (inputSelection.inputs Primitive.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := acceptance.record (inputSelection.record (generatedOrigin seed nodes inputIndex fuel))
              cases := cases.push (makeCase plan input emitted origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-! Reduction. -/

/-- The lexicographic shrink measure: plan size, then input. -/
structure Measure where
  plan : Nat
  input : Nat
  deriving Repr, BEq, DecidableEq

def Measure.StrictlySmaller (candidate source : Measure) : Prop :=
  candidate.plan < source.plan ∨ (candidate.plan = source.plan ∧ candidate.input < source.input)

instance (candidate source : Measure) : Decidable (candidate.StrictlySmaller source) := by
  unfold Measure.StrictlySmaller
  infer_instance

def CheckedInput.measure (value : CheckedInput) : Measure := ⟨value.plan.plan.size, value.input.val⟩

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  strict : candidate.measure.StrictlySmaller source.measure

private def sealReduction (source : CheckedInput) (plan : Plan) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofPlan? plan
  guard (plan.plan.nodes ≤ caseLimit)
  let candidate : CheckedInput := ⟨plan, input⟩
  if strict : candidate.measure.StrictlySmaller source.measure then some ⟨candidate, strict⟩ else none

/-- The plan reductions, normalized, with the input kept; then the inputs 0,
1 and half the input with the plan kept. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let input := source.input
  let raw := (planReductions source.plan.plan).map (fun plan => (plan.normalize, input)) ++
    [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (input.val / 2)].map fun value => (source.plan.plan, value)
  let mut seen : List String := []
  let mut result := []
  for (plan, input) in raw do
    if let some reduced := sealReduction source plan input then
      let key := (planJson reduced.candidate.plan.plan).compress ++ toString reduced.candidate.input.val
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("profileVersion", profileVersion), ("generatorVersion", traitVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the trait plan"
  unless (← json.getObjVal? "contract") == Enums.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the trait wrapper"
  unless (← provenance.getObjVal? "traitShapes") == shapesJson admitted.plan.plan do
    throw "saved trait shapes differ from the plan"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "trait-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported trait case origin"
  if kind = "trait-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ caseLimit do
      throw "saved generation budget exceeds profile limits"
    let plan ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan.plan == planJson admitted.plan.plan do
      throw "saved trait plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Primitive.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    inputSensitive plan validationFuel acceptance
    unless origin == acceptance.record (inputSelection.record
        (generatedOrigin (Seed.ofNat seed) nodes inputIndex validationFuel)) do
      throw "generated trait provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported trait provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved trait reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced trait provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "trait provenance contains unexpected fields"
  return fresh

/-- A shrink response stops before its compressed cases would exceed 1.5 MB,
below the campaign's 2 MiB tool-output limit. -/
def shrinkBytes : Nat := 1500000

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let mut cases : Array Json := #[]
  let mut bytes := 0
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentPlan", planJson source.plan.plan),
      ("parentInput", toJson (toString source.input.val))]
    let case ← emitCase reduced.candidate.plan reduced.candidate.input origin fuel
    let size := case.compress.utf8ByteSize
    if bytes + size > shrinkBytes then break
    bytes := bytes + size
    cases := cases.push case
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Traits
end

section
-- leanmerge: from Solcore.Synthesis.Source.HierarchyCases
/-! A trait hierarchy case retains its plan, drawn from the case seed, and the
plan's complete original Core reference at the case input. The reference
builds every closure from the plan, never from the source. Saved
observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Hierarchies
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Hierarchies

def caseSchema : String := "solcore-lean.semantic-trait-hierarchy-case.v1"
def planSchema : String := "solcore-lean.trait-hierarchy-plan.v1"
def profileVersion : String := "runtime-trait-hierarchies-v1/plan-seed-v1"

/-- The decode bound of a saved reference and the largest node budget. -/
def caseLimit : Nat := 4096
def defaultNodes : Nat := 2048
def minimumNodes : Nat := 256

/-- An admitted plan whose reference passes the full Core checker. The input
is a literal, so the check at zero holds at every input. -/
structure CheckedPlan where private mk ::
  plan : Plan
  admitted : plan.admitted = true
  checked : (plan.applied Word.zero).check = true

namespace CheckedPlan

def ofPlan? (plan : Plan) : Option CheckedPlan :=
  if admitted : plan.admitted = true then
    if checked : (plan.applied Word.zero).check = true then some ⟨plan, admitted, checked⟩ else none
  else none

def program (plan : CheckedPlan) (input : Word) : Wire.Program := plan.plan.applied input

end CheckedPlan

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program := value.plan.program value.input

/-! Plan JSON, with `TraitCases`' encoding of types, values, steps, heads,
impls and builders. Words are decimal strings; every decoder is strict and the
decoded plan must re-encode to the saved JSON. -/

private def wordJson (value : Nat) : Json := toJson (toString value)

def subImplJson (impl : SubImpl) : Json := Json.mkObj [
  ("head", Traits.headJson impl.head), ("steps", .arr (impl.steps.map Traits.stepJson).toArray)]

def helperJson (helper : Helper) : Json := Json.mkObj [
  ("call", toJson helper.call.name), ("method", toJson helper.method.name), ("op", toJson helper.op.name),
  ("constant", wordJson helper.constant)]

def argumentJson (argument : Argument) : Json := Json.mkObj [
  ("type", Traits.instJson argument.type), ("builder", Traits.builderJson argument.builder)]

def useJson (use : Use) : Json := Json.mkObj [
  ("method", toJson use.method.name), ("call", toJson use.call.name), ("type", Traits.instJson use.type),
  ("shift", toJson use.shift), ("builder", Traits.builderJson use.builder),
  ("arguments", .arr (use.arguments.map argumentJson).toArray)]

def planJson (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("declarations", .arr (plan.decls.map Enums.declJson).toArray),
  ("methods", Traits.methodsJson plan.base), ("impls", .arr (plan.impls.map Traits.implJson).toArray),
  ("subclass", toJson plan.sub.name), ("subImpls", .arr (plan.subImpls.map subImplJson).toArray),
  ("tops", .arr (plan.tops.map Traits.headJson).toArray),
  ("helpers", .arr (plan.helpers.map helperJson).toArray), ("uses", .arr (plan.uses.map useJson).toArray)]

private def decodeFuel : Nat := 64

private def wordOf (json : Json) : Except String Nat := do
  let text ← json.getStr?
  let some value := text.toNat? | throw "trait hierarchy plan constant is not a decimal Word"
  unless toString value = text && value < 2 ^ 256 do throw "trait hierarchy plan constant is not a canonical decimal Word"
  return value

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

private def opOf (json : Json) : Except String Traits.Op := do
  let some op := Enums.Op.ofString? (← json.getStr?) | throw "unknown trait hierarchy plan operation"
  return op

def subImplOf (json : Json) : Except String SubImpl := do
  return {head := ← Traits.headOfJson (← json.getObjVal? "head"), steps := ← (← array json "steps").mapM Traits.stepOf}

def helperOf (json : Json) : Except String Helper := do
  let some call := Call.ofString? (← json.getObjValAs? String "call") | throw "unknown trait hierarchy helper call"
  let some method := Method.ofString? (← json.getObjValAs? String "method") | throw "unknown trait hierarchy method"
  return {call, method, op := ← opOf (← json.getObjVal? "op"), constant := ← wordOf (← json.getObjVal? "constant")}

def argumentOf (json : Json) : Except String Argument := do
  return {type := ← Traits.instOf decodeFuel (← json.getObjVal? "type"),
          builder := ← Traits.builderOf (← json.getObjVal? "builder")}

def useOf (json : Json) : Except String Use := do
  let some method := Method.ofString? (← json.getObjValAs? String "method") | throw "unknown trait hierarchy method"
  let some call := Call.ofString? (← json.getObjValAs? String "call") | throw "unknown trait hierarchy call form"
  return {method, call, type := ← Traits.instOf decodeFuel (← json.getObjVal? "type"),
          shift := ← json.getObjValAs? Nat "shift", builder := ← Traits.builderOf (← json.getObjVal? "builder"),
          arguments := ← (← array json "arguments").mapM argumentOf}

def planOf (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported trait hierarchy plan schema"
  let methods ← (← array json "methods").mapM fun method => method.getStr?
  let some sub := Sub.ofString? (← json.getObjValAs? String "subclass") | throw "unknown trait hierarchy subclass"
  return {decls := ← (← array json "declarations").mapM Enums.declOf,
          unary := methods.contains "unary", binary := methods.contains "binary",
          impls := ← (← array json "impls").mapM Traits.implOf, sub,
          subImpls := ← (← array json "subImpls").mapM subImplOf,
          tops := ← (← array json "tops").mapM Traits.headOfJson,
          helpers := ← (← array json "helpers").mapM helperOf, uses := ← (← array json "uses").mapM useOf}

def checkedPlan (json : Json) : Except String CheckedPlan := do
  let plan ← planOf json
  unless plan.admitted do
    throw "trait hierarchy plan is outside the admitted declarations, impls, helpers, uses and builders"
  let some checked := CheckedPlan.ofPlan? plan | throw "trait hierarchy reference failed the full Core checker"
  unless json == planJson plan do throw "saved trait hierarchy plan differs from its canonical checked representation"
  unless plan.nodes ≤ caseLimit do throw "trait hierarchy reference exceeds the 4,096-node case limit"
  return checked

def shapesJson (plan : Plan) : Json :=
  Json.mkObj (plan.shapes.map fun (dimension, values) => (dimension, toJson values))

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ =>
        [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram) (origin : Json) (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("hierarchyPlan", planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("generatorVersion", toJson hierarchyVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      ("hierarchyShapes", shapesJson plan.plan)]),
    ("contract", Enums.contractJson emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw "trait hierarchy reference exceeds the 4,096-node case limit"
  return makeCase plan input (emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic trait hierarchy case schema"
  let plan ← checkedPlan (← json.getObjVal? "hierarchyPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its trait hierarchy plan's reference and runtime input"
  return ⟨plan, input⟩

/-- A generation filter on the reference, not a claim that this finite bank
covers a plan. -/
def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) := do
  Primitive.boundaryInputs.mapM fun input =>
    match (plan.program input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

def inputSensitive (plan : CheckedPlan) (fuel : Nat) (acceptance : Acceptance := .profile) :
    Except String Unit := do
  let results ← boundaryResults plan fuel
  unless results.any (fun value => results.any (fun other => value != other)) do
    throw "all eight boundary inputs returned the same Word"
  acceptance.check Primitive.boundaryInputs results

/-- The seed's plan, its uses dropped from the end while the reference
exceeds the budget. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String CheckedPlan := do
  let plan := (generate seed.toUInt64).fit nodes
  unless plan.nodes ≤ nodes do throw "trait hierarchy reference exceeds the node budget"
  let some checked := CheckedPlan.ofPlan? plan
    | throw "trait hierarchy reference failed admission or the full Core checker"
  return checked

private def generatedOrigin (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson "hierarchy-generated"), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
  ("inputIndex", toJson inputIndex), ("validationFuel", toJson fuel)]

/-- Attempt limits count plans; case limits count individual runtime inputs. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless minimumNodes ≤ nodes && nodes ≤ caseLimit do
          throw "trait hierarchy node budget is outside 256 to 4,096"
        let plan ← generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "hierarchy-profile"), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok plan =>
          let emitted := emit plan.plan
          for (input, inputIndex) in (inputSelection.inputs Primitive.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := acceptance.record (inputSelection.record (generatedOrigin seed nodes inputIndex fuel))
              cases := cases.push (makeCase plan input emitted origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-! Reduction. -/

/-- The lexicographic shrink measure: plan size, then input. -/
structure Measure where
  plan : Nat
  input : Nat
  deriving Repr, BEq, DecidableEq

def Measure.StrictlySmaller (candidate source : Measure) : Prop :=
  candidate.plan < source.plan ∨ (candidate.plan = source.plan ∧ candidate.input < source.input)

instance (candidate source : Measure) : Decidable (candidate.StrictlySmaller source) := by
  unfold Measure.StrictlySmaller
  infer_instance

def CheckedInput.measure (value : CheckedInput) : Measure := ⟨value.plan.plan.size, value.input.val⟩

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  strict : candidate.measure.StrictlySmaller source.measure

private def sealReduction (source : CheckedInput) (plan : Plan) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofPlan? plan
  guard (plan.plan.nodes ≤ caseLimit)
  let candidate : CheckedInput := ⟨plan, input⟩
  if strict : candidate.measure.StrictlySmaller source.measure then some ⟨candidate, strict⟩ else none

/-- The plan reductions, normalized, with the input kept; then the inputs 0,
1 and half the input with the plan kept. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let input := source.input
  let raw := (planReductions source.plan.plan).map (fun plan => (plan.normalize, input)) ++
    [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (input.val / 2)].map fun value => (source.plan.plan, value)
  let mut seen : List String := []
  let mut result := []
  for (plan, input) in raw do
    if let some reduced := sealReduction source plan input then
      let key := (planJson reduced.candidate.plan.plan).compress ++ toString reduced.candidate.input.val
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("profileVersion", profileVersion), ("generatorVersion", hierarchyVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the trait hierarchy plan"
  unless (← json.getObjVal? "contract") == Enums.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the trait hierarchy wrapper"
  unless (← provenance.getObjVal? "hierarchyShapes") == shapesJson admitted.plan.plan do
    throw "saved trait hierarchy shapes differ from the plan"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "hierarchy-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported trait hierarchy case origin"
  if kind = "hierarchy-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ caseLimit do
      throw "saved generation budget exceeds profile limits"
    let plan ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan.plan == planJson admitted.plan.plan do
      throw "saved trait hierarchy plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Primitive.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    inputSensitive plan validationFuel acceptance
    unless origin == acceptance.record (inputSelection.record
        (generatedOrigin (Seed.ofNat seed) nodes inputIndex validationFuel)) do
      throw "generated trait hierarchy provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported trait hierarchy provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved trait hierarchy reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced trait hierarchy provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "trait hierarchy provenance contains unexpected fields"
  return fresh

/-- A shrink response stops before its compressed cases would exceed 1.5 MB,
below the campaign's 2 MiB tool-output limit. -/
def shrinkBytes : Nat := 1500000

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let mut cases : Array Json := #[]
  let mut bytes := 0
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentPlan", planJson source.plan.plan),
      ("parentInput", toJson (toString source.input.val))]
    let case ← emitCase reduced.candidate.plan reduced.candidate.input origin fuel
    let size := case.compress.utf8ByteSize
    if bytes + size > shrinkBytes then break
    bytes := bytes + size
    cases := cases.push case
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Hierarchies
end
