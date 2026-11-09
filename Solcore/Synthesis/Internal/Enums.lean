import Solcore.Synthesis.Core.EnumData
import Solcore.Synthesis.Source.Emitter
import Solcore.Synthesis.Internal.Functions

/-!
# Profile: enums

The profile `runtime-enums`: views over enum values, reductions, emitter and cases.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.EnumMatch
/-! Views that `match` enum values, and the plans of the `runtime-enums`
profile. The original Core reference compiles each match itself: a
constructor pattern unwraps the sum chain with nested `caseE`, a tuple pattern
projects, a variable names the matched value, and an arm that fails calls the
let-bound thunk of the remaining arms. Arms are checked useful and matches
exhaustive by the pattern-matrix algorithm, with no reference to the source
or its compiler. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Enums

open Solcore.Core (Word)
open Solcore.Core.Wire

def matchVersion : String := "core-enum-match-v1"

/-- Pattern variables are `sc_a` to `sc_d`, or `sc_w`, which shadows the
view's Word parameter. -/
def names : List String := ["sc_a", "sc_b", "sc_c", "sc_d", "sc_w"]
def parameterName : Nat := 4

inductive Pat where
  | wild
  | var (name : Nat)
  | tuple (left right : Pat)
  | ctor0 (index : Nat) (form : Form)
  | ctor1 (index : Nat) (field : Pat) (form : Form)
  | ctor2 (index : Nat) (first second : Pat) (form : Form)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Pat

/-- A constructor or tuple pattern's constructor and subpatterns. -/
def head : Pat → Option (Nat × List Pat)
  | .tuple left right => some (0, [left, right])
  | .ctor0 index _ => some (index, [])
  | .ctor1 index field _ => some (index, [field])
  | .ctor2 index first second _ => some (index, [first, second])
  | .wild | .var _ => none

def nodes : Pat → Nat
  | .wild | .var _ | .ctor0 _ _ => 1
  | .tuple left right | .ctor2 _ left right _ => 1 + left.nodes + right.nodes
  | .ctor1 _ field _ => 1 + field.nodes

/-- Nesting depth of constructor and tuple patterns. -/
def depth : Pat → Nat
  | .wild | .var _ => 0
  | .ctor0 _ _ => 1
  | .tuple left right | .ctor2 _ left right _ => 1 + max left.depth right.depth
  | .ctor1 _ field _ => 1 + field.depth

def variables : Pat → List Nat
  | .wild | .ctor0 _ _ => []
  | .var name => [name]
  | .tuple left right | .ctor2 _ left right _ => left.variables ++ right.variables
  | .ctor1 _ field _ => field.variables

/-- Matching a value's constructors; variables and wildcards match anything. -/
def accepts : Pat → Value → Bool
  | .wild, _ | .var _, _ => true
  | .tuple left right, .tuple first second => left.accepts first && right.accepts second
  | .ctor0 index _, .ctor0 other _ => index = other
  | .ctor1 index field _, .ctor1 other value _ => index = other && field.accepts value
  | .ctor2 index left right _, .ctor2 other first second _ =>
      index = other && left.accepts first && right.accepts second
  | _, _ => false

end Pat

def Pat.form? : Pat → Option Form
  | .ctor0 _ form | .ctor1 _ _ form | .ctor2 _ _ _ form => some form
  | _ => none

/-- Patterns are typed structurally; any constructor form is admitted in a
pattern, the same-name form only for a same-name constructor. -/
def patTyped (decls : List Decl) : Nat → Ty → Pat → Bool
  | 0, _, _ => false
  | _ + 1, _, .wild => true
  | _ + 1, _, .var _ => true
  | fuel + 1, .tuple left right, .tuple first second =>
      patTyped decls fuel left first && patTyped decls fuel right second
  | _ + 1, .tuple _ _, _ => false
  | fuel + 1, type, pattern => match constructorsOf decls type, pattern.head, pattern.form? with
      | some constructors, some (index, fields), some form => match constructors[index]? with
          | some types => types.length = fields.length && formAdmitted decls type index true form &&
              (types.zip fields).all fun (fieldType, field) => patTyped decls fuel fieldType field
          | none => false
      | _, _, _ => false

/-- The variables a pattern binds at a type, in order. -/
def patBindings (decls : List Decl) : Nat → Ty → Pat → List (Nat × Ty)
  | 0, _, _ => []
  | _ + 1, _, .wild => []
  | _ + 1, type, .var name => [(name, type)]
  | fuel + 1, type, pattern => match constructorsOf decls type, pattern.head with
      | some constructors, some (index, fields) =>
          ((constructors.getD index []).zip fields).flatMap fun (fieldType, field) =>
            patBindings decls fuel fieldType field
      | _, _ => []

def patFuel : Nat := 4 * typeFuel

/-! The pattern-matrix algorithm: is a vector useful after these rows? -/

private def specialize (index arity : Nat) (rows : List (List Pat)) : List (List Pat) :=
  rows.filterMap fun
    | first :: rest => match first.head with
        | none => some (List.replicate arity .wild ++ rest)
        | some (other, fields) => if other = index then some (fields ++ rest) else none
    | [] => none

private def defaultRows (rows : List (List Pat)) : List (List Pat) :=
  rows.filterMap fun
    | first :: rest => if first.head.isNone then some rest else none
    | [] => none

private def anyUseful (results : List (Option Bool)) : Option Bool :=
  if results.contains (some true) then some true
  else if results.contains none then none else some false

/-- `none` when fuel runs out. A Word or parameter column admits only
variables and wildcards. -/
def useful (decls : List Decl) : Nat → List Ty → List (List Pat) → List Pat → Option Bool
  | 0, _, _, _ => none
  | _ + 1, _, [], _ => some true
  | _ + 1, [], _ :: _, _ => some false
  | _ + 1, _ :: _, _ :: _, [] => some false
  | fuel + 1, type :: types, rows, first :: rest =>
      match constructorsOf decls type with
      | none => useful decls fuel types (rows.map List.tail) rest
      | some constructors =>
          match first.head with
          | some (index, fields) =>
              let fieldTypes := constructors.getD index []
              useful decls fuel (fieldTypes ++ types) (specialize index fieldTypes.length rows) (fields ++ rest)
          | none =>
              let heads := rows.filterMap fun row => (row.headD .wild).head.map Prod.fst
              if (List.range constructors.length).all heads.contains then
                anyUseful ((List.range constructors.length).map fun index =>
                  let fieldTypes := constructors.getD index []
                  useful decls fuel (fieldTypes ++ types) (specialize index fieldTypes.length rows)
                    (fieldTypes.map (fun _ => Pat.wild) ++ rest))
              else useful decls fuel types (defaultRows rows) rest

def usefulFuel : Nat := 512

def usefulRow (decls : List Decl) (types : List Ty) (rows : List (List Pat)) (row : List Pat) : Option Bool :=
  useful decls usefulFuel types rows row

def exhaustive (decls : List Decl) (types : List Ty) (rows : List (List Pat)) : Option Bool :=
  (usefulRow decls types rows (types.map fun _ => .wild)).map (!·)

/-! Arm bodies: a left fold of terms, then the arm's constant. -/

inductive Op where
  | add
  | sub
  | xor
  | mul
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Op

def name : Op → String
  | .add => "add"
  | .sub => "sub"
  | .xor => "xor"
  | .mul => "mul"

def ofString? : String → Option Op
  | "add" => some .add
  | "sub" => some .sub
  | "xor" => some .xor
  | "mul" => some .mul
  | _ => none

def binary : Op → BinaryOp
  | .add => .wordAdd
  | .sub => .wordSub
  | .xor => .wordXor
  | .mul => .wordMul

def token : Op → String
  | .add => "+"
  | .sub => "-"
  | .xor => "^"
  | .mul => "*"

end Op

inductive Term where
  | name (name : Nat)
  | constant (value : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Body where
  first : Term
  rest : List (Op × Term)
  constant : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumTerms : Nat := 4

/-- An arm of a nested match: one pattern, or none for `default`. -/
structure InnerArm where
  patterns : List Pat
  body : Body
  deriving Repr, BEq, DecidableEq, Inhabited

inductive ArmBody where
  | expr (body : Body)
  | nested (scrutinee : Nat) (arms : List InnerArm)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- One pattern per column, or none for `default`. -/
structure Arm where
  patterns : List Pat
  body : ArmBody
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumArms : Nat := 8
def maximumInnerArms : Nat := 6

inductive Kind where
  | single
  | pair
  | generic
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Kind

def name : Kind → String
  | .single => "single"
  | .pair => "pair"
  | .generic => "generic"

def ofString? : String → Option Kind
  | "single" => some .single
  | "pair" => some .pair
  | "generic" => some .generic
  | _ => none

end Kind

/-- A view matches one value (`single`), two (`pair`), or one value of a
generic declaration at its parameter (`generic`), called at two instances.
Builders: one per scrutinee, or one per instance. -/
structure View where
  kind : Kind
  scrutinees : List Ty
  instances : List Ty
  arms : List Arm
  builders : List Builder
  wordOffset : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumViews : Nat := 3

structure Plan where
  decls : List Decl
  views : List View
  deriving Repr, BEq, DecidableEq, Inhabited

/-! Admission. -/

abbrev Names := List (Nat × Ty)

def lookupType (scope : Names) (name : Nat) : Option Ty :=
  (scope.find? (·.1 = name)).map Prod.snd

def termAdmitted (scope : Names) : Term → Bool
  | .name name => lookupType scope name == some .word
  | .constant value => value < 2 ^ 256

def bodyAdmitted (scope : Names) (body : Body) : Bool :=
  body.rest.length < maximumTerms && termAdmitted scope body.first &&
    body.rest.all (fun (_, term) => termAdmitted scope term) && body.constant < 2 ^ 256

/-- The rows' patterns are typed, each row's names distinct, `default` only
last, every arm useful and the match exhaustive. -/
def rowsAdmitted (decls : List Decl) (types : List Ty) (rows : List (List Pat)) : Bool := Id.run do
  let mut previous : List (List Pat) := []
  for (row, index) in rows.zipIdx do
    if row.isEmpty then
      unless index + 1 = rows.length do return false
      unless usefulRow decls types previous (types.map fun _ => .wild) == some true do return false
      return true
    unless row.length = types.length do return false
    unless (types.zip row).all (fun (type, pattern) => patTyped decls patFuel type pattern) do return false
    let variables := row.flatMap Pat.variables
    unless variables.length = variables.eraseDups.length && variables.all (· ≤ parameterName) do return false
    unless usefulRow decls types previous row == some true do return false
    previous := previous ++ [row]
  return exhaustive decls types previous == some true

def rowBindings (decls : List Decl) (types : List Ty) (row : List Pat) : Names :=
  (types.zip row).flatMap fun (type, pattern) => patBindings decls patFuel type pattern

/-- A nested match is on a variable of an enum or tuple type. -/
def innerAdmitted (decls : List Decl) (scope : Names) (scrutinee : Nat) (arms : List InnerArm) : Bool :=
  match lookupType scope scrutinee with
  | some type => (constructorsOf decls type).isSome && 0 < arms.length && arms.length ≤ maximumInnerArms &&
      rowsAdmitted decls [type] (arms.map (·.patterns)) &&
      arms.all fun arm => bodyAdmitted (rowBindings decls [type] arm.patterns ++ scope) arm.body
  | none => false

def armsAdmitted (decls : List Decl) (types : List Ty) (arms : List Arm) : Bool :=
  0 < arms.length && arms.length ≤ maximumArms && rowsAdmitted decls types (arms.map (·.patterns)) &&
    arms.all fun arm =>
      let scope := rowBindings decls types arm.patterns ++ [(parameterName, .word)]
      match arm.body with
      | .expr body => bodyAdmitted scope body
      | .nested scrutinee inner => innerAdmitted decls scope scrutinee inner

def typeAdmitted (decls : List Decl) (type : Ty) : Bool :=
  validUse decls false type && wireTypeNodes (wireTy decls type) ≤ typeLimit

/-- A scrutinee is an enum or an instance of a generic one. -/
def scrutineeAdmitted (decls : List Decl) (type : Ty) : Bool :=
  typeAdmitted decls type && (match type with
    | .enum _ | .applied _ _ => true
    | _ => false)

def View.instanceTypes (view : View) : List Ty :=
  match view.kind, view.scrutinees with
  | .generic, [scrutinee] => view.instances.map fun argument => Ty.subst argument scrutinee
  | _, scrutinees => scrutinees

def View.admitted (decls : List Decl) (view : View) : Bool :=
  view.wordOffset < 2 ^ 256 && armsAdmitted decls view.scrutinees view.arms &&
    view.builders.length = view.instanceTypes.length &&
    (view.instanceTypes.zip view.builders).all (fun (type, builder) => builder.admitted decls type) &&
    match view.kind, view.scrutinees, view.instances with
    | .single, [type], [] => scrutineeAdmitted decls type
    | .pair, [first, second], [] => scrutineeAdmitted decls first && scrutineeAdmitted decls second
    | .generic, [.applied index .param], [first, second] =>
        (decls[index]?.map (·.generic)).getD false && first != second &&
        typeAdmitted decls first && typeAdmitted decls second &&
        validUse decls true (.applied index .param) &&
        view.instanceTypes.all (scrutineeAdmitted decls)
    | _, _, _ => false

def Decl.admitted (decls : List Decl) (index : Nat) (decl : Decl) : Bool :=
  2 ≤ decl.constructors.length && decl.constructors.length ≤ maximumConstructors &&
    decl.constructors.all (fun fields => fields.length ≤ maximumFields &&
      fields.all (validIn decls index decl.generic)) &&
    (!decl.sameName || (decl.constructors.headD []).length > 0) &&
    declNodes decls decl ≤ typeLimit

def Plan.admitted (plan : Plan) : Bool :=
  0 < plan.decls.length && plan.decls.length ≤ maximumDecls &&
    plan.decls.zipIdx.all (fun (decl, index) => decl.admitted plan.decls index) &&
    0 < plan.views.length && plan.views.length ≤ maximumViews &&
    plan.views.all (View.admitted plan.decls)

/-! The Core reference. Variables are compiled from absolute levels: at depth
`d`, level `l` is de Bruijn index `d - 1 - l`. -/

abbrev Scope := List (Nat × Ty × Nat)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

private def varAt (depth level : Nat) : Expr := .var (depth - 1 - level)

def lookupLevel (scope : Scope) (name : Nat) : Option (Ty × Nat) :=
  (scope.find? (·.1 = name)).map Prod.snd

def termExpr (depth : Nat) (scope : Scope) : Term → Expr
  | .name name => match lookupLevel scope name with
      | some (_, level) => varAt depth level
      | none => .unit
  | .constant value => word value

def bodyExpr (depth : Nat) (scope : Scope) (body : Body) : Expr :=
  let folded := body.rest.foldl
    (fun accumulated (op, term) => .binary op.binary accumulated (termExpr depth scope term))
    (termExpr depth scope body.first)
  .binary .wordAdd folded (word body.constant)

/-- The `caseE` chain to constructor `target` of a value at `level` whose type
is the sum chain of `payloads`. `inner` receives the depth and the payload's
level. -/
def chainCases (failure : Nat → Expr) (inner : Nat → Nat → Expr) : Nat → Nat → List WireTy → Nat → Expr
  | depth, level, [_], _ => inner depth level
  | depth, level, _ :: _, 0 => .caseE (varAt depth level) (inner (depth + 1) depth) (failure (depth + 1))
  | depth, level, _ :: rest, target + 1 =>
      .caseE (varAt depth level) (failure (depth + 1)) (chainCases failure inner (depth + 1) depth rest target)
  | _, _, [], _ => .unit

/-- Match a pattern against the value at `level`. `success` continues at a
depth with the extended scope; `failure` falls back at a depth. Components
are projected and let-bound unless their pattern is a wildcard. -/
def patExpr (decls : List Decl) : Nat → Nat → Scope → Ty → Nat → Pat →
    (Nat → Scope → Expr) → (Nat → Expr) → Expr
  | 0, _, _, _, _, _, _, _ => .unit
  | fuel + 1, depth, scope, type, level, pattern, success, failure =>
      let pair := fun (depth level : Nat) (left right : Ty) (first second : Pat)
          (success : Nat → Scope → Expr) =>
        let continueSecond := fun (depth : Nat) (scope : Scope) =>
          if second == .wild then success depth scope
          else .letE (.second (varAt depth level))
            (patExpr decls fuel (depth + 1) scope right depth second success failure)
        if first == .wild then continueSecond depth scope
        else .letE (.first (varAt depth level))
          (patExpr decls fuel (depth + 1) scope left depth first continueSecond failure)
      match pattern with
      | .wild => success depth scope
      | .var name => success depth ((name, type, level) :: scope)
      | _ => match type, constructorsOf decls type, pattern.head with
          | .tuple left right, _, some (_, [first, second]) => pair depth level left right first second success
          | _, some constructors, some (index, fields) =>
              let types := constructors.getD index []
              let inner := fun (depth payload : Nat) => match types, fields with
                | [], [] => success depth scope
                | [fieldType], [field] => patExpr decls fuel depth scope fieldType payload field success failure
                | [left, right], [first, second] => pair depth payload left right first second success
                | _, _ => .unit
              chainCases failure inner depth level (payloadWires decls constructors) index
          | _, _, _ => .unit

def columnsExpr (decls : List Decl) (depth : Nat) (scope : Scope) :
    List ((Ty × Nat) × Pat) → (Nat → Scope → Expr) → (Nat → Expr) → Expr
  | [], success, _ => success depth scope
  | ((type, level), pattern) :: rest, success, failure =>
      patExpr decls patFuel depth scope type level pattern
        (fun depth scope => columnsExpr decls depth scope rest success failure) failure

/-- Arms in order: each but the last is tried with the thunk of the remaining
arms as its failure; the last is reached only when exhaustiveness says it
matches. -/
def armsExpr {α : Type} (decls : List Decl) (bodyOf : Nat → Scope → α → Expr) (scope : Scope)
    (columns : List (Ty × Nat)) : Nat → List (List Pat × α) → Expr
  | _, [] => word 0
  | depth, [(patterns, body)] =>
      columnsExpr decls depth scope (columns.zip patterns) (fun depth scope => bodyOf depth scope body)
        (fun _ => word 0)
  | depth, (patterns, body) :: rest =>
      .letE (.lambda .unit .word (armsExpr decls bodyOf scope columns (depth + 1) rest))
        (columnsExpr decls (depth + 1) scope (columns.zip patterns) (fun depth scope => bodyOf depth scope body)
          (fun later => .apply (varAt later depth) .unit))

def armBodyExpr (decls : List Decl) (depth : Nat) (scope : Scope) : ArmBody → Expr
  | .expr body => bodyExpr depth scope body
  | .nested scrutinee arms => match lookupLevel scope scrutinee with
      | some (type, level) =>
          armsExpr decls (fun depth scope body => bodyExpr depth scope body) scope [(type, level)] depth
            (arms.map fun arm => (arm.patterns, arm.body))
      | none => .unit

/-- A view's closure at its instance types: scrutinees, then the Word. -/
def viewExpr (decls : List Decl) (arms : List Arm) (types : List Ty) : Expr :=
  let count := types.length
  let body := armsExpr decls (armBodyExpr decls) [(parameterName, .word, count)]
    (types.zipIdx.map fun (type, index) => (type, index)) (count + 1)
    (arms.map fun arm => (arm.patterns, arm.body))
  let wires := types.map (wireTy decls)
  let final := Expr.lambda .word .word body
  (wires.zipIdx.reverse.foldl (fun (inner, innerType) (wire, _) =>
      (Expr.lambda wire innerType inner, Solcore.Core.Wire.Ty.function wire innerType))
    (final, Solcore.Core.Wire.Ty.function .word .word)).1

/-- The closures of a view and its calls: each call applies a view closure to
the builders' values and to `input + wordOffset`. -/
structure Closures where
  closures : List Expr
  calls : List (Nat × List Nat × Nat)

def View.closures (decls : List Decl) (view : View) (base : Nat) : Closures :=
  match view.kind with
  | .generic =>
      let types := view.instanceTypes
      let views := types.map fun type => viewExpr decls view.arms [type]
      let builders := (types.zip view.builders).map fun (type, builder) => builderExpr decls type builder
      ⟨views ++ builders, types.zipIdx.map fun (_, index) =>
        (base + index, [base + types.length + index], view.wordOffset)⟩
  | _ =>
      let types := view.scrutinees
      let builders := (types.zip view.builders).map fun (type, builder) => builderExpr decls type builder
      ⟨viewExpr decls view.arms types :: builders,
        [(base, (List.range types.length).map (base + 1 + ·), view.wordOffset)]⟩

/-- The calls' results combined as `r_0 + 3 r_1 + 5 r_2 + …`. -/
def combine (depth first count : Nat) : Expr :=
  (List.range count).foldl (fun accumulated index =>
      if index = 0 then varAt depth first
      else .binary .wordAdd accumulated (.binary .wordMul (varAt depth (first + index)) (word (2 * index + 1))))
    (word 0)

def Plan.closures (plan : Plan) : Closures :=
  plan.views.foldl (fun accumulated view =>
      let next := view.closures plan.decls accumulated.closures.length
      ⟨accumulated.closures ++ next.closures, accumulated.calls ++ next.calls⟩) ⟨[], []⟩

/-- The program: the closures let-bound in order, then the entry over the
input, binding each call's Word in order and combining them. -/
def Plan.expression (plan : Plan) : Expr :=
  let closures := plan.closures
  let input := closures.closures.length
  let callExpr := fun (depth : Nat) (call : Nat × List Nat × Nat) =>
    let (viewLevel, builders, offset) := call
    let applied := builders.foldl
      (fun function builder => Expr.apply function (.apply (varAt depth builder) (varAt depth input)))
      (varAt depth viewLevel)
    Expr.apply applied (.binary .wordAdd (varAt depth input) (word offset))
  let entry := closures.calls.foldr
    (fun call inner => fun depth => Expr.letE (callExpr depth call) (inner (depth + 1)))
    (fun depth => combine depth (input + 1) closures.calls.length)
  closures.closures.foldr (fun closure inner => .letE closure inner) (.lambda .word .word (entry (input + 1)))

def Plan.program (plan : Plan) : Program := {
  resultType := .function .word .word, dataDefinitions := [], body := plan.expression}

def Plan.applied (plan : Plan) (input : Word) : Program := {
  resultType := .word, dataDefinitions := [], body := .apply plan.expression (.word input)}

def Plan.nodes (plan : Plan) : Nat := programNodes (plan.applied Word.zero)

/-! Specified shapes, from the plan, never measured. -/

def fieldKind : Ty → String
  | .word => "word"
  | .param => "param"
  | .tuple _ _ => "tuple"
  | .enum _ => "enum"
  | .applied _ _ => "applied"

def argumentKind : Ty → String
  | .word => "word"
  | .param => "param"
  | .tuple _ _ => "tuple"
  | _ => "enum"

/-- The arguments of every generic instance inside a type. -/
def Ty.arguments : Ty → List Ty
  | .tuple left right => left.arguments ++ right.arguments
  | .applied _ argument => argument :: argument.arguments
  | _ => []

/-- Constructor forms, nullary, tuple, variable and wildcard patterns, and
wildcard positions: `field`, `component`, `deep` (below two layers). -/
def Pat.forms : Nat → Pat → List String
  | _, .wild => ["wildcard"]
  | _, .var _ => ["variable"]
  | level, .tuple left right =>
      "tuple" :: (inside level left "component" ++ inside level right "component")
  | _, .ctor0 _ form => ["nullary", form.name]
  | level, .ctor1 _ field form => form.name :: inside level field "field"
  | level, .ctor2 _ first second form => form.name :: (inside level first "field" ++ inside level second "field")
where
  inside (level : Nat) (pattern : Pat) (position : String) : List String :=
    (if pattern == .wild then ["wildcard:" ++ position] ++ (if level ≥ 1 then ["wildcard:deep"] else []) else []) ++
      pattern.forms (level + 1)

def rowForms (rows : List (List Pat)) : List String :=
  let catchAll := fun (row : List Pat) => row.all fun pattern => pattern.head.isNone
  let rowNames := rows.map fun row => (row.flatMap Pat.variables).eraseDups
  (rows.flatMap fun row => match row with
    | [] => ["default"]
    | [.wild] => ["wildcard:arm"] ++ ["wildcard"]
    | patterns =>
        (if patterns.length > 1 && !catchAll patterns && patterns.contains .wild then ["wildcard:column"] else []) ++
        (if patterns.length > 1 && patterns.all (· == .wild) then ["wildcard:arm"] else []) ++
        patterns.flatMap (Pat.forms 0) ++
        (if (row.flatMap Pat.variables).contains parameterName then ["shadow"] else [])) ++
  (if !rows.any catchAll then ["exhaustive"] else []) ++
  (if (rowNames.flatMap id).length != (rowNames.flatMap id).eraseDups.length then ["repeated"] else [])

def rowDepths (rows : List (List Pat)) : List String :=
  rows.flatMap fun row => row.filterMap fun pattern =>
    if pattern.depth = 0 then none else some (toString (min pattern.depth 3))

def Arm.innerRows : Arm → List (List Pat)
  | {body := .nested _ inner, ..} => inner.map (·.patterns)
  | _ => []

def Plan.shapes (plan : Plan) : List (String × List String) :=
  let decls := plan.decls
  let fieldTypes := decls.flatMap fun decl => decl.constructors.flatMap id
  let useTypes := plan.views.flatMap fun view => view.scrutinees ++ view.instanceTypes
  let arguments := (fieldTypes ++ useTypes).flatMap Ty.arguments
  let tables := plan.views.flatMap fun view =>
    (view.arms.map (·.patterns)) :: view.arms.filterMap fun arm =>
      if arm.innerRows.isEmpty then none else some arm.innerRows
  let rebound := plan.views.any fun view => view.arms.any fun arm => match arm.body with
    | .nested _ inner => inner.any fun innerArm =>
        (innerArm.patterns.flatMap Pat.variables).any (arm.patterns.flatMap Pat.variables).contains
    | .expr _ => false
  let nested := plan.views.any fun view => view.arms.any fun arm => !arm.innerRows.isEmpty
  let patterns := (tables.flatMap rowForms) ++ (if nested then ["nested"] else []) ++
    (if rebound then ["rebound"] else [])
  let sorted := fun (values : List String) => values.eraseDups.mergeSort (· ≤ ·)
  [("constructors", sorted (decls.map fun decl => toString decl.constructors.length)),
   ("fields", sorted (decls.flatMap (fun decl => decl.constructors.map fun fields => "count:" ++ toString fields.length) ++
      fieldTypes.map fun type => "type:" ++ fieldKind type)),
   ("declarations", sorted (decls.flatMap (fun decl =>
      [if decl.generic then "generic" else "plain"] ++ (if decl.sameName then ["same-name"] else [])) ++
      arguments.map fun argument => "argument:" ++ argumentKind argument)),
   ("views", sorted (plan.views.map (·.kind.name))),
   ("patterns", sorted (patterns.filter fun shape => !shape.startsWith "wildcard:")),
   ("wildcards", sorted ((patterns.filter (·.startsWith "wildcard:")).map (·.drop 9 |>.toString))),
   ("depths", sorted (tables.flatMap rowDepths))]

/-! Generation from the case seed's stream. -/

/-- Separates the plan stream from other uses of a case seed. -/
def domain : UInt64 := 0x656e756d6d617401

/-- A variable (one of the five names, unless the row already binds it) or a
wildcard; always two draws. -/
def drawLeafPat (used : List Nat) : Gen (Pat × List Nat) := do
  let choice ← draw 2
  let name ← draw names.length
  if choice = 0 || used.contains name then return (.wild, used) else return (.var name, name :: used)

def drawPatForm (decls : List Decl) (type : Ty) (index : Nat) : Gen Form := do
  match ← drawWeighted [3, 1, if formAdmitted decls type index true .sameName then 2 else 0] with
  | 0 => return .qualified
  | 1 => return .dot
  | _ => return .sameName

/-- Refinement weights out of 12 by nesting level: 3/4, 1/2, 1/3, then none. -/
def refineWeight : Nat → Nat
  | 0 => 9
  | 1 => 6
  | 2 => 4
  | _ => 0

/-- A random pattern at a type: a constructor or tuple pattern with random
subpatterns, or a leaf. -/
def drawPat (decls : List Decl) : Nat → Nat → Ty → List Nat → Gen (Pat × List Nat)
  | 0, _, _, used => pure (.wild, used)
  | fuel + 1, level, type, used => do
      let choice ← draw 12
      match constructorsOf decls type with
      | none => drawLeafPat used
      | some constructors =>
          if choice ≥ refineWeight level then drawLeafPat used
          else match type with
            | .tuple left right => do
                let (first, used) ← drawPat decls fuel (level + 1) left used
                let (second, used) ← drawPat decls fuel (level + 1) right used
                return (.tuple first second, used)
            | _ => do
                let index ← draw constructors.length
                let form ← drawPatForm decls type index
                match constructors.getD index [] with
                | [field] => do
                    let (pattern, used) ← drawPat decls fuel (level + 1) field used
                    return (.ctor1 index pattern form, used)
                | [first, second] => do
                    let (left, used) ← drawPat decls fuel (level + 1) first used
                    let (right, used) ← drawPat decls fuel (level + 1) second used
                    return (.ctor2 index left right form, used)
                | _ => return (.ctor0 index form, used)

def drawRow (decls : List Decl) (types : List Ty) : Gen (List Pat) := do
  let mut used : List Nat := []
  let mut row : List Pat := []
  for type in types do
    let (pattern, next) ← drawPat decls patFuel 0 type used
    used := next
    row := row ++ [pattern]
  return row

/-- A first-column constructor with leaf subpatterns, other columns leaves. -/
def completionRow (decls : List Decl) (types : List Ty) (index : Nat) : Gen (List Pat) := do
  let mut used : List Nat := []
  let mut row : List Pat := []
  for (type, column) in types.zipIdx do
    let fieldTypes := if column = 0 then ((constructorsOf decls type).getD []).getD index [] else []
    let mut fields : List Pat := []
    for _ in fieldTypes do
      let (pattern, next) ← drawLeafPat used
      used := next
      fields := fields ++ [pattern]
    if column = 0 then
      let form ← drawPatForm decls type index
      let pattern := match type, fields with
        | .tuple _ _, [first, second] => Pat.tuple first second
        | _, [] => .ctor0 index form
        | _, [field] => .ctor1 index field form
        | _, [first, second] => .ctor2 index first second form
        | _, _ => .wild
      row := row ++ [pattern]
    else
      let (pattern, next) ← drawLeafPat used
      used := next
      row := row ++ [pattern]
  return row

/-- Up to `target` useful random rows, three candidates each; then, at random,
each useful first-column constructor with leaf subpatterns; then, if not
exhaustive, a catch-all: `default`, wildcards, or a variable first. At most
`limit` rows. -/
def drawRows (decls : List Decl) (types : List Ty) (target limit : Nat) : Gen (List (List Pat)) := do
  let mut rows : List (List Pat) := []
  for _ in List.range (min target (limit - 1)) do
    let mut added := false
    for _ in List.range 3 do
      let row ← drawRow decls types
      if !added && usefulRow decls types rows row == some true then
        rows := rows ++ [row]
        added := true
  let complete ← draw 2
  if complete = 0 && exhaustive decls types rows != some true then
    let count := ((types.headD .word |> constructorsOf decls).getD []).length
    for index in List.range count do
      let row ← completionRow decls types index
      if rows.length + 1 < limit && usefulRow decls types rows row == some true then
        rows := rows ++ [row]
  if exhaustive decls types rows != some true then
    match ← draw 3 with
    | 0 => rows := rows ++ [[]]
    | 1 => rows := rows ++ [types.map fun _ => Pat.wild]
    | _ => do
        let name ← draw parameterName
        rows := rows ++ [(Pat.var name) :: (types.drop 1).map fun _ => Pat.wild]
  return rows

def visibleWords (scope : Names) : List Nat :=
  (List.range names.length).filter fun name => lookupType scope name == some .word

def drawTerm (words : List Nat) : Gen Term := do
  if words.isEmpty || (← draw 4) = 0 then return .constant (← drawConstant)
  return .name (words.getD (← draw words.length) 0)

def opOf : Nat → Op
  | 0 => .add
  | 1 => .sub
  | 2 => .xor
  | _ => .mul

/-- The Words the row binds, visible in its scope, in binding order. -/
def boundWords (bindings scope : Names) : List Nat :=
  (bindings.filter fun (name, type) => type == .word && lookupType scope name == some .word).map Prod.fst

/-- Every bound Word up to the term limit, then one drawn term if room is
left, combined by drawn operations. -/
def drawBody (scope : Names) (bound : List Nat) : Gen Body := do
  let words := visibleWords scope
  let required := (bound.take maximumTerms).map Term.name
  let extra ← draw 2
  let mut terms := required
  if terms.isEmpty || (extra = 0 && terms.length < maximumTerms) then
    terms := terms ++ [← drawTerm words]
  let mut rest : List (Op × Term) := []
  for term in terms.drop 1 do
    rest := rest ++ [(opOf (← draw 4), term)]
  return {first := terms.headD (.constant 0), rest, constant := ← drawBits}

/-- A quarter of the arms that bind an enum or tuple value match it again. -/
def drawArmBody (decls : List Decl) (types : List Ty) (row : List Pat) : Gen ArmBody := do
  let bindings := rowBindings decls types row
  let scope := bindings ++ [(parameterName, .word)]
  let candidates := bindings.filter fun (_, type) => (constructorsOf decls type).isSome
  if (← draw 4) = 0 && !candidates.isEmpty then
    let (name, type) := candidates.getD (← draw candidates.length) (0, .word)
    let rows ← drawRows decls [type] (2 + (← draw 3)) maximumInnerArms
    let mut arms : List InnerArm := []
    for row in rows do
      let inner := rowBindings decls [type] row
      arms := arms ++ [{patterns := row, body := ← drawBody (inner ++ scope) (boundWords inner (inner ++ scope))}]
    return .nested name arms
  return .expr (← drawBody scope (boundWords bindings scope))

def drawArms (decls : List Decl) (types : List Ty) : Gen (List Arm) := do
  let rows ← drawRows decls types (2 + (← draw 5)) maximumArms
  let mut arms : List Arm := []
  for row in rows do
    arms := arms ++ [{patterns := row, body := ← drawArmBody decls types row}]
  return arms

/-- The first arm a single-column match selects for a value. -/
def firstArm (arms : List Arm) (value : Value) : Nat :=
  (arms.findIdx? fun arm => match arm.patterns with
    | [] => true
    | [pattern] => pattern.accepts value
    | _ => false).getD arms.length

/-- Each tree is the first of four candidates whose arm no earlier tree
selects, or the first candidate. Without arms, a candidate's top-level
constructor stands for its arm. -/
def drawBuilder (decls : List Decl) (type : Ty) (arms : Option (List Arm)) : Gen Builder := do
  let offset ← draw 4
  let count := 1 + (← draw maximumTrees)
  let mut trees : List Value := []
  let mut hit : List Nat := []
  for _ in List.range count do
    let mut chosen : Option Value := none
    for _ in List.range 4 do
      let value ← drawValue decls valueFuel true type
      let arm := match arms, value.constructor? with
        | some arms, _ => firstArm arms value
        | none, some (index, _, _) => index
        | none, none => 0
      if chosen.isNone && !hit.contains arm then
        chosen := some value
        hit := arm :: hit
    let fallback ← drawValue decls valueFuel true type
    trees := trees ++ [chosen.getD fallback]
  return {offset, trees}

def drawArgument (decls : List Decl) : Gen Ty := do
  let plain := (List.range decls.length).filter fun index => !(decls.getD index default).generic
  match ← drawWeighted [2, 1, if plain.isEmpty then 0 else 1] with
  | 0 => return .word
  | 1 => return .tuple .word .word
  | _ => return .enum (plain.getD (← draw plain.length) 0)

def drawScrutinee (decls : List Decl) : Gen Ty := do
  let index ← draw decls.length
  if (decls.getD index default).generic then
    let type := Ty.applied index (← drawArgument decls)
    return if scrutineeAdmitted decls type then type else .applied index .word
  return .enum index

def drawView (decls : List Decl) : Gen View := do
  let generics := (List.range decls.length).filter fun index => (decls.getD index default).generic
  let kind ← drawWeighted [3, 2, if generics.isEmpty then 0 else 2]
  let wordOffset ← drawConstant
  match kind with
  | 0 => do
      let type ← drawScrutinee decls
      let arms ← drawArms decls [type]
      let builder ← drawBuilder decls type (some arms)
      return {kind := .single, scrutinees := [type], instances := [], arms, builders := [builder], wordOffset}
  | 1 => do
      let first ← drawScrutinee decls
      let second ← drawScrutinee decls
      let arms ← drawArms decls [first, second]
      let left ← drawBuilder decls first none
      let right ← drawBuilder decls second none
      return {kind := .pair, scrutinees := [first, second], instances := [], arms, builders := [left, right],
              wordOffset}
  | _ => do
      let index := generics.getD (← draw generics.length) 0
      let admit := fun (argument : Ty) => if scrutineeAdmitted decls (.applied index argument) then argument else .word
      let first := admit (← drawArgument decls)
      let drawn := admit (← drawArgument decls)
      let second := if drawn == first then (if first == .word then .tuple .word .word else .word) else drawn
      let arms ← drawArms decls [.applied index .param]
      let left ← drawBuilder decls (.applied index first) (some arms)
      let right ← drawBuilder decls (.applied index second) (some arms)
      return {kind := .generic, scrutinees := [.applied index .param], instances := [first, second], arms,
              builders := [left, right], wordOffset}

def drawPlan : Gen Plan := do
  let decls ← drawDecls
  let count := 1 + (← draw maximumViews)
  let mut views : List View := []
  for _ in List.range count do
    views := views ++ [← drawView decls]
  return {decls, views}

def generate (seed : UInt64) : Plan :=
  Id.run (drawPlan.run' {seed, domain, index := 0})

/-- Views are dropped from the end while the reference exceeds the budget and
more than one remains. -/
def Plan.fit (nodes : Nat) (plan : Plan) : Plan := Id.run do
  let mut fitted := plan
  for _ in List.range maximumViews do
    if fitted.nodes > nodes && fitted.views.length > 1 then
      fitted := {fitted with views := fitted.views.dropLast}
  return fitted

end Solcore.Synthesis.Core.Enums
end

section
-- leanmerge: from Solcore.Synthesis.Core.EnumShrink
/-! Reductions of enum plans: removing views, constructors, fields, arms,
nesting, terms, values and declarations, each followed by normalization. The
caller seals each candidate by admission, the full Core checker and a
strictly smaller measure. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Enums

/-- Field types weigh more as they nest, so flattening one to a Word shrinks it. -/
def Ty.weight : Ty → Nat
  | .word | .param => 1
  | .enum _ => 2
  | .tuple left right => 1 + left.weight + right.weight
  | .applied _ argument => 2 + argument.weight

def Body.size (body : Body) : Nat := 1 + body.rest.length

def Arm.size (arm : Arm) : Nat :=
  1 + (arm.patterns.map Pat.nodes).foldl (· + ·) 0 + match arm.body with
    | .expr body => body.size
    | .nested _ arms => 1 + (arms.map fun inner =>
        1 + (inner.patterns.map Pat.nodes).foldl (· + ·) 0 + inner.body.size).foldl (· + ·) 0

def View.size (view : View) : Nat :=
  1 + (view.arms.map Arm.size).foldl (· + ·) 0 +
    (view.builders.map fun builder => (builder.trees.map Value.nodes).foldl (· + ·) 0).foldl (· + ·) 0

def Decl.size (decl : Decl) : Nat :=
  (decl.constructors.map fun fields => 1 + (fields.map Ty.weight).foldl (· + ·) 0).foldl (· + ·) 0

def Plan.size (plan : Plan) : Nat :=
  (plan.decls.map Decl.size).foldl (· + ·) 0 + (plan.views.map View.size).foldl (· + ·) 0

/-- Rows that are useful after the earlier kept rows, in order. -/
def pruneRows (decls : List Decl) (types : List Ty) (rows : List (List Pat)) : List Nat := Id.run do
  let mut kept : List (List Pat) := []
  let mut indices : List Nat := []
  for (row, index) in rows.zipIdx do
    let candidate := if row.isEmpty then types.map fun _ => Pat.wild else row
    if usefulRow decls types kept candidate == some true then
      kept := kept ++ [candidate]
      indices := indices ++ [index]
  return indices

private def fixTerm (scope : Names) : Term → Term
  | .name name => if lookupType scope name == some .word then .name name else .constant 0
  | term => term

def fixBody (scope : Names) (body : Body) : Body :=
  {body with first := fixTerm scope body.first, rest := body.rest.map fun (op, term) => (op, fixTerm scope term)}

/-- Unreachable arms are pruned, names that no longer mean a Word become 0,
and a nested match on a name that no longer means an enum or tuple becomes
its first inner body. -/
def normalizeArms (decls : List Decl) (types : List Ty) (arms : List Arm) : List Arm :=
  let kept := pruneRows decls types (arms.map (·.patterns))
  (kept.filterMap fun index => arms[index]?).map fun arm =>
    let scope := rowBindings decls types arm.patterns ++ [(parameterName, .word)]
    match arm.body with
    | .expr body => {arm with body := .expr (fixBody scope body)}
    | .nested scrutinee inner => match lookupType scope scrutinee with
        | some type =>
            if (constructorsOf decls type).isSome then
              let keptInner := pruneRows decls [type] (inner.map (·.patterns))
              {arm with body := .nested scrutinee ((keptInner.filterMap fun index => inner[index]?).map fun innerArm =>
                {innerArm with body := fixBody (rowBindings decls [type] innerArm.patterns ++ scope) innerArm.body})}
            else {arm with body := .expr (fixBody scope ((inner.headD default).body))}
        | none => {arm with body := .expr (fixBody scope ((inner.headD default).body))}

def Plan.normalize (plan : Plan) : Plan :=
  {plan with views := plan.views.map fun view =>
    {view with arms := normalizeArms plan.decls view.scrutinees view.arms}}

/-! Typed rewriting of patterns and values at a declaration's constructors.
A rewrite sees each constructor occurrence with its declaration. -/

private def declOfType : Ty → Option Nat
  | .enum index | .applied index _ => some index
  | _ => none

/-- Does a pattern name constructor `ctor` of declaration `decl`? -/
def patNames (decls : List Decl) (decl ctor : Nat) : Nat → Ty → Pat → Bool
  | 0, _, _ => false
  | fuel + 1, type, pattern => match constructorsOf decls type, pattern.head with
      | some constructors, some (index, fields) =>
          (declOfType type == some decl && index = ctor) ||
            ((constructors.getD index []).zip fields).any fun (fieldType, field) =>
              patNames decls decl ctor fuel fieldType field
      | _, _ => false

/-- Rebuild a constructor pattern or value from its index, fields and form. -/
private def rebuildPat (index : Nat) (form : Form) : List Pat → Pat
  | [] => .ctor0 index form
  | [field] => .ctor1 index field form
  | [first, second] => .ctor2 index first second form
  | _ => .wild

private def rebuildValue (index : Nat) (form : Form) : List Value → Value
  | [] => .ctor0 index form
  | [field] => .ctor1 index field form
  | [first, second] => .ctor2 index first second form
  | _ => .leaf .input 0

/-- A constructor rewrite: from the declaration, the old index, the form and
the fields with their old types, the new index, form and fields; `none` keeps
the occurrence. -/
abbrev Rewrite := Nat → Nat → Form → List Ty → Option (Nat × Form × List Nat)

/-- Rewrite every constructor pattern; dropped fields by position, and a
field whose new type is a Word turned into a leaf pattern. -/
def rewritePat (decls : List Decl) (rewrite : Rewrite) (flatten : Nat → Nat → Nat → Bool) :
    Nat → Ty → Pat → Pat
  | 0, _, pattern => pattern
  | fuel + 1, type, pattern => match pattern, constructorsOf decls type with
      | .tuple left right, some [[leftType, rightType]] =>
          .tuple (rewritePat decls rewrite flatten fuel leftType left) (rewritePat decls rewrite flatten fuel rightType right)
      | .wild, _ | .var _, _ => pattern
      | _, some constructors => match pattern.head, pattern.form?, declOfType type with
          | some (index, fields), some form, some decl =>
              let types := constructors.getD index []
              let rewritten := ((types.zip fields).zipIdx).map fun ((fieldType, field), position) =>
                let field := rewritePat decls rewrite flatten fuel fieldType field
                if flatten decl index position && field.head.isSome then Pat.wild else field
              match rewrite decl index form types with
              | some (newIndex, newForm, positions) =>
                  rebuildPat newIndex newForm (positions.filterMap fun position => rewritten[position]?)
              | none => rebuildPat index form rewritten
          | _, _, _ => pattern
      | _, none => pattern

/-- Rewrite every constructor value; a flattened field becomes `sc_x`. -/
def rewriteValue (decls : List Decl) (rewrite : Rewrite) (flatten : Nat → Nat → Nat → Bool) :
    Nat → Ty → Value → Value
  | 0, _, value => value
  | fuel + 1, type, value => match value, constructorsOf decls type with
      | .tuple first second, some [[leftType, rightType]] =>
          .tuple (rewriteValue decls rewrite flatten fuel leftType first)
            (rewriteValue decls rewrite flatten fuel rightType second)
      | .leaf _ _, _ => value
      | _, some constructors => match value.constructor?, declOfType type with
          | some (index, fields, form), some decl =>
              let types := constructors.getD index []
              let rewritten := ((types.zip fields).zipIdx).map fun ((fieldType, field), position) =>
                if flatten decl index position then Value.leaf .input 0
                else rewriteValue decls rewrite flatten fuel fieldType field
              match rewrite decl index form types with
              | some (newIndex, newForm, positions) =>
                  rebuildValue newIndex newForm (positions.filterMap fun position => rewritten[position]?)
              | none => rebuildValue index form rewritten
          | _, _ => value
      | _, none => value

/-- The smallest value of a type: constructor 0 with `sc_x` leaves. -/
def minimalValue (decls : List Decl) : Nat → Ty → Value
  | 0, _ => .leaf .input 0
  | _ + 1, .word => .leaf .input 0
  | fuel + 1, .tuple left right => .tuple (minimalValue decls fuel left) (minimalValue decls fuel right)
  | fuel + 1, type => match constructorsOf decls type with
      | some constructors => rebuildValue 0 .qualified ((constructors.headD []).map (minimalValue decls fuel))
      | none => .leaf .input 0

/-- Apply a typed rewrite to every pattern and value of a plan, with the old
declarations' types, then install the new declarations. -/
def Plan.rewrite (plan : Plan) (decls : List Decl) (rewrite : Rewrite) (flatten : Nat → Nat → Nat → Bool)
    (dropArm : Ty → List Pat → Bool := fun _ _ => false) : Plan :=
  let old := plan.decls
  let patterns := fun (types : List Ty) (row : List Pat) =>
    (types.zip row).map fun (type, pattern) => rewritePat old rewrite flatten patFuel type pattern
  let arms := fun (types : List Ty) (arms : List Arm) =>
    (arms.filter fun arm => !(arm.patterns.zip types).any fun (pattern, type) => dropArm type [pattern]).map fun arm =>
      let body := match arm.body with
        | .expr body => ArmBody.expr body
        | .nested scrutinee inner =>
            let type := (lookupType (rowBindings old types arm.patterns) scrutinee).getD .word
            .nested scrutinee ((inner.filter fun innerArm => !dropArm type innerArm.patterns).map fun innerArm =>
              {innerArm with patterns := patterns [type] innerArm.patterns})
      {patterns := patterns types arm.patterns, body}
  {decls, views := plan.views.map fun view =>
    {view with arms := arms view.scrutinees view.arms,
               builders := (view.instanceTypes.zip view.builders).map fun (type, builder) =>
                 {builder with trees := builder.trees.map (rewriteValue old rewrite flatten valueFuel type)}}}

private def keepAll (count : Nat) : List Nat := List.range count

/-- With the old types, rebuild a value: constructor `ctor` of declaration
`decl` becomes the new declarations' minimal value, later ones are
renumbered, and a same-name form the new declaration lacks becomes
qualified. -/
def replaceRemoved (old new : List Decl) (decl ctor : Nat) : Nat → Ty → Value → Value
  | 0, _, value => value
  | fuel + 1, type, value => match value, constructorsOf old type with
      | .tuple first second, some [[leftType, rightType]] =>
          .tuple (replaceRemoved old new decl ctor fuel leftType first)
            (replaceRemoved old new decl ctor fuel rightType second)
      | .leaf _ _, _ => value
      | _, some constructors => match value.constructor?, declOfType type with
          | some (index, fields, form), some owner =>
              let types := constructors.getD index []
              let fields := (types.zip fields).map fun (fieldType, field) =>
                replaceRemoved old new decl ctor fuel fieldType field
              if owner = decl && index = ctor then minimalValue new valueFuel type
              else
                let index := if owner = decl && index > ctor then index - 1 else index
                let sameName := (new[owner]?.map (·.sameName)).getD false
                rebuildValue index (if form == .sameName && !(index = 0 && sameName) then .qualified else form) fields
          | _, _ => value
      | _, none => value

/-- Constructor `ctor` of declaration `decl` removed: arms naming it dropped,
values using it replaced, later constructors renumbered. -/
def removeConstructor (plan : Plan) (decl ctor : Nat) : Plan :=
  match plan.decls[decl]? with
  | none => plan
  | some target =>
      let old := plan.decls
      let sameName := target.sameName && ctor != 0
      let decls := old.set decl {target with constructors := target.constructors.eraseIdx ctor, sameName}
      let form := fun (index : Nat) (form : Form) =>
        if index = 0 && form == .sameName && !sameName then Form.qualified else form
      let rewrite : Rewrite := fun owner index oldForm types =>
        if owner != decl then none
        else if index < ctor then some (index, form index oldForm, keepAll types.length)
        else if index = ctor then none
        else some (index - 1, form (index - 1) oldForm, keepAll types.length)
      let dropArm := fun (type : Ty) (row : List Pat) => row.any (patNames old decl ctor patFuel type)
      let rewritten := plan.rewrite decls rewrite (fun _ _ _ => false) dropArm
      {rewritten with views := (plan.views.zip rewritten.views).map fun (view, next) =>
        {next with builders := (view.instanceTypes.zip view.builders).map fun (type, builder) =>
          {builder with trees := builder.trees.map (replaceRemoved old decls decl ctor valueFuel type)}}}

/-- Field `position` of constructor `ctor` of declaration `decl` removed. -/
def removeField (plan : Plan) (decl ctor position : Nat) : Plan :=
  match plan.decls[decl]? with
  | none => plan
  | some target =>
      let remaining := (target.constructors.getD ctor []).eraseIdx position
      let sameName := target.sameName && !(ctor = 0 && remaining.isEmpty)
      let decls := plan.decls.set decl {target with constructors := target.constructors.set ctor remaining, sameName}
      let rewrite : Rewrite := fun owner index form types =>
        if owner = decl && index = ctor then
          some (index, (if form == .sameName && !sameName then .qualified else form),
            (keepAll types.length).filter (· != position))
        else none
      plan.rewrite decls rewrite (fun _ _ _ => false)

/-- Field `position` of constructor `ctor` of declaration `decl` made a Word. -/
def flattenField (plan : Plan) (decl ctor position : Nat) : Plan :=
  match plan.decls[decl]? with
  | none => plan
  | some target =>
      let constructors := target.constructors.set ctor ((target.constructors.getD ctor []).set position .word)
      let decls := plan.decls.set decl {target with constructors}
      plan.rewrite decls (fun _ _ _ _ => none) (fun owner index field => owner = decl && index = ctor && field = position)

def Ty.mentions (decl : Nat) : Ty → Bool
  | .enum index => index = decl
  | .applied index argument => index = decl || argument.mentions decl
  | .tuple left right => left.mentions decl || right.mentions decl
  | _ => false

/-- Later declaration references move down after declaration `decl`. -/
def Ty.shiftAfter (decl : Nat) : Ty → Ty
  | .enum index => .enum (if index > decl then index - 1 else index)
  | .applied index argument => .applied (if index > decl then index - 1 else index) (argument.shiftAfter decl)
  | .tuple left right => .tuple (left.shiftAfter decl) (right.shiftAfter decl)
  | type => type

/-- Declaration `decl` removed when nothing refers to it. -/
def removeDecl (plan : Plan) (decl : Nat) : Option Plan :=
  let fieldTypes := plan.decls.flatMap fun target => target.constructors.flatMap id
  let useTypes := plan.views.flatMap fun view => view.scrutinees ++ view.instances
  if (fieldTypes ++ useTypes).any (Ty.mentions decl) then none
  else
    let decls := (plan.decls.eraseIdx decl).map fun target =>
      {target with constructors := target.constructors.map (·.map (Ty.shiftAfter decl))}
    let views := plan.views.map fun view =>
      {view with scrutinees := view.scrutinees.map (Ty.shiftAfter decl),
                 instances := view.instances.map (Ty.shiftAfter decl)}
    some {decls, views}

/-- Every constructor or tuple subpattern of a pattern replaced by `_`, one
at a time. -/
def generalizations : Pat → List Pat
  | .wild | .var _ | .ctor0 _ _ => []
  | .tuple left right =>
      ((Pat.wild :: generalizations left).map fun pattern => Pat.tuple pattern right) ++
        ((Pat.wild :: generalizations right).map fun pattern => Pat.tuple left pattern)
  | .ctor1 index field form => (Pat.wild :: generalizations field).map fun pattern => Pat.ctor1 index pattern form
  | .ctor2 index first second form =>
      ((Pat.wild :: generalizations first).map fun pattern => Pat.ctor2 index pattern second form) ++
        ((Pat.wild :: generalizations second).map fun pattern => Pat.ctor2 index first pattern form)

/-- Rows with one pattern generalized, including a top-level pattern to `_`. -/
def rowGeneralizations (row : List Pat) : List (List Pat) :=
  row.zipIdx.flatMap fun (pattern, column) =>
    ((if pattern.head.isSome then [Pat.wild] else []) ++ generalizations pattern).map fun next => row.set column next

/-- Leaves replaced by `sc_x`, one at a time. -/
def leafSimplifications : Value → List Value
  | .leaf .input _ => []
  | .leaf _ _ => [.leaf .input 0]
  | .tuple left right => (leafSimplifications left).map (Value.tuple · right) ++
      (leafSimplifications right).map (Value.tuple left ·)
  | .ctor0 _ _ => []
  | .ctor1 index field form => (leafSimplifications field).map (Value.ctor1 index · form)
  | .ctor2 index first second form => (leafSimplifications first).map (Value.ctor2 index · second form) ++
      (leafSimplifications second).map (Value.ctor2 index first · form)

def bodyReductions (body : Body) : List Body :=
  (List.range body.rest.length).map fun index => {body with rest := body.rest.eraseIdx index}

def armReductions (arm : Arm) : List Arm :=
  (rowGeneralizations arm.patterns).map (fun patterns => {arm with patterns}) ++
    match arm.body with
    | .expr body => (bodyReductions body).map fun body => {arm with body := .expr body}
    | .nested scrutinee inner =>
        [{arm with body := .expr (inner.headD default).body}] ++
        (List.range inner.length).map (fun index => {arm with body := .nested scrutinee (inner.eraseIdx index)}) ++
        inner.zipIdx.flatMap fun (innerArm, index) =>
          (rowGeneralizations innerArm.patterns).map (fun patterns =>
              {arm with body := .nested scrutinee (inner.set index {innerArm with patterns})}) ++
            (bodyReductions innerArm.body).map fun body =>
              {arm with body := .nested scrutinee (inner.set index {innerArm with body})}

def viewReductions (view : View) : List View :=
  let arms := view.arms
  (List.range arms.length).map (fun index => {view with arms := arms.eraseIdx index}) ++
  ((List.range arms.length).filter (· ≥ 1)).map (fun index =>
    {view with arms := arms.take index ++ [{(arms.getD index default) with patterns := []}]}) ++
  arms.zipIdx.flatMap (fun (arm, index) => (armReductions arm).map fun next => {view with arms := arms.set index next}) ++
  view.builders.zipIdx.flatMap fun (builder, index) =>
    ((if builder.trees.length > 1 then
        (List.range builder.trees.length).map fun tree => {builder with trees := builder.trees.eraseIdx tree}
      else []) ++
      builder.trees.zipIdx.flatMap fun (tree, position) =>
        (leafSimplifications tree).map fun next => {builder with trees := builder.trees.set position next}).map
      fun next => {view with builders := view.builders.set index next}

/-- Every plan reduction before normalization: views, constructors, fields,
flattening, declarations, then each view's arms, patterns, bodies and
builders. -/
def planReductions (plan : Plan) : List Plan :=
  let views := plan.views
  (if views.length > 1 then (List.range views.length).map fun index => {plan with views := views.eraseIdx index}
    else []) ++
  plan.decls.zipIdx.flatMap (fun (decl, index) =>
    (if decl.constructors.length > 2 then
      (List.range decl.constructors.length).map (removeConstructor plan index) else []) ++
    decl.constructors.zipIdx.flatMap fun (fields, ctor) =>
      (List.range fields.length).map (removeField plan index ctor) ++
        ((fields.zipIdx.filter fun (field, _) => field != .word).map fun (_, position) =>
          flattenField plan index ctor position)) ++
  (List.range plan.decls.length).filterMap (removeDecl plan) ++
  views.zipIdx.flatMap fun (view, index) => (viewReductions view).map fun next => {plan with views := views.set index next}

end Solcore.Synthesis.Core.Enums
end

section
-- leanmerge: from Solcore.Synthesis.Source.EnumEmitter
/-! Source emission of an enum plan: top-level `enum` declarations, one
function per view whose body is one `match`, one builder function per
scrutinee or instance, and `run`, which calls every view on its builders'
values. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Enums

open Solcore.Synthesis.Core.Enums

def emitterVersion : String := "solcore-source-enums-v2"
def wrapperVersion : String := "solcore-word-enums-contract-v1"

def contractName : String := "SynthesizedEnums"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedEnumsDeploy"]
def runtimePath : List String := ["SynthesizedEnumsDeploy", "SynthesizedEnums"]

def enumName (index : Nat) : String := "Sc_T" ++ toString index

/-- Constructor `ctor` of declaration `index`; a same-name constructor 0
carries the enum's name. -/
def constructorName (decls : List Decl) (index ctor : Nat) : String :=
  if ctor = 0 && (decls[index]?.map (·.sameName)).getD false then enumName index
  else enumName index ++ "_" ++ toString ctor

def typeText : Ty → String
  | .word => "word"
  | .param => "a"
  | .tuple left right => "(" ++ typeText left ++ ", " ++ typeText right ++ ")"
  | .enum index => enumName index
  | .applied index argument => enumName index ++ "<" ++ typeText argument ++ ">"

private def indented (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate indent ' ') ++ text

private def arguments (texts : List String) : String :=
  if texts.isEmpty then "" else "(" ++ ", ".intercalate texts ++ ")"

def declLines (decls : List Decl) (index : Nat) (decl : Decl) : List String :=
  let count := decl.constructors.length
  ["enum " ++ enumName index ++ (if decl.generic then "<a>" else "") ++ " {"] ++
    decl.constructors.zipIdx.map (fun (fields, ctor) =>
      indented 4 (constructorName decls index ctor ++ arguments (fields.map typeText) ++
        (if ctor + 1 < count then "," else ""))) ++
    ["}", ""]

private def declIndex : Ty → Nat
  | .enum index | .applied index _ => index
  | _ => 0

def constructorText (decls : List Decl) (type : Ty) (ctor : Nat) : Form → String
  | .qualified => enumName (declIndex type) ++ "." ++ constructorName decls (declIndex type) ctor
  | .dot => "." ++ constructorName decls (declIndex type) ctor
  | .sameName => enumName (declIndex type)

def leafText : LeafOp → Nat → String
  | .input, _ => "sc_x"
  | .add, constant => "(sc_x + " ++ toString constant ++ ")"
  | .xor, constant => "(sc_x ^ " ++ toString constant ++ ")"
  | .mul, constant => "(sc_x * " ++ toString constant ++ ")"

def valueText (decls : List Decl) : Nat → Ty → Value → String
  | 0, _, _ => "sc_x"
  | _ + 1, .word, .leaf op constant => leafText op constant
  | fuel + 1, .tuple left right, .tuple first second =>
      "(" ++ valueText decls fuel left first ++ ", " ++ valueText decls fuel right second ++ ")"
  | fuel + 1, type, value => match constructorsOf decls type, value.constructor? with
      | some constructors, some (ctor, fields, form) =>
          let types := constructors.getD ctor []
          constructorText decls type ctor form ++
            arguments ((types.zip fields).map fun (fieldType, field) => valueText decls fuel fieldType field)
      | _, _ => "sc_x"

def patText (decls : List Decl) : Nat → Ty → Pat → String
  | 0, _, _ => "_"
  | _ + 1, _, .wild => "_"
  | _ + 1, _, .var name => names.getD name "_"
  | fuel + 1, .tuple left right, .tuple first second =>
      "(" ++ patText decls fuel left first ++ ", " ++ patText decls fuel right second ++ ")"
  | fuel + 1, type, pattern => match constructorsOf decls type, pattern.head, pattern.form? with
      | some constructors, some (ctor, fields), some form =>
          let types := constructors.getD ctor []
          constructorText decls type ctor form ++
            arguments ((types.zip fields).map fun (fieldType, field) => patText decls fuel fieldType field)
      | _, _, _ => "_"

def termText : Term → String
  | .name name => names.getD name "sc_w"
  | .constant value => toString value

def bodyLine (indent : Nat) (body : Body) : String :=
  let folded := body.rest.foldl
    (fun accumulated (op, term) => "(" ++ accumulated ++ " " ++ op.token ++ " " ++ termText term ++ ")")
    (termText body.first)
  indented indent ("return (" ++ folded ++ " + " ++ toString body.constant ++ ");")

def rowHeader (decls : List Decl) (types : List Ty) : List Pat → String
  | [] => "default {"
  | [pattern] => "case " ++ patText decls patFuel (types.headD .word) pattern ++ " {"
  | patterns => "case (" ++ ", ".intercalate ((types.zip patterns).map fun (type, pattern) =>
      patText decls patFuel type pattern) ++ ") {"

/-- The binding of a scrutinee name at an arm, as in the original Core. -/
private def scrutineeType (decls : List Decl) (types : List Ty) (row : List Pat) (name : Nat) : Ty :=
  (lookupType (rowBindings decls types row) name).getD .word

def armLines (decls : List Decl) (types : List Ty) (indent : Nat) (arm : Arm) : List String :=
  let body := match arm.body with
    | .expr body => [bodyLine (indent + 4) body]
    | .nested scrutinee arms =>
        let type := scrutineeType decls types arm.patterns scrutinee
        [indented (indent + 4) ("match (" ++ names.getD scrutinee "sc_w" ++ ") {")] ++
          arms.flatMap (fun inner =>
            [indented (indent + 8) (rowHeader decls [type] inner.patterns), bodyLine (indent + 12) inner.body,
             indented (indent + 8) "}"]) ++
          [indented (indent + 4) "}"]
  [indented indent (rowHeader decls types arm.patterns)] ++ body ++ [indented indent "}"]

def viewName (index : Nat) : String := "sc_view" ++ toString index

def builderName (view builder : Nat) : String := "sc_make" ++ toString view ++ "_" ++ toString builder

private def scrutineeNames : List String := ["sc_e", "sc_f"]

def viewLines (decls : List Decl) (index : Nat) (view : View) : List String :=
  let parameters := (view.scrutinees.zip scrutineeNames).map fun (type, name) => name ++ ": " ++ typeText type
  let header := "function " ++ viewName index ++ (if view.kind == .generic then "<a>" else "") ++ "(" ++
    ", ".intercalate (parameters ++ ["sc_w: word"]) ++ ") returns (word) {"
  [header, indented 4 ("match (" ++ ", ".intercalate (scrutineeNames.take view.scrutinees.length) ++ ") {")] ++
    view.arms.flatMap (armLines decls view.scrutinees 8) ++ [indented 4 "}", "}", ""]

def builderLines (decls : List Decl) (name : String) (type : Ty) (builder : Builder) : List String :=
  let header := "function " ++ name ++ "(sc_x: word) returns (" ++ typeText type ++ ") {"
  let returned := fun (indent : Nat) (tree : Value) =>
    indented indent ("return " ++ valueText decls valueFuel type tree ++ ";")
  match builder.trees with
  | [tree] => [header, returned 4 tree, "}", ""]
  | trees =>
      let count := trees.length
      [header, indented 4 ("let sc_k: word = ((sc_x + " ++ toString builder.offset ++ ") & 3);")] ++
        (trees.take (count - 1)).zipIdx.flatMap (fun (tree, residue) =>
          [indented 4 ("if (sc_k == " ++ toString residue ++ ") {"), returned 8 tree, indented 4 "}"]) ++
        [returned 4 (trees.getLastD default), "}", ""]

/-- Each call: the view, its builders and the view's Word offset. -/
def calls (plan : Plan) : List (Nat × List Nat × Nat) :=
  plan.views.zipIdx.flatMap fun (view, index) => match view.kind with
    | .generic => (List.range view.builders.length).map fun builder => (index, [builder], view.wordOffset)
    | _ => [(index, List.range view.builders.length, view.wordOffset)]

def runLines (plan : Plan) : List String :=
  let callLines := (calls plan).zipIdx.map fun ((view, builders, offset), index) =>
    indented 8 ("let sc_r" ++ toString index ++ ": word = " ++ viewName view ++ "(" ++
      ", ".intercalate (builders.map (fun builder => builderName view builder ++ "(sc_input)") ++
        ["(sc_input + " ++ toString offset ++ ")"]) ++ ");")
  let combined := (List.range (calls plan).length).foldl (fun accumulated index =>
      if index = 0 then "sc_r0"
      else "(" ++ accumulated ++ " + (sc_r" ++ toString index ++ " * " ++ toString (2 * index + 1) ++ "))") ""
  ["contract " ++ contractName ++ " {",
   indented 4 ("function " ++ methodName ++ "(input: uint256) public returns (uint256) {"),
   indented 8 "let sc_input: word = Typedef.rep(input);"] ++ callLines ++
    [indented 8 ("return uint256(" ++ combined ++ ");"), indented 4 "}", "}"]

def emit (plan : Plan) : EmittedProgram :=
  let lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;", ""] ++
    plan.decls.zipIdx.flatMap (fun (decl, index) => declLines plan.decls index decl) ++
    plan.views.zipIdx.flatMap (fun (view, index) =>
      viewLines plan.decls index view ++
        (view.instanceTypes.zip view.builders).zipIdx.flatMap fun ((type, builder), builderIndex) =>
          builderLines plan.decls (builderName index builderIndex) type builder) ++
    runLines plan
  { source := "\n".intercalate lines ++ "\n", contractName, methodName, methodSignature, deployPath, runtimePath }

end Solcore.Synthesis.Source.Enums
end

section
-- leanmerge: from Solcore.Synthesis.Source.EnumCases
/-! An enum case retains its plan, drawn from the case seed, and the plan's
complete original Core reference at the case input. The reference compiles
every match itself from the plan, never from the source. Saved observations
never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Enums
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Enums

def caseSchema : String := "solcore-lean.semantic-enum-case.v1"
def planSchema : String := "solcore-lean.enum-plan.v1"
def profileVersion : String := "runtime-enums-v1/plan-seed-v1"

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

def tyJson : Enums.Ty → Json
  | .word => toJson "word"
  | .param => toJson "param"
  | .tuple left right => Json.mkObj [("tuple", .arr #[tyJson left, tyJson right])]
  | .enum index => Json.mkObj [("enum", toJson index)]
  | .applied index argument => Json.mkObj [("enum", toJson index), ("argument", tyJson argument)]

def declJson (decl : Decl) : Json := Json.mkObj [
  ("generic", toJson decl.generic), ("sameName", toJson decl.sameName),
  ("constructors", .arr (decl.constructors.map fun fields => Json.arr (fields.map tyJson).toArray).toArray)]

def patJson : Pat → Json
  | .wild => toJson "_"
  | .var name => Json.mkObj [("var", toJson (names.getD name "_"))]
  | .tuple left right => Json.mkObj [("tuple", .arr #[patJson left, patJson right])]
  | .ctor0 index form => Json.mkObj [("constructor", toJson index), ("form", toJson form.name), ("fields", .arr #[])]
  | .ctor1 index field form =>
      Json.mkObj [("constructor", toJson index), ("form", toJson form.name), ("fields", .arr #[patJson field])]
  | .ctor2 index first second form => Json.mkObj [("constructor", toJson index), ("form", toJson form.name),
      ("fields", .arr #[patJson first, patJson second])]

def valueJson : Enums.Value → Json
  | .leaf op constant => Json.mkObj [("leaf", toJson op.name), ("constant", wordJson constant)]
  | .tuple left right => Json.mkObj [("tuple", .arr #[valueJson left, valueJson right])]
  | .ctor0 index form => Json.mkObj [("constructor", toJson index), ("form", toJson form.name), ("fields", .arr #[])]
  | .ctor1 index field form =>
      Json.mkObj [("constructor", toJson index), ("form", toJson form.name), ("fields", .arr #[valueJson field])]
  | .ctor2 index first second form => Json.mkObj [("constructor", toJson index), ("form", toJson form.name),
      ("fields", .arr #[valueJson first, valueJson second])]

def termJson : Enums.Term → Json
  | .name name => Json.mkObj [("name", toJson (names.getD name "_"))]
  | .constant value => Json.mkObj [("constant", wordJson value)]

def bodyJson (body : Body) : Json := Json.mkObj [
  ("terms", .arr ((body.first :: body.rest.map Prod.snd).map termJson).toArray),
  ("operations", .arr (body.rest.map fun (op, _) => toJson op.name).toArray),
  ("constant", wordJson body.constant)]

private def patternsJson (patterns : List Pat) : Json := .arr (patterns.map patJson).toArray

def armJson (arm : Arm) : Json := match arm.body with
  | .expr body => Json.mkObj [("patterns", patternsJson arm.patterns), ("return", bodyJson body)]
  | .nested scrutinee arms => Json.mkObj [("patterns", patternsJson arm.patterns),
      ("match", toJson (names.getD scrutinee "_")),
      ("arms", .arr (arms.map fun inner => Json.mkObj [("patterns", patternsJson inner.patterns),
        ("return", bodyJson inner.body)]).toArray)]

def builderJson (builder : Builder) : Json := Json.mkObj [
  ("offset", toJson builder.offset), ("values", .arr (builder.trees.map valueJson).toArray)]

def viewJson (view : View) : Json := Json.mkObj [
  ("kind", toJson view.kind.name), ("scrutinees", .arr (view.scrutinees.map tyJson).toArray),
  ("instances", .arr (view.instances.map tyJson).toArray), ("arms", .arr (view.arms.map armJson).toArray),
  ("builders", .arr (view.builders.map builderJson).toArray), ("wordOffset", wordJson view.wordOffset)]

def planJson (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("declarations", .arr (plan.decls.map declJson).toArray),
  ("views", .arr (plan.views.map viewJson).toArray)]

private def decodeFuel : Nat := 64

private def wordOf (json : Json) : Except String Nat := do
  let text ← json.getStr?
  let some value := text.toNat? | throw "enum plan constant is not a decimal Word"
  unless toString value = text && value < 2 ^ 256 do throw "enum plan constant is not a canonical decimal Word"
  return value

private def nameOf (json : Json) : Except String Nat := do
  let text ← json.getStr?
  let some index := names.idxOf? text | throw "unknown enum pattern variable"
  return index

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

def tyOf : Nat → Json → Except String Enums.Ty
  | 0, _ => throw "enum plan type is too deep"
  | fuel + 1, json => do
      if let .ok text := json.getStr? then
        match text with
        | "word" => return .word
        | "param" => return .param
        | _ => throw "unknown enum plan type"
      if let .ok components := json.getObjValAs? (Array Json) "tuple" then
        let [left, right] := components.toList | throw "enum plan tuple types have two components"
        return .tuple (← tyOf fuel left) (← tyOf fuel right)
      let index ← json.getObjValAs? Nat "enum"
      match json.getObjVal? "argument" with
      | .ok argument => return .applied index (← tyOf fuel argument)
      | .error _ => return .enum index

private def formOf (json : Json) : Except String Form := do
  let some form := Form.ofString? (← json.getObjValAs? String "form") | throw "unknown constructor form"
  return form

def patOf : Nat → Json → Except String Pat
  | 0, _ => throw "enum pattern is too deep"
  | fuel + 1, json => do
      if json == toJson "_" then return .wild
      if let .ok name := json.getObjVal? "var" then return .var (← nameOf name)
      if let .ok components := json.getObjValAs? (Array Json) "tuple" then
        let [left, right] := components.toList | throw "enum tuple patterns have two components"
        return .tuple (← patOf fuel left) (← patOf fuel right)
      let index ← json.getObjValAs? Nat "constructor"
      let form ← formOf json
      match ← array json "fields" with
      | [] => return .ctor0 index form
      | [field] => return .ctor1 index (← patOf fuel field) form
      | [first, second] => return .ctor2 index (← patOf fuel first) (← patOf fuel second) form
      | _ => throw "enum constructor patterns have at most two fields"

def valueOf : Nat → Json → Except String Enums.Value
  | 0, _ => throw "enum value is too deep"
  | fuel + 1, json => do
      if let .ok op := json.getObjValAs? String "leaf" then
        let some op := LeafOp.ofString? op | throw "unknown enum value leaf"
        return .leaf op (← wordOf (← json.getObjVal? "constant"))
      if let .ok components := json.getObjValAs? (Array Json) "tuple" then
        let [left, right] := components.toList | throw "enum tuple values have two components"
        return .tuple (← valueOf fuel left) (← valueOf fuel right)
      let index ← json.getObjValAs? Nat "constructor"
      let form ← formOf json
      match ← array json "fields" with
      | [] => return .ctor0 index form
      | [field] => return .ctor1 index (← valueOf fuel field) form
      | [first, second] => return .ctor2 index (← valueOf fuel first) (← valueOf fuel second) form
      | _ => throw "enum constructor values have at most two fields"

private def termOf (json : Json) : Except String Enums.Term := do
  if let .ok name := json.getObjVal? "name" then return .name (← nameOf name)
  return .constant (← wordOf (← json.getObjVal? "constant"))

def bodyOf (json : Json) : Except String Body := do
  let terms ← (← array json "terms").mapM termOf
  let operations ← (← array json "operations").mapM fun operation => do
    let some op := Op.ofString? (← operation.getStr?) | throw "unknown enum body operation"
    return op
  let first :: rest := terms | throw "an enum body has a term"
  unless operations.length = rest.length do throw "an enum body has one operation per later term"
  return {first, rest := operations.zip rest, constant := ← wordOf (← json.getObjVal? "constant")}

private def patternsOf (json : Json) : Except String (List Pat) := do
  (← array json "patterns").mapM (patOf decodeFuel)

def armOf (json : Json) : Except String Arm := do
  let patterns ← patternsOf json
  match json.getObjVal? "match" with
  | .ok scrutinee =>
      let arms ← (← array json "arms").mapM fun inner => do
        return ({patterns := ← patternsOf inner, body := ← bodyOf (← inner.getObjVal? "return")} : InnerArm)
      return {patterns, body := .nested (← nameOf scrutinee) arms}
  | .error _ => return {patterns, body := .expr (← bodyOf (← json.getObjVal? "return"))}

def builderOf (json : Json) : Except String Builder := do
  let trees ← (← array json "values").mapM (valueOf decodeFuel)
  return {offset := ← json.getObjValAs? Nat "offset", trees}

def viewOf (json : Json) : Except String View := do
  let some kind := Kind.ofString? (← json.getObjValAs? String "kind") | throw "unknown enum view kind"
  let scrutinees ← (← array json "scrutinees").mapM (tyOf decodeFuel)
  let instances ← (← array json "instances").mapM (tyOf decodeFuel)
  let arms ← (← array json "arms").mapM armOf
  let builders ← (← array json "builders").mapM builderOf
  return {kind, scrutinees, instances, arms, builders, wordOffset := ← wordOf (← json.getObjVal? "wordOffset")}

def declOf (json : Json) : Except String Decl := do
  let constructors ← (← array json "constructors").mapM fun fields => do
    let fields ← fields.getArr?
    fields.toList.mapM (tyOf decodeFuel)
  return {generic := ← json.getObjValAs? Bool "generic", sameName := ← json.getObjValAs? Bool "sameName",
          constructors}

def planOf (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported enum plan schema"
  let decls ← (← array json "declarations").mapM declOf
  return {decls, views := ← (← array json "views").mapM viewOf}

def checkedPlan (json : Json) : Except String CheckedPlan := do
  let plan ← planOf json
  unless plan.admitted do
    throw "enum plan is outside the admitted declarations, views, arms, patterns, bodies and builders"
  let some checked := CheckedPlan.ofPlan? plan | throw "enum reference failed the full Core checker"
  unless json == planJson plan do throw "saved enum plan differs from its canonical checked representation"
  unless plan.nodes ≤ caseLimit do throw "enum reference exceeds the 4,096-node case limit"
  return checked

def shapesJson (plan : Plan) : Json :=
  Json.mkObj (plan.shapes.map fun (dimension, values) => (dimension, toJson values))

/-- The reference on one input, with the observation fields of the primitive profile. -/
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

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Primitive.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram) (origin : Json) (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("enumPlan", planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("generatorVersion", toJson matchVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      ("enumShapes", shapesJson plan.plan)]),
    ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw "enum reference exceeds the 4,096-node case limit"
  return makeCase plan input (emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic enum case schema"
  let plan ← checkedPlan (← json.getObjVal? "enumPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its enum plan's reference and runtime input"
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

/-- The seed's plan, its views dropped from the end while the reference
exceeds the budget. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String CheckedPlan := do
  let plan := (generate seed.toUInt64).fit nodes
  unless plan.nodes ≤ nodes do throw "enum reference exceeds the node budget"
  let some checked := CheckedPlan.ofPlan? plan | throw "enum reference failed admission or the full Core checker"
  return checked

private def generatedOrigin (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson "enum-generated"), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
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
        unless minimumNodes ≤ nodes && nodes ≤ caseLimit do throw "enum node budget is outside 256 to 4,096"
        let plan ← generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "enum-profile"), ("reason", toJson error),
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
      ("profileVersion", profileVersion), ("generatorVersion", matchVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the enum plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the enum wrapper"
  unless (← provenance.getObjVal? "enumShapes") == shapesJson admitted.plan.plan do
    throw "saved enum shapes differ from the plan"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "enum-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported enum case origin"
  if kind = "enum-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ caseLimit do
      throw "saved generation budget exceeds profile limits"
    let plan ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan.plan == planJson admitted.plan.plan do
      throw "saved enum plan differs from its generation seed"
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
      throw "generated enum provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported enum provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved enum reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced enum provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "enum provenance contains unexpected fields"
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

end Solcore.Synthesis.Source.Enums
end
