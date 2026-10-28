import Solcore.Synthesis.Core.EnumMatch

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
