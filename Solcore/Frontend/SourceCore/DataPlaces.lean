import Solcore.Frontend.SourceCore.DataExpressions
import Solcore.Frontend.SourceCore.Lowering
import Solcore.Frontend.SourceCore.Internal.FaultSites

/-!
# Lowering of places

Structural places, compiled to ordinary Core getter and updater functions. Main declarations:
`SourceCoreDataPlaces.Error`, `SourceCoreDataPlaces.declaredBinders`,
`SourceCoreDataPlaces.rootBinder`.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreDataPlaces
/-! Structural places compile to ordinary Core getter and updater functions.
All keys are evaluated once before selection. Compound arithmetic uses that
selection; reconstruction reads the latest root after the RHS. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDataPlaces

open SourceInference
abbrev Checked := SourceCoreDataCatalog.Checked
abbrev Error := SourceCoreBasic.Error
abbrev Scope := SourceCoreBasic.Scope
abbrev ExpressionLowerer := SourceCoreControl.ExpressionLowerer

def instructionBinders (instructions : List MatchPatternInstruction) : List TypedBinder :=
  instructions.filterMap fun | .binder binder => some binder | _ => none

def patternBinders (pattern : TypedMatchPattern) : List TypedBinder :=
  match pattern.resolution with
  | .binder binder => [binder]
  | .constructor _ children | .tuple children => instructionBinders children
  | _ => []

def declaredBinders (source : TypedSource) : List TypedBinder :=
  source.inputs ++ source.nodes.flatMap fun
    | .expression node => match node.form with
        | .lambda parameters _ _ => parameters
        | _ => []
    | .statement node => match node.form with
        | .letDecl binder _ => [binder]
        | .forLoop initial _ post _ => (initial ++ post).filterMap fun
            | .letDecl binder _ => some binder
            | _ => none
        | .matchWith resolution => resolution.cases.flatMap (fun arm => patternBinders arm.pattern)
        | _ => []

def rootBinder (source : TypedSource) (id : Resolved.LocalId) : Except Error TypedBinder := do
  if id.owner ≠ source.owner then throw (.ownerMismatch source.owner id.owner)
  match (declaredBinders source).filter (fun binder => decide (binder.id = id)) with
  | [binder] =>
      unless binder.scheme.quantified.isEmpty do throw (.polymorphicBinding id)
      unless binder.schemeRequirements.isEmpty do throw (.bindingRequirementsPresent id)
      pure binder
  | [] => throw (.missingBinding id)
  | _ => throw (.duplicateBinding id)

structure MemberBranch where
  constructor : Core.ConstructorId
  payloadTypes : List Core.Ty
  deriving Repr

inductive Step where
  | index (layout : Core.OrderedMapping.Layout) (key : ExpressionId)
      (valueType : TypeSystem.Ty)
  | member (dataType : Core.DataTypeId) (index : Nat) (branches : List MemberBranch)
      (fieldType : Core.Ty)
  deriving Repr

structure Route where
  rootSourceType : TypeSystem.Ty
  rootType : Core.Ty
  leafType : Core.Ty
  steps : List Step
  rootMapping : Option Core.OrderedMapping.Layout
  deriving Repr

def Step.resultType : Step → Core.Ty
  | .index layout _ _ => layout.valueType
  | .member _ _ _ type => type

def project (checked : Checked) (site : SourceCoreElaboration.ErrorSite) (type : TypeSystem.Ty) :
    Except Error Core.Ty := SourceCoreGeneralTypes.projectType checked site type

def memberStep (checked : Checked) (signatures : ProgramSignatures)
    (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (type : TypeSystem.Ty) (index : Nat) : Except Error (Step × TypeSystem.Ty) := do
  let type := SourceCoreDataCatalog.erase type
  let (declaration, arguments) ← match SourceCoreDataCatalog.nominalParts type with
    | some parts => pure parts
    | none => throw (.projectedAssignment root)
  let signature ← match signatures.dataTypes.filter (fun data => decide (data.id = declaration)) with
    | [signature] => pure signature
    | _ => throw (.projectedAssignment root)
  unless signature.parameters.length = arguments.length && !signature.constructors.isEmpty do
    throw (.projectedAssignment root)
  let identity ← match checked.catalog.identity? type with
    | some identity => pure identity
    | none => throw (.projectedAssignment root)
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  let mut selected : Option TypeSystem.Ty := none
  let mut branches := []
  for (constructor, position) in signature.constructors.zipIdx do
    let payloadTypes := constructor.payloadTypes.map substitution.apply
    let field ← match payloadTypes[index]? with
      | some field => pure field
      | none => throw (.projectedAssignment root)
    match selected with
    | none => selected := some field
    | some previous => unless SourceCoreDataCatalog.erase previous = SourceCoreDataCatalog.erase field do
        throw (.projectedAssignment root)
    let resolved ← (checked.catalog.resolveConstructor signatures {
      constructor := constructor.id, parameterSubstitution := substitution,
      payloadTypes, resultType := type }).mapError (fun _ => SourceCoreBasic.Error.projectedAssignment root)
    unless resolved.owner = identity && resolved.index = position do throw (.projectedAssignment root)
    branches := branches ++ [⟨resolved, ← payloadTypes.mapM (project checked site)⟩]
  let field ← match selected with
    | some field => pure field
    | none => throw (.projectedAssignment root)
  pure (.member identity index branches (← project checked site field), field)

def routeSteps (checked : Checked) (signatures : ProgramSignatures)
    (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) :
    TypeSystem.Ty → List PlaceProjection → Except Error (List Step × TypeSystem.Ty)
  | type, [] => pure ([], type)
  | type, projection :: rest => do
      let (step, selected) ← match projection with
        | .member _ index => memberStep checked signatures site root type index
        | .index key => do
            let (keySource, valueSource) ← match SourceCoreDataCatalog.erase type with
              | .mapping key value => pure (key, value)
              | _ => throw (.projectedAssignment root)
            if key.occurrence.owner ≠ source.owner then
              throw (.ownerMismatch source.owner key.occurrence.owner)
            let keyNode ← match source.lookupExpression? key with
              | some node => pure node
              | none => throw (.missingExpression key)
            let keyType ← project checked (.occurrence key.occurrence) keyNode.type
            let projectedKey ← project checked site keySource
            SourceCoreBasic.ensureType site projectedKey keyType
            let projectedValue ← project checked site valueSource
            let identity ← match checked.catalog.identity? type with
              | some identity => pure identity
              | none => throw (.projectedAssignment root)
            let layout : Core.OrderedMapping.Layout := ⟨projectedKey, projectedValue, identity⟩
            unless checked.catalog.definitions[identity.index]? = some layout.definition do
              throw (.projectedAssignment root)
            pure (.index layout key valueSource, valueSource)
      let (steps, final) ← routeSteps checked signatures source site root selected rest
      pure (step :: steps, final)

/-- Authenticate the retained path against the root declaration and every
constructor's payload, independently of the ambient de Bruijn positions. -/
def describe (checked : Checked) (signatures : ProgramSignatures) (source : TypedSource)
    (site : SourceCoreElaboration.ErrorSite) (assignment : AssignmentResolution) : Except Error Route := do
  let root := assignment.target.root
  unless assignment.requirements.isEmpty do throw (.assignmentRequirementsPresent root)
  let binder ← rootBinder source root
  let rootType ← project checked (.binder root) binder.scheme.body
  let (steps, selected) ← routeSteps checked signatures source site root binder.scheme.body assignment.target.projections
  unless SourceCoreDataCatalog.erase selected = SourceCoreDataCatalog.erase assignment.target.type do
    throw (.projectedAssignment root)
  let rootMapping ← match SourceCoreDataCatalog.erase binder.scheme.body with
    | .mapping key value => do
        let identity ← match checked.catalog.identity? binder.scheme.body with
          | some identity => pure identity
          | none => throw (.projectedAssignment root)
        let layout : Core.OrderedMapping.Layout :=
          ⟨← project checked site key, ← project checked site value, identity⟩
        unless checked.catalog.definitions[identity.index]? = some layout.definition do
          throw (.projectedAssignment root)
        pure (some layout)
    | _ => pure none
  pure ⟨binder.scheme.body, rootType, ← project checked site assignment.target.type, steps, rootMapping⟩

structure PreparedIndex where
  layout : Core.OrderedMapping.Layout
  key : ExpressionId
  keyPosition : Nat
  comparison : Core.Expr
  default : Core.Expr
  missing : Core.Word
  deriving Repr

inductive PreparedStep where
  | index (prepared : PreparedIndex)
  | member (dataType : Core.DataTypeId) (index : Nat) (branches : List MemberBranch) (fieldType : Core.Ty)
  deriving Repr

structure Prepared where
  route : Route
  steps : List PreparedStep
  keys : List (ExpressionId × Core.Ty)
  invalidProjection : Core.Word
  deriving Repr

def prepare (checked : Checked) (fuel : Nat) (route : Route)
    (invalid : Core.Word) (missing : TypeSystem.Ty → Core.Word) : Except Error Prepared := do
  let mut steps := []
  let mut keys := []
  for step in route.steps do
    match step with
    | .member dataType index branches fieldType => steps := steps ++ [.member dataType index branches fieldType]
    | .index layout key valueType =>
        let keySource ← match checked.catalog.entries[layout.dataType.index]? with
          | some entry => match entry.sourceType with
            | .mapping key _ => pure key
            | _ => throw (.missingExpression key)
          | none => throw (.missingExpression key)
        let comparison ← (SourceCoreDataEquality.prepare fuel checked keySource).mapError
          (fun _ => SourceCoreBasic.Error.missingExpression key)
        let default ← (SourceCoreDefaultValue.prepare (valueType.size + 1) checked valueType).mapError
          (fun _ => SourceCoreBasic.Error.missingExpression key)
        steps := steps ++ [.index ⟨layout, key, keys.length, comparison.expression, default.expression, missing valueType⟩]
        keys := keys ++ [(key, layout.keyType)]
  pure ⟨route, steps, keys, invalid⟩

def shift (count : Nat) (expression : Core.Expr) : Core.Expr :=
  (List.range count).foldl (fun expression _ => expression.weakenAt 0) expression

def pack : List Core.Expr → Core.Expr
  | [] => .unit
  | [one] => one
  | one :: rest => .pair one (pack rest)

def replacePacked (index : Nat) (types : List Core.Ty) (payload value : Core.Expr) : Core.Expr :=
  pack (types.zipIdx.map fun (_, position) => if position = index then value
    else SourceCoreDataExpressions.projectPacked position types payload)

def normalizeRoot (prepared : Prepared) (optional : Core.Expr) : Core.Expr :=
  match prepared.route.rootMapping with
  | some layout => .caseE optional
      (.inRight .unit (Core.OrderedMapping.empty layout)) (.inRight .unit (.var 0))
  | none => optional

def Prepared.keyTypes (prepared : Prepared) : List Core.Ty := prepared.keys.map (·.2)
def Prepared.optionalLeaf (prepared : Prepared) : Core.Ty := Core.OptionalCell.cellType prepared.route.leafType

def selectedIndex (prepared : Prepared) (index : PreparedIndex) (current keys : Core.Expr) : Core.Expr :=
  let key := SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys
  Core.LanguageResult.bind index.layout.valueType
    (Core.OrderedMapping.lookup index.layout index.comparison current key)
    (.caseE (.var 0)
      (.caseE index.default
        (Core.LanguageResult.failure index.layout.valueType (.word index.missing))
        (Core.LanguageResult.success (.var 0)))
      (Core.LanguageResult.success (.var 0)))

def select (prepared : Prepared) : List PreparedStep → Core.Expr → Core.Expr → Core.Expr
  | [], current, _ => Core.LanguageResult.success (.inRight .unit current)
  | .index index :: rest, current, keys =>
      Core.LanguageResult.bind prepared.optionalLeaf (selectedIndex prepared index current keys)
        (select prepared rest (.var 0) (shift 1 keys))
  | .member dataType index branches _ :: rest, current, keys =>
      .matchData dataType (Core.LanguageResult.resultType prepared.optionalLeaf) current
        (branches.map fun branch => select prepared rest
          (SourceCoreDataExpressions.projectPacked index branch.payloadTypes (.var 0)) (shift 1 keys))

/-- Updater follows the latest structure, including defaults, before replacing
the leaf. A path failure therefore precedes even a constant leaf modifier. -/
def update (prepared : Prepared) : List PreparedStep → Core.Ty → Core.Expr → Core.Expr → Core.Expr → Core.Expr
  | [], _, _, _, replacement => Core.LanguageResult.success replacement
  | .index index :: rest, _, current, keys, replacement =>
      Core.LanguageResult.bind index.layout.type (selectedIndex prepared index current keys)
        (Core.LanguageResult.bind index.layout.type
          (update prepared rest index.layout.valueType (.var 0) (shift 1 keys) (shift 1 replacement))
          (Core.OrderedMapping.insert index.layout index.comparison (shift 2 current)
            (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keys)) (.var 0)))
  | .member dataType index branches fieldType :: rest, _, current, keys, replacement =>
      .matchData dataType (Core.LanguageResult.resultType (.namedData dataType)) current
        (branches.map fun branch =>
          Core.LanguageResult.bind (.namedData dataType)
            (update prepared rest fieldType
              (SourceCoreDataExpressions.projectPacked index branch.payloadTypes (.var 0))
              (shift 1 keys) (shift 1 replacement))
            (Core.LanguageResult.success (.construct branch.constructor
              (replacePacked index branch.payloadTypes (.var 1) (.var 0)))))

def getter (prepared : Prepared) (keyType : Core.Ty) : Core.Expr :=
  .lambda (.product (Core.OptionalCell.cellType prepared.route.rootType) keyType)
    (Core.LanguageResult.resultType prepared.optionalLeaf)
    (match prepared.steps with
      | [] => Core.LanguageResult.success (normalizeRoot prepared (.first (.var 0)))
      | steps => .caseE (normalizeRoot prepared (.first (.var 0)))
          (Core.LanguageResult.failure prepared.optionalLeaf (.word prepared.invalidProjection))
          (select prepared steps (.var 0) (.second (.var 1))))

def setter (prepared : Prepared) (keyType : Core.Ty) : Core.Expr :=
  .lambda (.product (Core.OptionalCell.cellType prepared.route.rootType)
    (.product keyType prepared.route.leafType)) (Core.LanguageResult.resultType prepared.route.rootType)
    (match prepared.steps with
      | [] => Core.LanguageResult.success (.second (.second (.var 0)))
      | steps => .caseE (normalizeRoot prepared (.first (.var 0)))
          (Core.LanguageResult.failure prepared.route.rootType (.word prepared.invalidProjection))
          (update prepared steps prepared.route.rootType (.var 0)
            (.first (.second (.var 1))) (.second (.second (.var 1)))))

/-- What a compound modifier checks after the structural update: nothing, a
zero right-hand side (`Panic(0x12)`), or the exact result of checked
`+ - * / %` (`operator`) on the snapshot and the right-hand side against a
fixed-width integer type's range (`Panic(0x11)`), which for `/ %` comes after
the zero test. -/
inductive Check where
  | total
  | divisor
  | range (type : TypeSystem.FixedInteger) (operator : Syntax.BinaryOp)
  deriving Repr, DecidableEq

/-- A compound modifier: its total Core operation on the old leaf and the
right-hand side, and its check. The check is made by `guard`, after the
structural update, because the source semantics traverses the latest root
before it applies the operation. -/
structure Modifier where
  operation : Core.BinaryOp
  check : Check
  deriving Repr, DecidableEq

/-- A modifier that never panics. -/
def Modifier.total (operation : Core.BinaryOp) : Modifier := ⟨operation, .total⟩

/-- The check of a modifier, after the structural update and before the write,
under the updated root, the modified leaf, the right-hand side and the
snapshot. A zero right-hand side fails with `Panic(0x12)`, for `/= %=` at a
fixed-width integer type too; checked arithmetic outside the type's range fails
with `Panic(0x11)`. Either writes nothing. -/
def guard (outputType : Core.Ty) (operator : Option Modifier) (write : Core.Expr) : Core.Expr :=
  match operator with
  | some ⟨_, .divisor⟩ => .ifE (.binary .wordEq (.var 2) (.word Core.Word.zero))
      (Core.LanguageResult.failure outputType
        (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero))) write
  | some ⟨_, .range type binary⟩ =>
      if SourceCorePrimitive.checkedDivision binary then
        .ifE (.binary .wordEq (.var 2) (.word Core.Word.zero))
          (Core.LanguageResult.failure outputType
            (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero)))
          (.ifE (.caseE (.var 3) (.bool false) (SourceCorePrimitive.checkedOutside type binary 0 3))
            (Core.LanguageResult.failure outputType
              (.word (SourceCorePanics.reason SourceCorePanics.arithmetic))) write)
      else
        .ifE (.caseE (.var 3) (.bool false) (SourceCorePrimitive.checkedOutside type binary 0 3))
          (Core.LanguageResult.failure outputType
            (.word (SourceCorePanics.reason SourceCorePanics.arithmetic))) write
  | _ => write

/-- The range check of `+= -= *=`. -/
theorem guard_range_plain {outputType : Core.Ty} {operation : Core.BinaryOp} {type : TypeSystem.FixedInteger}
    {binary : Syntax.BinaryOp} {write : Core.Expr} (plain : SourceCorePrimitive.checkedDivision binary = false) :
    guard outputType (some ⟨operation, .range type binary⟩) write =
      .ifE (.caseE (.var 3) (.bool false) (SourceCorePrimitive.checkedOutside type binary 0 3))
        (Core.LanguageResult.failure outputType
          (.word (SourceCorePanics.reason SourceCorePanics.arithmetic))) write := by
  simp [guard, plain]

/-- The check of `/= %=`: the zero test, then the range check. -/
theorem guard_range_division {outputType : Core.Ty} {operation : Core.BinaryOp} {type : TypeSystem.FixedInteger}
    {binary : Syntax.BinaryOp} {write : Core.Expr} (division : SourceCorePrimitive.checkedDivision binary = true) :
    guard outputType (some ⟨operation, .range type binary⟩) write =
      .ifE (.binary .wordEq (.var 2) (.word Core.Word.zero))
        (Core.LanguageResult.failure outputType
          (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero)))
        (.ifE (.caseE (.var 3) (.bool false) (SourceCorePrimitive.checkedOutside type binary 0 3))
          (Core.LanguageResult.failure outputType
            (.word (SourceCorePanics.reason SourceCorePanics.arithmetic))) write) := by
  simp [guard, division]

/-- The zero test of checked `/= %=` passes: the right-hand side is a nonzero
word, or the operator does not divide. -/
def DivisorPasses (binary : Syntax.BinaryOp) (right : Core.Value) : Prop :=
  SourceCorePrimitive.checkedDivision binary = true → ∃ word, right = .word word ∧ word ≠ Core.Word.zero

/-- A zero test that came out `true` saw a zero word. -/
theorem zeroTest_true {environment : Core.Environment} {store final : Core.Store}
    {updated changed right : Core.Value}
    (condition : Core.Evaluates (updated :: changed :: right :: environment) store
      (.binary .wordEq (.var 2) (.word Core.Word.zero)) (.bool true) final) :
    right = .word Core.Word.zero ∧ final = store := by
  cases condition with
  | binary left zero applied =>
    cases left with
    | var found =>
      cases zero
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      cases right <;> simp [Core.BinaryOp.apply] at applied
      rename_i word
      have same : word = Core.Word.zero := by simpa using applied
      subst same
      exact ⟨rfl, rfl⟩

/-- A zero test that came out `false` saw a nonzero word. -/
theorem zeroTest_false {environment : Core.Environment} {store final : Core.Store}
    {updated changed right : Core.Value}
    (condition : Core.Evaluates (updated :: changed :: right :: environment) store
      (.binary .wordEq (.var 2) (.word Core.Word.zero)) (.bool false) final) :
    (∃ word, right = .word word ∧ word ≠ Core.Word.zero) ∧ final = store := by
  cases condition with
  | binary left zero applied =>
    cases left with
    | var found =>
      cases zero
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      cases right <;> simp [Core.BinaryOp.apply] at applied
      rename_i word
      have different : word ≠ Core.Word.zero := by simpa using applied
      exact ⟨⟨word, rfl, different⟩, rfl⟩

/-- The right-hand sides that pass the check of a modifier without a range
check (`guard_inRange` covers checked arithmetic). -/
inductive Passes : Option Modifier → Core.Value → Prop where
  | total {operator : Option Modifier} {right : Core.Value}
      (total : ∀ modifier, operator = some modifier → modifier.check = .total) : Passes operator right
  | nonzero {operation : Core.BinaryOp} {right : Core.Word}
      (nonzero : right ≠ Core.Word.zero) : Passes (some ⟨operation, .divisor⟩) (.word right)

/-- A range check is not among the passing modifiers of `Passes`. -/
theorem Passes.not_range {operation : Core.BinaryOp} {type : TypeSystem.FixedInteger}
    {binary : Syntax.BinaryOp} {right : Core.Value}
    (passes : Passes (some ⟨operation, .range type binary⟩) right) : False := by
  cases passes with
  | total total => cases total _ rfl

theorem guard_passes {environment : Core.Environment} {before after : Core.Store}
    {outputType : Core.Ty} {operator : Option Modifier} {write : Core.Expr} {result : Core.Value}
    {updated changed right : Core.Value} (passes : Passes operator right)
    (written : Core.Evaluates (updated :: changed :: right :: environment) before write result after) :
    Core.Evaluates (updated :: changed :: right :: environment) before (guard outputType operator write)
      result after := by
  cases passes with
  | total total =>
    match operator, total with
    | none, _ => exact written
    | some ⟨_, .total⟩, _ => exact written
    | some ⟨_, .divisor⟩, total => cases total _ rfl
    | some ⟨_, .range _ _⟩, total => cases total _ rfl
  | nonzero nonzero =>
    exact .ifFalse (.binary (.var rfl) .word (by simp [Core.BinaryOp.apply, nonzero])) written

/-- Checked arithmetic in the type's range, by a nonzero divisor for `/ %`,
passes the check. -/
theorem guard_inRange {environment : Core.Environment} {before after : Core.Store}
    {outputType : Core.Ty} {operation : Core.BinaryOp} {type : TypeSystem.FixedInteger}
    {binary : Syntax.BinaryOp} {write : Core.Expr} {result : Core.Value} {updated changed : Core.Value}
    {leftType : Core.Ty} {left right : Core.Word}
    (divisor : DivisorPasses binary (.word right))
    (inRange : SourceCorePrimitive.checkedInRange type binary left right = true)
    (written : Core.Evaluates (updated :: changed :: .word right :: .inRight leftType (.word left) :: environment)
      before write result after) :
    Core.Evaluates (updated :: changed :: .word right :: .inRight leftType (.word left) :: environment) before
      (guard outputType (some ⟨operation, .range type binary⟩) write) result after := by
  have outside := SourceCorePrimitive.checkedOutside_evaluates
    (environment := .word left :: updated :: changed :: .word right :: .inRight leftType (.word left) ::
      environment)
    (store := before) (left := 0) (right := 3) type binary rfl rfl
  rw [inRange] at outside
  cases division : SourceCorePrimitive.checkedDivision binary
  · rw [guard_range_plain division]
    exact .ifFalse (.caseRight (.var rfl) outside) written
  · rw [guard_range_division division]
    obtain ⟨word, same, nonzero⟩ := divisor division
    cases same
    exact .ifFalse (.binary (.var rfl) .word (by simp [Core.BinaryOp.apply, nonzero]))
      (.ifFalse (.caseRight (.var rfl) outside) written)

theorem guard_panic {environment : Core.Environment} {store : Core.Store}
    {outputType : Core.Ty} {operation : Core.BinaryOp} {write : Core.Expr} {updated changed : Core.Value} :
    Core.Evaluates (updated :: changed :: .word Core.Word.zero :: environment) store
      (guard outputType (some ⟨operation, .divisor⟩) write)
      (.inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero))) store :=
  .ifTrue (.binary (.var rfl) .word (by simp [Core.BinaryOp.apply])) (.inLeft .word)

/-- Checked arithmetic outside the type's range, by a nonzero divisor for
`/ %`, fails with `Panic(0x11)` and writes nothing. -/
theorem guard_overflow {environment : Core.Environment} {store : Core.Store}
    {outputType : Core.Ty} {operation : Core.BinaryOp} {type : TypeSystem.FixedInteger}
    {binary : Syntax.BinaryOp} {write : Core.Expr} {updated changed : Core.Value} {leftType : Core.Ty}
    {left right : Core.Word}
    (divisor : DivisorPasses binary (.word right))
    (outside : SourceCorePrimitive.checkedInRange type binary left right = false) :
    Core.Evaluates (updated :: changed :: .word right :: .inRight leftType (.word left) :: environment) store
      (guard outputType (some ⟨operation, .range type binary⟩) write)
      (.inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.arithmetic))) store := by
  have test := SourceCorePrimitive.checkedOutside_evaluates
    (environment := .word left :: updated :: changed :: .word right :: .inRight leftType (.word left) ::
      environment)
    (store := store) (left := 0) (right := 3) type binary rfl rfl
  rw [outside] at test
  cases division : SourceCorePrimitive.checkedDivision binary
  · rw [guard_range_plain division]
    exact .ifTrue (.caseRight (.var rfl) test) (.inLeft .word)
  · rw [guard_range_division division]
    obtain ⟨word, same, nonzero⟩ := divisor division
    cases same
    exact .ifFalse (.binary (.var rfl) .word (by simp [Core.BinaryOp.apply, nonzero]))
      (.ifTrue (.caseRight (.var rfl) test) (.inLeft .word))

/-- Checked `/= %=` fail with `Panic(0x12)` on a zero right-hand side and write
nothing. -/
theorem guard_rangeZero {environment : Core.Environment} {store : Core.Store}
    {outputType : Core.Ty} {operation : Core.BinaryOp} {type : TypeSystem.FixedInteger}
    {binary : Syntax.BinaryOp} {write : Core.Expr} {updated changed : Core.Value}
    (division : SourceCorePrimitive.checkedDivision binary = true) :
    Core.Evaluates (updated :: changed :: .word Core.Word.zero :: environment) store
      (guard outputType (some ⟨operation, .range type binary⟩) write)
      (.inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero))) store := by
  rw [guard_range_division division]
  exact .ifTrue (.binary (.var rfl) .word (by simp [Core.BinaryOp.apply])) (.inLeft .word)

/-- The range check passes on the snapshot that follows the guard's three
binders: the snapshot is absent, or the exact result lies in the type's range. -/
def RangePasses (type : TypeSystem.FixedInteger) (binary : Syntax.BinaryOp) :
    Core.Environment → Core.Value → Prop
  | [], _ => False
  | snapshot :: _, right => (∃ rightType payload, snapshot = .inLeft rightType payload) ∨
      ∃ leftType left rightWord, snapshot = .inRight leftType (.word left) ∧ right = .word rightWord ∧
        SourceCorePrimitive.checkedInRange type binary left rightWord = true

/-- A completed range test leaves the store, and is `false` only when the
range check passes. -/
theorem range_condition_inv {environment : Core.Environment} {store final : Core.Store}
    {value : Core.Value} {type : TypeSystem.FixedInteger} {binary : Syntax.BinaryOp}
    {updated changed right : Core.Value}
    (condition : Core.Evaluates (updated :: changed :: right :: environment) store
      (.caseE (.var 3) (.bool false) (SourceCorePrimitive.checkedOutside type binary 0 3)) value final) :
    final = store ∧ (value = .bool false → RangePasses type binary environment right) ∧
      (value = .bool true → ∃ leftType left rightWord, environment.head? = some (.inRight leftType (.word left)) ∧
        right = .word rightWord ∧ SourceCorePrimitive.checkedInRange type binary left rightWord = false) := by
  cases environment with
  | nil =>
    exfalso
    cases condition with
    | caseLeft scrutinee _ | caseRight scrutinee _ =>
      cases scrutinee with
      | var found => simp at found
  | cons snapshot rest =>
    cases condition with
    | caseLeft scrutinee branch =>
      cases scrutinee with
      | var found =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
        cases branch
        exact ⟨rfl, fun _ => .inl ⟨_, _, found⟩, fun impossible => by cases impossible⟩
    | caseRight scrutinee branch =>
      cases scrutinee with
      | var found =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
        obtain ⟨a, b, foundA, foundB, sameValue, sameStore⟩ := SourceCorePrimitive.checkedOutside_inv branch
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at foundA foundB
        subst foundA sameValue
        refine ⟨sameStore, fun passed => .inr ⟨_, a, b, found, foundB, ?_⟩,
          fun failed => ⟨_, a, b, by rw [found]; rfl, foundB, ?_⟩⟩
        · simpa using passed
        · simpa using failed

/-- A completed check of checked compound arithmetic either passed and wrote,
by a nonzero divisor for `/ %` and on an absent snapshot or an exact result in
the type's range, or failed without changing the store: with `Panic(0x11)`
outside the range, or with `Panic(0x12)` on a zero divisor of `/ %`. -/
theorem guard_range_inv {environment : Core.Environment} {before after : Core.Store}
    {outputType : Core.Ty} {operation : Core.BinaryOp} {type : TypeSystem.FixedInteger}
    {binary : Syntax.BinaryOp} {write : Core.Expr} {result : Core.Value}
    {updated changed right : Core.Value}
    (evaluated : Core.Evaluates (updated :: changed :: right :: environment) before
      (guard outputType (some ⟨operation, .range type binary⟩) write) result after) :
    (DivisorPasses binary right ∧ RangePasses type binary environment right ∧
      Core.Evaluates (updated :: changed :: right :: environment) before write result after) ∨
    ((∃ leftType left rightWord, environment.head? = some (.inRight leftType (.word left)) ∧
        right = .word rightWord ∧ SourceCorePrimitive.checkedInRange type binary left rightWord = false) ∧
      DivisorPasses binary right ∧
      result = .inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.arithmetic)) ∧
      after = before) ∨
    (SourceCorePrimitive.checkedDivision binary = true ∧ right = .word Core.Word.zero ∧
      result = .inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero)) ∧
      after = before) := by
  have range : DivisorPasses binary right →
      Core.Evaluates (updated :: changed :: right :: environment) before
        (.ifE (.caseE (.var 3) (.bool false) (SourceCorePrimitive.checkedOutside type binary 0 3))
          (Core.LanguageResult.failure outputType
            (.word (SourceCorePanics.reason SourceCorePanics.arithmetic))) write) result after →
      (DivisorPasses binary right ∧ RangePasses type binary environment right ∧
        Core.Evaluates (updated :: changed :: right :: environment) before write result after) ∨
      ((∃ leftType left rightWord, environment.head? = some (.inRight leftType (.word left)) ∧
          right = .word rightWord ∧ SourceCorePrimitive.checkedInRange type binary left rightWord = false) ∧
        DivisorPasses binary right ∧
        result = .inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.arithmetic)) ∧
        after = before) := by
    intro divisor evaluated
    cases evaluated with
    | ifTrue condition failed =>
      obtain ⟨sameStore, _, outside⟩ := range_condition_inv condition
      subst sameStore
      cases failed with
      | inLeft reason => cases reason; exact .inr ⟨outside rfl, divisor, rfl, rfl⟩
    | ifFalse condition written =>
      obtain ⟨sameStore, passes, _⟩ := range_condition_inv condition
      subst sameStore
      exact .inl ⟨divisor, passes rfl, written⟩
  cases division : SourceCorePrimitive.checkedDivision binary
  · rw [guard_range_plain division] at evaluated
    rcases range (fun impossible => by rw [division] at impossible; cases impossible) evaluated with
      passed | failed
    · exact .inl passed
    · exact .inr (.inl failed)
  · rw [guard_range_division division] at evaluated
    cases evaluated with
    | ifTrue condition failed =>
      obtain ⟨zero, sameStore⟩ := zeroTest_true condition
      subst sameStore
      cases failed with
      | inLeft reason => cases reason; exact .inr (.inr ⟨rfl, zero, rfl, rfl⟩)
    | ifFalse condition rest =>
      obtain ⟨nonzero, sameStore⟩ := zeroTest_false condition
      subst sameStore
      rcases range (fun _ => nonzero) rest with passed | failed
      · exact .inl passed
      · exact .inr (.inl failed)

theorem guard_rangePasses {environment : Core.Environment} {before after : Core.Store}
    {outputType : Core.Ty} {operation : Core.BinaryOp} {type : TypeSystem.FixedInteger}
    {binary : Syntax.BinaryOp} {write : Core.Expr} {result : Core.Value} {updated changed right : Core.Value}
    (divisor : DivisorPasses binary right)
    (passes : RangePasses type binary environment right)
    (written : Core.Evaluates (updated :: changed :: right :: environment) before write result after) :
    Core.Evaluates (updated :: changed :: right :: environment) before
      (guard outputType (some ⟨operation, .range type binary⟩) write) result after := by
  cases environment with
  | nil => exact passes.elim
  | cons snapshot rest =>
    rcases passes with ⟨rightType, payload, rfl⟩ | ⟨leftType, left, rightWord, rfl, rfl, inRange⟩
    · cases division : SourceCorePrimitive.checkedDivision binary
      · rw [guard_range_plain division]
        exact .ifFalse (.caseLeft (.var rfl) .bool) written
      · rw [guard_range_division division]
        obtain ⟨word, rfl, nonzero⟩ := divisor division
        exact .ifFalse (.binary (.var rfl) .word (by simp [Core.BinaryOp.apply, nonzero]))
          (.ifFalse (.caseLeft (.var rfl) .bool) written)
    · exact guard_inRange divisor inRange written

/-- A completed check without a range check either passed and wrote, or
panicked on a zero right-hand side without changing the store. A range check
is the last case, and `guard_range_inv` inverts it. -/
theorem guard_inv {environment : Core.Environment} {before after : Core.Store}
    {outputType : Core.Ty} {operator : Option Modifier} {write : Core.Expr} {result : Core.Value}
    {updated changed right : Core.Value}
    (evaluated : Core.Evaluates (updated :: changed :: right :: environment) before
      (guard outputType operator write) result after) :
    (Passes operator right ∧
      Core.Evaluates (updated :: changed :: right :: environment) before write result after) ∨
    (∃ operation, operator = some ⟨operation, .divisor⟩ ∧ right = .word Core.Word.zero ∧
      result = .inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero)) ∧
      after = before) ∨
    (∃ operation type binary, operator = some ⟨operation, .range type binary⟩ ∧
      ((DivisorPasses binary right ∧ RangePasses type binary environment right ∧
          Core.Evaluates (updated :: changed :: right :: environment) before write result after) ∨
        ((∃ leftType left rightWord, environment.head? = some (.inRight leftType (.word left)) ∧
            right = .word rightWord ∧ SourceCorePrimitive.checkedInRange type binary left rightWord = false) ∧
          DivisorPasses binary right ∧
          result = .inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.arithmetic)) ∧
          after = before) ∨
        (SourceCorePrimitive.checkedDivision binary = true ∧ right = .word Core.Word.zero ∧
          result = .inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero)) ∧
          after = before))) := by
  match operator, evaluated with
  | none, evaluated => exact .inl ⟨.total (fun _ none => by cases none), evaluated⟩
  | some ⟨operation, .total⟩, evaluated =>
    exact .inl ⟨.total (fun _ same => by cases same; rfl), evaluated⟩
  | some ⟨operation, .range type binary⟩, evaluated =>
    exact .inr (.inr ⟨operation, type, binary, rfl, guard_range_inv evaluated⟩)
  | some ⟨operation, .divisor⟩, evaluated =>
    cases evaluated with
    | ifTrue condition failed =>
      cases condition with
      | binary left zero applied =>
        cases left with
        | var found =>
          cases zero
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
          subst found
          cases right <;> simp [Core.BinaryOp.apply] at applied
          rename_i word
          have same : word = Core.Word.zero := by simpa using applied
          subst same
          cases failed with
          | inLeft reason => cases reason; exact .inr (.inl ⟨operation, rfl, rfl, rfl, rfl⟩)
    | ifFalse condition written =>
      cases condition with
      | binary left zero applied =>
        cases left with
        | var found =>
          cases zero
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
          subst found
          cases right <;> simp [Core.BinaryOp.apply] at applied
          rename_i word
          have different : word ≠ Core.Word.zero := by simpa using applied
          exact .inl ⟨.nonzero different, written⟩

/-- With a Unit right-hand side, as in-place `~` has, no check fails: the
guard is its write. -/
theorem guard_unit_inv {environment : Core.Environment} {before after : Core.Store}
    {outputType : Core.Ty} {operator : Option Modifier} {write : Core.Expr} {result : Core.Value}
    {updated changed : Core.Value}
    (evaluated : Core.Evaluates (updated :: changed :: .unit :: environment) before
      (guard outputType operator write) result after) :
    Core.Evaluates (updated :: changed :: .unit :: environment) before write result after := by
  rcases guard_inv evaluated with ⟨_, written⟩ | ⟨_, _, impossible, _, _⟩ |
      ⟨_, _, _, _, ⟨_, _, written⟩ | ⟨⟨_, _, _, _, impossible, _⟩, _⟩ | ⟨_, impossible, _⟩⟩
  · exact written
  · cases impossible
  · exact written
  · cases impossible
  · cases impossible

def binaryOperator (integer : Bool) : Syntax.ValueAssignOp → Option Modifier
  | .equal => none
  | .add => some (.total (if integer then .integerAdd else .wordAdd))
  | .subtract => some (.total (if integer then .integerSub else .wordSub))
  | .multiply => some (.total (if integer then .integerMul else .wordMul))
  | .divide => some (.total (if integer then .integerDiv else .wordDiv))
  | .modulo => some (.total (if integer then .integerMod else .wordMod))
  | .bitAnd => some (.total (if integer then .integerAnd else .wordAnd))
  | .bitOr => some (.total (if integer then .integerOr else .wordOr))
  | .bitXor => some (.total (if integer then .integerXor else .wordXor))
  -- Shifts and unchecked arithmetic take Words only; `lower` rejects them at
  -- Integer leaves.
  | .shiftLeft => some (.total .wordShl)
  | .shiftRight => some (.total .wordShr)
  | .uncheckedAdd => some (.total .wordAdd)
  | .uncheckedSubtract => some (.total .wordSub)
  | .uncheckedMultiply => some (.total .wordMul)
  | .uncheckedDivide => some ⟨.wordDiv, .divisor⟩
  | .uncheckedModulo => some ⟨.wordMod, .divisor⟩

/-- The compound assignments with the type's own meaning at a target type:
checked `+= -= *= /= %=` and their unchecked forms at a fixed-width integer
type, with the type and the binary operator. The match tests the operator
first, so every other operator reduces to `none` at any target. -/
def checkedCompound (target : TypeSystem.Ty) (operator : Syntax.ValueAssignOp) :
    Option (TypeSystem.FixedInteger × Syntax.BinaryOp) :=
  match operator, target with
  | .add, .constructor (.builtin (.fixed type)) => some (type, .add)
  | .subtract, .constructor (.builtin (.fixed type)) => some (type, .subtract)
  | .multiply, .constructor (.builtin (.fixed type)) => some (type, .multiply)
  | .divide, .constructor (.builtin (.fixed type)) => some (type, .divide)
  | .modulo, .constructor (.builtin (.fixed type)) => some (type, .modulo)
  | .uncheckedAdd, .constructor (.builtin (.fixed type)) => some (type, .uncheckedAdd)
  | .uncheckedSubtract, .constructor (.builtin (.fixed type)) => some (type, .uncheckedSubtract)
  | .uncheckedMultiply, .constructor (.builtin (.fixed type)) => some (type, .uncheckedMultiply)
  | .uncheckedDivide, .constructor (.builtin (.fixed type)) => some (type, .uncheckedDivide)
  | .uncheckedModulo, .constructor (.builtin (.fixed type)) => some (type, .uncheckedModulo)
  | _, _ => none

/-- Word's operation for checked `+ - * / %` at a fixed-width integer type: in
the type's range, and by a nonzero divisor, it is the exact result's word.
`/ %` are signed on the signed types. For unchecked `+ - * / %` it is the same
operation, whose low `N` bits are those of the exact result (`wrapLeaf`). -/
def checkedWordOperation (type : TypeSystem.FixedInteger) : Syntax.BinaryOp → Core.BinaryOp
  | .add | .uncheckedAdd => .wordAdd
  | .subtract | .uncheckedSubtract => .wordSub
  | .divide | .uncheckedDivide => if type.signed then .wordSdiv else .wordDiv
  | .modulo | .uncheckedModulo => if type.signed then .wordSmod else .wordMod
  | _ => .wordMul

/-- The check of a compound assignment with the type's own meaning: checked
arithmetic tests the exact result against the type's range (`/ %` a zero
divisor first), unchecked `/= %=` test a zero divisor, and unchecked
`+= -= *=` test nothing. -/
def fixedCheck (type : TypeSystem.FixedInteger) : Syntax.BinaryOp → Check
  | .uncheckedAdd | .uncheckedSubtract | .uncheckedMultiply => .total
  | .uncheckedDivide | .uncheckedModulo => .divisor
  | binary => .range type binary

/-- The modifier of a value assignment at its target's static type: checked
`+= -= *= /= %=` at a fixed-width integer type compute Word's operation, and
`guard` tests a zero divisor of `/= %=` and checks the exact result against the
type's range; every other operator takes `binaryOperator`'s modifier. -/
def assignmentModifier (target : TypeSystem.Ty) (integer : Bool) (operator : Syntax.ValueAssignOp) :
    Option Modifier :=
  match checkedCompound target operator with
  | some (type, binary) => some ⟨checkedWordOperation type binary, fixedCheck type binary⟩
  | none => binaryOperator integer operator

/-- Outside the checked compound assignments the modifier is `binaryOperator`'s. -/
theorem assignmentModifier_plain {target : TypeSystem.Ty} {integer : Bool} {operator : Syntax.ValueAssignOp}
    (plain : checkedCompound target operator = none) :
    assignmentModifier target integer operator = binaryOperator integer operator := by
  simp [assignmentModifier, plain]

/-- A Word target has no checked compound assignment. -/
theorem checkedCompound_word (operator : Syntax.ValueAssignOp) : checkedCompound .word operator = none := by
  cases operator <;> rfl

/-- Plain assignment is never checked. -/
theorem checkedCompound_equal (target : TypeSystem.Ty) : checkedCompound target .equal = none := by
  unfold checkedCompound
  split <;> simp_all

/-- `binaryOperator` never selects the range check. -/
theorem binaryOperator_not_range {integer : Bool} {operator : Syntax.ValueAssignOp} {operation : Core.BinaryOp}
    {type : TypeSystem.FixedInteger} {binary : Syntax.BinaryOp} :
    binaryOperator integer operator ≠ some ⟨operation, .range type binary⟩ := by
  cases operator <;> simp [binaryOperator, Modifier.total]

/-- The modifier the place lowering emits: in-place `~` keeps
`binaryOperator`'s, and a value assignment takes `assignmentModifier`'s. -/
def placeModifier (target : TypeSystem.Ty) (integer : Bool) (operator : Syntax.ValueAssignOp) (bitNot : Bool) :
    Option Modifier :=
  if bitNot then binaryOperator integer operator else assignmentModifier target integer operator

/-- A compound result wrapped to a fixed-width integer type's width, for
unchecked arithmetic at a fixed-width target: the low `N` bits of Word's
operation are those of the exact result, so they (`wordAnd` with the type's
mask) on an unsigned type, or their sign extension (`wordSignExtend`) on a
signed one, are the wrapped result's word. Without a type it is the result. -/
@[simp] def wrapLeaf : Option TypeSystem.FixedInteger → Core.Expr → Core.Expr
  | none, result => result
  | some type, result =>
      if type.signed then
        .binary .wordSignExtend (.word (Core.Word.ofNatModulo (type.width.bits / 8 - 1))) result
      else .binary .wordAnd result (.word (Core.Word.ofNatModulo (2 ^ type.width.bits - 1)))

/-- The type a value assignment's result is wrapped to: the target's, for
unchecked `+= -= *= /= %=` at a fixed-width integer type; none for every other
assignment and for in-place `~`. -/
def placeWrap (target : TypeSystem.Ty) (operator : Syntax.ValueAssignOp) (bitNot : Bool) :
    Option TypeSystem.FixedInteger :=
  if bitNot then none
  else match checkedCompound target operator with
    | some (type, .uncheckedAdd) | some (type, .uncheckedSubtract) | some (type, .uncheckedMultiply)
    | some (type, .uncheckedDivide) | some (type, .uncheckedModulo) => some type
    | _ => none

/-- Without the type's own compound meaning there is nothing to wrap. -/
theorem placeWrap_plain {target : TypeSystem.Ty} {operator : Syntax.ValueAssignOp} {bitNot : Bool}
    (plain : checkedCompound target operator = none) : placeWrap target operator bitNot = none := by
  simp [placeWrap, plain]

def modified (type : Core.Ty) (operator : Option Modifier) (bitNot : Bool)
    (snapshot rhs : Core.Expr) (invalid : Core.Word) (wrap : Option TypeSystem.FixedInteger := none) :
    Core.Expr :=
  if bitNot then .caseE snapshot (Core.LanguageResult.failure type (.word invalid))
    (Core.LanguageResult.success (.unary (if type = .integer then .integerNot else .wordNot) (.var 0)))
  else match operator with
    | none => Core.LanguageResult.success rhs
    | some modifier => .caseE snapshot (Core.LanguageResult.failure type (.word invalid))
        (Core.LanguageResult.success (wrapLeaf wrap (.binary modifier.operation (.var 0) (shift 1 rhs))))

/-- Internal binders: reference, keys, snapshot, RHS, modified leaf, updated
root, store result. Source expressions are shifted only at their insertion. -/
def execute (prepared : Prepared) (reference : Core.Expr) (keys : SourceCoreBasic.LoweredExpr)
    (rhs next : Core.Expr) (outputType : Core.Ty) (operator : Option Modifier)
    (bitNot : Bool) (invalidOperand : Core.Word) (wrap : Option TypeSystem.FixedInteger := none) :
    Core.Expr :=
  .letE reference
    (Core.LanguageResult.bind outputType (shift 1 keys.expression)
      (Core.LanguageResult.bind outputType
        (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
        (Core.LanguageResult.bind outputType (shift 3 rhs)
          (Core.LanguageResult.bind outputType
            (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand wrap)
            (Core.LanguageResult.bind outputType
              (.apply (setter prepared keys.type)
                (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
              (guard outputType operator
                (.letE (.storeCell (.var 5) (.inRight .unit (.var 0))) (shift 7 next))))))))

def lower (checked : Checked) (signatures : ProgramSignatures) (expression : ExpressionLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : Option ExpressionId)
    (outputType : Core.Ty) (next : Core.Expr) (reasonAt : ExpressionId → Core.Word)
    (invalidProjection invalidOperand : Core.Word) (missing : TypeSystem.Ty → Core.Word) : Except Error Core.Expr := do
  let route ← describe checked signatures source site assignment
  let (index, storedType) ← match SourceCoreLocalCell.lookup? scope assignment.target.root with
    | some found => pure found
    | none => throw (.missingBinding assignment.target.root)
  SourceCoreBasic.ensureType site route.rootType storedType
  let prepared ← prepare checked fuel route invalidProjection missing
  let keys ← prepared.keys.mapM fun (id, expected) => do
    let key ← expression fuel source scope id reasonAt
    SourceCoreBasic.ensureType (.occurrence id.occurrence) expected key.type
    pure key
  let bitNot := rhs.isNone
  if operator ≠ .equal || bitNot then
    unless route.leafType = .word || (route.leafType = .integer && !operator.wordOnly) do
      throw (.unsupportedAssignmentOperator operator)
  let rhs ← match rhs with
    | none => pure (Core.LanguageResult.success .unit)
    | some id => do
        let value ← expression fuel source scope id reasonAt
        SourceCoreBasic.ensureType site route.leafType value.type
        pure value.expression
  pure (execute prepared (.var index) (SourceCoreCalls.packArguments keys) rhs next outputType
    (placeModifier assignment.target.type (route.leafType = .integer) operator bitNot) bitNot invalidOperand
    (placeWrap assignment.target.type operator bitNot))

end Solcore.Frontend.SourceCoreDataPlaces
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreDataPlaceFaultSites
/-! Exact assignment-site diagnostics for absent projected roots and missing
mapping defaults. Header items share their owning for statement's span. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDataPlaceFaultSites

open SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

structure Site where
  owner : Key
  location : SourceCoreElaboration.ErrorSite
  binder : Resolved.LocalId
  missingType : Option TypeSystem.Ty
  reason : Core.Word
  diagnostic : SourceCoreFaultSites.Diagnostic
  deriving Repr, DecidableEq

structure Program where
  base : SourceCoreProgramFaultSites.Program
  expressions : SourceCoreDataFaultSites.Program
  places : List Site
  rootTable : SourceCoreFaultSites.Table
  deriving Repr

inductive Error where
  | base (error : SourceCoreDataFaultSites.Error)
  | lowering (error : SourceCoreBasic.Error)
  | reasonSpaceExhausted
  deriving Repr, DecidableEq

private def add (start : Nat) (owner : Key) (location : SourceCoreElaboration.ErrorSite)
    (span : Syntax.SourceSpan) (binder : Resolved.LocalId) (missingType : Option TypeSystem.Ty)
    (sites : List Site) : Except Error (List Site) := do
  if sites.any (fun site => decide (site.owner = owner ∧ site.location = location ∧
      site.binder = binder ∧ site.missingType = missingType)) then return sites
  let reason ← match Core.Word.ofNat? (start + sites.length) with
    | some reason => pure reason
    | none => throw .reasonSpaceExhausted
  let diagnostic : SourceCoreFaultSites.Diagnostic := {
    error := match missingType with
      | none => .invalidPlaceProjection
      | some type => .typeMismatch type none
    site := location, span := some span
  }
  pure (sites ++ [⟨owner, location, binder, missingType, reason, diagnostic⟩])

private def targets (node : StatementNode) : List AssignmentResolution :=
  match node.form with
  | .assignValue assignment _ _ | .assignBitNot assignment => [assignment]
  | .forLoop initial _ post _ => (initial ++ post).filterMap fun
      | .assignValue assignment _ _ | .assignBitNot assignment => some assignment
      | _ => none
  | _ => []

def prepare (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (plan : Plan) (root : Key) : Except Error Program := do
  let expressions ← (SourceCoreDataFaultSites.prepare plan root).mapError Error.base
  let used := expressions.rootTable.reads.map (·.reason.val) ++
    expressions.rootTable.additional.map (·.1.val) ++ [expressions.rootTable.escapedReason.val]
  let start := used.foldl max 0 + 1
  let mut places := []
  for specialized in plan.specializations do
    let source := specialized.function.typedBody
    for node in source.nodes do
      match node with
      | .statement node =>
          let site := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
          for assignment in targets node do
            let route ← (SourceCoreDataPlaces.describe checked signatures source site assignment).mapError Error.lowering
            unless route.steps.isEmpty do
              places ← add start specialized.key site node.span assignment.target.root none places
            for step in route.steps do
              match step with
              | .index _ _ valueType =>
                  places ← add start specialized.key site node.span assignment.target.root (some valueType) places
              | _ => pure ()
      | _ => pure ()
  let rootTable := { expressions.rootTable with
    additional := expressions.rootTable.additional ++ places.map (fun site => (site.reason, site.diagnostic)) }
  pure ⟨expressions.base, expressions, places, rootTable⟩

def Program.reasonAt (program : Program) (owner : Key) (id : ExpressionId) : Core.Word :=
  program.expressions.reasonAt owner id

def Program.placeReason (program : Program) (owner : Key) (site : SourceCoreElaboration.ErrorSite)
    (binder : Resolved.LocalId) (missingType : Option TypeSystem.Ty) : Core.Word :=
  match program.places.find? (fun candidate => decide (candidate.owner = owner ∧ candidate.location = site ∧
      candidate.binder = binder ∧ candidate.missingType = missingType)) with
  | some candidate => candidate.reason
  | none => Core.Word.zero

end Solcore.Frontend.SourceCoreDataPlaceFaultSites
end
