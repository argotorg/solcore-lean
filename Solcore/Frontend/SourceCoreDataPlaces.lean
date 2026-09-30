import Solcore.Frontend.SourceCoreGeneralTypes
import Solcore.Frontend.SourceCoreAssignments

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

private def memberStep (checked : Checked) (signatures : ProgramSignatures)
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

private def routeSteps (checked : Checked) (signatures : ProgramSignatures)
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

def binaryOperator (integer : Bool) : Syntax.ValueAssignOp → Option Core.BinaryOp
  | .equal => none
  | .add => some (if integer then .integerAdd else .wordAdd)
  | .subtract => some (if integer then .integerSub else .wordSub)
  | .multiply => some (if integer then .integerMul else .wordMul)
  | .divide => some (if integer then .integerDiv else .wordDiv)
  | .modulo => some (if integer then .integerMod else .wordMod)
  | .bitAnd => some (if integer then .integerAnd else .wordAnd)
  | .bitOr => some (if integer then .integerOr else .wordOr)
  | .bitXor => some (if integer then .integerXor else .wordXor)

def modified (type : Core.Ty) (operator : Option Core.BinaryOp) (bitNot : Bool)
    (snapshot rhs : Core.Expr) (invalid : Core.Word) : Core.Expr :=
  if bitNot then .caseE snapshot (Core.LanguageResult.failure type (.word invalid))
    (Core.LanguageResult.success (.unary (if type = .integer then .integerNot else .wordNot) (.var 0)))
  else match operator with
    | none => Core.LanguageResult.success rhs
    | some operator => .caseE snapshot (Core.LanguageResult.failure type (.word invalid))
        (Core.LanguageResult.success (.binary operator (.var 0) (shift 1 rhs)))

/-- Internal binders: reference, keys, snapshot, RHS, modified leaf, updated
root, store result. Source expressions are shifted only at their insertion. -/
def execute (prepared : Prepared) (reference : Core.Expr) (keys : SourceCoreBasic.LoweredExpr)
    (rhs next : Core.Expr) (outputType : Core.Ty) (operator : Option Core.BinaryOp)
    (bitNot : Bool) (invalidOperand : Core.Word) : Core.Expr :=
  .letE reference
    (Core.LanguageResult.bind outputType (shift 1 keys.expression)
      (Core.LanguageResult.bind outputType
        (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
        (Core.LanguageResult.bind outputType (shift 3 rhs)
          (Core.LanguageResult.bind outputType
            (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand)
            (Core.LanguageResult.bind outputType
              (.apply (setter prepared keys.type)
                (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
              (.letE (.storeCell (.var 5) (.inRight .unit (.var 0))) (shift 7 next)))))))

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
    unless route.leafType = .word || route.leafType = .integer do
      throw (.unsupportedAssignmentOperator operator)
  let rhs ← match rhs with
    | none => pure (Core.LanguageResult.success .unit)
    | some id => do
        let value ← expression fuel source scope id reasonAt
        SourceCoreBasic.ensureType site route.leafType value.type
        pure value.expression
  pure (execute prepared (.var index) (SourceCoreCalls.packArguments keys) rhs next outputType
    (binaryOperator (route.leafType = .integer) operator) bitNot invalidOperand)

end Solcore.Frontend.SourceCoreDataPlaces
