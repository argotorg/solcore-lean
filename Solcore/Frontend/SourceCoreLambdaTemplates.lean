import Solcore.Frontend.SourceCoreCompatibleMarkedFunctions
import Solcore.Frontend.SourceCoreCallableViews

/-! Source-lambda manifests and exact native templates. The ordinary Core
manifest records owned callable and binder keys, actual payload types, and
actual lexical reference variables. Later weakening acts on those variables.

Structural scanning is not source emission history. `Compiled` additionally
retains the actual compiler equation; an enclosing artifact must retain that
receipt and its chosen source representation. Authentication checks exact code,
descriptor and typed captures, while source locations require the allocation
ledger. Dynamic ancestry of occurrence-specific instantiated views remains a
separate transport boundary. Unused principal bundles emit no native lambda.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreLambdaTemplates
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Scope := SourceCoreFunctions.Scope
abbrev Origin := SourceCoreStageCodebook.Origin
abbrev Context := SourceCoreAllocationCodebook.IndexedContext
abbrev Active := TypeSystem.Substitution

inductive Error where
  | contexts (error : SourceCoreAllocationContexts.Error)
  | metadata (error : SourceCoreAllocationCodebook.Error)
  | contractsUnavailable
  | missingOrigin (origin : Origin)
  | missingContext (owner : Key) (active : Active)
  | invalidLambda (id : ExpressionId)
  | sourceViewMismatch (owner : Key)
  | projection (error : SourceCoreCompatibleCatalog.Error)
  | scopeMismatch (id : Resolved.LocalId)
  | duplicateScope
  | invalidCaptureType (type : Core.Ty)
  | malformedManifest (detail : String)
  | descriptorMismatch (expected actual : Word)
  | unknownDescriptor (id : Word)
  | callableTypeMismatch
  | missingCapture (index : Nat)
  | captureMismatch (index : Nat)
  | captureOutsideWorld (location : Nat)
  | closureMismatch
  | foreignDefinitions
  | globalSlotMismatch (index : Nat)
  | globalEnvironmentMismatch
  | traversalExhausted
  | compilation (error : SourceCoreCompatibleMarkedFunctions.Error)
  deriving Repr

structure Lambda where private mk ::
  descriptor : Word
  owner : Key
  id : ExpressionId
  active : Active
  context : Context
  originalSource : TypedSource
  principalSource : TypedSource
  original : ExpressionNode
  node : ExpressionNode
  parameterType : Core.Ty
  resultType : Core.Ty

structure Inventory (checked : Checked) where private mk ::
  base : Base checked
  contexts : SourceCoreAllocationDiscovery.Prepared
  lambdas : List Lambda

/-- The source heap can retain these principal closures even though their
native empty bundle is Unit. Their source metadata/captures must be recovered
from the allocation ledger, not from a nonexistent executable template. -/
def Inventory.unusedPrincipals {checked : Checked} (inventory : Inventory checked) : List SourceCoreLocalPolymorphism.Binding :=
  inventory.base.locals.bindings.filter (fun binding => binding.instances.isEmpty)

def Inventory.lambdaAt? {checked : Checked} (inventory : Inventory checked) (id : Word) : Option Lambda :=
  inventory.lambdas.find? (fun lambda => decide (lambda.descriptor = id))

/-- Actual metadata from the sealed base artifact, including both original and
contextual sources. The static principal view is retained separately; it does
not claim to encode dynamic read-view ancestry. -/
def prepare {checked : Checked} (base : Base checked) : Except Error (Inventory checked) := do
  let receipts ← (SourceCoreAllocationContexts.fromPrepared base.plan base.contexts).mapError Error.contexts
  let contexts ← (SourceCoreAllocationDiscovery.prepare checked.catalog.definitions receipts.contexts).mapError Error.metadata
  let callable ← match base.callableContext with
    | some callable => pure callable | none => throw .contractsUnavailable
  let mut lambdas := []
  for entry in callable.table.entries do
    match entry.origin with
    | .lambda owner id active =>
      let context ← match contexts.metadata.contextAt? owner active with
        | some context => pure context | none => throw (.missingContext owner active)
      let caller ← (SourceCompilationPlan.exactSpecialization base.plan owner).mapError
        (fun _ => Error.missingOrigin entry.origin)
      let original ← match caller.function.typedBody.lookupExpression? id with
        | some node => pure node | none => throw (.invalidLambda id)
      let node ← match context.inventory.source.lookupExpression? id with
        | some node => pure node | none => throw (.invalidLambda id)
      let (parameters, result) ← match node.form with
        | .lambda parameters result _ => pure (parameters, result)
        | _ => throw (.invalidLambda id)
      let inherited := (base.contexts.find? (fun parent => decide
        (parent.caller.key = owner ∧ parent.substitution = active))).map (·.witnesses) |>.getD []
      let principalSource := SourceTypedRuntime.rewriteLocalRequirements inherited
        (caller.function.typedBody.applySubstitution active)
      let parameterType ← (checked.catalog.project (TypeSystem.Ty.productMany (parameters.map (·.scheme.body)))).mapError Error.projection
      let resultType ← (checked.catalog.project result).mapError Error.projection
      lambdas := lambdas ++ [⟨entry.id, owner, id, active, context, caller.function.typedBody,
        principalSource, original, node, parameterType, resultType⟩]
    | _ => pure ()
  pure ⟨base, contexts, lambdas⟩

/-- Type annotations have unit payloads. Real capture references remain in a
separate product, so renaming never hides their actual environment indices. -/
def scopeManifest : List (Word × Core.Ty) → Expr
  | [] => .unit
  | (key, type) :: rest => .pair (.pair (.word key) (.inLeft type .unit)) (scopeManifest rest)

def scopeManifestType : List (Word × Core.Ty) → Core.Ty
  | [] => .unit
  | (_, type) :: rest => .product (.product .word (.sum .unit type)) (scopeManifestType rest)

private def scopeManifest? : Expr → Option (List (Word × Core.Ty))
  | .unit => some []
  | .pair (.pair (.word key) (.inLeft type .unit)) rest => (scopeManifest? rest).map ((key, type) :: ·)
  | _ => none

private def capturedIndices? : Scope → Expr → Option (List Nat)
  | [], .unit => some []
  | [_], .var index => some [index]
  | _ :: next :: rest, .pair (.var index) tail => (capturedIndices? (next :: rest) tail).map (index :: ·)
  | _, _ => none

def manifestBody (descriptor : Word) (fields : List (Word × Core.Ty)) (captures body : Expr) : Expr :=
  .letE (.pair (.word descriptor) (.pair (scopeManifest fields) (captures.weakenAt 0))) (body.weakenAt 0)

private def scopeFields (lambda : Lambda) (scope : Scope) : Except Error (List (Word × Core.Ty)) := do
  unless (scope.map Prod.fst).Nodup do throw .duplicateScope
  scope.mapM fun (binder, type) => do
    let row ← match lambda.context.bindingAt? binder with
      | some row => pure row | none => throw (.scopeMismatch binder)
    pure (row.key, type)

/-- The shared compiler calls this after parameter allocation has been
lowered. Source lexical references occupy contiguous saved-environment slots;
the raw lambda argument adds the initial shift inside its body. -/
def hook {checked : Checked} (inventory : Inventory checked) (owner : Key) (active : Active) :
    SourceCoreFunctions.RawLambdaBodyHook := fun context source scope node parameter result body => do
  let fail := fun error => SourceCoreBasic.Error.sourceAllocation (reprStr error)
  let lambda ← match inventory.lambdas.find? (fun lambda => decide
      (lambda.owner = owner ∧ lambda.id = node.id ∧ lambda.active = active)) with
    | some lambda => pure lambda
    | none => throw (fail (.missingOrigin (.lambda owner node.id active)))
  if context.owner != owner || source.owner != owner.declaration ||
      SourceCoreAllocationCodebook.sourceView source != SourceCoreAllocationCodebook.sourceView lambda.context.inventory.source then
    throw (fail (.sourceViewMismatch owner))
  if node.form != lambda.node.form || parameter != lambda.parameterType || result != lambda.resultType then
    throw (fail .callableTypeMismatch)
  let fields ← (scopeFields lambda scope).mapError fail
  for (_, type) in scope do
    unless type.isWellFormed checked.catalog.definitions do throw (fail (.invalidCaptureType type))
  pure (manifestBody lambda.descriptor fields (SourceCoreSourceCells.captures id scope) body)

def representation {checked : Checked} (inventory : Inventory checked)
    (original : SourceCoreGeneralFunctions.Representation) : SourceCoreGeneralFunctions.Representation :=
  {original with rawLambdaBodyAt := hook inventory}

structure Receipt where private mk ::
  lambda : Lambda
  scope : Scope
  scopeFields : List (Word × Core.Ty)
  /-- Indices in the saved Core closure environment, after installation and
  every surrounding administrative renaming. -/
  references : List Nat
  parameterType : Core.Ty
  resultType : Core.Ty
  body : Expr
  carrier : Expr

/-- Decode one complete contracted anonymous lambda. Scope keys are checked
against immutable source binder metadata; payload types are checked by the
actual native checker and the capture authenticator, rather than inferred
from those source binder schemes. -/
def decode {checked : Checked} (inventory : Inventory checked) (carrier : Expr) : Except Error Receipt := do
  let .pair (.pair (.inLeft .word .unit) (.lambda parameter (.sum .word result) body)) (.word descriptor) := carrier
    | throw (.malformedManifest "complete callable shape")
  let .letE (.pair (.word key) (.pair fields captures)) _ := body | throw (.malformedManifest "shape")
  if descriptor != key then throw (.descriptorMismatch key descriptor)
  let lambda ← match inventory.lambdaAt? key with
    | some lambda => pure lambda | none => throw (.unknownDescriptor key)
  if parameter != lambda.parameterType || result != lambda.resultType then throw .callableTypeMismatch
  let fields ← match scopeManifest? fields with | some fields => pure fields | none => throw (.malformedManifest "shape")
  unless (fields.map Prod.fst).Nodup do throw .duplicateScope
  let scope ← fields.mapM fun (key, type) => do
    let row ← match lambda.context.bindings.find? (fun row => decide (row.key = key)) with
      | some row => pure row | none => throw (.malformedManifest "shape")
    unless type.isWellFormed checked.catalog.definitions do throw (.invalidCaptureType type)
    pure (row.binding.binder.id, type)
  let references ← match capturedIndices? scope captures with
    | some references => pure references | none => throw (.malformedManifest "shape")
  unless references.Nodup do throw .duplicateScope
  if references.any (· == 0) then throw (.malformedManifest "lambda argument in source captures")
  pure ⟨lambda, scope, fields, references.map (· - 1), parameter, result, body, carrier⟩

/-- Syntactic manifest recognition only. The complete decoder owns all keys,
source metadata and actual shape checks. -/
private def hasManifest : Expr → Bool
  | .lambda _ _ (.letE (.pair (.word _) (.pair fields _)) _) => (scopeManifest? fields).isSome
  | _ => false

mutual
  def scan {checked : Checked} (inventory : Inventory checked) : Nat → Expr → Except Error (List Receipt)
    | 0, _ => .error .traversalExhausted
    | fuel + 1, expression => do
      match expression with
      | .pair (.pair identity lambda) descriptor =>
        if hasManifest lambda then
          let receipt ← decode inventory expression
          let .lambda _ _ (.letE _ inner) := lambda | throw (.malformedManifest "shape")
          pure (receipt :: (← scan inventory fuel inner))
        else
          -- The left child can itself be a complete contracted callable,
          -- for example the first component of a polymorphic bundle. Keep
          -- that pair intact so its manifested lambda is not scanned alone.
          pure ((← scan inventory fuel (.pair identity lambda)) ++ (← scan inventory fuel descriptor))
      | .unit | .bool _ | .word _ | .integer _ | .var _ => pure []
      | .lambda _ _ body =>
        if hasManifest expression then throw (.malformedManifest "manifest outside complete callable carrier")
        scan inventory fuel body
      | .pair left right | .apply left right | .storeCell left right | .binary _ left right | .letE left right =>
        pure ((← scan inventory fuel left) ++ (← scan inventory fuel right))
      | .first operand | .second operand | .loadCell operand | .inLeft _ operand | .inRight _ operand |
        .newCell _ operand | .construct _ operand | .unary _ operand => scan inventory fuel operand
      | .caseE first second third | .ifE first second third | .ternary _ first second third =>
        pure ((← scan inventory fuel first) ++ (← scan inventory fuel second) ++ (← scan inventory fuel third))
      | .matchData _ _ scrutinee branches => pure ((← scan inventory fuel scrutinee) ++ (← scanBranches inventory fuel branches))
  def scanBranches {checked : Checked} (inventory : Inventory checked) : Nat → List Expr → Except Error (List Receipt)
    | _, [] => pure []
    | 0, _ :: _ => .error .traversalExhausted
    | fuel + 1, head :: tail => do
      pure ((← scan inventory fuel head) ++ (← scanBranches inventory fuel tail))
end

def installedTemplate (index : Nat) (expression : Expr) : Expr :=
  (List.range index).foldl (fun expression _ => expression.weakenAt 0) expression

structure Compiled {checked : Checked} (inventory : Inventory checked)
    (original : SourceCoreGeneralFunctions.Representation) (fuel : Nat) where private mk ::
  compilation : SourceCoreCompatibleMarkedFunctions.Compilation inventory.base (representation inventory original) fuel
  /-- Templates are scanned after the exact administrative weakening used
  when the compiled globals are installed. Duplicated emission sites remain. -/
  groups : List (List Receipt)
  scanned : (compilation.closures.zipIdx.mapM fun (closure, index) =>
    scan inventory (SourceCoreCompatibleMarkedFunctions.scanBudget (installedTemplate index closure))
      (installedTemplate index closure)) = .ok groups


def Compiled.templates {checked : Checked} {inventory : Inventory checked}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled inventory original fuel) : List Receipt := compiled.groups.flatten

def compile {checked : Checked} (inventory : Inventory checked)
    (original : SourceCoreGeneralFunctions.Representation) (fuel : Nat) :
    Except Error (Compiled inventory original fuel) := do
  let compilation ← (SourceCoreCompatibleMarkedFunctions.compileWithReceipt inventory.base
    (representation inventory original) fuel).mapError Error.compilation
  match scanned : compilation.closures.zipIdx.mapM (fun (closure, index) =>
      scan inventory (SourceCoreCompatibleMarkedFunctions.scanBudget (installedTemplate index closure))
        (installedTemplate index closure)) with
  | .error error => throw error
  | .ok groups => pure ⟨compilation, groups, scanned⟩

structure Captured (scope : Scope) (references : List Nat) (environment : Core.Environment) (world : StoreTyping) where private mk ::
  locations : List Nat
  exact : (references.zip scope |>.zip locations |>.all (fun ((index, (_, type)), location) =>
    decide (environment[index]? = some (.cellRef (OptionalCell.cellType type) location) ∧
      world[location]? = some (OptionalCell.cellType type)))) = true
  lengths : references.length = scope.length ∧ locations.length = scope.length

private def captureLocations (scope : Scope) (references : List Nat) (environment : Core.Environment)
    (world : StoreTyping) : Except Error (Captured scope references environment world) := do
  if references.length != scope.length then throw (.malformedManifest "shape")
  let locations ← (references.zip scope).mapM fun (index, (_, type)) => do
    let captured ← match environment[index]? with
      | some captured => pure captured | none => throw (.missingCapture index)
    let .cellRef actual location := captured | throw (.captureMismatch index)
    if actual != OptionalCell.cellType type then throw (.captureMismatch index)
    if world[location]? != some (OptionalCell.cellType type) then throw (.captureOutsideWorld location)
    pure location
  if lengths : references.length = scope.length ∧ locations.length = scope.length then
    if exact : (references.zip scope |>.zip locations |>.all (fun ((index, (_, type)), location) =>
        decide (environment[index]? = some (.cellRef (OptionalCell.cellType type) location) ∧
          world[location]? = some (OptionalCell.cellType type)))) = true then
      pure ⟨locations, exact, lengths⟩
    else throw (.malformedManifest "shape")
  else throw (.malformedManifest "shape")

/-- This receipt checks exact native code and typed capture references. It
must be paired with `Compiled` membership from the enclosing artifact and the
source allocation ledger before identifying a source closure. -/
structure Authenticated (receipt : Receipt) (definitions : DataEnvironment) (world : StoreTyping)
    (store : Store) (value : Core.Value) where private mk ::
  environment : Core.Environment
  captures : Captured receipt.scope receipt.references environment world
  stored : RuntimeStoreHasTypes world store definitions
  typed : RuntimeValueHasType world value
    (CallableContract.functionType receipt.parameterType receipt.resultType) definitions
  exact : value = .pair (.pair (.inLeft .word .unit)
    (.closure receipt.parameterType (LanguageResult.resultType receipt.resultType) receipt.body environment))
    (.word receipt.lambda.descriptor)

def authenticate (receipt : Receipt) {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (stored : RuntimeStoreHasTypes world store definitions) (value : Core.Value)
    (typed : RuntimeValueHasType world value
      (CallableContract.functionType receipt.parameterType receipt.resultType) definitions) :
    Except Error (Authenticated receipt definitions world store value) := do
  let .pair (.pair (.inLeft .word .unit) (.closure parameter result body environment)) (.word descriptor) := value
    | throw .closureMismatch
  if parameter != receipt.parameterType || result != LanguageResult.resultType receipt.resultType ||
      body != receipt.body || descriptor != receipt.lambda.descriptor then throw .closureMismatch
  let captures ← captureLocations receipt.scope receipt.references environment world
  if exact : value = .pair (.pair (.inLeft .word .unit)
      (.closure receipt.parameterType (LanguageResult.resultType receipt.resultType) receipt.body environment))
      (.word receipt.lambda.descriptor) then
    pure ⟨environment, captures, stored, typed, exact⟩
  else throw .closureMismatch

def freshGlobals (globals : List SourceCoreCalls.Signature) (base : Nat := 0) : Core.Environment :=
  globals.zipIdx.map fun (signature, index) =>
    .cellRef (OptionalCell.cellType signature.functionType) (base + globals.length - 1 - index)

private def expectedGlobals {checked : Checked} {inventory : Inventory checked}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled inventory original fuel) (base : Nat) : Except Error (List (Nat × Core.Value)) := do
  let globals := inventory.base.globals
  if compiled.compilation.closures.length != globals.length then throw .globalEnvironmentMismatch
  globals.zipIdx.mapM fun (signature, index) => do
    let cached ← match compiled.compilation.closures[index]? with
      | some cached => pure cached | none => throw (.globalSlotMismatch index)
    let .lambda parameter result body := installedTemplate index cached | throw (.globalSlotMismatch index)
    if parameter != signature.parameterType || result != LanguageResult.resultType signature.resultType then
      throw (.globalSlotMismatch index)
    let captured := List.replicate index Core.Value.unit ++ freshGlobals globals base
    pure (base + globals.length - 1 - index,
      .inRight .unit (.closure parameter result body captured))

structure Globals {checked : Checked} {inventory : Inventory checked}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled inventory original fuel) (store : Store) (base : Nat) where private mk ::
  slots : List (Nat × Core.Value)
  generated : expectedGlobals compiled base = .ok slots
  exact : slots.all (fun (index, value) => decide (store[index]? = some value)) = true

def snapshotGlobals {checked : Checked} {inventory : Inventory checked}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled inventory original fuel) (store : Store) (base : Nat := 0) :
    Except Error (Globals compiled store base) := do
  match generated : expectedGlobals compiled base with
  | .error error => throw error
  | .ok slots =>
    if exact : slots.all (fun (index, value) => decide (store[index]? = some value)) = true then
      pure ⟨slots, generated, exact⟩
    else
      match slots.find? (fun (index, value) => decide (store[index]? != some value)) with
      | some (index, _) => throw (.globalSlotMismatch index)
      | none => throw .globalEnvironmentMismatch

/-- An export receipt is indexed by the artifact's actual compiler/scanner
receipt. Structural manifest decoding alone cannot produce this membership. -/
structure Export {checked : Checked} {inventory : Inventory checked}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled inventory original fuel) (definitions : DataEnvironment)
    (world : StoreTyping) (store : Store) (value : Core.Value) where private mk ::
  /-- Ambient marker definitions may extend this artifact's definitions, but
  cannot replace the constructor payload table of its catalog. -/
  definitionsPrefix : definitions.take checked.catalog.definitions.length = checked.catalog.definitions
  globalsBase : Nat
  globals : Globals compiled store globalsBase
  template : Receipt
  member : template ∈ compiled.templates
  closure : Authenticated template definitions world store value
  capturedGlobals : (closure.environment.drop (closure.environment.length - inventory.base.globals.length)) =
    freshGlobals inventory.base.globals globalsBase

def authenticateCompiled {checked : Checked} {inventory : Inventory checked}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled inventory original fuel) {definitions : DataEnvironment}
    {world : StoreTyping} {store : Store} (stored : RuntimeStoreHasTypes world store definitions)
    (value : Core.Value) (parameter result : Core.Ty)
    (typed : RuntimeValueHasType world value (CallableContract.functionType parameter result) definitions)
    (globalsBase : Nat := 0) : Except Error (Export compiled definitions world store value) := do
  if definitionsPrefix : definitions.take checked.catalog.definitions.length = checked.catalog.definitions then
    let globals ← snapshotGlobals compiled store globalsBase
    let .pair (.pair (.inLeft .word .unit) (.closure _ _ body _)) (.word descriptor) := value | throw .closureMismatch
    let selected ← match compiled.templates.attach.find? (fun item => decide
        (item.val.lambda.descriptor = descriptor ∧ item.val.body = body ∧
          item.val.parameterType = parameter ∧ item.val.resultType = result)) with
      | some item => pure item | none => throw .closureMismatch
    if types : selected.val.parameterType = parameter ∧ selected.val.resultType = result then
      let authenticated ← authenticate selected.val stored value (by simpa only [types.1, types.2] using typed)
      if capturedGlobals : authenticated.environment.drop
          (authenticated.environment.length - inventory.base.globals.length) =
          freshGlobals inventory.base.globals globalsBase then
        pure ⟨definitionsPrefix, globalsBase, globals, selected.val, selected.property, authenticated, capturedGlobals⟩
      else throw .globalEnvironmentMismatch
    else throw .closureMismatch
  else throw .foreignDefinitions

theorem scopeManifest_hasType {definitions : DataEnvironment} {context : Core.Context}
    (fields : List (Word × Core.Ty)) (wellFormed : ∀ field ∈ fields, field.2.WellFormed definitions) :
    HasType context (scopeManifest fields) (scopeManifestType fields) definitions := by
  induction fields with
  | nil => exact .unit
  | cons head tail ih =>
    exact .pair (.pair .word (.inLeft (wellFormed head (by simp)) .unit))
      (ih (fun field member => wellFormed field (List.mem_cons_of_mem head member)))

/-- The manifest's saved references run before parameter binding. Its pure
metadata/capture product adds one private environment value and no heap cell. -/
theorem manifestBody_hasType {definitions : DataEnvironment} {context : Core.Context}
    {fields : List (Word × Core.Ty)} {captures body : Expr} {captureType resultType parameterType : Core.Ty}
    (descriptor : Word) (fieldsWF : ∀ field ∈ fields, field.2.WellFormed definitions)
    (capturesTyped : HasType context captures captureType definitions)
    (bodyTyped : HasType (parameterType :: context) body resultType definitions) :
    HasType (parameterType :: context) (manifestBody descriptor fields captures body) resultType definitions := by
  have shifted : HasType (parameterType :: context) (captures.weakenAt 0) captureType definitions := by
    simpa only [Core.Context.insertAt] using capturesTyped.weakenAt (inserted := parameterType) 0
  unfold manifestBody
  apply HasType.letE (.pair .word (.pair (scopeManifest_hasType fields fieldsWF) shifted))
  simpa only [Core.Context.insertAt] using bodyTyped.weakenAt 0

def scopeManifestValue : List (Word × Core.Ty) → Core.Value
  | [] => .unit
  | (key, type) :: rest => .pair (.pair (.word key) (.inLeft type .unit)) (scopeManifestValue rest)

theorem scopeManifest_evaluates (fields : List (Word × Core.Ty)) (environment : Core.Environment) (store : Store) :
    Evaluates environment store (scopeManifest fields) (scopeManifestValue fields) store := by
  induction fields with
  | nil => exact .unit
  | cons head tail ih => exact .pair (.pair .word (.inLeft .unit)) ih

/-- Adding the private manifest binder preserves higher-order results and
stores under Core's established relational renaming, with finite evaluation
witnesses on both sides. Exact closure environments may grow. -/
theorem manifestBody_related {environment : Core.Environment} {store finalStore : Store}
    {fields : List (Word × Core.Ty)} {captures body : Expr} {captureValue result : Core.Value}
    (descriptor : Word)
    (captureEvaluation : Evaluates environment store (captures.weakenAt 0) captureValue store)
    (bodyEvaluation : Evaluates environment store body result finalStore) :
    ∃ result' finalStore', Evaluates environment store (manifestBody descriptor fields captures body) result' finalStore' ∧
      ValuesRelated result result' ∧ StoresRelated finalStore finalStore' := by
  let manifest := Core.Value.pair (.word descriptor) (.pair (scopeManifestValue fields) captureValue)
  have evaluated : Evaluates environment store
      (.pair (.word descriptor) (.pair (scopeManifest fields) (captures.weakenAt 0))) manifest store :=
    .pair .word (.pair (scopeManifest_evaluates fields environment store) captureEvaluation)
  have environments : EnvironmentsRelated (Renaming.insertion 0) environment (manifest :: environment) := by
    refine EnvironmentsRelated.intro (fun index bound => ?_) (fun index bound => ?_)
    · simpa [Renaming.insertion] using Nat.succ_lt_succ bound
    · simpa [Renaming.insertion] using ValuesRelated.refl environment[index]
  obtain ⟨result', finalStore', renamed, resultRelated, storesRelated⟩ :=
    bodyEvaluation.rename environments (StoresRelated.refl store)
  exact ⟨result', finalStore', .letE evaluated (by simpa only [Expr.rename_insertion] using renamed),
    resultRelated, storesRelated⟩

/-- Evaluation uses the actual extended environment. Higher-order results and
stores should be compared with `Core.Evaluates.rename` / `ValuesRelated`,
rather than an invalid exact-store weakening assertion. -/
theorem manifestBody_evaluates {environment : Core.Environment} {store finalStore : Store}
    {fields : List (Word × Core.Ty)} {captures body : Expr} {manifest result : Core.Value}
    (descriptor : Word)
    (pureManifest : Evaluates environment store
      (.pair (.word descriptor) (.pair (scopeManifest fields) (captures.weakenAt 0))) manifest store)
    (bodyEvaluation : Evaluates (manifest :: environment) store (body.weakenAt 0) result finalStore) :
    Evaluates environment store (manifestBody descriptor fields captures body) result finalStore :=
  .letE pureManifest bodyEvaluation

end Solcore.Frontend.SourceCoreLambdaTemplates
