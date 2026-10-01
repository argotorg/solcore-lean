import Solcore.Frontend.SourceCoreCompatibleDataExpressions
import Solcore.Frontend.SourceCoreCallableContracts
import Solcore.Frontend.SourceRuntimeValidation

/-! Accepted public source arguments become ordinary Core expressions beneath
already installed global references. Data keeps the compatible codec and raw
registry; named functions read the cached global cell, while builtins use the
existing native template. Neither path evaluates or walks a source body.

The source validator runs before encoding, with its original plan, budget and
error order. Closure/instantiated values remain rejected at every depth. The
owning artifact supplies the actual cached global code and initialized store;
this adapter certifies expressions under those reference types, not arbitrary
host-created closure code or a foreign artifact's globals. -/

set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleInputs
open SourceInference TypeSystem
abbrev Values := SourceCoreCompatibleValues.Context
abbrev Extended := SourceCoreCompatibleValues.Extended
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Signature := SourceCoreCalls.Signature
abbrev Table := SourceCoreStageCodebook.Table
abbrev Lowered := SourceCoreBasic.LoweredExpr

inductive Error where
  | source (error : SourceCompilationPlan.Error)
  | catalog (error : SourceCoreCompatibleCatalog.Error)
  | metadata (error : SourceCoreRawMetadata.Error)
  | codec (error : SourceCoreCompatibleValues.Error)
  | globalsOrderMismatch
  | globalTypeMismatch (key : Key)
  | missingGlobal (key : Key)
  | missingContract (origin : SourceCoreStageCodebook.Origin)
  | contractMismatch (origin : SourceCoreStageCodebook.Origin)
  | identitySpaceExhausted
  | payloadCountMismatch
  | unsupportedValue
  | exhausted
  | checkFailed (expected : Core.Ty)
  deriving Repr

structure Context where private mk ::
  values : Values
  /-- Prepared runtime frontier owning all cached global slots. -/
  plan : Plan
  /-- The old public boundary validates against this plan before preparing any
  additional runtime evidence frontier. -/
  validationPlan : Plan
  globals : List Signature
  codebook : Option Table
  definitions : Core.DataEnvironment
  internalReason : Core.Word

def Context.coreContext (context : Context) : Core.Context := context.globals.map (·.referenceType)

private def native (values : Values) (type : Ty) : Except Error Core.Ty :=
  (values.checked.project type).map (·.type) |>.mapError Error.catalog

private def descriptor (table : Table) (origin : SourceCoreStageCodebook.Origin) : Except Error Core.Word :=
  match table.idAt? origin with
  | some id => pure id | none => throw (.missingContract origin)

/-- Check slot order, projected signatures and retained named staging flags
once. The artifact has already authenticated and compiled its executable plan. -/
private def validatePrepared (values : Values) (plan : Plan) (globals : List Signature)
    (codebook : Option Table) : Except Error Unit := do
  unless globals.map (·.key) = plan.specializations.reverse.map (·.key) do throw .globalsOrderMismatch
  for signature in globals do
    let specialized ← (SourceCompilationPlan.exactSpecialization plan signature.key).mapError Error.source
    let (parameter, result) ← match specialized.function.type with
      | .function parameter result => pure (parameter, result)
      | _ => throw (.globalTypeMismatch signature.key)
    let projectedParameter ← native values parameter
    let projectedResult ← native values result
    unless signature.parameterType = projectedParameter && signature.resultType = projectedResult do
      throw (.globalTypeMismatch signature.key)
    if values.checked.catalog.callableContracts then
      let table ← match codebook with
        | some table => pure table | none => throw (.missingContract (.named signature.key))
      let id ← descriptor table (.named signature.key)
      let entry ← match table.entryAt? id with
        | some entry => pure entry | none => throw (.missingContract (.named signature.key))
      let contract ← match entry.contract with
        | some contract => pure contract | none => throw (.contractMismatch (.named signature.key))
      unless contract.owner = signature.key &&
          contract.parameters = specialized.function.typedBody.inputs &&
          contract.stagedResult = (specialized.function.returnComptime ||
            SourceCompilationPlan.sourceTypeIsComptimeOnly specialized.function.inferredBodyType) &&
          entry.parameterCount = specialized.function.typedBody.inputs.length do
        throw (.contractMismatch (.named signature.key))
  pure ()

def prepare (values : Values) (plan : Plan) (globals : List Signature) (codebook : Option Table)
    (definitions : Core.DataEnvironment) (internalReason : Core.Word := Core.Word.zero)
    (validationPlan : Option Plan := none) : Except Error Context :=
  match validatePrepared values plan globals codebook with
  | .error error => .error error
  | .ok _ => .ok (.mk values plan (validationPlan.getD plan) globals codebook definitions internalReason)

/-- Preparing cached globals retains the exact compatible value owner. -/
theorem prepare_values {values : Values} {plan : Plan} {globals : List Signature}
    {codebook : Option Table} {definitions : Core.DataEnvironment} {internalReason : Core.Word}
    {validationPlan : Option Plan} {context : Context}
    (accepted : prepare values plan globals codebook definitions internalReason validationPlan = .ok context) :
    context.values = values := by
  unfold prepare at accepted
  cases checked : validatePrepared values plan globals codebook with
  | error error => simp [checked] at accepted
  | ok value => simp [checked] at accepted; cases accepted; rfl

/-- Pure data projection deliberately excludes every executable source leaf. -/
def dataOnly? : SourceValue → Option SourceCoreCompatibleValues.Value
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .proxy inner => some (.proxy inner)
  | .product left right => do pure (.product (← dataOnly? left) (← dataOnly? right))
  | .constructed instantiation payloads => do
      pure (.constructed instantiation (← payloads.mapM dataOnly?))
  | .mapping key value entries => do
      pure (.mapping key value (← entries.mapM fun entry => do pure (← dataOnly? entry.1, ← dataOnly? entry.2)))
  | .global .. | .builtin .. | .closure .. | .instantiated .. => none
  decreasing_by
    all_goals first
      | decreasing_trivial
      | have smaller := List.sizeOf_lt_of_mem (by assumption)
        cases entry
        simp_all only [SourceTypedRuntime.Value.mapping.sizeOf_spec, Prod.mk.sizeOf_spec]
        omega

/-- Executable structural size for accepted input carriers. It never walks a
closure body, source table or global evidence ledger. Raw type sizes account
for the pure defaults transported beside mapping entries. -/
def encodingSize : SourceValue → Nat
  | .product left right => encodingSize left + encodingSize right + 1
  | .constructed instantiation payloads =>
      instantiation.resultType.size +
        (instantiation.payloadTypes.foldl (fun total type => total + type.size) 0) +
        (payloads.foldl (fun total value => total + encodingSize value + 1) 0) + 1
  | .mapping key value entries => key.size + value.size +
      (entries.foldl (fun total entry => total + encodingSize entry.1 + encodingSize entry.2 + 1) 0) + 1
  | .proxy inner => inner.size + 1
  | _ => 1
  decreasing_by
    all_goals first
      | decreasing_trivial
      | have smaller := List.sizeOf_lt_of_mem (by assumption)
        cases entry
        simp_all only [SourceTypedRuntime.Value.mapping.sizeOf_spec, Prod.mk.sizeOf_spec]
        omega

private def identity (index : Nat) : Except Error Core.Word :=
  match Core.Word.ofNat? (index + 1) with
  | some word => pure word | none => throw .identitySpaceExhausted

private def decorate (context : Context) (origin : SourceCoreStageCodebook.Origin)
    (type : Core.Ty) (raw : Core.Expr) : Except Error Core.Expr := do
  if context.values.checked.catalog.callableContracts then
    let table ← match context.codebook with
      | some table => pure table | none => throw (.missingContract origin)
    let id ← descriptor table origin
    pure (Core.LanguageResult.bind type raw (Core.LanguageResult.success (Core.CallableContract.wrap id (.var 0))))
  else pure raw

private def global (context : Context) (key : Key) (type : Core.Ty) : Except Error Core.Expr := do
  let (signature, index) ← match context.globals.zipIdx.find? (fun pair => decide (pair.1.key = key)) with
    | some found => pure found | none => throw (.missingGlobal key)
  decorate context (.named key) type
    (SourceCoreFunctions.namedReference signature index (← identity index) context.internalReason)

private def builtin (context : Context) (function : BuiltinFunctionId) (type : Core.Ty) : Except Error Core.Expr := do
  let index ← match BuiltinFunctionId.all.zipIdx.find? (fun pair => decide (pair.1 = function)) with
    | some (_, index) => pure index | none => throw .unsupportedValue
  if context.values.checked.catalog.callableContracts then
    let table ← match context.codebook with
      | some table => pure table | none => throw (.missingContract (.builtin function))
    let id ← descriptor table (.builtin function)
    let entry ← match table.entryAt? id with
      | some entry => pure entry | none => throw (.missingContract (.builtin function))
    unless entry.parameterCount = function.parameterTypes.length && entry.contract.isNone do
      throw (.contractMismatch (.builtin function))
  decorate context (.builtin function) type (Core.LanguageResult.success
    (Core.TaggedFunction.identified (← identity (context.globals.length + index))
      (SourceCoreInteger.builtinClosure function)))

mutual
  private def encodeRaw : Nat → Context → (values : Values) → Ty → SourceValue → Except Error (Extended values.registry Lowered)
    | 0, _, _, _, _ => throw .exhausted
    | fuel + 1, context, values, expected, value => do
        let type ← native values expected
        match dataOnly? value with
        | some data =>
            let encoded ← (SourceCoreCompatibleValues.encode (fuel + 1) values expected data).mapError Error.codec
            let expression ← match SourceCoreCompatibleDataExpressions.quote encoded.value with
              | some expression => pure expression | none => throw .unsupportedValue
            pure ⟨encoded.context.registry, encoded.preserves, ⟨type, Core.LanguageResult.success expression⟩⟩
        | none =>
            match SourceCoreRawMetadata.runtimeType expected, value with
            | .function .., .global key _ =>
                pure ⟨values.registry, .refl _, ⟨type, ← global context key type⟩⟩
            | .function .., .builtin function =>
                pure ⟨values.registry, .refl _, ⟨type, ← builtin context function type⟩⟩
            | .product leftType rightType, .product left right =>
                let left ← encodeRaw fuel context values leftType left
                let next := values.extend left.registry left.preserves
                let right ← encodeRaw fuel context next rightType right
                pure ⟨right.registry, left.preserves.trans right.preserves,
                  ⟨type, Core.LocalSequence.pair left.value.type right.value.type left.value.expression right.value.expression⟩⟩
            | .mapping keyType valueType, .mapping actualKey actualValue entries =>
                let registered ← (values.registry.intern expected (.mapping actualKey actualValue)).mapError Error.metadata
                let next := values.extend registered.registry registered.preserves
                let layout ← (values.checked.catalog.mappingLayout keyType valueType).mapError Error.catalog
                let entries ← encodeEntries fuel context next actualKey actualValue layout entries
                let next := next.extend entries.registry entries.preserves
                let fallback ← encodeDefault fuel context next actualValue layout.valueType
                pure ⟨fallback.registry, registered.preserves.trans (entries.preserves.trans fallback.preserves),
                  ⟨type, Core.LanguageResult.bind type
                    (Core.LocalSequence.pair layout.type layout.lookupResult entries.value.expression fallback.value.expression)
                    (Core.LanguageResult.success (SourceCoreMappingWithDefault.pack (.word registered.id)
                      (.second (.var 0)) (.first (.var 0))))⟩⟩
            | _, .constructed instantiation payloads =>
                let registered ← (values.registry.intern expected (.constructor instantiation)).mapError Error.metadata
                let constructor ← (values.checked.resolveConstructor instantiation).mapError Error.catalog
                let next := values.extend registered.registry registered.preserves
                let payloads ← encodePayloads fuel context next instantiation.payloadTypes payloads
                pure ⟨payloads.registry, registered.preserves.trans payloads.preserves,
                  ⟨type, SourceCoreCompatibleDataExpressions.construct constructor registered.id payloads.value.expression⟩⟩
            | _, _ => throw .unsupportedValue

  private def encodePayloads (fuel : Nat) (context : Context) (values : Values) (types : List Ty) (payloads : List SourceValue) :
      Except Error (Extended values.registry Lowered) := do
    unless types.length = payloads.length do throw .payloadCountMismatch
    match fuel, types, payloads with
    | _, [], [] => pure ⟨values.registry, .refl _, ⟨.unit, Core.LanguageResult.success .unit⟩⟩
    | 0, _, _ => throw .exhausted
    | fuel + 1, [type], [value] => encodeRaw fuel context values type value
    | fuel + 1, type :: types, value :: payloads =>
        let head ← encodeRaw fuel context values type value
        let next := values.extend head.registry head.preserves
        let tail ← encodePayloads fuel context next types payloads
        pure ⟨tail.registry, head.preserves.trans tail.preserves,
          ⟨.product head.value.type tail.value.type,
            Core.LocalSequence.pair head.value.type tail.value.type head.value.expression tail.value.expression⟩⟩
    | _, _, _ => throw .payloadCountMismatch

  private def encodeEntries : Nat → Context → (values : Values) → Ty → Ty → Core.OrderedMapping.Layout →
      List (SourceValue × SourceValue) → Except Error (Extended values.registry Lowered)
    | _, _, values, _, _, layout, [] => pure ⟨values.registry, .refl _,
        ⟨layout.type, Core.LanguageResult.success (Core.OrderedMapping.empty layout)⟩⟩
    | 0, _, _, _, _, _, _ :: _ => throw .exhausted
    | fuel + 1, context, values, keyType, valueType, layout, (key, value) :: entries => do
        let key ← encodeRaw fuel context values keyType key
        let next := values.extend key.registry key.preserves
        let value ← encodeRaw fuel context next valueType value
        let next := next.extend value.registry value.preserves
        let tail ← encodeEntries fuel context next keyType valueType layout entries
        let pair := Core.LocalSequence.pair layout.keyType layout.valueType key.value.expression value.value.expression
        pure ⟨tail.registry, key.preserves.trans (value.preserves.trans tail.preserves),
          ⟨layout.type, Core.LanguageResult.bind layout.type
            (Core.LocalSequence.pair (.product layout.keyType layout.valueType) layout.type pair tail.value.expression)
            (Core.LanguageResult.success (.construct layout.consConstructor (.var 0)))⟩⟩

  private def encodeDefault (fuel : Nat) (context : Context) (values : Values) (rawType : Ty) (type : Core.Ty) :
      Except Error (Extended values.registry Lowered) := do
    match SourceTypedRuntime.defaultValue? (rawType.size + 1) rawType with
    | none => pure ⟨values.registry, .refl _, ⟨.sum .unit type, Core.LanguageResult.success (.inLeft type .unit)⟩⟩
    | some source =>
        let encoded ← encodeRaw fuel context values rawType source
        pure ⟨encoded.registry, encoded.preserves, ⟨.sum .unit type,
          Core.LanguageResult.bind (.sum .unit type) encoded.value.expression
            (Core.LanguageResult.success (.inRight .unit (.var 0)))⟩⟩
end

private def encodeArgumentsRaw (fuel : Nat) (context : Context) (values : Values) :
    List Ty → List SourceValue → Except Error (Extended values.registry (List Lowered))
  | [], [] => pure ⟨values.registry, .refl _, []⟩
  | type :: types, value :: arguments => do
      let head ← encodeRaw fuel context values type value
      let next := values.extend head.registry head.preserves
      let tail ← encodeArgumentsRaw fuel context next types arguments
      pure ⟨tail.registry, head.preserves.trans tail.preserves, head.value :: tail.value⟩
  | _, _ => throw .payloadCountMismatch

structure Encoded (context : Context) (expected : List Ty) (arguments : List SourceValue) (validationFuel : Nat) where private mk ::
  values : Values
  preserves : SourceCoreRawMetadata.Extends context.values.registry values.registry
  parts : List Lowered
  expression : Core.Expr
  type : Core.Ty
  packed : SourceCoreCalls.packArguments parts = ⟨type, expression⟩
  typed : Core.HasType context.coreContext expression (Core.LanguageResult.resultType type) context.definitions
  validated : SourceTypedRuntime.validateInputs context.values.checked.signatures context.validationPlan
    validationFuel expected arguments = none

/-- Validation fuel controls the original deep validator, not the width of an
already accepted list. Encoding has a structural budget derived from the input
and its source types, including their pure transported defaults. -/
def encode (context : Context) (expected : List Ty) (arguments : List SourceValue)
    (validationFuel : Nat := 256) : Except Error (Encoded context expected arguments validationFuel) := do
  match validated : SourceTypedRuntime.validateInputs context.values.checked.signatures context.validationPlan
      validationFuel expected arguments with
  | some error => throw (.source error)
  | none =>
      let encodingFuel := (arguments.foldl (fun total value => total + encodingSize value) 0) +
        (expected.foldl (fun total type => total + type.size) 0) + 32
      let raw ← encodeArgumentsRaw encodingFuel context context.values expected arguments
      let values := context.values.extend raw.registry raw.preserves
      let packed := SourceCoreCalls.packArguments raw.value
      if typed : Core.infer? context.coreContext packed.expression context.definitions = some (Core.LanguageResult.resultType packed.type) then
        pure (.mk values raw.preserves raw.value packed.expression packed.type rfl (Core.infer_sound typed) validated)
      else throw (.checkFailed packed.type)

end Solcore.Frontend.SourceCoreCompatibleInputs
