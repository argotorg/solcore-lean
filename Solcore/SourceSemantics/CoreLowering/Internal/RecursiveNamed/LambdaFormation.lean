import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogExpressions

/-!
# Recursive named rows: lambda formation

Heads of lambda formation and the meaning of formation trees.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads
/-! Static lambda formation receipts retain the accepted code and its complete
builtin runtime body. Changing the captured source environment reconstructs
the same receipt field by field; no body law or native type supplies source
provenance. Actual formation uses the aligned named history separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues

variable {values : SourceCoreCompatibleValues.Context}
  {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {program : Program}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Captures are the only changed closure field. Every compiler input and
output remains the actual accepted receipt. -/
def recaptureCode (code : Code indexed function scope administrative)
    (environment : Dynamic.Environment) : Code indexed {function with captured := environment} scope administrative :=
  {code with sourceNode := code.sourceNode}

def recaptureContext (code : Code indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context code) (environment : Dynamic.Environment) :
    CallableIndexedLambdaEntryPrefix.Context (recaptureCode code environment) :=
  {inputs with context := inputs.context}

theorem recaptureFrame (frame : Dynamic.ClosureFrame program function) (environment : Dynamic.Environment) :
    Dynamic.ClosureFrame program {function with captured := environment} :=
  {frame with code := {frame.code with occurrence := frame.code.occurrence}}

/-- Recapture changes only the source capture environment. The generic
static Tree, actual view callback, flow and full code remain the same receipt. -/
def recaptureBodyWith
    {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (code : Code indexed function scope administrative)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith expressionSyntax certificates code program registry faults)
    (environment : Dynamic.Environment) :
    CallableIndexedLambdaStaticBodySupport.BodyWith expressionSyntax certificates (recaptureCode code environment) program registry faults :=
  { toContext := recaptureContext code body.toContext environment
    frame := recaptureFrame body.frame environment
    readFuel := body.readFuel, policy := body.policy, callback := body.callback
    flow := body.flow, generated := body.generated, projection := body.projection, emitted := body.emitted
    actualTree := body.actualTree, actualSites := body.actualSites, tree := body.tree, sites := body.sites
    valid := body.valid, unique := body.unique }

/-- The complete actual and canonical trees, code equality and runtime ledger
are rebuilt together. The closure frame alone is insufficient for this step. -/
def recaptureBody (code : Code indexed function scope administrative)
    (body : CallableIndexedLambdaRuntimeBody.Body code program registry faults)
    (environment : Dynamic.Environment) :
    CallableIndexedLambdaRuntimeBody.Body (recaptureCode code environment) program registry faults :=
  CallableIndexedLambdaRuntimeBody.Body.fromWith
    (recaptureBodyWith code body.toWith environment)

/-- Typing of a used prefix comes from real values in the same environment.
The native environment outside that prefix is retained by the caller. -/
theorem typed_prefix {definitions : DataEnvironment} {world : StoreTyping}
    {environment : Environment} {context : Core.Context} (leading : Core.Context)
    (typed : RuntimeEnvironmentHasTypes world environment context definitions)
    (same : NativeExpressionContextSupport.Agrees leading.length leading context) :
    RuntimeEnvironmentHasTypes world (environment.take leading.length) leading definitions := by
  induction leading generalizing environment context with
  | nil => exact .nil
  | cons head tail ih =>
    cases typed with
    | nil => have atZero := same 0 (by simp); simp at atZero
    | cons valueTyped tailTyped =>
      have atZero := same 0 (by simp)
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atZero
      subst head
      exact .cons valueTyped (ih tailTyped (by
        intro index smaller
        exact same (index + 1) (by simp only [List.length_cons]; omega)))

/-- Only the canonical administrative suffix is shortened. The ordered source
cells and full actual capture environment keep their original identities. -/
theorem environments_prefix {catalog : SourceCoreDataCatalog.Catalog}
    {definitions : DataEnvironment} {mapping : LocationMap} {world : StoreTyping}
    {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (leading : Core.Context)
    (same : NativeExpressionContextSupport.Agrees leading.length leading administrative) :
    DataHeap.EnvRepresents catalog mapping world leading scope environment
      (canonical.take (scope.length + leading.length)) definitions := by
  induction related with
  | nil typed => simpa only [List.length_nil, Nat.zero_add] using (DataHeap.EnvRepresentsIn.nil (typed_prefix leading typed same))
  | cons reference _ ih => simpa only [List.length_cons, Nat.add_right_comm, List.take_succ_cons] using (DataHeap.EnvRepresentsIn.cons reference ih)
  | internal reference absent _ ih => simpa only [List.length_cons, Nat.add_right_comm, List.take_succ_cons] using (DataHeap.EnvRepresentsIn.internal reference absent ih)

theorem agrees_prefix {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (bound : Nat) :
    EnvironmentsAgree ξ (canonical.take bound) actual := by
  intro index value found
  apply agrees
  simp only [List.getElem?_take, Option.ite_none_right_eq_some] at found
  exact found.2

open RecursiveNamedCatalog RecursiveNamedLambdaFormationEntries

def nativePrefix (caller : Header indexed.ancestry values indexed.layouts.definitions program) : Core.Context :=
  caller.named.signature.parameterType :: indexed.base.globals.map (·.referenceType) ++ [.cell indexed.ancestry.layout.frame.type]

/-- The exact bundle, all inventory globals and the independent frame reference
fix only the used administrative prefix. Any unused native suffix is arbitrary. -/
theorem entry_prefix_for
    {caller : Header indexed.ancestry values indexed.layouts.definitions program}
    {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    {context : Core.Context} {environment : Dynamic.Environment}
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world context scope environment canonical indexed.layouts.definitions) :
    NativeExpressionContextSupport.Agrees (nativePrefix caller).length (nativePrefix caller) context := by
  have typed := related.runtime_hasTypes.type_tags
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (SourceCoreLocalCell.coreContext scope ++ context)[index]? = some value.type := by
    rw [← typed]
    simp [found]
  intro index smaller
  cases index with
  | zero =>
    have bundle := entry.bundle
    rw [typed] at bundle
    simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append] using bundle
  | succ slot =>
    have bound : slot < indexed.base.globals.length + 1 := by
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map,
        List.length_nil] at smaller
      omega
    by_cases globalSlot : slot < indexed.base.globals.length
    · let signature := indexed.base.globals[slot]
      have selected : indexed.base.globals[slot]? = some signature := List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
      obtain ⟨target, member, sameSlot, sameSignature⟩ := complete slot signature selected
      have found := entry.catalog.globals target member
      have atType := tag found
      rw [sameSlot] at atType
      have outside : ¬ scope.length + 1 + slot < scope.length := by omega
      have offset : scope.length + 1 + slot - scope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        globalSlot, selected, signature, sameSignature, SourceCoreCalls.Signature.referenceType,
        OptionalCell.referenceType, Value.type] using atType
    · have last : slot = indexed.base.globals.length := by omega
      have atType := tag entry.reference
      rw [globals] at atType
      have outside : ¬ scope.length + 1 + indexed.base.globals.length < scope.length := by omega
      have offset : scope.length + 1 + indexed.base.globals.length - scope.length = indexed.base.globals.length + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, nativePrefix, List.getElem?_append, outside, offset,
        last, Value.type] using atType


theorem entry_prefix
    {caller : Header indexed.ancestry values indexed.layouts.definitions program}
    {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    {context : Core.Context} {environment : Dynamic.Environment}
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (entry : Entry (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world context scope environment canonical indexed.layouts.definitions) :
    NativeExpressionContextSupport.Agrees (nativePrefix caller).length (nativePrefix caller) context :=
  entry_prefix_for complete globals (CallableIndexedLambdaNestedFormationEntries.Entry.of_named entry) related

def captures_for
    {caller : Header indexed.ancestry values indexed.layouts.definitions program}
    {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {context actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world context scope environment canonical indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions) :
    Captures indexed mapping world scope environment actual := by
  let represented := environments_prefix related (nativePrefix caller) (entry_prefix_for complete globals entry related)
  let same : EnvironmentsAgree ξ (canonical.take (scope.length + (nativePrefix caller).length)) actual :=
    agrees_prefix agrees (scope.length + (nativePrefix caller).length)
  exact {
    administrative := nativePrefix caller
    canonical := canonical.take (scope.length + (nativePrefix caller).length)
    actualContext := actualContext
    embedding := ξ
    represented := represented
    agrees := same
    respects := TypedLexicalWhile.environment_respects represented.runtime_hasTypes typed same
    typed := typed }


def captures
    {caller : Header indexed.ancestry values indexed.layouts.definitions program}
    {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {context actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (entry : Entry (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world context scope environment canonical indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions) :
    Captures indexed mapping world scope environment actual :=
  captures_for complete globals (CallableIndexedLambdaNestedFormationEntries.Entry.of_named entry) related agrees typed

/-- The actual finite capture retains all catalog slots and the same physical
frame. Slot bounds are static and independent of native environment typing. -/
theorem capture_globals_for
    {caller : Header indexed.ancestry values indexed.layouts.definitions program}
    {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {context actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world context scope environment canonical indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions) :
    CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 scope
      (captures_for complete globals entry related agrees typed).canonical entry.catalog.authority.frameLocation := by
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 scope canonical
      entry.catalog.authority.frameLocation :=
    ⟨entry.catalog.globals, by simpa only [globals] using entry.reference⟩
  apply observed.take
  · intro header member
    have bound := slots header member
    simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  · simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega


theorem capture_globals
    {caller : Header indexed.ancestry values indexed.layouts.definitions program}
    {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
    {locations : Locations} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {context actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
    (entry : Entry (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world context scope environment canonical indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions) :
    CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 scope
      (captures complete globals entry related agrees typed).canonical entry.catalog.authority.frameLocation :=
  capture_globals_for complete globals slots (CallableIndexedLambdaNestedFormationEntries.Entry.of_named entry) related agrees typed

/-- Actual compiled preparation relates the ordered global and function rows.
Every retained Header's real selected slot then has the required finite bound. -/
theorem cached_capture_slots (cached : SourceCoreUnifiedCompilation.Compiled)
    {values : SourceCoreCompatibleValues.Context} {program : Program}
    (headers : Inventory cached.indexed.ancestry values cached.indexed.layouts.definitions program) :
    ∀ header, header ∈ headers → header.slot < cached.indexed.base.globals.length := by
  intro header _member
  rw [CallableIndexedPreparedInventories.cached_globals, List.length_map]
  exact (List.getElem?_eq_some_iff.mp header.selected).1

section Lambda
variable {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
  {locations : Locations (ambient := CallableIndexedAmbient.ambientDefinitions indexed)}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}

/-- This receipt contains the actual lambda compiler output and its static body
at the finite named prefix. The source capture environment is supplied only
when the original formation is evaluated. -/
structure LambdaWith
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  code : Code indexed (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
    scope (nativePrefix caller)
  body : CallableIndexedLambdaStaticBodySupport.BodyWith expressionSyntax certificates code program registry faults
  compilation : code.compilation = CallableIndexedNamedGeneration.context indexed caller.named
  active : code.active = []
  identifier : code.id = id
  emitted : code.lowered = lowered
  sourceType : code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
  nativeType : lowered.type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore
  ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions []
  coercions : code.sourceNode.coercions = []
  snapshots : code.policy.snapshotLambda code.id = true

theorem site_native_type {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId}
    (site : CallableIndexedLambdaGeneration.Site indexed caller.named parameters result statements
      context evidence [] scope (nativePrefix caller)) :
    site.code.lowered.type = CallableContract.functionType
      site.code.receipt.parameterCore site.code.receipt.resultCore := by
  have checked := site.code.receipt.checked
  rw [site.code.callables] at checked
  unfold SourceCoreBasic.ensureType at checked
  have reported : site.code.reported = CallableContract.functionType
      site.code.receipt.parameterCore site.code.receipt.resultCore := by
    split at checked
    · assumption
    · cases checked
  have nativeType : site.code.lowered.type = site.code.reported :=
    congrArg SourceCoreBasic.LoweredExpr.type site.code.receipt.emitted
  exact nativeType.trans reported

/-- The actual contextual generation site supplies every compiler field. The
independent source annotation and complete static body stay explicit. -/
theorem LambdaWith.of_site
    {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId}
    (site : CallableIndexedLambdaGeneration.Site indexed caller.named parameters result statements
      context evidence [] scope (nativePrefix caller))
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith expressionSyntax certificates site.code program registry faults)
    (sourceType : site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence []))
    (requirements : site.code.sourceNode.requirements = [])
    (coercions : site.code.sourceNode.coercions = []) :
    Nonempty (LambdaWith expressionSyntax certificates (registry := registry) (faults := faults) caller context evidence scope
      site.code.id site.code.lowered) := by
  have nativeType := site_native_type site
  exact ⟨{
    parameters := parameters, result := result, statements := statements, code := site.code,
    body := body, compilation := site.compilation, active := site.active,
    identifier := rfl, emitted := rfl, sourceType := sourceType, nativeType := nativeType,
    ordinary := by rw [requirements, coercions]; rfl,
    coercions := coercions, snapshots := site.snapshots }⟩

structure Lambda (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  code : Code indexed (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
    scope (nativePrefix caller)
  body : CallableIndexedLambdaRuntimeBody.Body code program registry faults
  compilation : code.compilation = CallableIndexedNamedGeneration.context indexed caller.named
  active : code.active = []
  identifier : code.id = id
  emitted : code.lowered = lowered
  sourceType : code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
  nativeType : lowered.type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore
  ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions []
  coercions : code.sourceNode.coercions = []
  snapshots : code.policy.snapshotLambda code.id = true

/-- The actual contextual generation site supplies every compiler field. The
independent source annotation and complete static body stay explicit. -/
theorem Lambda.of_site {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId}
    (site : CallableIndexedLambdaGeneration.Site indexed caller.named parameters result statements
      context evidence [] scope (nativePrefix caller))
    (body : CallableIndexedLambdaRuntimeBody.Body site.code program registry faults)
    (sourceType : site.code.sourceNode.type = FunctionValues.sourceType
      (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence []))
    (requirements : site.code.sourceNode.requirements = [])
    (coercions : site.code.sourceNode.coercions = []) :
    Nonempty (Lambda (registry := registry) (faults := faults) caller context evidence scope
      site.code.id site.code.lowered) := by
  have nativeType := site_native_type site
  exact ⟨{
    parameters := parameters, result := result, statements := statements, code := site.code,
    body := body, compilation := site.compilation, active := site.active,
    identifier := rfl, emitted := rfl, sourceType := sourceType, nativeType := nativeType,
    ordinary := by rw [requirements, coercions]; rfl,
    coercions := coercions, snapshots := site.snapshots }⟩


def Lambda.formed {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure caller.named head.parameters head.result head.statements context evidence environment

def Lambda.actualCode {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Code indexed (head.formed environment) scope (nativePrefix caller) :=
  recaptureCode head.code environment

def Lambda.history {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (entry : Entry (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1
      scope mapping world heap store canonical) (environment : Dynamic.Environment) : History (head.actualCode environment) where
  native := entry.catalog.authority.current
  ghost := .named entry.origin
  metadata := CallableIndexedNamedGeneration.state caller.named
  carried := entry.history
  source := rfl
  owner := by
    change caller.named.signature.key = head.code.compilation.owner
    rw [head.compilation]
    rfl
  active := head.active.symm

theorem Lambda.reference_index {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered) :
    head.code.referenceIndex = scope.length + 1 + indexed.base.globals.length := by
  simp only [Code.referenceIndex, head.compilation, SourceCoreCallableIndexedAncestry.creationReferenceIndex,
    CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext]

theorem Lambda.reference {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (entry : Entry (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1
      scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope environment canonical indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions) :
    (captures complete globals entry related agrees typed).canonical[(head.actualCode environment).referenceIndex]? =
      some (.cellRef indexed.ancestry.layout.frame.type entry.catalog.authority.frameLocation) := by
  have bound : head.code.referenceIndex < scope.length + (nativePrefix caller).length := by
    rw [Lambda.reference_index head]
    simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  change (canonical.take (scope.length + (nativePrefix caller).length))[head.code.referenceIndex]? = _
  rw [List.getElem?_take, if_pos bound, Lambda.reference_index head, ← globals]
  exact entry.reference

/-- Source lambda inversion is indexed by the actual closure fields in Code:
the value is the closure over the copies of the creation environment. No body
semantics or reconstructed source context is needed. -/
theorem source_value_of_code
    (code : Code indexed function scope administrative)
    (unique : NodeOccurrencesUnique function.source)
    (emptyCoercions : code.sourceNode.coercions = [])
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (evaluation : Dynamic.ExpressionEvaluates program function.context function.evidence
      function.source environment before code.id value after) :
    ∃ captured, value = .closure {function with captured := captured} ∧
      Dynamic.EnvironmentCopies function.source environment before captured after := by
  have contains := lookupExpression?_sound code.sourceFound
  cases evaluation with
  | intro found raw coercions =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique contains))
    subst same
    rw [emptyCoercions] at coercions
    cases coercions
    rw [code.sourceForm] at raw
    cases raw with
    | lambda _ snapshot => exact ⟨_, rfl, snapshot⟩
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique contains))
    subst same
    rw [code.sourceForm] at form
    cases form

/-- The actual lambda form and empty coercion path exclude every fault branch. -/
theorem excludes_fault_of_code
    (code : Code indexed function scope administrative)
    (unique : NodeOccurrencesUnique function.source)
    (emptyCoercions : code.sourceNode.coercions = [])
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program function.context function.evidence
      function.source function.captured before code.id reason after) : False := by
  have contains := lookupExpression?_sound code.sourceFound
  cases failed with
  | missing absent => exact Dynamic.ExpressionAbsentIn.excludes_contains absent contains
  | form found raw =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique contains))
    subst same
    rw [code.sourceForm] at raw
    cases raw
  | coercion found _ failed =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique contains))
    subst same
    rw [emptyCoercions] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique contains))
    subst same
    rw [code.sourceForm] at form
    cases form


theorem Lambda.source_value {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source caller.named))
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (evaluation : Dynamic.ExpressionEvaluates program context evidence
      (CallableIndexedNamedGeneration.source caller.named) environment before id value after) :
    ∃ captured, value = .closure (head.formed captured) ∧
      Dynamic.EnvironmentCopies (CallableIndexedNamedGeneration.source caller.named) environment before captured after := by
  apply source_value_of_code (head.actualCode environment) unique head.coercions
  change Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
    environment before head.code.id value after
  simpa only [head.identifier] using evaluation

theorem Lambda.excludes_fault {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source caller.named))
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context evidence
      (CallableIndexedNamedGeneration.source caller.named) environment before id reason after) : False := by
  apply excludes_fault_of_code (head.actualCode environment) unique head.coercions
  change Dynamic.ExpressionFaults program context evidence (CallableIndexedNamedGeneration.source caller.named)
    environment before head.code.id reason after
  simpa only [head.identifier] using failed

/-- Formation copies the captured cells and stores the complete static body
over the copies in the same fixed function model used by the heap. The
original native environment is never shortened. -/
theorem Lambda.formation {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (profile : values.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (entry : Entry (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1
      scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope environment canonical indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry
      (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile)) mapping world heap store) :
    ∃ value captured finalHeap finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
        environment heap id (.closure (head.formed captured)) finalHeap ∧
      Dynamic.EnvironmentCopies (CallableIndexedNamedGeneration.source caller.named) environment heap captured
        finalHeap ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word value) finalStore ∧
      CompatiblePayload.ValueRep values.checked registry
        (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile)
        finalMap finalWorld head.code.sourceNode.type (.closure (head.formed captured)) value lowered.type ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry
        (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile))
        finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap finalHeap := by
  let current := captures complete globals entry related agrees typed
  let code := head.actualCode environment
  let history := head.history entry environment
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation current code history head.snapshots
    (Lambda.reference_index head) heaps (head.reference complete globals entry related agrees typed)
    entry.catalog.authority.frame.read
  let body : CallableIndexedLambdaRuntimeBody.Body formed.closureCode program registry faults :=
    recaptureBody head.code head.body formed.captured
  obtain ⟨source, evaluated, represented⟩ := CallableIndexedLambdaRuntimeValues.formation indexed program registry
    faults formed body profile heaps.runtime_hasTypes head.ordinary head.coercions
  refine ⟨CallableIndexedLambdaValues.value code formed.embedding history.native formed.closureActual,
    formed.captured, formed.finalHeap, formed.finalStore, formed.finalMap, formed.finalWorld, ?_, formed.copy, ?_, ?_,
    formed.heaps, formed.maps, formed.worlds, formed.frame, formed.copy.metadata_extends⟩
  · change Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
      environment heap head.code.id (.closure (head.formed formed.captured)) formed.finalHeap at source
    simpa only [head.identifier] using source
  · exact Eq.mp (congrArg (fun expression => Evaluates actual store expression
      (.inRight .word (CallableIndexedLambdaValues.value code formed.embedding history.native formed.closureActual))
        formed.finalStore)
      (congrArg (fun output : SourceCoreBasic.LoweredExpr => output.expression.rename ξ) head.emitted)) evaluated
  · rw [head.sourceType, head.nativeType]
    exact .function represented

def Lambdas (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered)

/-- Existing call heads keep their original complete receipts. Lambda formation
is a leaf of the same call family and does not add a recursive body premise. -/
inductive Head (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (prior : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | existing {scope id lowered} (head : prior children scope id lowered) :
      Head caller context evidence prior children scope id lowered
  | lambda {scope id lowered}
      (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered) :
      Head caller context evidence prior children scope id lowered

theorem Lambda.projected {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (alignment : FormationHeader (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
      (CallableIndexedNamedGeneration.context indexed caller.named) 0)
    {node : ExpressionNode} (found : caller.function.source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  rw [alignment.source] at found
  have sourceFound : (CallableIndexedNamedGeneration.source caller.named).lookupExpression? id = some head.code.sourceNode := by
    simpa only [CallableIndexedLambdaGeneration.closure, head.identifier] using head.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  rw [head.sourceType, head.nativeType]
  exact head.code.projection

theorem Lambda.native {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (administrative : Core.Context)
    (same : NativeExpressionContextSupport.Agrees
      (SourceCoreLocalCell.coreContext scope ++ nativePrefix caller).length
      (SourceCoreLocalCell.coreContext scope ++ nativePrefix caller)
      (SourceCoreLocalCell.coreContext scope ++ administrative)) :
    CompatibleExpressionScalarNativeTyping.NativeTyping indexed.layouts.definitions
      (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  have native := NativeExpressionContextSupport.typing head.code.typed (NativeExpressionContextSupport.of_typing head.code.typed) same
  have wellFormed := CompatibleExpressionCertificateNativeTyping.project_wellFormed head.code.projection
  have extended := wellFormed.extend_definitions (CallableIndexedAmbient.ambientDefinitions indexed).basePrefix
  refine ⟨?_, ?_⟩
  · rw [head.nativeType]
    exact extended
  · have changed := Eq.mp (congrArg (fun expression => HasType
        (SourceCoreLocalCell.coreContext scope ++ administrative) expression
        (LanguageResult.resultType (CallableContract.functionType head.code.receipt.parameterCore head.code.receipt.resultCore))
        indexed.layouts.definitions)
        (congrArg (fun output : SourceCoreBasic.LoweredExpr => output.expression) head.emitted)) native
    rw [head.nativeType]
    exact changed

theorem preserves_at
    (profile : values.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (alignment : FormationHeader (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller (CallableIndexedNamedGeneration.context indexed caller.named) 0)
    (size : Nat) (unique : NodeOccurrencesUnique caller.function.source) :
    RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile))
      program context evidence caller.function.source (Lambdas (registry := registry) (faults := faults) caller context evidence) faults
      (protectedEntry (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1) := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    related heaps locals agrees typed installed trace
  obtain ⟨head⟩ := certified
  obtain ⟨entry⟩ := installed
  have sourceFound : (CallableIndexedNamedGeneration.source caller.named).lookupExpression? id = some head.code.sourceNode := by
    simpa only [CallableIndexedLambdaGeneration.closure, head.identifier] using head.code.sourceFound
  rw [alignment.source] at found unique trace
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  cases trace.sound with
  | value evaluated =>
    obtain ⟨captured, rfl, copy⟩ := head.source_value unique evaluated
    obtain ⟨value, formedCaptured, finalHeap, finalStore, finalMap, finalWorld, _, formedCopy, native, represented,
        finalHeaps, maps, worlds, frame, metadata⟩ :=
      head.formation profile complete alignment.globals entry related agrees typed heaps
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formedCopy
    exact ⟨_, finalStore, finalMap, finalWorld, native, .value represented, finalHeaps, maps, worlds, frame, metadata⟩
  | fault failed => exact False.elim (head.excludes_fault unique failed)

theorem reflects_at
    (profile : values.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (alignment : FormationHeader (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller (CallableIndexedNamedGeneration.context indexed caller.named) 0)
    (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile))
      program context evidence caller.function.source (Lambdas (registry := registry) (faults := faults) caller context evidence) faults
      (protectedEntry (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1) := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    related heaps locals agrees typed installed completed
  obtain ⟨head⟩ := certified
  obtain ⟨entry⟩ := installed
  have sourceFound : (CallableIndexedNamedGeneration.source caller.named).lookupExpression? id = some head.code.sourceNode := by
    simpa only [CallableIndexedLambdaGeneration.closure, head.identifier] using head.code.sourceFound
  rw [alignment.source] at found
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨nativeValue, captured, finalHeap, formedStore, finalMap, finalWorld, source, _, native, represented,
      finalHeaps, maps, worlds, frame, metadata⟩ :=
    head.formation profile complete alignment.globals entry related agrees typed heaps
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound native
  have original : Dynamic.ExpressionEvaluatesOutcome program context evidence caller.function.source environment before id
      (.value (.closure (head.formed captured))) finalHeap := by
    rw [alignment.source]
    exact .value source
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size original
  exact ⟨sourceSize, _, finalHeap, finalMap, finalWorld, sized, .value represented, finalHeaps, maps, worlds, frame,
    metadata⟩

section GenericLambda
variable {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}

def LambdaWith.formed {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : LambdaWith expressionSyntax certificates (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure caller.named head.parameters head.result head.statements context evidence environment

def LambdaWith.actualCode {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : LambdaWith expressionSyntax certificates (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Code indexed (head.formed environment) scope (nativePrefix caller) :=
  recaptureCode head.code environment

def LambdaWith.history {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    (head : LambdaWith expressionSyntax certificates (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (entry : Entry (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1
      scope mapping world heap store canonical) (environment : Dynamic.Environment) : History (head.actualCode environment) where
  native := entry.catalog.authority.current
  ghost := .named entry.origin
  metadata := CallableIndexedNamedGeneration.state caller.named
  carried := entry.history
  source := rfl
  owner := by
    change caller.named.signature.key = head.code.compilation.owner
    rw [head.compilation]
    rfl
  active := head.active.symm

theorem LambdaWith.reference_index {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : LambdaWith expressionSyntax certificates (registry := registry) (faults := faults) caller context evidence scope id lowered) :
    head.code.referenceIndex = scope.length + 1 + indexed.base.globals.length := by
  simp only [Code.referenceIndex, head.compilation, SourceCoreCallableIndexedAncestry.creationReferenceIndex,
    CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext]

theorem LambdaWith.reference {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
    (head : LambdaWith expressionSyntax certificates (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (entry : Entry (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1
      scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope environment canonical indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions) :
    (captures complete globals entry related agrees typed).canonical[(head.actualCode environment).referenceIndex]? =
      some (.cellRef indexed.ancestry.layout.frame.type entry.catalog.authority.frameLocation) := by
  have bound : head.code.referenceIndex < scope.length + (nativePrefix caller).length := by
    rw [LambdaWith.reference_index head]
    simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  change (canonical.take (scope.length + (nativePrefix caller).length))[head.code.referenceIndex]? = _
  rw [List.getElem?_take, if_pos bound, LambdaWith.reference_index head, ← globals]
  exact entry.reference

/-- The body keeps the actual Code view, canonical Tree and emitted flow while
formation replaces only the captured source environment. -/
def LambdaWith.actualBody {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : LambdaWith expressionSyntax certificates (registry := registry) (faults := faults)
      caller context evidence scope id lowered) (environment : Dynamic.Environment) :
    CallableIndexedLambdaStaticBodySupport.BodyWith expressionSyntax certificates
      (head.actualCode environment) program registry faults :=
  recaptureBodyWith head.code head.body environment

/-- Formation supplies the ordered capture condition from the real catalog
entry. The same-Code/History origin receipt is independent and stays explicit. -/
theorem LambdaWith.capture_condition
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical actual : Environment} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {ξ : Renaming}
    (head : LambdaWith expressionSyntax certificates (registry := registry) (faults := faults)
      caller context evidence scope id lowered)
    (origin : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
      (code : Code indexed function scope administrative) → History code → Prop)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
    (entry : Entry (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1
      scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope environment canonical indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)
    (originAt : origin (head.actualCode environment) (head.history entry environment)) :
    CallableIndexedLambdaRuntimeValues.captureCondition indexed program
      (fun {_ _ _} code => CallableIndexedLambdaStaticBodySupport.BodyWith expressionSyntax certificates code program registry faults)
      origin (headers := headers) (locations := locations) 1
      (captures complete globals entry related agrees typed) (head.actualCode environment)
      (head.history entry environment) (head.actualBody environment) :=
  ⟨originAt, entry.catalog.authority.frameLocation, capture_globals complete globals slots entry related agrees typed⟩

end GenericLambda

end Lambda
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationTreeMeaning
/-! Lambda formation belongs to the existing expression tree. The same static
code retains its complete builtin body receipt. Actual named-call output supplies
aligned callee state; neither a native type nor an arbitrary BodyState supplies
source history. Indirect lambda application remains a separate boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationTreeMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedLambdaFormationHeads

variable {values : SourceCoreCompatibleValues.Context}
  {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program} {locations : Locations}
  {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

abbrev Calls (authenticated : Bool) := Head (registry := registry) (faults := faults) caller context evidence
  (RecursiveNamedCallEvidenceHeads.Calls (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (if authenticated then some evidence else none) headers
    (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source context)

abbrev Expressions (authenticated : Bool) :=
  RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor (Calls (caller := caller) (headers := headers)
    (context := context) (evidence := evidence) (registry := registry) (faults := faults) authenticated)
    fuel values caller.function.source context solved reasonAt

local notation "P" => RecursiveNamedLambdaFormationEntries.protectedEntry
  (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1

variable (profile : values.checked.catalog.callableContracts = true)
local notation "F" => CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile

/-- Local scopes are shared exactly; only the used administrative prefix is
required to agree. An arbitrary unused administrative suffix remains present. -/
theorem agrees_scope (leading : Core.Context) {source target : Core.Context}
    (same : NativeExpressionContextSupport.Agrees source.length source target) :
    NativeExpressionContextSupport.Agrees (leading ++ source).length (leading ++ source) (leading ++ target) := by
  induction leading with
  | nil => exact same
  | cons head tail ih => simpa only [List.cons_append, List.length_cons] using ih.lift head

theorem projected (authenticated : Bool)
    (alignment : RecursiveNamedLambdaFormationEntries.FormationHeader
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
      (CallableIndexedNamedGeneration.context indexed caller.named) 0)
    {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (head : Calls (caller := caller) (headers := headers) (context := context) (evidence := evidence)
      (registry := registry) (faults := faults) authenticated children scope id lowered)
    (found : caller.function.source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  cases head with
  | lambda head => exact head.projected alignment found
  | existing head =>
    cases authenticated with
    | false =>
      exact RecursiveNamedCallEvidenceHeads.projected (evidence := []) (.ordinary head) found
    | true =>
      exact RecursiveNamedCallEvidenceHeads.projected head found

theorem native (authenticated : Bool)
    {administrative : Core.Context}
    (slots : RecursiveNamedExpressionNativeTyping.Slots (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers
      (CallableIndexedNamedGeneration.context indexed caller.named) administrative)
    (same : NativeExpressionContextSupport.Agrees (nativePrefix caller).length (nativePrefix caller) administrative)
    {children : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Calls (caller := caller) (headers := headers) (context := context) (evidence := evidence)
      (registry := registry) (faults := faults) authenticated children scope id lowered)
    (childrenTyped : ∀ child code, children scope child code →
      CompatibleExpressionScalarNativeTyping.NativeTyping indexed.layouts.definitions
        (SourceCoreLocalCell.coreContext scope ++ administrative) code) :
    CompatibleExpressionScalarNativeTyping.NativeTyping indexed.layouts.definitions
      (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  cases head with
  | lambda head => exact head.native administrative (agrees_scope _ same)
  | existing head =>
    cases authenticated with
    | false =>
      exact RecursiveNamedCallEvidenceHeads.native_at (evidence := evidence) (CallableIndexedAmbient.ambientDefinitions indexed).basePrefix slots (.ordinary head) childrenTyped
    | true =>
      exact RecursiveNamedCallEvidenceHeads.native_at (evidence := evidence) (CallableIndexedAmbient.ambientDefinitions indexed).basePrefix slots head childrenTyped

section Compiler
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates

def lambdaForm : ExpressionForm → Prop
  | .lambda _ _ _ => True
  | _ => False

/-- The actual lambda compiler output retains its Code and complete static Body.
Every other form and every ordered child uses the same sole compiler recursion. -/
theorem of_functions (authenticated : Bool)
    (alignment : RecursiveNamedLambdaFormationEntries.FormationHeader
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
      (CallableIndexedNamedGeneration.context indexed caller.named) 0)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {admitted : ExpressionId → Prop}
    (admission : AdmissionFor lambdaForm caller.function.source admitted) (coverage : ReachedCoverage headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers context)
    (emptyEvidence : SelectedEmptyEvidence (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source admitted)
    (order : ∀ id callee arguments instantiation node, admitted id → caller.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered (CallableIndexedNamedGeneration.context indexed caller.named).plan instantiation)
    (unique : NodeOccurrencesUnique caller.function.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations caller.function.source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw caller.function.source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw caller.function.source context (CompatibleExpressionBuiltins.Syntax caller.function.source))
    (selectedValid : SelectedDeclarationLaw (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source context admitted)
    (policyFor : PolicyForWith (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (headers := headers) (if authenticated then some evidence else none) policy (CallableIndexedNamedGeneration.context indexed caller.named) readFuel values caller.function.source context scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callableProfile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax caller.function.source id → caller.function.source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → caller.function.source.lookupExpression? id = some node → node.coercions = [])
    (lambdas : ∀ fuel id node lowered, admitted id → caller.function.source.lookupExpression? id = some node →
      lambdaForm node.form → ExpressionHasType caller.function.source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
        (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source scope id reasonAt = .ok lowered →
      Nonempty (Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered))
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : caller.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType caller.function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source scope id reasonAt = .ok lowered) :
    Expressions (caller := caller) (headers := headers) (context := context) (evidence := evidence)
      (registry := registry) (faults := faults) (fuel := readFuel)
      (solved := (CallableIndexedNamedGeneration.context indexed caller.named).solvedRequirements) (reasonAt := reasonAt)
      authenticated scope id lowered := by
  apply tree_of_functions_at_runtime_with_calls (if authenticated then some evidence else none)
    (Calls (caller := caller) (headers := headers) (context := context) (evidence := evidence)
      (registry := registry) (faults := faults) authenticated)
    (fun head => .existing head) (fun {_ _ _ _ _} head found => projected authenticated alignment head found)
    lambdaForm admission coverage sourceTypes emptyEvidence order unique declarations signatures
    constructorValid fragmentValid selectedValid policyFor native active callableProfile fragmentCoercions coercions
    (fun fuel id node lowered allowed found form typed accepted => by
      obtain ⟨head⟩ := lambdas fuel id node lowered allowed found form typed accepted
      exact .lambda head) allowed found typed accepted
end Compiler

section Meaning
variable (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (alignments : ∀ header, header ∈ headers → RecursiveNamedLambdaFormationEntries.FormationHeader
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed header
    (CallableIndexedNamedGeneration.context indexed header.named) 0)
  (callerAligned : RecursiveNamedLambdaFormationEntries.FormationHeader
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
    (CallableIndexedNamedGeneration.context indexed caller.named) 0)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (unique : NodeOccurrencesUnique caller.function.source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include owners complete alignments callerAligned unique in
theorem call_preserves_at (authenticated : Bool) (idsUnique : RequirementIdsUnique context)
    {children : GenericExpressionMeaning.Certificate} (budget size : Nat) (within : size ≤ budget)
    (childrenMeaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry F)
        program context evidence caller.function.source children faults P))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := 0) F registry header faults
        (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) F registry))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry F)
      program context evidence caller.function.source
      (Calls (caller := caller) (headers := headers) (context := context) (evidence := evidence)
        (registry := registry) (faults := faults) authenticated children) faults P := by
  intro scope id lowered head
  cases head with
  | lambda head => exact RecursiveNamedLambdaFormationHeads.preserves_at profile complete callerAligned size unique ⟨head⟩
  | existing head =>
    have forget := fun {scope mapping world heap store canonical} (entry : P scope mapping world heap store canonical) =>
      RecursiveNamedLambdaFormationEntries.catalog entry
    have authorized : ∀ header, header ∈ headers → BodyAuthorization
        (headers := headers) (locations := locations) (capturePrefix := 0) F registry header
        (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) F registry) := by
      intro header member
      exact RecursiveNamedLambdaFormationEntries.authorize F registry (alignments header member)
    intro node found
    cases authenticated with
    | false =>
      exact RecursiveNamedExpressionHeadBounds.preserves_at_for F P RecursiveNamedLambdaFormationEntries.transport forget
        _ authorized budget size within unique owners childrenMeaning bodies head found
    | true =>
      exact RecursiveNamedCallEvidenceHeads.preserves_at_for F P RecursiveNamedLambdaFormationEntries.transport forget
        _ authorized budget size within idsUnique unique owners childrenMeaning bodies head found

include complete alignments callerAligned in
theorem call_reflects_at (authenticated : Bool)
    {children : GenericExpressionMeaning.Certificate} (budget size : Nat) (within : size ≤ budget)
    (childrenMeaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry F)
        program context evidence caller.function.source children faults P))
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := 0) F registry header faults
        (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) F registry))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry F)
      program context evidence caller.function.source
      (Calls (caller := caller) (headers := headers) (context := context) (evidence := evidence)
        (registry := registry) (faults := faults) authenticated children) faults P := by
  intro scope id lowered head
  cases head with
  | lambda head => exact RecursiveNamedLambdaFormationHeads.reflects_at profile complete callerAligned size ⟨head⟩
  | existing head =>
    have forget := fun {scope mapping world heap store canonical} (entry : P scope mapping world heap store canonical) =>
      RecursiveNamedLambdaFormationEntries.catalog entry
    have authorized : ∀ header, header ∈ headers → BodyAuthorization
        (headers := headers) (locations := locations) (capturePrefix := 0) F registry header
        (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) F registry) := by
      intro header member
      exact RecursiveNamedLambdaFormationEntries.authorize F registry (alignments header member)
    intro node found
    cases authenticated with
    | false =>
      exact RecursiveNamedExpressionHeadBounds.reflects_at_for F P RecursiveNamedLambdaFormationEntries.transport forget
        _ authorized budget size within childrenMeaning bodies head found
    | true =>
      exact RecursiveNamedCallEvidenceHeads.reflects_at_for F P RecursiveNamedLambdaFormationEntries.transport forget
        _ authorized budget size within childrenMeaning bodies head found

include complete alignments callerAligned extension unique owners uninitialized missing in
theorem preserves_at [FunctionCalls.FaultTokens faults] (authenticated : Bool)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := 0) F registry header faults
        (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) F registry))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry F)
      program context evidence caller.function.source
      (Expressions (caller := caller) (headers := headers) (context := context) (evidence := evidence)
        (registry := registry) (faults := faults) (fuel := fuel) (solved := solved) (reasonAt := reasonAt) authenticated) faults P := by
  apply RecursiveNamedExpressionTreeBounds.preserves_at_with_literals_with_for F extension
    (CallableIndexedLambdaValues.identity_faithful indexed) (CallableIndexedLambdaRuntimeValues.observations indexed program registry faults profile)
    (CallableIndexedLambdaRuntimeValues.runtime_views indexed program registry faults profile) evidence unique uninitialized missing
    _ P (CompatibleExpressionLiteralRuntime.preserves F program context evidence sameLedger runtime unique faults)
    budget size within
  intro certificate child childWithin children
  apply RecursiveNamedExpressionTreeBounds.head_preserves_at_with_calls F extension
    (CallableIndexedLambdaValues.identity_faithful indexed) (CallableIndexedLambdaRuntimeValues.observations indexed program registry faults profile)
    (CallableIndexedLambdaRuntimeValues.runtime_views indexed program registry faults profile) evidence unique missing
    P RecursiveNamedLambdaFormationEntries.transport _ budget child childWithin children
  exact call_preserves_at profile complete alignments callerAligned unique owners authenticated runtime.idsUnique budget child childWithin
    (fun smaller strict => children smaller (Nat.le_of_lt strict)) bodies

include complete alignments callerAligned extension uninitialized missing in
theorem reflects_at [FunctionCalls.FaultTokens faults] (authenticated : Bool)
    (sameLedger : context.solvedRequirements = solved)
    (runtime : RuntimeRequirementLedgerValid context)
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := 0) F registry header faults
        (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) F registry))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry F)
      program context evidence caller.function.source
      (Expressions (caller := caller) (headers := headers) (context := context) (evidence := evidence)
        (registry := registry) (faults := faults) (fuel := fuel) (solved := solved) (reasonAt := reasonAt) authenticated) faults P := by
  apply RecursiveNamedExpressionTreeBounds.reflects_at_with_literals_with_for F extension
    (CallableIndexedLambdaValues.identity_faithful indexed) (CallableIndexedLambdaRuntimeValues.observations indexed program registry faults profile)
    (CallableIndexedLambdaRuntimeValues.runtime_views indexed program registry faults profile) evidence uninitialized missing
    _ P (CompatibleExpressionLiteralRuntime.reflects F program context evidence sameLedger runtime caller.function.source faults)
    budget size within
  intro certificate child childWithin children
  apply RecursiveNamedExpressionTreeBounds.head_reflects_at_with_calls F extension
    (CallableIndexedLambdaValues.identity_faithful indexed) (CallableIndexedLambdaRuntimeValues.observations indexed program registry faults profile)
    (CallableIndexedLambdaRuntimeValues.runtime_views indexed program registry faults profile) evidence missing
    P RecursiveNamedLambdaFormationEntries.transport _ budget child childWithin children
  exact call_reflects_at profile complete alignments callerAligned authenticated budget child childWithin
    (fun smaller strict => children smaller (Nat.le_of_lt strict)) bodies

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationTreeMeaning
end
