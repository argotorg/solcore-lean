import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationEntries
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallEvidenceHeads
import Solcore.SourceSemantics.CoreLowering.NativeExpressionContextSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts

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
    Captures indexed mapping world scope environment actual := by
  let represented := environments_prefix related (nativePrefix caller) (entry_prefix complete globals entry related)
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

/-- The actual finite capture retains all catalog slots and the same physical
frame. Slot bounds are static and independent of native environment typing. -/
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
      (captures complete globals entry related agrees typed).canonical entry.catalog.authority.frameLocation := by
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
    coercions := coercions }⟩

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
    coercions := coercions }⟩


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

theorem Lambda.source_value {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source caller.named))
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (evaluation : Dynamic.ExpressionEvaluates program context evidence
      (CallableIndexedNamedGeneration.source caller.named) environment before id value after) :
    value = .closure (head.formed environment) ∧ after = before := by
  have contains := lookupExpression?_sound head.code.sourceFound
  rw [head.identifier] at contains
  cases evaluation with
  | intro found raw coercions =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique contains))
    subst same
    rw [head.coercions] at coercions
    cases coercions
    rw [head.code.sourceForm] at raw
    cases raw
    exact ⟨rfl, rfl⟩
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique contains))
    subst same
    rw [head.code.sourceForm] at form
    cases form

theorem Lambda.excludes_fault {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source caller.named))
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context evidence
      (CallableIndexedNamedGeneration.source caller.named) environment before id reason after) : False := by
  have contains := lookupExpression?_sound head.code.sourceFound
  rw [head.identifier] at contains
  cases failed with
  | missing absent => exact Dynamic.ExpressionAbsentIn.excludes_contains absent contains
  | form found raw =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique contains))
    subst same
    rw [head.code.sourceForm] at raw
    cases raw
  | coercion found _ failed =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique contains))
    subst same
    rw [head.coercions] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique contains))
    subst same
    rw [head.code.sourceForm] at form
    cases form

/-- Formation stores the complete static body in the same fixed function
model used by the heap. The original native environment is never shortened. -/
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
    (stored : RuntimeStoreHasTypes world store indexed.layouts.definitions) :
    ∃ value,
      Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
        environment heap id (.closure (head.formed environment)) heap ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word value) store ∧
      CompatiblePayload.ValueRep values.checked registry
        (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile)
        mapping world head.code.sourceNode.type (.closure (head.formed environment)) value lowered.type := by
  let captured := captures complete globals entry related agrees typed
  let code := head.actualCode environment
  let history := head.history entry environment
  let body : CallableIndexedLambdaRuntimeBody.Body code program registry faults := recaptureBody head.code head.body environment
  obtain ⟨source, evaluated, represented⟩ := CallableIndexedLambdaRuntimeValues.formation (function := head.formed environment) (scope := scope) indexed program registry faults
    captured code history body profile stored (head.reference complete globals entry related agrees typed)
    entry.catalog.authority.frame.read heap head.ordinary head.coercions
  refine ⟨CallableIndexedLambdaValues.value code captured.embedding history.native actual, ?_, ?_, ?_⟩
  · change Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
      environment heap head.code.id (.closure (head.formed environment)) heap at source
    simpa only [head.identifier] using source
  · exact Eq.mp (congrArg (fun expression => Evaluates actual store expression
      (.inRight .word (CallableIndexedLambdaValues.value code captured.embedding history.native actual)) store)
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
    obtain ⟨rfl, rfl⟩ := head.source_value unique evaluated
    obtain ⟨value, _, native, represented⟩ := head.formation profile complete alignment.globals entry related agrees typed heaps.runtime_hasTypes
    exact ⟨_, store, mapping, world, native, .value represented, heaps, .refl _, .refl _, .refl _ _, .refl _⟩
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
  obtain ⟨nativeValue, source, native, represented⟩ := head.formation profile complete alignment.globals entry related agrees typed heaps.runtime_hasTypes
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound native
  have original : Dynamic.ExpressionEvaluatesOutcome program context evidence caller.function.source environment before id
      (.value (.closure (head.formed environment))) before := by
    rw [alignment.source]
    exact .value source
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size original
  exact ⟨sourceSize, _, before, mapping, world, sized, .value represented, heaps, .refl _, .refl _, .refl _ _, .refl _⟩

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
