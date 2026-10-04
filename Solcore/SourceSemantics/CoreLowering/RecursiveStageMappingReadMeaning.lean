import Solcore.SourceSemantics.CoreLowering.RecursiveStagePrimitiveMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCompletion

/-! Staged mapping reads reconstruct their source initialization from the
original completed Core derivation. The static encoder receipt authenticates
its empty mapping, and the actual native write retains the entire heap. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingReadMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleMapping.VirtualRoot

/-- Pure quoted values are recovered by inspecting their original execution.
No second execution or determinism argument is used. -/
theorem quoted_completed {native result : Value} {code : Expr}
    (quoted : Quoted native code) {environment : Environment} {before after : Store}
    (evaluated : Evaluates environment before code result after) : result = native ∧ after = before := by
  exact CompatibleExpressionReadCompletion.quoted_completed quoted evaluated

private theorem var_completed {environment : Environment} {before after : Store}
    {index : Nat} {expected result : Value}
    (lookup : environment[index]? = some expected)
    (evaluated : Evaluates environment before (.var index) result after) : result = expected ∧ after = before := by
  exact CompatibleExpressionReadCompletion.var_completed lookup evaluated

private theorem load_completed {environment : Environment} {before after : Store}
    {index target : Nat} {type : Ty} {result : Value}
    (lookup : environment[index]? = some (.cellRef type target))
    (evaluated : Evaluates environment before (.loadCell (.var index)) result after) :
    before.read? target = some result ∧ after = before := by
  exact CompatibleExpressionReadCompletion.load_completed lookup evaluated

/-- The original lazy-read code either keeps its present payload or writes the
quoted empty value to that same cell. The original write determines the final
store, including all unrelated and administrative cells. -/
theorem read_completed {environment : Environment} {before after : Store}
    {index target : Nat} {type : Ty} {optional empty result : Value} {literal : Expr}
    (lookup : environment[index]? = some (.cellRef type target))
    (read : before.read? target = some optional) (quoted : Quoted empty literal)
    (evaluated : Evaluates environment before
      (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal) result after) :
    (∃ annotation payload, optional = .inRight annotation payload ∧ result = .inRight .word payload ∧ after = before) ∨
    (∃ annotation payload, optional = .inLeft annotation payload ∧ result = .inRight .word empty ∧
      before.write? target (.inRight .unit empty) = some after) := by
  exact CompatibleExpressionReadCompletion.read_completed lookup read quoted evaluated


variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}

/-- This leaf retains the actual local-read compiler receipt and its independent
raw source binding. Only declared mappings enter this separate family. -/
def Supported : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  ∃ receipt : CompatibleExpressionReads.Certificate fuel values source scope id (reasonAt id) lowered.expression,
    receipt.type = lowered.type ∧ CompatibleExpressionReads.StaticBinding receipt context ∧
    ∃ key value, receipt.declared.scheme.body = .mapping key value

/-- The real compiler and an independently typed, reached mapping declaration
supply the leaf certificate. Coincident native projections do not select it. -/
theorem of_accepted {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId} {declared : TypedBinder} {key value : TypeSystem.Ty}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id) = .ok lowered.expression)
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (typed : ExpressionHasType source context id node.type)
    (form : node.form = .reference name (.local binder))
    (declaration : SourceCoreDataPlaces.rootBinder source binder = .ok declared)
    (declaredType : declared.scheme.body = .mapping key value) :
    Supported (fuel := fuel) (values := values) (source := source) (context := context) (reasonAt := reasonAt) scope id lowered := by
  obtain ⟨certificate, sameType, binding⟩ :=
    CompatibleExpressionReads.loweredRead_of_accepted accepted read unique declarations typed
  have actual := CompatibleExpressionReads.metadata_of_read read
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans actual.found)
  have formed := certificate.form
  rw [nodeEq, form] at formed
  have ⟨_, sameBinder⟩ : name = certificate.name ∧ binder = certificate.binder := by
    simpa only [ExpressionForm.reference.injEq, ReferenceResolution.local.injEq] using formed
  have actualDeclaration := certificate.declaration
  rw [← sameBinder] at actualDeclaration
  have sameDeclaration := Except.ok.inj (actualDeclaration.symm.trans declaration)
  refine ⟨certificate, sameType, binding, key, value, ?_⟩
  rw [sameDeclaration]
  exact declaredType

private theorem quoted_rename {native : Value} {literal : Expr} (quoted : Quoted native literal) (ξ : Renaming) :
    literal.rename ξ = literal := by
  exact CompatibleExpressionReadCompletion.quoted_rename quoted ξ

private theorem mapping_rename {native : Value} {literal : Expr} (quoted : Quoted native literal)
    (index : Nat) (ξ : Renaming) :
    (SourceCoreCompatibleDataExpressions.readMapping (.var index) literal).rename ξ =
      SourceCoreCompatibleDataExpressions.readMapping (.var (ξ index)) literal := by
  exact CompatibleExpressionReadCompletion.mapping_rename quoted index ξ

private theorem cells_write_exists {cells : List Dynamic.Cell} {index : Nat} {cell : Dynamic.Cell}
    (found : Dynamic.Heap.CellAt cells index cell) (value : Dynamic.Value) : ∃ updated,
      Dynamic.Heap.CellsWrite cells index {cell with value := some value} updated := by
  exact CompatibleExpressionReadCompletion.cells_write_exists found value

private theorem writes_exists {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads heap location cell) (value : Dynamic.Value) :
    ∃ after, Dynamic.Heap.Writes heap location (some value) after := by
  exact CompatibleExpressionReadCompletion.writes_exists read value


variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (sameSource : invocation.source = source)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {faults : FunctionCalls.FaultRep}

include sameSource extension in
/-- The original completed mapping read supplies either the stored source value
or the actual empty-mapping write. Reflection never invokes preservation,
constructs a native replay, or uses evaluation determinism. -/
theorem reflects :
    RecursiveStagePrimitiveMeaning.Reflects functions (registry := registry) program stages invocation context
      (Supported (fuel := fuel) (values := values) (source := source) (context := context) (reasonAt := reasonAt)) faults := by
  intro scope id lowered supported root found mapping world administrative environment canonical actual before store ξ result finalStore
    environments heaps locals agrees evaluated
  obtain ⟨certificate, sameType, binding, declaredMapping⟩ := supported
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans (sameSource ▸ found))
  obtain ⟨sourceValue, after, raw, represented, finalHeaps, frame, metadata⟩ :=
    certificate.mapping_completed (faults := faults) functions extension program context invocation.evidence binding declaredMapping
      environments heaps locals agrees evaluated
  have contains : ContainsExpression invocation.source id certificate.node := by
    simpa only [sameSource] using lookupExpression?_sound certificate.metadata.found
  have atomic : Staging.Recursive.AtomicForm certificate.node.form := certificate.form ▸ .reference _ _
  cases represented with
  | value payload =>
    refine ⟨.value sourceValue, after, mapping, world,
      .atomicValue contains atomic certificate.metadata.coercions ?_, .value ?_,
      finalHeaps, .refl _, .refl _, frame, metadata⟩
    · simpa only [sameSource, certificate.metadata.requirements] using raw
    · simpa only [CompatibleAmbientHeap.payloadModel, nodeEq, sameType] using payload

private theorem occurrence_form {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    {node : ExpressionNode} {form : ExpressionForm}
    (unique : NodeOccurrencesUnique invocation.source) (found : invocation.source.lookupExpression? id = some node)
    (owned : Staging.Recursive.Occurrence invocation id form) : node.form = form := by
  obtain ⟨other, contains, formed, _, _⟩ := owned
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact formed

private theorem reference_no_stage {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (unique : NodeOccurrencesUnique invocation.source) (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    {program : Program} {stages : Staging.Recursive.Registry} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {failedScope : Staging.Recursive.Scope} {call : ExpressionId} {reason : Staging.CallGuard.Fault}
    (trace : Staging.Recursive.Expression program stages invocation context environment before id
      (.fault (.stage failedScope call reason)) after) : False := by
  cases trace with
  | tupleFault owned children =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | group owned child =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | pairLeftFault owned child =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | pairRightFault owned first second =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | unaryOperandFault owned child =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | binaryLeftFault owned child =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | binaryRightFault owned first continues second =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | conditional owned test branch =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | conditionalFault owned test =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | calleeFault owned child =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | rejected owned child guard =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | argumentsFault owned child guard children =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same
  | applied owned uncoerced child guard children arity applies =>
    have same := occurrence_form unique found owned
    rw [form] at same
    cases same

include sameSource extension in
/-- Forward mapping-read preservation reuses the ordinary read proof and the
independent staged erasure. A local reference cannot conceal a stage rejection. -/
theorem preserves (unique : NodeOccurrencesUnique source)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    (supported : Supported (fuel := fuel) (values := values) (source := source) (context := context) (reasonAt := reasonAt) scope id code)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? id = some node)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.Outcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrativeContext scope environment canonical ambient.definitions)
    (heaps : GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Staging.Recursive.Expression program stages invocation context environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.expression.rename ξ) value finalStore ∧
      RecursiveStagePrimitiveMeaning.Result functions (registry := registry) finalMap finalWorld node.type code.type faults outcome value ∧
      GenericHeap.HeapRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨certificate, sameType, binding, _⟩ := supported
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans (sameSource ▸ found))
  have plain := fun (outcome : Dynamic.ExpressionOutcome)
      (evaluation : Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence source environment before id outcome after) =>
    certificate.preserves functions extension program context invocation.evidence binding environments heaps locals agrees
      (uninitialized id) unique evaluation
  cases outcome with
  | value output =>
    obtain ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata⟩ :=
      plain _ (.value (sameSource ▸ trace.value_plain))
    cases represented with
    | value payload =>
      refine ⟨_, finalStore, mapping, world, evaluated, .value ?_, finalHeaps, .refl _, .refl _, frame, metadata⟩
      simpa only [CompatibleAmbientHeap.payloadModel, nodeEq, sameType] using payload
  | fault failure =>
    cases failure with
    | semantic reason =>
      obtain ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata⟩ :=
        plain _ (.fault (sameSource ▸ trace.semanticFault_plain))
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, mapping, world, evaluated, ?_, finalHeaps, .refl _, .refl _, frame, metadata⟩
        simpa only [sameType] using (RecursiveStagePrimitiveMeaning.Result.fault (functions := functions) (registry := registry) matched)
    | stage failedScope call reason =>
      exact False.elim (reference_no_stage (sameSource ▸ unique) found (nodeEq ▸ certificate.form) trace)

end Solcore.SourceSemantics.CoreLowering.RecursiveStageMappingReadMeaning
