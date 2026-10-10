import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectFormationReceipts

/-! Formation uses an explicit receiving function model and a positive
closure constructor. The original functions-independent elementary producer
runs once, and the same incoming heap is retained under that receiving model.
No weaker heap model is inverted into stronger global provenance. Reflection
retains its independent Source grade and exact dictionary-bearing packet. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelFormationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (StaticMember)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (qualification : Facet compiled)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (models : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (lift : ∀ {mapping world function native bindings parameter result},
    StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result →
    models.Represents registry mapping world (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result))

/-- This post uses the receiving function model directly. Formation preserves
the incoming heap and constructs only the positive closure representation. -/
structure Post
    {callerProtocol : ProtectedStateTransition.Protocol (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (context : SourceSemantics.Context) (sourceType : TypeSystem.Ty) (type : Ty)
    (outcome : Dynamic.ExpressionOutcome) (result : Core.Value)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  admission : PostAdmission bridge context sourceType outcome reached
  cells : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry models
    index.mapping index.world index.heap index.store
  result : FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models)
    index.mapping index.world sourceType type faults outcome result

namespace Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (qualified : qualification.ordinary code support)
  (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

local notation "history" => CallableIndexedOwnedPreparedDirectFormationReceipts.Ordinary.history_at
  captured code owner support initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

/-- The complete leaf output retains all real effects and the stronger facet
inside the original existential at the same reached packet. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  GenericExpressionMeaning.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      models)
    mapping world code.sourceNode.type code.lowered.type faults outcome result ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry models mapping world after finalStore ∧
  LocationMap.Extends mapping mapping ∧ WorldExtends world world ∧
  AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
  ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
      ⟨scope, mapping, world, after, finalStore, canonical⟩,
    (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
    Post (models := models) (registry := registry) (faults := faults)
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      function.context code.sourceNode.type code.lowered.type outcome result reached ∧
    StaticMember qualification headers keys bodyRegistry faults mapping world function carrier
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

/-- The proved strong post is attached without selecting another state or
running formation again. Source admission belongs to that post's actual trace. -/
private theorem result_at_formation
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word carrier) store)
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function carrier
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore)
    (post : Post (models := models) (registry := registry) (faults := faults)
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      function.context code.sourceNode.type code.lowered.type
      (.value (.closure function)) (.inRight .word carrier) ⟨initial, packet⟩) :
    ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (models := models) (support := support) (initial := initial) (packet := packet)
      (.value (.closure function)) heap (.inRight .word carrier) store :=
  ⟨nativeTrace, post.result, post.cells, .refl _, .refl _, .refl _ _, .refl _,
    ⟨initial, packet⟩, Relates.refl initial, post, member⟩

variable
  (cells : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry models mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include lift cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile qualified prefixContext observed in
private theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word carrier) store ∧
    StaticMember qualification headers keys bodyRegistry faults mapping world function carrier
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
    Post (models := models) (registry := registry) (faults := faults)
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller) function.context code.sourceNode.type code.lowered.type
      (.value (.closure function)) (.inRight .word carrier) ⟨initial, packet⟩ ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word carrier ∧ finalStore = store) := by
  obtain ⟨sourceTrace, nativeTrace, member, determined⟩ :=
    CallableIndexedOwnedPreparedDirectFormationReceipts.Ordinary.formation_member
      captured code owner qualification profile support qualified prepared initial packet prefixContext observed
      cells.runtime_hasTypes ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models)
      mapping world code.sourceNode.type code.lowered.type faults
      (.value (.closure function)) (.inRight .word carrier) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact .function (lift member)
  have post := after_expression (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ ⟨initial, packet⟩ admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) (AdministrativePreserved.refl mapping store)
  exact ⟨sourceTrace, nativeTrace, member, ⟨post, cells, represented⟩, determined⟩

include profile lift qualified prefixContext observed prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- The actual Source value/fault head selects the authentic lambda. Exactly
one prepared formation establishes native completion and the stronger post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore,
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (models := models) (support := support) (initial := initial) (packet := packet)
        outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
      obtain ⟨rfl, rfl⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions evaluated
      obtain ⟨_sourceTrace, nativeTrace, member, post, _determined⟩ :=
        formation_post
          (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
          (support := support) (qualified := qualified) (prepared := prepared)
          (initial := initial) (packet := packet) (prefixContext := prefixContext) (observed := observed)
          (models := models) (lift := lift) (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
          (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
      exact ⟨_, store, result_at_formation (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (models := models) captured code owner qualification support initial packet nativeTrace member post⟩
  | fault failed =>
      exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions failed)

include profile lift qualified prefixContext observed prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Native completion is compared with one genuine formation. Its own Source
grade is obtained from that factory trace; preservation is not invoked again. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (models := models) (support := support) (initial := initial) (packet := packet)
        outcome after result finalStore := by
  obtain ⟨sourceTrace, nativeTrace, member, post, determined⟩ :=
    formation_post
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
      (support := support) (qualified := qualified) (prepared := prepared)
      (initial := initial) (packet := packet) (prefixContext := prefixContext) (observed := observed)
      (models := models) (lift := lift) (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
      (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure function), heap, sized,
    result_at_formation (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (models := models) captured code owner qualification support initial packet nativeTrace member post⟩

end Ordinary

namespace Principal
variable
  (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (qualified : qualification.principal code support)
  (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

local notation "history" => CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.history_at
  captured code owner support initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

/-- The selected-method leaf retains its own principal packet and dictionary.
The outer payload registry is independent of the retained body registry. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  GenericExpressionMeaning.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      models)
    mapping world code.sourceNode.type code.lowered.type faults outcome result ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry models mapping world after finalStore ∧
  LocationMap.Extends mapping mapping ∧ WorldExtends world world ∧
  AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
  ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
      ⟨scope, mapping, world, after, finalStore, captured.canonical⟩,
    (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
    Post (models := models) (registry := registry) (faults := faults)
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      function.context code.sourceNode.type code.lowered.type outcome result reached ∧
    StaticMember qualification headers keys bodyRegistry faults mapping world function carrier
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

private theorem result_at_formation
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word carrier) store)
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function carrier
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore)
    (post : Post (models := models) (registry := registry) (faults := faults)
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      function.context code.sourceNode.type code.lowered.type
      (.value (.closure function)) (.inRight .word carrier) ⟨initial, packet⟩) :
    ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (models := models) (support := support) (initial := initial) (packet := packet)
      (.value (.closure function)) heap (.inRight .word carrier) store :=
  ⟨nativeTrace, post.result, post.cells, .refl _, .refl _, .refl _ _, .refl _,
    ⟨initial, packet⟩, Relates.refl initial, post, member⟩

variable
  (cells : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry models mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include lift cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile qualified in
private theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word carrier) store ∧
    StaticMember qualification headers keys bodyRegistry faults mapping world function carrier
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
    Post (models := models) (registry := registry) (faults := faults)
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) function.context code.sourceNode.type code.lowered.type
      (.value (.closure function)) (.inRight .word carrier) ⟨initial, packet⟩ ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word carrier ∧ finalStore = store) := by
  obtain ⟨sourceTrace, nativeTrace, member, determined⟩ :=
    CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.formation_member
      captured code owner qualification profile support qualified prepared initial packet
      cells.runtime_hasTypes ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models)
      mapping world code.sourceNode.type code.lowered.type faults
      (.value (.closure function)) (.inRight .word carrier) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact .function (lift member)
  have post := after_expression (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ ⟨initial, packet⟩ admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) (AdministrativePreserved.refl mapping store)
  exact ⟨sourceTrace, nativeTrace, member, ⟨post, cells, represented⟩, determined⟩

include profile lift qualified prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Source inversion keeps the actual selected principal, then invokes one
prepared method formation at its original dictionary-bearing packet. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore,
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (models := models) (support := support) (initial := initial) (packet := packet)
        outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
      obtain ⟨rfl, rfl⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions evaluated
      obtain ⟨_sourceTrace, nativeTrace, member, post, _determined⟩ :=
        formation_post
          (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
          (support := support) (qualified := qualified) (prepared := prepared)
          (initial := initial) (packet := packet)
          (models := models) (lift := lift) (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
          (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
      exact ⟨_, store, result_at_formation (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (models := models) captured code owner qualification support initial packet nativeTrace member post⟩
  | fault failed =>
      exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions failed)

include profile lift qualified prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- The native grade is independent of the Source grade obtained from one
actual method factory trace. The same strong post and reached pool are retained. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (models := models) (support := support) (initial := initial) (packet := packet)
        outcome after result finalStore := by
  obtain ⟨sourceTrace, nativeTrace, member, post, determined⟩ :=
    formation_post
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
      (support := support) (qualified := qualified) (prepared := prepared)
      (initial := initial) (packet := packet)
      (models := models) (lift := lift) (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
      (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure function), heap, sized,
    result_at_formation (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (models := models) captured code owner qualification support initial packet nativeTrace member post⟩

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelFormationBounds
