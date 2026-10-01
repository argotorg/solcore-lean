import Solcore.SourceSemantics.CoreLowering.FunctionCallBody

/-! Finite ordinary closure-call composition. Static code/capture certificates
are separate from the universal child body preservation/reflection hypotheses.
The parameter wrapper, heap extensions and source call trace are derived here.
This is not an unconditional theorem for every accepted function compiler:
instantiating the child body hypotheses, caller expression evaluation, staged
calls, globals and generalized local functions remain separate work. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.FunctionCalls
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open FunctionArguments FunctionCallBody

abbrev FaultRep := Dynamic.SemanticFault → Word → Prop

inductive ResultRepresents {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (model : GenericHeap.PayloadModel catalog projects)
    (mapping : LocationMap) (world : StoreTyping) (sourceType : TypeSystem.Ty) (type : Ty) (faults : FaultRep) :
    Dynamic.ExpressionOutcome → Value → Prop where
  | value {source value} (represented : model.Represents mapping world sourceType source value type) :
      ResultRepresents model mapping world sourceType type faults (.value source) (.inRight .word value)
  | fault {reason token} (represented : faults reason token) :
      ResultRepresents model mapping world sourceType type faults (.fault reason) (.inLeft type (.word token))

/-- A universal semantic IH for an independently certified body. It is not a
field of the static function code certificate. Source traces supply finiteness. -/
def BodyPreserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (model : GenericHeap.PayloadModel catalog projects)
    (program : Program) (function : Dynamic.Closure) (certificate : FunctionCode.BodyCertificate)
    (faults : FaultRep) : Prop :=
  ∀ {scope type body}, certificate function.source scope function.body type body →
  ∀ {context staticFinal facts}, StatementsHaveType function.source
    {returnType := function.resultType, loopDepth := 0} context function.body staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Trace program function context environment before outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (body.rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld function.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-- The source body trace is constructed from Core execution. No finite source
trace is a premise of this universal reflection obligation. -/
def BodyReflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (model : GenericHeap.PayloadModel catalog projects)
    (program : Program) (function : Dynamic.Closure) (certificate : FunctionCode.BodyCertificate)
    (faults : FaultRep) : Prop :=
  ∀ {scope type body}, certificate function.source scope function.body type body →
  ∀ {context staticFinal facts}, StatementsHaveType function.source
    {returnType := function.resultType, loopDepth := 0} context function.body staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (body.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Trace program function context environment before outcome after ∧
      ResultRepresents model finalMap finalWorld function.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

variable {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
  {program : Program} {function : Dynamic.Closure} {bodyCertificate : FunctionCode.BodyCertificate}
  {policy : SourceCoreFunctions.Policy} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  {faults : FaultRep}

/-- Source closure-call preservation includes the production parameter wrapper.
Previously existing administrative values and shared captured locations remain
related through the returned map/world extension and administrative frame. -/
theorem preserves
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (bodyMeaning : BodyPreserves model program function bodyCertificate faults)
    {before after : Dynamic.Heap} {store : Store} {arguments : List Dynamic.Value} {values : List Value}
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment} {outcome : Dynamic.ExpressionOutcome}
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (execution : Outcome program context caller function.evidence before (.closure function) arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues values :: actual) store
        (code.artifact.rawBody.rename layout.embedding.lift) value finalStore ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have arity : function.parameters.length = arguments.length := by
    rw [← code.artifact.parametersTree.binders, List.length_map]
    exact represented.length.1
  obtain ⟨types, callContext, environment, bound, extension, allocated, trace⟩ := execution.trace arity
  obtain ⟨entry⟩ := entry_exists layout code extension represented heaps locals
  obtain ⟨rfl, rfl⟩ := allocations_same allocated entry.allocation
  obtain ⟨_, _, typed, _⟩ := frame_body_at code.frame extension
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
    bodyMeaning code.artifact.bodyTree typed entry.environments entry.heaps entry.locals entry.lookups trace
  exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, result, finalHeaps,
    entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata⟩

/-- A completed Core closure body constructs its source call, including body
faults and escaped control. Only the reusable universal child theorem is assumed;
there is no source execution premise and no first-order restriction on the store. -/
theorem reflects
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (bodyMeaning : BodyReflects model program function bodyCertificate faults)
    {before : Dynamic.Heap} {store finalStore : Store} {arguments : List Dynamic.Value} {values : List Value}
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment) {value : Value}
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (evaluated : Evaluates (DataPatternValues.packValues values :: actual) store
      (code.artifact.rawBody.rename layout.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Outcome program context caller function.evidence before (.closure function) arguments outcome after ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨types, callContext, _, _, extension, typed, _⟩ := frame_body code.frame
  obtain ⟨entry⟩ := entry_exists layout code extension represented heaps locals
  obtain ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
    bodyMeaning code.artifact.bodyTree typed entry.environments entry.heaps entry.locals entry.lookups
      (entry.agreement.unwrap evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace.call code.frame extension entry.allocation,
    result, finalHeaps, entry.maps.trans maps, entry.worlds.trans worlds,
    entry.frame.trans frame, entry.metadata.trans metadata⟩

/-- A finite source invocation supplies sufficient fuel for the existing Core
machine. Fuel exhaustion is not interpreted as a terminal source outcome. -/
theorem preserves_sufficient_fuel
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (bodyMeaning : BodyPreserves model program function bodyCertificate faults)
    {before after : Dynamic.Heap} {store : Store} {arguments : List Dynamic.Value} {values : List Value}
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment} {outcome : Dynamic.ExpressionOutcome}
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (execution : Outcome program context caller function.evidence before (.closure function) arguments outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (code.artifact.rawBody.rename layout.embedding.lift)
          (DataPatternValues.packValues values :: actual) store) = .done value finalStore) ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    preserves layout code bodyMeaning represented heaps locals execution
  obtain ⟨required, runs⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required, runs, represented, finalHeaps, maps, worlds, frame, metadata⟩

/-- Every completed machine run of the authenticated closure body constructs
an independent source call under the explicit child reflection theorem. -/
theorem reflects_done
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (bodyMeaning : BodyReflects model program function bodyCertificate faults)
    {before : Dynamic.Heap} {store finalStore : Store} {arguments : List Dynamic.Value} {values : List Value}
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment) {value : Value} {fuel : Nat}
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (completed : runStateful fuel (.initial (code.artifact.rawBody.rename layout.embedding.lift)
      (DataPatternValues.packValues values :: actual) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Outcome program context caller function.evidence before (.closure function) arguments outcome after ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects layout code bodyMeaning context caller represented heaps locals (runStateful_evaluation_sound completed)

/-- The last application expression emitted by the tagged call helper enters
exactly the captured body and actual environment authenticated above. -/
theorem application_agreement (parameter result : Ty) (body : Expr) (ξ : Renaming)
    (captured caller : Environment) (arguments : Value) (store : Store) :
    ContinuationAgreement
      (arguments :: FunctionValues.value parameter result body ξ captured :: caller) store
      (.apply (.second (.var 1)) (.var 0)) (arguments :: captured) store (body.rename ξ.lift) := by
  constructor
  · intro value finalStore evaluated
    exact .apply (.second (.var rfl)) (.var rfl) evaluated
  · intro value finalStore evaluated
    obtain ⟨size, sized⟩ := evaluation_has_size evaluated
    obtain ⟨_, _, bodyEvaluation⟩ := sized.apply_body
      (show Evaluates (arguments :: FunctionValues.value parameter result body ξ captured :: caller) store
        (.second (.var 1)) (.closure parameter (LanguageResult.resultType result) (body.rename ξ.lift) captured) store
        from .second (.var rfl)) (.var rfl)
    exact bodyEvaluation.sound

end Solcore.SourceSemantics.CoreLowering.FunctionCalls
