import Solcore.SourceSemantics.CoreLowering.FunctionCalls

/-! The call composition is instantiated with actual semantic proofs for empty
Unit bodies. Parameter count, lexical captures, administrative values and the
payload model are arbitrary. Neither child execution direction is assumed. -/

set_option autoImplicit false
namespace Tests.SourceCoreFunctionCalls
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open Core GeneralHeap FunctionArguments FunctionCallBody FunctionCalls

private def unitBody : FunctionCode.BodyCertificate := fun _ _ statements type code =>
  statements = [] ∧ type = .unit ∧ code = LanguageResult.success .unit

private theorem empty_preserves {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog} {program : SourceSemantics.Program} {function : Dynamic.Closure}
    {faults : FunctionCalls.FaultRep}
    (unitRep : ∀ mapping world, model.Represents mapping world .unit .unit .unit .unit)
    (resultUnit : function.resultType = .unit) :
    BodyPreserves model program function unitBody faults := by
  intro scope type body certified context staticFinal facts typed mapping world administrativeContext
    environment canonical actual before store ξ outcome after environments heaps locals layout trace
  obtain ⟨empty, rfl, rfl⟩ := certified
  cases trace with
  | returned execution => rw [empty] at execution; cases execution
  | unit _ execution =>
    rw [empty] at execution
    cases execution
    exact ⟨.inRight .word .unit, store, mapping, world, .inRight .unit,
      .value (resultUnit ▸ unitRep mapping world), heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | fault execution => rw [empty] at execution; cases execution
  | escaped execution escape =>
    rw [empty] at execution
    cases execution
    rcases escape with ⟨_, impossible⟩ | ⟨_, impossible⟩ <;> cases impossible

private theorem empty_reflects {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog} {program : SourceSemantics.Program} {function : Dynamic.Closure}
    {faults : FunctionCalls.FaultRep}
    (unitRep : ∀ mapping world, model.Represents mapping world .unit .unit .unit .unit)
    (resultUnit : function.resultType = .unit) :
    BodyReflects model program function unitBody faults := by
  intro scope type body certified context staticFinal facts typed mapping world administrativeContext
    environment canonical actual before store ξ value finalStore environments heaps locals layout evaluated
  obtain ⟨empty, rfl, rfl⟩ := certified
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated
    (show Evaluates actual store ((LanguageResult.success .unit).rename ξ) (.inRight .word .unit) store from .inRight .unit)
  exact ⟨.value .unit, before, mapping, world, .unit resultUnit (by rw [empty]; exact .nil),
    .value (resultUnit ▸ unitRep mapping world), heaps, .refl _, .refl _, .refl _ _, .refl _⟩

/-- An authenticated empty-body closure with any finite argument list executes
its real parameter wrapper and application. Administrative closures and cyclic
captured cells are allowed by the generic initial heap relation. -/
example {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : SourceSemantics.Program} {function : Dynamic.Closure} {policy : SourceCoreFunctions.Policy}
    {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {actual : Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program unitBody policy function scope layout.administrativeContext)
    {before : Dynamic.Heap} {store : Store} {arguments : List Dynamic.Value} {values : List Value}
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment) (callerEnvironment : Environment)
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (unitRep : ∀ mapping world, model.Represents mapping world .unit .unit .unit .unit)
    (resultUnit : function.resultType = .unit) :
    ∃ after finalStore finalMap finalWorld,
      Outcome program context caller function.evidence before (.closure function) arguments (.value .unit) after ∧
      Evaluates (DataPatternValues.packValues values :: actual) store
        (code.artifact.rawBody.rename layout.embedding.lift) (.inRight .word .unit) finalStore ∧
      Evaluates (DataPatternValues.packValues values ::
        FunctionValues.value code.artifact.parameterCore code.artifact.resultCore code.artifact.rawBody layout.embedding actual ::
        callerEnvironment) store (.apply (.second (.var 1)) (.var 0)) (.inRight .word .unit) finalStore ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨_, callContext, _, _, extension, _, _⟩ := frame_body code.frame
  obtain ⟨entry⟩ := entry_exists layout code extension represented heaps locals
  have trace : Trace program function callContext entry.environment entry.heap (.value .unit) entry.heap :=
    .unit resultUnit (by rw [code.artifact.bodyTree.1]; exact .nil)
  have sourceCall : Outcome program context caller function.evidence before (.closure function) arguments (.value .unit) entry.heap :=
    trace.call code.frame extension entry.allocation
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
    FunctionCalls.preserves layout code (empty_preserves (faults := fun _ _ => False) unitRep resultUnit)
      represented heaps locals sourceCall
  cases result with
  | @value source value payload =>
    have coreUnit : value = .unit := by
      have typed := model.runtime_hasType payload
      have unitType : code.artifact.resultCore = .unit := code.artifact.bodyTree.2.1
      rw [unitType] at typed
      cases typed
      rfl
    subst value
    exact ⟨entry.heap, finalStore, finalMap, finalWorld, sourceCall, evaluated,
      (FunctionCalls.application_agreement _ _ _ _ _ callerEnvironment _ store).wrap evaluated,
      finalHeaps, maps, worlds, frame, metadata⟩

/-- Core-only completion reconstructs an independent source call for the same
body family. The body reflection hypothesis is discharged above. -/
example {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : SourceSemantics.Program} {function : Dynamic.Closure} {policy : SourceCoreFunctions.Policy}
    {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {actual : Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program unitBody policy function scope layout.administrativeContext)
    {before : Dynamic.Heap} {store finalStore : Store} {arguments : List Dynamic.Value} {values : List Value}
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment) {value : Value}
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (unitRep : ∀ mapping world, model.Represents mapping world .unit .unit .unit .unit)
    (resultUnit : function.resultType = .unit)
    (evaluated : Evaluates (DataPatternValues.packValues values :: actual) store
      (code.artifact.rawBody.rename layout.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Outcome program context caller function.evidence before (.closure function) arguments outcome after ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.resultCore (fun _ _ => False) outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  FunctionCalls.reflects layout code (empty_reflects unitRep resultUnit) context caller represented heaps locals evaluated

end Tests.SourceCoreFunctionCalls
