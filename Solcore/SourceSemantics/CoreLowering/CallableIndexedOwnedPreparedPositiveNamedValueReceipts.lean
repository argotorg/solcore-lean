import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveFunctionOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapGlobalCallRecipes

/-! Named formation retains the actual bootstrap capture chosen by the
existing recipe. The reached read observes that same carrier, and the positive
function model stores its complete owner, Source dictionary and installed code.
Argument receipts use the same capture under the receiving model. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveNamedValueReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key NamedSourceAt NamedInstalledCode)
open CallableIndexedOwnedFunctionEntries (OwnedPool)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins (Owner NamedAssociation functions)
open CallableIndexedOwnedPreparedBootstrapGlobalCallRecipes (Recipe)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  (qualification : Facet compiled)
  {mapping : LocationMap} {world : StoreTyping}
  (origin : Owner (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (profile := profile))
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (recipe : Recipe (CallableIndexedLambdaValues.model compiled.indexed profile) origin header mapping world)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD source)
  {identity : Word}
  (number : Word.ofNat? (header.slot + 1) = some identity)
  (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
    (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
  (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
    (.named header.named.signature.key))
  (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType)
    (header.code.rename recipe.capture.embedding.lift) recipe.capture.captured)
    header.named.signature.functionType compiled.indexed.layouts.definitions)

/-- The installed template is inherited from the same recipe capture. Map
and world extension leave its embedding and captured values unchanged. -/
theorem installed : NamedInstalledCode recipe.capture := by
  simpa only [Recipe.capture, NamedInstalledCode, CallableIndexedOwnedFunctionValues.NamedCapture.extend]
    using recipe.installed

/-- Construct the positive association from the real recipe and complete
carrier fields; no older function relation is inverted. -/
noncomputable def association :
    NamedAssociation headers keys bodyRegistry profile mapping world
      header.named.specialized.function.type source (recipe.carrier identity descriptor.id)
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) :=
  .named origin recipe.member sourceAt recipe.capture (installed origin recipe)
    number projection descriptor typed

include sourceAt number projection typed in
/-- The receiving model records the same actual named carrier. -/
theorem represented
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableIndexedOwnedPreparedPositiveFunctionOrigins.PayloadOrigins qualification headers keys
      bodyRegistry registry faults profile mapping world header.named.specialized.function.type
      (.global source) (recipe.carrier identity descriptor.id)
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate sourceAt wellFormed
  have sameType : header.named.specialized.function.type = source.instantiation.type :=
    (congrArg (fun global => global.instantiation.type) sourceAt.retained).symm
  have callable := sameType.trans certified.callable_type
  have related : CallableIndexedOwnedPreparedPositiveFunctionOrigins.FunctionOrigins qualification headers keys
      bodyRegistry faults profile mapping world header.named.specialized.function.type
      (.global source) (recipe.carrier identity descriptor.id)
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) :=
    .global ⟨association origin recipe sourceAt number projection descriptor typed⟩
  rw [callable] at related ⊢
  exact .function related

include sourceAt number projection typed in
/-- The actual live read is for the literal recipe capture. The original
reference evaluator runs once and returns the same store and positive carrier. -/
theorem of_read {heap : Dynamic.Heap} {store : Store}
    {internalReason : Word} {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope}
    {canonical actual : Environment} {xi : Renaming}
    (pool : OwnedPool headers keys mapping world heap store)
    (entry : RecursiveNamedCatalog.Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers origin.owner.key.locations origin.owner.key.capturePrefix callerPrefix scope
      mapping world heap store canonical)
    (agrees : EnvironmentsAgree xi canonical actual)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (read : store.read? (origin.owner.key.locations header) = some (.inRight .unit
      (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename recipe.capture.embedding.lift) recipe.capture.captured))) :
    let expression := LanguageResult.bind
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
      (SourceCoreFunctions.namedReference header.named.signature (xi (scope.length + callerPrefix + header.slot))
        identity internalReason)
      (LanguageResult.success (descriptor.wrap (.var 0)))
    Evaluates actual store expression (.inRight .word (recipe.carrier identity descriptor.id)) store ∧
    CallableIndexedOwnedPreparedPositiveFunctionOrigins.PayloadOrigins qualification headers keys
      bodyRegistry registry faults profile mapping world header.named.specialized.function.type
      (.global source) (recipe.carrier identity descriptor.id)
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) ∧
    (∀ result finalStore, Evaluates actual store expression result finalStore →
      result = .inRight .word (recipe.carrier identity descriptor.id) ∧ finalStore = store) := by
  dsimp only
  let capture := CallableIndexedOwnedFunctionEntries.named_capture_reached
    pool origin.owner recipe.member recipe.capture read
  have evaluation := NamedCalls.native_reference (identity := identity) (internalReason := internalReason)
    descriptor (entry.reindex agrees header recipe.member) capture.read
  exact ⟨evaluation, represented qualification origin recipe sourceAt number projection descriptor typed wellFormed,
    fun _ _ completed => Core.evaluation_deterministic completed evaluation⟩

variable
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {context : SourceSemantics.Context} {sourceTree : TypedSource}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
  (admitted : Admission bridge context initial)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context sourceTree)
  {calleeHeap : Dynamic.Heap} {arguments : List Dynamic.Value} {payloads : List Value}
  {types : List TypeSystem.Ty} {parameter result : TypeSystem.Ty} {packed : Dynamic.Value}
  (extension : Dynamic.HeapTypesExtend calleeHeap index.heap)
  (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap arguments types)
  (packing : Dynamic.ValuesPack arguments packed)
  (bundle : TypeSystem.Ty.productMany types = parameter)

include sourceAt bridge initial admitted runtime extension argumentsTyped packing bundle in
/-- Ordered argument admission uses the same positive model and bootstrap
owner. The recipe's actual capture is passed to the original named producer. -/
theorem at_arguments
    (currentRecipe : Recipe (CallableIndexedLambdaValues.model compiled.indexed profile) origin header
      index.mapping index.world)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global source) (.function parameter result))
    (representedArguments : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
      index.mapping index.world header.bindings arguments payloads)
    (profiles : CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := headers) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      (functions qualification headers keys bodyRegistry faults profile) origin.owner (header := header))
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType) :
    CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.Receipt
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (mapping := index.mapping) (world := index.world) (before := index.heap)
      (arguments := arguments) (payloads := payloads)
      (functions qualification headers keys bodyRegistry faults profile) (.global source) source.evidence
      (currentRecipe.carrier identity descriptor.id) header.function.resultType header.output :=
  CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts.named
    (functions qualification headers keys bodyRegistry faults profile)
    bridge initial admitted runtime extension argumentsTyped packing bundle
    origin.owner currentRecipe.member origin.capture_zero (origin.globals currentRecipe.member)
    sourceAt currentRecipe.capture identity descriptor.id sameLayouts wellFormed calleeTyped
    representedArguments profiles syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveNamedValueReceipts
