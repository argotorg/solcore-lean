import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AppliedViews
import Solcore.SourceSemantics.Staging.RecursiveScope
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
import Solcore.SourceSemantics.Staging.RecursiveTraceProperties
import Solcore.SourceSemantics.CoreLowering.CallStageBoundary
import Solcore.SourceSemantics.CoreLowering.ContractedFunctionCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings

/-!
# The recursive staged profile: calls

Universal semantic interfaces of the recursive staged profile: the stage registry, projection, meaning, arguments and calls.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveStageRegistry
/-! Authentic invocation scopes for anonymous closures. The actual original
sidecar supplies the caller marker/stage table; complete declaration and local
substitutions remain attached. Codebook origins, canonical-source receipts and
actual lambda metadata establish selection. No body evaluation is part of the
registry, and arbitrary Core-typed functions cannot enter it. Named/global
scope selection and traversal-wide receipt extraction remain separate work. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageRegistry
open Frontend Frontend.SourceInference SourceCoreStageContracts AuthenticatedCallableLedger

/-- The runtime lexical context/evidence belong to the closure. Its guard
frame comes from the original sidecar, including the original return marker. -/
def scope (sidecar : Sidecar) (active : TypeSystem.Substitution) (function : Dynamic.Closure) : Staging.Recursive.Scope := {
  origin := ⟨function.source.owner, sidecar.caller.parameterSubstitution, active⟩
  source := function.source, owned := rfl, context := function.context, evidence := function.evidence
  guards := CallableLedger.frame sidecar }

inductive Selected (checkedProgram : CheckedProgram) (plan : Plan) (table : SourceCoreStageCodebook.Table) :
    Dynamic.Closure → Staging.Recursive.Scope → Prop where
  | lambda {sidecar : Sidecar} {id : ExpressionId} {active : TypeSystem.Substitution}
      {descriptor : Core.Word} {function : Dynamic.Closure}
      (prepared : prepareSidecar plan sidecar.caller.key = .ok sidecar)
      (site : LambdaSite plan table sidecar.caller.key id active descriptor)
      (source : LambdaSourceAlignment.SourceReceipt checkedProgram plan sidecar.caller.key active function.source)
      (owner : function.source.owner = sidecar.caller.key.declaration)
      (origin : CallableLedger.LambdaOrigin plan sidecar.caller.key id active function site.contract) :
      Selected checkedProgram plan table function (scope sidecar active function)

  | applied {checked : SourceCoreCompatibleCatalog.Checked}
      {base : SourceCoreCompatibleFunctions.Prepared checked}
      {inputs : SourceCoreCallableAncestryPreparation.Inputs base}
      {callerFrame lexicalFrame : SourceCoreCallablePairedFrames.Frame}
      {caller lexical : SourceCoreCallableAncestryReadRecipes.State} {view target : Core.Word}
      {sidecar : Sidecar} {function : Dynamic.Closure}
      (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame caller lexical view target)
      (sameProgram : base.sourceProgram = checkedProgram) (samePlan : base.plan = plan)
      (sameTable : inputs.callable.table = table)
      (prepared : prepareSidecar plan sidecar.caller.key = .ok sidecar)
      (sameOwner : recipe.read.template.owner = sidecar.caller.key)
      (site : LambdaSite plan table sidecar.caller.key recipe.read.template.id recipe.read.template.active target)
      (source : function.source = (recipe.read.after lexical).metadata.source)
      (owner : function.source.owner = sidecar.caller.key.declaration)
      (origin : CallableLedger.LambdaOrigin plan sidecar.caller.key recipe.read.template.id
        recipe.read.template.active function site.contract) :
      Selected checkedProgram plan table function
        (scope sidecar (recipe.read.substitution.compose lexical.metadata.active) function)

def registry (checkedProgram : CheckedProgram) (plan : Plan) (table : SourceCoreStageCodebook.Table) :
    Staging.Recursive.Registry where
  Closure := Selected checkedProgram plan table
  source := by intro function selected related; cases related <;> rfl
  context := by intro function selected related; cases related <;> rfl
  evidence := by intro function selected related; cases related <;> rfl

/-- Actual sidecar/table preparation and the emitted lambda's static receipt
select a recursive body scope, even when compilation used a raw metadata view.
The caller passes static source/code provenance, never a child execution. -/
theorem selected_of_prepare {checkedProgram : CheckedProgram} {plan : Plan}
    {checked : SourceCoreDataCatalog.Checked} {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {table : SourceCoreStageCodebook.Table} {active : TypeSystem.Substitution}
    {sidecar : Sidecar} {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {view : TypedSource} {lexical : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {function : Dynamic.Closure}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreStageCodebook.prepare checkedProgram plan checked limits firstId = .ok table)
    (prepared : prepareSidecar plan compilation.owner = .ok sidecar)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id active))
    (source : LambdaSourceAlignment.SourceReceipt checkedProgram plan compilation.owner active function.source)
    (owner : function.source.owner = compilation.owner.declaration)
    (metadata : LambdaMetadataViews.MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (artifact : DecoratedFunctionCode.LambdaCertificate bodyCertificate policy compilation view lexical id node
      function.parameters function.resultType function.body reportedType lowered) :
    (registry checkedProgram plan table).Closure function (scope sidecar active function) := by
  obtain ⟨site⟩ := lambda_site_of_descriptor accepted descriptor
  have same := (CallContractCertificates.sidecar_of_accepted prepared).2
  let alignedSite : LambdaSite plan table sidecar.caller.key id active descriptor.id := by
    simpa only [same] using site
  have alignedSource : LambdaSourceAlignment.SourceReceipt checkedProgram plan sidecar.caller.key active function.source := by
    simpa only [same] using source
  exact Selected.lambda (by simpa only [same] using prepared) alignedSite alignedSource
    (by simpa only [same] using owner)
    (LambdaMetadataViews.lambda_origin alignedSource alignedSite.original metadata unique artifact.raw.found artifact.raw.form)

@[simp] theorem scope_localSubstitution (sidecar : Sidecar) (active : TypeSystem.Substitution) (function : Dynamic.Closure) :
    (scope sidecar active function).origin.localSubstitution = active := rfl

@[simp] theorem scope_declarationSubstitution (sidecar : Sidecar) (active : TypeSystem.Substitution) (function : Dynamic.Closure) :
    (scope sidecar active function).origin.declarationSubstitution = sidecar.caller.parameterSubstitution := rfl

@[simp] theorem scope_returnMarker (sidecar : Sidecar) (active : TypeSystem.Substitution) (function : Dynamic.Closure) :
    (scope sidecar active function).guards.stages.callerReturnComptime = sidecar.caller.function.returnComptime := rfl

/-- A selected scope always keeps the original static sidecar. In particular,
its return marker is not recomputed from the source/Core function result type. -/
theorem Selected.original {checkedProgram : CheckedProgram} {plan : Plan} {table : SourceCoreStageCodebook.Table}
    {function : Dynamic.Closure} {selected : Staging.Recursive.Scope}
    (related : Selected checkedProgram plan table function selected) :
    ∃ sidecar active, prepareSidecar plan sidecar.caller.key = .ok sidecar ∧
      selected = scope sidecar active function ∧ selected.origin.declaration = sidecar.caller.key.declaration := by
  cases related with
  | lambda prepared _ _ owner _ => exact ⟨_, _, prepared, rfl, owner⟩
  | applied _ _ _ _ prepared _ _ _ owner _ => exact ⟨_, _, prepared, rfl, owner⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveStageRegistry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveStageProjection
/-! Codebook authentication and recursive lambda scope selection for the actual
projection-parameterized public factory. No law about the projection is needed
to recover original contracts: their markers and complete contextual source
substitutions come from retained factory receipts. This does not infer payload
code or capture correctness from the projected Core type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageProjection
open Frontend Frontend.SourceInference SourceCoreStageCodebook GeneralHeap
open CallContractCertificates CallEntryCertificates AuthenticatedCallableLedger RecursiveStageRegistry

theorem lambda_site_of_descriptor {program : CheckedProgram} {plan : Plan} {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {table : Table} {owner : Key} {id : ExpressionId} {active : TypeSystem.Substitution}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda owner id active)) :
    Nonempty (LambdaSite plan table owner id active descriptor.id) := by
  obtain ⟨entry, member, origin, id_eq⟩ := descriptor_entry descriptor
  have authenticated := prepareWithProjection_authenticates accepted entry member
  unfold Authenticated at authenticated
  rw [origin] at authenticated
  generalize count_eq : entry.parameterCount = count at authenticated
  generalize contract_eq : entry.contract = contract at authenticated
  cases authenticated with
  | originalLambda selected prepared =>
    exact ⟨⟨entry, member, origin, id_eq, _, contract_eq, .original _ _ _ selected prepared⟩⟩
  | contextualLambda selected prepared =>
    exact ⟨⟨entry, member, origin, id_eq, _, contract_eq, .contextual _ _ _ _ selected prepared⟩⟩

/-- Named provenance uses the exact source instantiation selected by the plan;
its original parameter markers are obtained from the real named factory. -/
theorem named_origin {program : CheckedProgram} {plan : Plan} {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {table : Table} {key : Key} {function : Dynamic.GlobalFunction}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.named key))
    (selected : SourceCompilationPlan.exactInstantiationKey plan function.instantiation = .ok key) (raw : Core.Value) :
    CallableLedger.OriginRep plan table (.global function) (.pair raw (.word descriptor.id)) := by
  obtain ⟨entry, member, origin, id_eq⟩ := descriptor_entry descriptor
  have authenticated := prepareWithProjection_authenticates accepted entry member
  unfold Authenticated at authenticated
  rw [origin] at authenticated
  generalize count_eq : entry.parameterCount = count at authenticated
  generalize contract_eq : entry.contract = contract at authenticated
  cases authenticated with
  | named prepared =>
    have related := CallableLedger.OriginRep.named (raw := raw) member origin contract_eq selected prepared
    simpa only [id_eq] using related

/-- Builtin descriptors retain their bypass status, with no user-callable
contract fabricated from their projected Core function type. -/
theorem builtin_origin {program : CheckedProgram} {plan : Plan} {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {table : Table} {function : Dynamic.BuiltinFunction}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.builtin function.id)) (raw : Core.Value) :
    CallableLedger.OriginRep plan table (.builtin function) (.pair raw (.word descriptor.id)) := by
  obtain ⟨entry, member, origin, id_eq⟩ := descriptor_entry descriptor
  have authenticated := prepareWithProjection_authenticates accepted entry member
  unfold Authenticated at authenticated
  rw [origin] at authenticated
  generalize count_eq : entry.parameterCount = count at authenticated
  generalize contract_eq : entry.contract = contract at authenticated
  cases authenticated with
  | builtin =>
    have related := CallableLedger.OriginRep.builtin (plan := plan) (raw := raw) member origin contract_eq
    simpa only [id_eq] using related


/-- Actual lambda metadata selects its original invocation frame under the
projection-parameterized public factory. -/
theorem selected_of_prepare {checkedProgram : CheckedProgram} {plan : Plan}
    {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty} {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {table : SourceCoreStageCodebook.Table} {active : TypeSystem.Substitution}
    {sidecar : Sidecar} {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {view : TypedSource} {lexical : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {function : Dynamic.Closure}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreStageCodebook.prepareWithProjection checkedProgram plan projectType limits firstId = .ok table)
    (prepared : SourceCoreStageContracts.prepareSidecar plan compilation.owner = .ok sidecar)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id active))
    (source : LambdaSourceAlignment.SourceReceipt checkedProgram plan compilation.owner active function.source)
    (owner : function.source.owner = compilation.owner.declaration)
    (metadata : LambdaMetadataViews.MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (artifact : DecoratedFunctionCode.LambdaCertificate bodyCertificate policy compilation view lexical id node
      function.parameters function.resultType function.body reportedType lowered) :
    (registry checkedProgram plan table).Closure function (scope sidecar active function) := by
  obtain ⟨site⟩ := lambda_site_of_descriptor accepted descriptor
  have same := (CallContractCertificates.sidecar_of_accepted prepared).2
  let alignedSite : LambdaSite plan table sidecar.caller.key id active descriptor.id := by
    simpa only [same] using site
  have alignedSource : LambdaSourceAlignment.SourceReceipt checkedProgram plan sidecar.caller.key active function.source := by
    simpa only [same] using source
  exact Selected.lambda (by simpa only [same] using prepared) alignedSite alignedSource
    (by simpa only [same] using owner)
    (LambdaMetadataViews.lambda_origin alignedSource alignedSite.original metadata unique artifact.raw.found artifact.raw.form)


/-- The same actual decision rows cover the represented guarded calls. -/
theorem covers_of_prepare {catalog : SourceCoreDataCatalog.Catalog} (underlying : GenericHeap.PayloadModel catalog)
    {program : CheckedProgram} {plan : Plan} {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : Limits} {firstId : Nat} {site : SourceCoreCallableContracts.Callsite} {sidecar : Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (accepted : prepareWithProjection program plan projectType limits firstId = .ok site.table)
    (caller : SourceCoreStageContracts.prepareSidecar plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (sourceType : TypeSystem.Ty) (type : Core.Ty) :
    CallStageBoundary.Covers (CallableLedger.model underlying plan site.table) (CallableLedger.frame sidecar)
      site site.call arguments sourceType type := by
  have rows := CallCodebookCertificates.rows_of_prepareWithProjection accepted caller contains form
  rw [← (sidecar_of_accepted caller).1]
  intro mapping world source carrier contract represented bound
  exact CallableLedger.covers underlying rows sourceType type represented bound


end Solcore.SourceSemantics.CoreLowering.RecursiveStageProjection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveStageMeaning
/-! Universal semantic interfaces for the recursive staged profile. Static
expression/body certificates remain free of execution assumptions. The semantic
IHs range over related heaps and real lexical renamings, and their fault relation
retains the failing invocation scope. An actual compiler profile must establish
these IHs and the static closure-scope registry; Core typing does not supply them. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageMeaning
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly

abbrev Certificate := GenericExpressionMeaning.Certificate
abbrev FaultRep := Staging.Recursive.Failure → Word → Prop

inductive ResultRepresentsFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : StoreTyping) (sourceType : TypeSystem.Ty) (type : Ty) (faults : FaultRep) :
    Staging.Recursive.Outcome → Value → Prop where
  | value {source value} (represented : model.Represents mapping world sourceType source value type) :
      ResultRepresentsFor model mapping world sourceType type faults (.value source) (.inRight .word value)
  | fault {failure token} (represented : faults failure token) :
      ResultRepresentsFor model mapping world sourceType type faults (.fault failure) (.inLeft type (.word token))

def PreservesFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (registry : Staging.Recursive.Registry) (frame : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, frame.source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Staging.Recursive.Expression program registry frame context environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def ReflectsFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (registry : Staging.Recursive.Registry) (frame : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, frame.source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expression program registry frame context environment before id outcome after ∧
      ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-- A completed staged body keeps both its actual statement exit and the
source rule converting that exit to a callable result. -/
def BodyTrace (program : Program) (registry : Staging.Recursive.Registry) (frame : Staging.Recursive.Scope) (function : Dynamic.Closure)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ finalContext control,
    Staging.Recursive.Statements program registry frame context environment before function.body finalContext control after ∧
      Staging.Recursive.BodyResult function.resultType control outcome

def BodyPreservesFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (registry : Staging.Recursive.Registry) (frame : Staging.Recursive.Scope) (function : Dynamic.Closure)
    (certificate : FunctionCode.BodyCertificate) (faults : FaultRep) : Prop :=
  ∀ {scope type body}, certificate function.source scope function.body type body →
  ∀ {context staticFinal facts}, StatementsHaveType function.source
    {returnType := function.resultType, loopDepth := 0} context function.body staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    BodyTrace program registry frame function context environment before outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (body.rename ξ) value finalStore ∧
      ResultRepresentsFor model finalMap finalWorld function.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def BodyReflectsFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (registry : Staging.Recursive.Registry) (frame : Staging.Recursive.Scope) (function : Dynamic.Closure)
    (certificate : FunctionCode.BodyCertificate) (faults : FaultRep) : Prop :=
  ∀ {scope type body}, certificate function.source scope function.body type body →
  ∀ {context staticFinal facts}, StatementsHaveType function.source
    {returnType := function.resultType, loopDepth := 0} context function.body staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    Evaluates actual store (body.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      BodyTrace program registry frame function context environment before outcome after ∧
      ResultRepresentsFor model finalMap finalWorld function.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

theorem ResultRepresentsFor.extend {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions} {mapping futureMapping : LocationMap}
    {world futureWorld : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty} {faults : FaultRep}
    {outcome : Staging.Recursive.Outcome} {value : Value}
    (represented : ResultRepresentsFor model mapping world sourceType type faults outcome value)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ResultRepresentsFor model futureMapping futureWorld sourceType type faults outcome value := by
  cases represented with
  | value payload => exact .value (model.extend payload maps worlds)
  | fault failure => exact .fault failure

/-- Legacy interfaces use the same relation with the original catalog projection and definitions. -/
abbrev ResultRepresents {catalog : SourceCoreDataCatalog.Catalog} :=
  @ResultRepresentsFor catalog (GenericHeap.strictProjection catalog) catalog.definitions

abbrev Preserves {catalog : SourceCoreDataCatalog.Catalog} :=
  @PreservesFor catalog (GenericHeap.strictProjection catalog) catalog.definitions

abbrev Reflects {catalog : SourceCoreDataCatalog.Catalog} :=
  @ReflectsFor catalog (GenericHeap.strictProjection catalog) catalog.definitions

abbrev BodyPreserves {catalog : SourceCoreDataCatalog.Catalog} :=
  @BodyPreservesFor catalog (GenericHeap.strictProjection catalog) catalog.definitions

abbrev BodyReflects {catalog : SourceCoreDataCatalog.Catalog} :=
  @BodyReflectsFor catalog (GenericHeap.strictProjection catalog) catalog.definitions

abbrev ResultRepresents.value {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {faults : FaultRep} {source : Dynamic.Value} {value : Value}
    (represented : model.Represents mapping world sourceType source value type) :
    ResultRepresents model mapping world sourceType type faults (.value source) (.inRight .word value) :=
  ResultRepresentsFor.value represented

abbrev ResultRepresents.fault {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {faults : FaultRep}
    {failure : Staging.Recursive.Failure} {token : Word} (represented : faults failure token) :
    ResultRepresents model mapping world sourceType type faults (.fault failure) (.inLeft type (.word token)) :=
  ResultRepresentsFor.fault represented

theorem ResultRepresents.extend {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog} {mapping futureMapping : LocationMap}
    {world futureWorld : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty} {faults : FaultRep}
    {outcome : Staging.Recursive.Outcome} {value : Value}
    (represented : ResultRepresents model mapping world sourceType type faults outcome value)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ResultRepresents model futureMapping futureWorld sourceType type faults outcome value :=
  ResultRepresentsFor.extend represented maps worlds

/-- A nested failure in the callee bypasses both outer gates and all
arguments. Its original fault label and the callee's exact heap survive. -/
theorem preserves_callee_fault_for {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {certificate : Certificate} {faults : FaultRep}
    {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId} {scope : SourceCoreLocalCell.Scope}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (childMeaning : PreservesFor model program registry frame context certificate faults)
    (unknown : Word) (result : Ty) (argumentCode : Expr)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (child : Staging.Recursive.Expression program registry frame context environment before callee (.fault failure) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown result (lowered.expression.rename ξ) argumentCode)
        (.inLeft result (.word token)) finalStore ∧ faults failure token ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata⟩ :=
    childMeaning certified found environments heaps locals layout child
  cases represented with
  | fault reason =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      CallableContract.call_callee_failure site.gates unknown evaluated,
      reason, finalHeaps, maps, worlds, preserved, metadata⟩

theorem preserves_callee_fault {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {certificate : Certificate} {faults : FaultRep}
    {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId} {scope : SourceCoreLocalCell.Scope}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (childMeaning : Preserves model program registry frame context certificate faults)
    (unknown : Word) (result : Ty) (argumentCode : Expr)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (child : Staging.Recursive.Expression program registry frame context environment before callee (.fault failure) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown result (lowered.expression.rename ξ) argumentCode)
        (.inLeft result (.word token)) finalStore ∧ faults failure token ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves_callee_fault_for certified found childMeaning unknown result argumentCode
    environments heaps locals layout child

/-- The real Core gate follows a recursively staged callee prefix. The IH can
itself contain nested argument/body guards; no plain child execution is used. -/
theorem preserves_rejection_for {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {certificate : Certificate} {faults : FaultRep} {site : SourceCoreCallableContracts.Callsite}
    {call callee : ExpressionId} {arguments : List ExpressionId} {scope : SourceCoreLocalCell.Scope}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (childMeaning : PreservesFor model program registry frame context certificate faults)
    (coverage : CallStageBoundary.CoversFor model frame.guards site call arguments node.type lowered.type)
    (reasonMeaning : ∀ reason token, CallStageBoundary.ReasonRepresents site reason token →
      faults (.stage frame call reason) token)
    (unknown : Word) (result : Ty) (argumentCode : Expr)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {callable : Dynamic.Value} {reason : Staging.CallGuard.Fault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (child : Staging.Recursive.Expression program registry frame context environment before callee (.value callable) after)
    (rejected : Staging.CallBoundary.GuardRejects frame.guards call arguments callable reason) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown result (lowered.expression.rename ξ) argumentCode)
        (.inLeft result (.word token)) finalStore ∧
      faults (.stage frame call reason) token ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨carrier, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, metadata⟩ :=
    childMeaning certified found environments heaps locals layout child
  cases represented with
  | value payload =>
    obtain ⟨contract, bound⟩ : ∃ contract, frame.guards.Binds callable contract := by
      cases rejected with | contract bound _ => exact ⟨_, bound⟩
    obtain ⟨dispatch⟩ := coverage payload bound
    rw [dispatch.shape] at evaluated
    exact ⟨dispatch.reason reason, finalStore, finalMap, finalWorld,
      site.lower_stage_failure unknown dispatch.row _ dispatch.found (dispatch.rejected rejected) evaluated,
      reasonMeaning reason _ (dispatch.reason_represents reason), finalHeaps, maps, worlds, preserved, metadata⟩

theorem preserves_rejection {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {certificate : Certificate} {faults : FaultRep} {site : SourceCoreCallableContracts.Callsite}
    {call callee : ExpressionId} {arguments : List ExpressionId} {scope : SourceCoreLocalCell.Scope}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (childMeaning : Preserves model program registry frame context certificate faults)
    (coverage : CallStageBoundary.Covers model frame.guards site call arguments node.type lowered.type)
    (reasonMeaning : ∀ reason token, CallStageBoundary.ReasonRepresents site reason token →
      faults (.stage frame call reason) token)
    (unknown : Word) (result : Ty) (argumentCode : Expr)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {callable : Dynamic.Value} {reason : Staging.CallGuard.Fault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (child : Staging.Recursive.Expression program registry frame context environment before callee (.value callable) after)
    (rejected : Staging.CallBoundary.GuardRejects frame.guards call arguments callable reason) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown result (lowered.expression.rename ξ) argumentCode)
        (.inLeft result (.word token)) finalStore ∧
      faults (.stage frame call reason) token ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves_rejection_for certified found childMeaning coverage reasonMeaning unknown result argumentCode
    environments heaps locals layout child rejected

end Solcore.SourceSemantics.CoreLowering.RecursiveStageMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveStageArguments
/-! Recursive stage correspondence for the actual argument packing helper.
The static Tree is reused from actual list compilation receipts. Universal
staged child theorems are instantiated at each real inserted-prefix layout;
compound argument executions are constructed, never assumed at those layouts.
Faults preserve the originating invocation scope and call through the bundle. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageArguments
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly DataPatternValues
open DataExpressionSequence (Tree Values pair_rename)
open RecursiveStageMeaning

inductive ResultFor {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : StoreTyping) (types : List TypeSystem.Ty)
    (codes : List SourceCoreBasic.LoweredExpr) (faults : FaultRep) : Staging.Recursive.ValuesOutcome → Value → Prop where
  | values {sources values}
      (represented : Values model mapping world types (codes.map (·.type)) sources values) :
      ResultFor model mapping world types codes faults (.values sources) (.inRight .word (packValues values))
  | fault {reason token} (represented : faults reason token) :
      ResultFor model mapping world types codes faults (.fault reason)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token))

section Ambient
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : Certificate} {faults : FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}

/-- Successful evaluation keeps left-to-right effects and every represented
payload, including captured references inside earlier argument values. -/
theorem preserves_values_for (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : PreservesFor model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.Recursive.Expressions program registry frame context environment before ids (.values sources) after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual before store ξ sources after with
  | nil =>
    cases execution
    exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | single found generated =>
    cases execution with
    | cons head tail =>
      cases tail
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout head
      cases represented with
      | value payload =>
        exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
          finalHeaps, maps, worlds, frame, metadata⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head rest =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning generated found environments heaps locals layout head
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
          maps, worlds, frame, metadata⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix layout coreValue) rest
        have nonempty : values ≠ [] := by
          intro absent
          have lengths := restRep.length.2
          simp [absent] at lengths
        refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
          .cons (model.extend payload maps worlds) restRep, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [GenericExpressionMeaning.rename_prefix] at second
        have combined := LocalSequence.pair_success lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
        simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

/-- A source fault evaluates only its successful prefix. The generated helper
propagates the exact token without evaluating later arguments. -/
theorem preserves_fault_for (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : PreservesFor model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.Recursive.Expressions program registry frame context environment before ids (.fault reason) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual before store ξ after with
  | nil => cases execution
  | single found generated =>
    cases execution with
    | headFault failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout failed
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched,
          finalHeaps, maps, worlds, frame, metadata⟩
    | tailFault _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | headFault failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout failed
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata⟩
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type evaluated
    | tailFault head failed =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning generated found environments heaps locals layout head
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
          maps, worlds, frame, metadata⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix layout coreValue) failed
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [GenericExpressionMeaning.rename_prefix] at second
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second


/-- Completed Core bundles reconstruct the recursive staged argument trace.
The earlier successful argument payload is kept under the exact inserted slot;
a later stage failure is propagated with its original scope and call. -/
theorem reflects_for (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : ReflectsFor model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expressions program registry frame context environment before ids outcome after ∧
      ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual before store ξ value finalStore with
  | nil =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (show Evaluates actual store
      ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
    exact ⟨.values [], before, mapping, world, .nil, .values (values := []) .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | single found generated =>
    obtain ⟨outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout evaluated
    cases represented with
    | value payload =>
      exact ⟨.values [_], after, finalMap, finalWorld,
        .cons execution .nil, .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata⟩
    | fault matched =>
      exact ⟨.fault _, after, finalMap, finalWorld,
        .headFault execution, .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    change Evaluates actual store ((LocalSequence.pair lowered.type
      (SourceCoreCalls.packArguments (nextCode :: codes)).type lowered.expression
      (SourceCoreCalls.packArguments (nextCode :: codes)).expression).rename ξ) value finalStore at evaluated
    rw [pair_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft first _ =>
      obtain ⟨outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout first
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.pair_left_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first)
        exact ⟨.fault _, after, finalMap, finalWorld, .headFault execution, .fault matched,
          finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight first continuation =>
      obtain ⟨outcome, middle, middleMap, middleWorld, execution, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning generated found environments heaps locals layout first
      cases represented with
      | @value sourceValue coreValue payload =>
        rename_i middleStore coreValue
        have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical
            (coreValue :: actual) := GenericExpressionMeaning.agree_prefix layout coreValue
        cases continuation with
        | caseLeft second _ =>
          have shifted := second
          rw [← GenericExpressionMeaning.rename_prefix] at shifted
          obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
            maps, worlds, frame, metadata⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
              (locals.mono firstMetadata) nextLayout shifted
          cases result with
          | fault matched =>
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
              (LocalSequence.pair_right_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second)
            exact ⟨.fault _, after, finalMap, finalWorld, .tailFault execution sourceTrace, .fault matched,
              finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans metadata⟩
        | caseRight second _ =>
          have shifted := second
          rw [← GenericExpressionMeaning.rename_prefix] at shifted
          obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
            maps, worlds, frame, metadata⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
              (locals.mono firstMetadata) nextLayout shifted
          cases result with
          | @values sources values restRep =>
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
              (LocalSequence.pair_success lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second)
            have nonempty : values ≠ [] := by
              intro absent
              have lengths := restRep.length.2
              simp [absent] at lengths
            refine ⟨.values (sourceValue :: sources), after, finalMap, finalWorld,
              .cons execution sourceTrace, ?_, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans metadata⟩
            simpa [packValues, nonempty] using
              ResultFor.values (codes := lowered :: nextCode :: codes)
                (.cons (model.extend payload maps worlds) restRep)

/-- Finite source arguments, including failures, produce the actual Core
bundle. Child correspondence is universal over all related states. -/
theorem preserves_for (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : PreservesFor model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.ValuesOutcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.Recursive.Expressions program registry frame context environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases outcome with
  | values sources =>
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := preserves_values_for tree meaning environments heaps locals layout execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented,
      finalHeaps, maps, worlds, frame, metadata⟩
  | fault reason =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := preserves_fault_for tree meaning environments heaps locals layout execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault represented,
      finalHeaps, maps, worlds, frame, metadata⟩

/-- Only an existing finite source trace supplies a sufficient fuel bound. -/
theorem preserves_sufficient_fuel_for (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : PreservesFor model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.ValuesOutcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.Recursive.Expressions program registry frame context environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) ∧
      ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := preserves_for tree meaning environments heaps locals layout execution
  obtain ⟨required, runs⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required, runs, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem reflects_done_for (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : ReflectsFor model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value} {fuel : Nat}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (completed : runStateful fuel
      (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expressions program registry frame context environment before ids outcome after ∧
      ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects_for tree meaning environments heaps locals layout (runStateful_evaluation_sound completed)

/-- An accepted user-callable gate evaluates recursive staged arguments at
its two real hidden slots. An argument failure returns before application and
keeps its own origin, rather than relabelling it as a fault at the caller. -/
theorem preserves_call_argument_fault_for
    {site : SourceCoreCallableContracts.Callsite} {call callee : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : PreservesFor model program registry frame context certificate faults)
    (coverage : CallStageBoundary.CoversFor model frame.guards site call ids node.type lowered.type)
    (unknown : Word) (resultType : Ty)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before middle after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {callable : Dynamic.Value} {contract : Staging.CallGuard.Contract}
    {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (child : Staging.Recursive.Expression program registry frame context environment before callee (.value callable) middle)
    (bound : frame.guards.Binds callable contract)
    (accepted : Staging.CallBoundary.GuardAccepts frame.guards call ids callable)
    (arguments : Staging.Recursive.Expressions program registry frame context environment middle ids (.fault failure) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown resultType (lowered.expression.rename ξ)
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)) (.inLeft resultType (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨carrier, middleStore, middleMap, middleWorld, calleeRun, represented, middleHeaps,
    firstMaps, firstWorlds, firstFrame, firstMetadata⟩ := meaning certified found environments heaps locals layout child
  cases represented with
  | value payload =>
    obtain ⟨dispatch⟩ := coverage payload bound
    rw [dispatch.shape] at calleeRun
    have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) canonical
        (.unit :: .pair dispatch.function (.word dispatch.contract) :: actual) := GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix layout (.pair dispatch.function (.word dispatch.contract))) .unit
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentRun, matched, finalHeaps,
      maps, worlds, preserved, metadata⟩ := preserves_fault_for tree meaning
        (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata) nextLayout arguments
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentRun
    have gate : CallableContract.decision site.gates .beforeArguments unknown dispatch.contract = none := by
      rw [site.decision_known .beforeArguments unknown dispatch.contract dispatch.row dispatch.found]
      exact SourceCoreCallableContracts.reason_accepted _ _ _ (dispatch.accepted accepted)
    exact ⟨token, finalStore, finalMap, finalWorld,
      CallableContract.call_argument_failure site.gates unknown calleeRun gate argumentRun,
      matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
      firstFrame.trans preserved, firstMetadata.trans metadata⟩


end Ambient

/-- The legacy result keeps the original catalog projection and runtime definitions. -/
abbrev Result {catalog : SourceCoreDataCatalog.Catalog} :=
  @ResultFor catalog (GenericHeap.strictProjection catalog) catalog.definitions

abbrev Result.values {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {faults : FaultRep} {sources : List Dynamic.Value} {values : List Value}
    (represented : Values model mapping world types (codes.map (·.type)) sources values) :
    Result model mapping world types codes faults (.values sources) (.inRight .word (packValues values)) :=
  ResultFor.values represented

abbrev Result.fault {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {faults : FaultRep}
    {reason : Staging.Recursive.Failure} {token : Word} (represented : faults reason token) :
    Result model mapping world types codes faults (.fault reason)
      (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) :=
  ResultFor.fault represented

variable {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
  {program : Program} {registry : Staging.Recursive.Registry} {frame : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : Certificate} {faults : FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}

theorem preserves_values (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.Recursive.Expressions program registry frame context environment before ids (.values sources) after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves_values_for tree meaning environments heaps locals layout execution

theorem preserves_fault (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.Recursive.Expressions program registry frame context environment before ids (.fault reason) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves_fault_for tree meaning environments heaps locals layout execution

theorem reflects (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Reflects model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expressions program registry frame context environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects_for tree meaning environments heaps locals layout evaluated

theorem preserves (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.ValuesOutcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.Recursive.Expressions program registry frame context environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves_for tree meaning environments heaps locals layout execution

theorem preserves_sufficient_fuel (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Staging.Recursive.ValuesOutcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Staging.Recursive.Expressions program registry frame context environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves_sufficient_fuel_for tree meaning environments heaps locals layout execution

theorem reflects_done (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Reflects model program registry frame context certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value} {fuel : Nat}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (completed : runStateful fuel
      (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Expressions program registry frame context environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects_done_for tree meaning environments heaps locals layout completed

/-- An accepted user-callable gate evaluates recursive staged arguments at
its two real hidden slots. An argument failure returns before application and
keeps its own origin, rather than relabelling it as a fault at the caller. -/
theorem preserves_call_argument_fault
    {site : SourceCoreCallableContracts.Callsite} {call callee : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (certified : certificate scope callee lowered) (found : frame.source.lookupExpression? callee = some node)
    (tree : Tree frame.source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program registry frame context certificate faults)
    (coverage : CallStageBoundary.Covers model frame.guards site call ids node.type lowered.type)
    (unknown : Word) (resultType : Ty)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before middle after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {callable : Dynamic.Value} {contract : Staging.CallGuard.Contract}
    {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (child : Staging.Recursive.Expression program registry frame context environment before callee (.value callable) middle)
    (bound : frame.guards.Binds callable contract)
    (accepted : Staging.CallBoundary.GuardAccepts frame.guards call ids callable)
    (arguments : Staging.Recursive.Expressions program registry frame context environment middle ids (.fault failure) after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (site.lower unknown resultType (lowered.expression.rename ξ)
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)) (.inLeft resultType (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  preserves_call_argument_fault_for certified found tree meaning coverage unknown resultType
    environments heaps locals layout child bound accepted arguments

end Solcore.SourceSemantics.CoreLowering.RecursiveStageArguments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveStageCalls
/-! The actual closure parameter prefix composes with recursively staged body
meaning. Forward preservation accepts a finite independent staged invocation;
reflection reconstructs that invocation from Core completion. The body IH is
universal over related states, and scope selection is static provenance.
Neither is hidden inside code authenticity or supplied as a child evaluation.
The ordinary decorated-code profile still requires canonical source alignment;
metadata-view body simulation and new source-cell layouts are separate work. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveStageCalls
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open FunctionArguments FunctionCallBody RecursiveStageMeaning

variable {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
  {program : Program} {registry : Staging.Recursive.Registry} {caller : Staging.Recursive.Scope}
  {function : Dynamic.Closure} {bodyCertificate : FunctionCode.BodyCertificate}
  {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
  {table : SourceCoreStageCodebook.Table} {active : TypeSystem.Substitution}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {actual : Environment} {faults : RecursiveStageMeaning.FaultRep}

/-- Parameter allocation is derived from the emitted wrapper. A failure deep
inside the selected body keeps its own scope label and exact mutated heap. -/
theorem preserves
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    (bodyMeaning : ∀ child, registry.Closure function child →
      RecursiveStageMeaning.BodyPreserves model program registry child function bodyCertificate faults)
    {before after : Dynamic.Heap} {store : Store} {arguments : List Dynamic.Value} {values : List Value}
    {context : SourceSemantics.Context} {outcome : Staging.Recursive.Outcome}
    (represented : Arguments model mapping world code.artifact.raw.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (execution : Staging.Recursive.Applies program registry caller context before (.closure function) arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues values :: actual) store
        (code.artifact.raw.rawBody.rename layout.embedding.lift) value finalStore ∧
      RecursiveStageMeaning.ResultRepresents model finalMap finalWorld function.resultType code.artifact.raw.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have arity : function.parameters.length = arguments.length := by
    rw [← code.artifact.raw.parametersTree.binders, List.length_map]
    exact represented.length.1
  cases execution with
  | closureArity mismatch => exact False.elim (mismatch arity)
  | closure selected _ extension copy allocated executed returned =>
    obtain ⟨entry⟩ := ContractedFunctionCalls.entry_exists layout code extension represented heaps locals
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy entry.copy
    obtain ⟨rfl, rfl⟩ := allocations_same allocated entry.allocation
    obtain ⟨_, _, typed, _⟩ := frame_body_at code.frame extension
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
      bodyMeaning _ selected code.artifact.raw.bodyTree typed entry.environments entry.heaps entry.locals entry.lookups
        ⟨_, _, executed, returned⟩
    exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, result, finalHeaps,
      entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata⟩

/-- A selected authentic body scope is an input of code/value provenance.
Core completion alone then constructs the finite recursive source invocation;
no prior source trace or body evaluation is assumed. -/
theorem reflects
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : ContractedFunctionValues.Code catalog program bodyCertificate policy compilation table active
      function scope layout.administrativeContext)
    {child : Staging.Recursive.Scope} (selected : registry.Closure function child)
    (bodyMeaning : RecursiveStageMeaning.BodyReflects model program registry child function bodyCertificate faults)
    {before : Dynamic.Heap} {store finalStore : Store} {arguments : List Dynamic.Value} {values : List Value}
    (context : SourceSemantics.Context) {value : Value}
    (represented : Arguments model mapping world code.artifact.raw.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (evaluated : Evaluates (DataPatternValues.packValues values :: actual) store
      (code.artifact.raw.rawBody.rename layout.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Staging.Recursive.Applies program registry caller context before (.closure function) arguments outcome after ∧
      RecursiveStageMeaning.ResultRepresents model finalMap finalWorld function.resultType code.artifact.raw.resultCore faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨types, callContext, _, _, extension, typed, _⟩ := frame_body code.frame
  obtain ⟨entry⟩ := ContractedFunctionCalls.entry_exists layout code extension represented heaps locals
  obtain ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
    bodyMeaning code.artifact.raw.bodyTree typed entry.environments entry.heaps entry.locals entry.lookups
      (entry.agreement.unwrap evaluated)
  obtain ⟨finalContext, control, executed, returned⟩ := trace
  exact ⟨outcome, after, finalMap, finalWorld,
    .closure selected code.frame extension entry.copy entry.allocation executed returned,
    result, finalHeaps, entry.maps.trans maps, entry.worlds.trans worlds,
    entry.frame.trans frame, entry.metadata.trans metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveStageCalls
end
