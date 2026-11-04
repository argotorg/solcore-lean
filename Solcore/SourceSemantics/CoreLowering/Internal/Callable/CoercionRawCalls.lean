import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionContextualConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins

/-!
# Coercions: raw named calls

Certificates, meaning, admission and arguments of raw named calls under coercion.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallCertificates
/-! One actual outer direct call selects an ordinary catalog header. Coverage
is required only for this reached full record; coercion methods in the same
global inventory need not be ordinary headers. The ordered argument Tree uses
the original source and actual callback results. Execution laws are absent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallCertificates
open Core Frontend SourceInference GeneralHeap
open CallableCoercionExpressionCertificates RecursiveNamedCatalog

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilerProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project caller compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)

/-- Reached inventory coverage retains the entire specialization and signature,
not just their keys or erased native types. No all-global coverage is required. -/
structure Reached (header : Header prepared values ambient.definitions program) : Prop where
  member : header ∈ headers
  plan : compilation.plan = base.plan
  specialized : receipt.selection.specialized = header.named.specialized
  signature : receipt.native.signature = header.named.signature
  slot : receipt.native.index = header.slot
  occurrenceOrder : instantiation.parameterSubstitution.map Prod.fst =
    (receipt.selection.specialized.parameterSubstitution.map Prod.fst).reverse
  emptyPredicates : instantiation.predicates = []
  headerOrder : header.instantiation.parameterSubstitution.map Prod.fst =
    (header.named.specialized.parameterSubstitution.map Prod.fst).reverse

/-- Restrict the full selected record with the legacy empty-predicate fact. -/
theorem Reached.selected (reached : Reached receipt (headers := headers) header) :
    RecursiveNamedCallEvidenceHeads.Selected receipt (headers := headers) header :=
  ⟨reached.member, reached.plan, reached.specialized, reached.signature, reached.slot,
    reached.occurrenceOrder, reached.headerOrder⟩

theorem Reached.metadata (reached : Reached receipt (headers := headers) header) :
    instantiation = header.instantiation := reached.selected receipt |>.metadata receipt

theorem Reached.predicates (reached : Reached receipt (headers := headers) header) :
    instantiation.predicates = [] := reached.emptyPredicates

theorem Reached.arity (reached : Reached receipt (headers := headers) header) :
    header.function.parameters.length = arguments.length := reached.selected receipt |>.arity receipt

/-- Independent original typing determines the raw return type and source
callee fields before the output coercion path. It does not run the source. -/
theorem source_types {context : SourceSemantics.Context}
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (typed : ExpressionHasType source context id node.type) :
    node.rawType = header.function.resultType ∧
    ∃ calleeNode name, source.lookupExpression? callee = some calleeNode ∧
      calleeNode.form = .reference name (.declaration header.instantiation) ∧
      calleeNode.requirements = [] ∧ calleeNode.coercions = [] ∧
      SourceSemantics.DeclarationInstantiation.Valid context header.instantiation := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | intro contains raw rawEq _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.found)
    subst same
    rw [receipt.form, reached.metadata] at raw
    cases raw with
    | directCall calleeValid application _ =>
      cases application with
      | intro signatureMember _ declarationEq _ resultEq _ _ =>
        have result := resultEq.symm.trans (sourceTypes.result header reached.member _ signatureMember declarationEq)
        refine ⟨rawEq.trans result, ?_⟩
        cases calleeValid with
        | intro contains form valid _ requirements coercions =>
          exact ⟨_, _, lookupExpression?_complete unique contains, form, requirements, coercions, valid.toValid closed residual⟩

include receipt in
/-- With no signature predicates, the original ordered direct-call split
produces an empty invocation dictionary in every caller environment. -/
theorem source_dictionary {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (predicates : instantiation.predicates = [])
    (typed : ExpressionHasType source context id node.type)
    (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.DirectCallProducesEvidence context evidence node.requirements node.coercions instantiation.predicates [] := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | intro contains raw _ _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.found)
    subst same
    rw [receipt.form] at raw
    cases raw with
    | directCall _ application _ =>
      cases application with
      | intro _ _ _ _ _ _ predicatesEq =>
        cases requirements with
        | directCall valid =>
          rw [← predicatesEq, predicates] at valid
          rw [predicates]
          cases valid with
          | intro _ _ signatureValid steps ids =>
            cases signatureValid
            exact .intro steps ids .nil

/-- The static argument certificate refers to exactly the ordered code list
returned by the real outer compiler callback on the original source. -/
structure Certificate (readFuel : Nat) (context : SourceSemantics.Context)
    (header : Header prepared values ambient.definitions program) where
  reached : Reached receipt (headers := headers) header
  rawType : node.rawType = header.function.resultType
  calleeNode : ExpressionNode
  name : String
  calleeFound : source.lookupExpression? callee = some calleeNode
  calleeForm : calleeNode.form = .reference name (.declaration header.instantiation)
  calleeRequirements : calleeNode.requirements = []
  calleeCoercions : calleeNode.coercions = []
  valid : SourceSemantics.DeclarationInstantiation.Valid context header.instantiation
  evidence : header.function.evidence = []
  dictionary : ∀ evidence, Dynamic.DirectCallProducesEvidence context evidence node.requirements node.coercions instantiation.predicates []
  children : DataExpressionSequence.Tree source
    (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
    scope arguments (header.bindings.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments
  nativeTypes : receipt.loweredArguments.map (·.type) = header.bindings.map Prod.snd

theorem of_tree {readFuel : Nat} {context : SourceSemantics.Context}
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (typed : ExpressionHasType source context id node.type)
    (children : DataExpressionSequence.Tree source
      (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
      scope arguments (header.bindings.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
    (nativeTypes : receipt.loweredArguments.map (·.type) = header.bindings.map Prod.snd) :
    Nonempty (Certificate receipt readFuel context (headers := headers) header) := by
  obtain ⟨rawType, calleeNode, name, found, form, requirements, coercions, valid⟩ :=
    source_types receipt reached sourceTypes unique closed residual typed
  exact ⟨⟨reached, rawType, calleeNode, name, found, form, requirements, coercions, valid,
    sourceTypes.evidence header reached.member, source_dictionary receipt unique reached.predicates typed, children, nativeTypes⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallMeaning
/-! Raw ordinary calls retain their original requirement/coercion lists.
Actual argument and callee grades are consumed by the existing bounded call
proof; the catalog mutual theorem closes both meaning families internally.
Source and Core grades are independent. Initial catalog and method authority,
and static profiles at actual body entries, remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning
open CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

private theorem dictionary_empty {context : SourceSemantics.Context}
    {caller result : Dynamic.EvidenceEnvironment} {requirements : List RequirementId}
    {coercions : List CoercionStep}
    (produced : Dynamic.DirectCallProducesEvidence context caller requirements coercions [] result) : result = [] := by
  cases produced with
  | intro _ _ produced => simpa using produced.length_eq.2.symm

section RawTrace
variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {node calleeNode : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {invocation : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}

theorem raw_inv
    (form : node.form = .call callee arguments (.declaration instantiation))
    (found : source.lookupExpression? callee = some calleeNode)
    (predicates : instantiation.predicates = []) (empty : invocation = [])
    (trace : RawOutcome program context evidence source environment before node outcome after) :
    ∃ size, RecursiveNamedArgumentTraceBounds.TraceAt program context evidence invocation source environment before
      arguments instantiation size outcome after := by
  subst invocation
  cases outcome with
  | value value =>
    obtain ⟨size, raw⟩ := SourceExecutionSize.ExpressionFormEvaluates.has_size trace
    refine ⟨size, ?_⟩
    rw [form] at raw
    cases raw with
    | directCall _ _ _ _ _ evaluated produced applied =>
      rw [predicates] at produced
      cases dictionary_empty produced
      exact .apply evaluated (.value applied)
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
  | fault reason =>
    obtain ⟨size, raw⟩ := SourceExecutionSize.ExpressionFormFaults.has_size trace
    refine ⟨size, ?_⟩
    rw [form] at raw
    cases raw with
    | directCalleeMissing absent =>
      exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
    | directArguments _ _ failed =>
      exact .argumentFault failed (SourceExecutionSize.child_lt_stepSize (by simp))
    | directRequirements _ failed =>
      rw [predicates] at failed
      have impossible : ∀ ids bad, ¬ Dynamic.RequirementsFault context evidence ids [] bad := by intro ids bad h; cases h
      exact False.elim (impossible _ _ failed)
    | directApply evaluated produced failed =>
      rw [predicates] at produced
      cases dictionary_empty produced
      exact .apply evaluated (.fault failed)
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))

theorem raw_intro {name : String} {size : Nat}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (found : source.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (requirements : calleeNode.requirements = []) (coercions : calleeNode.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (produced : Dynamic.DirectCallProducesEvidence context evidence node.requirements node.coercions instantiation.predicates invocation)
    (trace : RecursiveNamedArgumentTraceBounds.TraceAt program context evidence invocation source environment before
      arguments instantiation size outcome after) :
    RawOutcome program context evidence source environment before node outcome after := by
  cases trace with
  | argumentFault failed _ =>
    change Dynamic.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _
    rw [form]
    exact .directArguments (lookupExpression?_sound found) calleeForm failed.sound
  | apply evaluated called _ _ =>
    cases called with
    | value applied =>
      change Dynamic.ExpressionFormEvaluates _ _ _ _ _ _ _ _ _ _ _
      rw [form]
      exact .directCall (lookupExpression?_sound found) calleeForm requirements coercions valid evaluated.sound produced applied.sound
    | fault failed =>
      change Dynamic.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _
      rw [form]
      exact .directApply evaluated.sound produced failed.sound
end RawTrace

section RawLaws
variable {checked : Checked} {base : Base checked}
  {ancestry : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : ((Program.ofChecked compilerProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (bodyCompilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (bodyCompilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {reasonAt : ExpressionId → Word} {readFuel fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {project : Projector} {callerFunction : Specialized} {child : SourceCoreEvidence.Child}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project callerFunction compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)
  {header : Header ancestry values ambient.definitions (Program.ofChecked compilerProgram)}
  (certified : Certificate receipt readFuel context (headers := headers) header)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative
    scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : RecursiveNamedCatalog.Entry headers locations capturePrefix compilation.administrativePrefix
    scope mapping world before store canonical)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing
  certified environments heaps locals agrees actualTyped installed in
/-- Every raw argument/body obligation is supplied by catalog mutual induction.
The only source execution input is the independent original raw-form trace. -/
theorem raw_preserves :
    RawFormPreserves (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before actual mapping world store node ξ receipt.operand := by
  intro outcome after raw
  have form := receipt.form
  rw [certified.reached.metadata] at form
  have predicates : header.instantiation.predicates = [] := by
    rw [← certified.reached.metadata]
    exact certified.reached.predicates
  obtain ⟨size, trace⟩ := raw_inv form certified.calleeFound predicates certified.evidence raw
  have packed : header.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    rw [← certified.reached.signature]
    exact receipt.native.inputType
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, admin, metadata, _⟩ :=
    RecursiveNamedExpressionHeadBounds.call_preserves_bounded functions certified.children certified.nativeTypes packed size
      (fun n _ => RecursiveNamedCatalogMutualMeaning.expression_preserves_at functions extension faithful observations runtimeViews owners
        uninitialized missing escaped prefixMatches profiles evidence valid sourceUnique callerUninitialized callerMissing n)
      (fun n _ => RecursiveNamedCatalogMutualMeaning.preserves_at functions extension faithful observations runtimeViews owners
        uninitialized missing escaped prefixMatches profiles n header certified.reached.member)
      owners certified.reached.member installed environments heaps locals agrees actualTyped trace (Nat.le_refl size)
  refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, admin, metadata⟩
  · simpa only [receipt.native.emitted, certified.reached.signature, certified.reached.slot,
      NamedCalls.Arguments.call_rename] using evaluated
  · simpa only [certified.rawType, receipt.native.emitted, certified.reached.signature, header.resultType] using represented

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing
  certified environments heaps locals agrees actualTyped installed in
/-- Only the actual native completion is measured. Reflection constructs its
independent source trace and never consumes preservation or a source run. -/
theorem raw_reflects :
    RawFormReflects (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before actual mapping world store node ξ receipt.operand := by
  intro value finalStore completed
  obtain ⟨size, measured⟩ := evaluation_has_size completed
  have packed : header.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    rw [← certified.reached.signature]
    exact receipt.native.inputType
  simp only [receipt.native.emitted, certified.reached.signature, certified.reached.slot,
    NamedCalls.Arguments.call_rename] at measured
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, admin, metadata, _⟩ :=
    RecursiveNamedExpressionHeadBounds.call_reflects_bounded functions certified.children certified.nativeTypes packed size
      (fun n _ => RecursiveNamedCatalogMutualMeaning.expression_reflects_at functions extension faithful observations runtimeViews
        uninitialized missing escaped prefixMatches profiles evidence valid callerUninitialized callerMissing n)
      (fun n _ => RecursiveNamedCatalogMutualMeaning.reflects_at functions extension faithful observations runtimeViews
        uninitialized missing escaped prefixMatches profiles n header certified.reached.member)
      certified.reached.member installed environments heaps locals agrees actualTyped measured (Nat.le_refl size)
  have form := receipt.form
  rw [certified.reached.metadata] at form
  have produced : Dynamic.DirectCallProducesEvidence context evidence node.requirements node.coercions
      header.instantiation.predicates header.function.evidence := by
    simpa only [certified.reached.metadata, certified.evidence] using certified.dictionary evidence
  refine ⟨outcome, after, finalMap, finalWorld,
    raw_intro form certified.calleeFound certified.calleeForm certified.calleeRequirements certified.calleeCoercions certified.valid produced trace,
    ?_, finalHeaps, maps, worlds, admin, metadata⟩
  simpa only [certified.rawType, receipt.native.emitted, certified.reached.signature, header.resultType] using represented

end RawLaws

section Outer
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : ((Program.ofChecked compilerProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (bodyCompilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (bodyCompilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {reasonAt : ExpressionId → Word} {readFuel fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {project : Projector} {callerFunction : Specialized} {child : SourceCoreEvidence.Child}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project callerFunction compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)
  {header : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)}
  (certified : Certificate receipt readFuel context (headers := headers) header)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative
    scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : RecursiveNamedCatalog.Entry headers locations capturePrefix compilation.administrativePrefix
    scope mapping world before store canonical)

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {methods : CallableCoercionPathMeaning.Profiles (prepared := prepared) (values := values)
    (program := Program.ofChecked compilerProgram) (context := context) (evidence := evidence)}
  (methodUninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (methodMissing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {calls : List CallableCoercionSpine.Call}
  (emitted : CallableCoercionMethodEntries.Emitted compilerProgram project compilation callerFunction receipt.available
    scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : CallableCoercionPathMeaning.Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (methodEntry : CallableCoercionMethodEntries.Entry methods ambient.definitions actual mapping world before store)

include checkedAccepted extension definitions registered faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing certified environments heaps locals agrees actualTyped installed
  methodUninitialized methodMissing emitted steps chain ledger methodEntry in
/-- The final consumer closes raw arguments and recursive ordinary bodies and
then preserves the independent original ordered output path. -/
theorem preserves
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  exact CallableCoercionExpressionMeaning.preserves functions checkedAccepted extension definitions registered faithful observations runtimeViews
    methodUninitialized methodMissing receipt.toOutput emitted steps chain ledger methodEntry sourceUnique
    (by intros; simp [receipt.form])
    (raw_preserves functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles
      valid sourceUnique callerUninitialized callerMissing receipt certified environments heaps locals agrees actualTyped installed) trace

include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid callerUninitialized callerMissing certified environments heaps locals agrees actualTyped installed
  methodUninitialized methodMissing emitted steps chain methodEntry in
/-- Original native completion supplies both the raw call and the ordered path
completion. No prior source execution or preservation law is an input. -/
theorem reflects
    {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  exact CallableCoercionExpressionMeaning.reflects functions extension definitions registered faithful observations runtimeViews
    methodUninitialized methodMissing receipt.toOutput emitted steps chain methodEntry
    (raw_reflects functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
      valid callerUninitialized callerMissing receipt certified environments heaps locals agrees actualTyped installed) completed
end Outer

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallAdmission
/-! The reached header already retains closed declaration validity from its
independent source instantiation. Transport that exact witness into the real
caller context. Its residual-variable flag and lexical variables are unchanged;
no inference from ground types or native code is needed. Ordered argument Trees,
actual profiles and entry/capture/history receipts remain separate inputs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallAdmission
open Core Frontend SourceInference GeneralHeap
open CallableCoercionExpressionCertificates CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog

/-- A closed catalog context embeds in any context with the same signatures
and independently well-formed rigid binders. The target scopes are unchanged. -/
theorem catalog_supports {signatures : ProgramSignatures} {context : SourceSemantics.Context}
    (same : context.signatures = signatures) (binders : TypeParameterBindersWellFormed context) :
    Dynamic.TypeContextSupports (SourceSemantics.Context.ofSignatures signatures) context := by
  exact {
    signatures := same
    parameters := by intro parameter member; cases member
    parameterOwners := by intro parameter member; cases member
    variables := by intro metavariable member; cases member
    residualVariables := by intro impossible; cases impossible
    targetBinders := binders
  }

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilerProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project caller compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)


/-- Use the complete source instantiation in the actual reached header. This
contains range well-formedness, staging fields and the full predicate list. -/
theorem header_valid (header : Header prepared values ambient.definitions program)
    {context : SourceSemantics.Context}
    (signatures : context.signatures = program.signatures)
    (binders : TypeParameterBindersWellFormed context) :
    SourceSemantics.DeclarationInstantiation.Valid context header.instantiation := by
  have instantiated := header.frame.instantiated
  cases instantiated with
  | intro _ _ _ _ valid _ _ _ =>
    exact Dynamic.DeclarationInstantiation.Valid.transportContext (catalog_supports signatures binders) valid

/-- Original static typing supplies binder well-formedness; the reached header
supplies closed range validity even in a residually open caller context. -/
theorem source_types {context : SourceSemantics.Context}
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source)
    (signatures : context.signatures = program.signatures)
    (typed : ExpressionHasType source context id node.type) :
    node.rawType = header.function.resultType ∧
    ∃ calleeNode name, source.lookupExpression? callee = some calleeNode ∧
      calleeNode.form = .reference name (.declaration header.instantiation) ∧
      calleeNode.requirements = [] ∧ calleeNode.coercions = [] ∧
      SourceSemantics.DeclarationInstantiation.Valid context header.instantiation := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | intro contains raw rawEq rawTyped _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.found)
    subst same
    rw [receipt.form, reached.metadata] at raw
    cases raw with
    | directCall calleeValid application _ =>
      cases application with
      | intro signatureMember _ declarationEq _ resultEq _ _ =>
        have result := resultEq.symm.trans (sourceTypes.result header reached.member _ signatureMember declarationEq)
        refine ⟨rawEq.trans result, ?_⟩
        cases calleeValid with
        | intro contains form valid _ requirements coercions =>
          exact ⟨_, _, lookupExpression?_complete unique contains, form, requirements, coercions, header_valid header signatures rawTyped.binders⟩

/-- Reuse the original certificate and exact callback code list. This factory
requires neither closed flexible scopes nor a false residual-variable flag. -/
theorem of_tree {readFuel : Nat} {context : SourceSemantics.Context}
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source)
    (signatures : context.signatures = program.signatures)
    (typed : ExpressionHasType source context id node.type)
    (children : DataExpressionSequence.Tree source
      (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
      scope arguments (header.bindings.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
    (nativeTypes : receipt.loweredArguments.map (·.type) = header.bindings.map Prod.snd) :
    Nonempty (Certificate receipt readFuel context (headers := headers) header) := by
  obtain ⟨rawType, calleeNode, name, found, form, requirements, coercions, valid⟩ :=
    source_types receipt reached sourceTypes unique signatures typed
  exact ⟨⟨reached, rawType, calleeNode, name, found, form, requirements, coercions, valid,
    sourceTypes.evidence header reached.member, source_dictionary receipt unique reached.predicates typed, children, nativeTypes⟩⟩


end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallScalarArguments
/-! Actual ordered argument lowering supplies the scalar argument Trees and
native type vector. The original caller context and parent metadata are kept.
Only the reached full ordinary header is needed; no inventory-wide coverage or
argument/body execution law is part of this static extraction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallScalarArguments
open Core Frontend SourceInference GeneralHeap
open CallableCoercionExpressionCertificates CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilerProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project caller compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)


/-- Original raw application typing fixes the ordered source parameter list,
including before a nonempty parent output-coercion path. -/
theorem argument_types {context : SourceSemantics.Context}
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id node.type) :
    ExpressionsHaveTypes source context arguments (header.bindings.map (fun binding => binding.1.scheme.body)) := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | intro contains raw _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.found)
    subst same
    rw [receipt.form, reached.metadata] at raw
    cases raw with
    | directCall _ application argumentsTyped =>
      cases application with
      | intro signatureMember _ declarationEq parameterEq _ _ _ =>
        have parameters := parameterEq.symm.trans (sourceTypes.parameters header reached.member _ signatureMember declarationEq)
        exact parameters ▸ argumentsTyped

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The scalar grammar embeds without changing any source, context, code or
metadata. Its semantic laws are already closed by the existing finite Tree. -/
theorem embed {readFuel : Nat} {context : SourceSemantics.Context}
    {id : ExpressionId} {code : Lowered}
    (tree : CompatibleExpressionConditionals.Tree readFuel values source context compilation.solvedRequirements reasonAt scope id code) :
    Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id code :=
  .fragment (.fragment (.fragment (.fragment (.fragment (.fragment tree)))))

private theorem sequence
    {readFuel : Nat} {context : SourceSemantics.Context} {ids : List ExpressionId}
    {types : List TypeSystem.Ty} {codes : List Lowered}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source context ids types)
    (accepted : ids.mapM (fun id => child fuel source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type → child fuel source scope id reasonAt = .ok code →
      CompatibleExpressionConditionals.Tree readFuel values source context compilation.solvedRequirements reasonAt scope id code) :
    DataExpressionSequence.Tree source
      (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
      scope ids types codes ∧ types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst codes
    exact ⟨.nil, rfl⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at accepted
      obtain ⟨code, first, accepted⟩ := bind_ok accepted
      obtain ⟨restCodes, rest, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have tree := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨remaining, projected⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      have sequence : DataExpressionSequence.Tree source
          (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
          scope (id :: ids) (type :: types) (code :: restCodes) := by
        cases remaining with
        | nil => exact sourceType ▸ .single found (embed tree)
        | single nextFound nextTree => exact sourceType ▸ .cons found (embed tree) (.single nextFound nextTree)
        | cons nextFound nextTree tailTree => exact sourceType ▸ .cons found (embed tree) (.cons nextFound nextTree tailTree)
      refine ⟨sequence, ?_⟩
      simp [List.mapM_cons, ← sourceType, tree.projected found, projected, bind, Except.bind]

/-- The actual contextual callback is consumed at each ordered argument. No
argument Tree or native parameter vector is supplied by the caller. -/
theorem of_contextual {readFuel : Nat} {context : SourceSemantics.Context}
    {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId}
    (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures locals parents
      assignments diagnostics compilation native parent skipInitializer)
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source)
    (sourceSignatures : context.signatures = program.signatures)
    (typed : ExpressionHasType source context id node.type)
    (syntaxTrees : ∀ argument, argument ∈ arguments → CompatibleExpressionConditionals.Syntax source argument)
    (ordinary : CompatibleExpressionConditionals.Ordinary source locals compilation.owner)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values) :
    Nonempty (Certificate receipt readFuel context (headers := headers) header) := by
  have argumentsTyped := argument_types receipt reached sourceTypes unique typed
  obtain ⟨children, projected⟩ := sequence (headers := headers) (compilation := compilation) unique argumentsTyped receipt.argumentsAccepted
    (fun argument member node code found typed accepted =>
      CompatibleExpressionConditionals.tree_of_contextual ordinary unique declarations (syntaxTrees argument member) found typed
        readPolicy lowerPolicy leafPolicy (by simpa only [childEq] using accepted))
  have nativeTypes := Except.ok.inj (projected.symm.trans (sourceTypes.projections header reached.member))
  exact CallableCoercionRawNamedCallAdmission.of_tree receipt reached sourceTypes unique sourceSignatures typed children nativeTypes

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallScalarArguments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallBuiltinArguments
/-! Actual ordered argument lowering supplies recursive builtin argument Trees and
native type vector. The original caller context and parent metadata are kept.
Only the reached full ordinary header is needed; no inventory-wide coverage or
argument/body execution law is part of this static extraction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallBuiltinArguments
open Core Frontend SourceInference GeneralHeap
open CallableCoercionExpressionCertificates CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilerProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project caller compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)


private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The builtin grammar embeds without changing any source, context, code or
metadata. Its semantic laws are already closed by the existing finite Tree. -/
theorem embed {readFuel : Nat} {context : SourceSemantics.Context}
    {id : ExpressionId} {code : Lowered}
    (tree : CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt scope id code) :
    Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id code :=
  .fragment tree

private theorem sequence
    {readFuel : Nat} {context : SourceSemantics.Context} {ids : List ExpressionId}
    {types : List TypeSystem.Ty} {codes : List Lowered}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source context ids types)
    (accepted : ids.mapM (fun id => child fuel source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type → child fuel source scope id reasonAt = .ok code →
      CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt scope id code) :
    DataExpressionSequence.Tree source
      (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
      scope ids types codes ∧ types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst codes
    exact ⟨.nil, rfl⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at accepted
      obtain ⟨code, first, accepted⟩ := bind_ok accepted
      obtain ⟨restCodes, rest, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have tree := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨remaining, projected⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      have sequence : DataExpressionSequence.Tree source
          (Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt)
          scope (id :: ids) (type :: types) (code :: restCodes) := by
        cases remaining with
        | nil => exact sourceType ▸ .single found (embed tree)
        | single nextFound nextTree => exact sourceType ▸ .cons found (embed tree) (.single nextFound nextTree)
        | cons nextFound nextTree tailTree => exact sourceType ▸ .cons found (embed tree) (.cons nextFound nextTree tailTree)
      refine ⟨sequence, ?_⟩
      simp [List.mapM_cons, ← sourceType, tree.projected found, projected, bind, Except.bind]

/-- The actual contextual callback is consumed at each ordered argument. No
argument Tree or native parameter vector is supplied by the caller. -/
theorem of_contextual {readFuel : Nat} {context : SourceSemantics.Context}
    {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId}
    (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures locals parents
      assignments diagnostics compilation (some native) parent skipInitializer)
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source)
    (sourceSignatures : context.signatures = program.signatures)
    (nativeSignatures : context.signatures = values.checked.signatures)
    (typed : ExpressionHasType source context id node.type)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (syntaxTrees : ∀ argument, argument ∈ arguments → CompatibleExpressionBuiltins.Syntax source argument)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values) :
    Nonempty (Certificate receipt readFuel context (headers := headers) header) := by
  have argumentsTyped := CallableCoercionRawNamedCallScalarArguments.argument_types receipt reached sourceTypes unique typed
  obtain ⟨children, projected⟩ := sequence (headers := headers) (compilation := compilation) unique argumentsTyped receipt.argumentsAccepted
    (fun argument member node code found typed accepted =>
      CompatibleExpressionBuiltins.tree_of_contextual_with_validity ordinary unique constructorValid declarations nativeSignatures (syntaxTrees argument member) found typed
        readPolicy lowerPolicy leafPolicy (by simpa only [childEq] using accepted))
  have nativeTypes := Except.ok.inj (projected.symm.trans (sourceTypes.projections header reached.member))
  exact CallableCoercionRawNamedCallAdmission.of_tree receipt reached sourceTypes unique sourceSignatures typed children nativeTypes

/-- Independent program typing supplies the source parameter/result receipt.
Native projections and the exact ordinary invocation evidence remain explicit. -/
theorem of_program {readFuel : Nat} {context : SourceSemantics.Context}
    {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId}
    (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures locals parents
      assignments diagnostics compilation (some native) parent skipInitializer)
    (reached : Reached receipt (headers := headers) header)
    (programTyped : ProgramWellFormed program)
    (projections : ∀ memberHeader, memberHeader ∈ headers →
      (memberHeader.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
        .ok (memberHeader.bindings.map Prod.snd))
    (evidence : ∀ memberHeader, memberHeader ∈ headers → memberHeader.function.evidence = [])
    (unique : NodeOccurrencesUnique source)
    (sourceSignatures : context.signatures = program.signatures)
    (nativeSignatures : context.signatures = values.checked.signatures)
    (typed : ExpressionHasType source context id node.type)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (syntaxTrees : ∀ argument, argument ∈ arguments → CompatibleExpressionBuiltins.Syntax source argument)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values) :
    Nonempty (Certificate receipt readFuel context (headers := headers) header) := by
  exact of_contextual receipt childEq reached
    (RecursiveNamedSourceSignatureFacts.source_types programTyped sourceSignatures projections evidence)
    unique sourceSignatures nativeSignatures typed constructorValid syntaxTrees ordinary declarations readPolicy lowerPolicy leafPolicy

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallBuiltinArguments
end
