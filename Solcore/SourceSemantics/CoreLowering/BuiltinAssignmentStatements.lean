import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualBuiltins
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinMeaning

/-! Concrete builtin assignment heads close the shared expression contract by
induction on the recursive builtin/data grammar. The compiler extractor retains
independent source typing and actual native checker receipts as static inputs.
No source child execution or universal body meaning is an input here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinAssignmentStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

abbrev Head (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) (administrative : Core.Context)
    (definitions : DataEnvironment) (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
    (rhs : ExpressionId) :=
  GenericAssignmentStatements.Head values source context
    (CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt)
    scope administrative definitions assignment operator rhs

theorem Head.of_lower {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {next code : Expr} {output result : Ty} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (extract : ∀ id lowered, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs,
      code = head.emit next output :=
  GenericAssignmentStatements.Head.of_lower unique signatures sourceTyped writable rightTyped profile extract accepted typed

/-- Actual contextual lowering supplies concrete builtin expression certificates
for every reached key/RHS. Source syntax/typing and the native checker receipt
are retained explicitly; no child meaning or execution is assumed. -/
theorem Head.of_contextual_lower
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {site : SourceCoreElaboration.ErrorSite} {next code : Expr} {output result : Ty}
    {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (children : ∀ id lowered, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments diagnostics compilation
        (some native) parent skipInitializer fuel source scope id reasonAt = .ok lowered →
      ∃ node, source.lookupExpression? id = some node ∧ CompatibleExpressionBuiltins.Syntax source id ∧
        ExpressionHasType source context id node.type ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (accepted : lower values values.checked.signatures
      (SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments diagnostics compilation
        (some native) parent skipInitializer) fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head readFuel values source context compilation.solvedRequirements reasonAt scope administrative definitions assignment operator rhs,
      code = head.emit next output := by
  apply Head.of_lower unique sourceSignatures sourceTyped writable rightTyped profile ?_ accepted typed
  intro id lowered member generated
  obtain ⟨node, found, syntaxTree, sourceTyped, nativeTyped⟩ := children id lowered member generated
  exact ⟨node, found, CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations sourceSignatures
    syntaxTree found sourceTyped readPolicy lowerPolicy leafPolicy generated, nativeTyped⟩

namespace Head
variable {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : Head readFuel values source context solved reasonAt scope administrative ambient.definitions assignment operator rhs)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include extension valid unique uninitialized missing faithful observations functionTypes environments heaps locals agrees actualTyped in
theorem preserves_prefix {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  exact GenericAssignmentStatements.Head.preserves_prefix functions extension program evidence
    (CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing) faithful observations head environments heaps locals agrees actualTyped trace

include extension valid unique uninitialized missing faithful observations functionTypes environments heaps locals agrees actualTyped in
theorem preserves_fault (errors : head.Errors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact GenericAssignmentStatements.Head.preserves_fault functions extension program evidence
    (CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing) faithful observations head environments heaps locals agrees actualTyped errors trace next output

include extension valid unique uninitialized missing faithful observations functionTypes environments heaps locals agrees actualTyped in
theorem reflects (errors : head.Errors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  exact GenericAssignmentStatements.Head.reflects functions extension program evidence
    (CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing) (CompatibleExpressionBuiltins.reflects functions extension faithful observations functionTypes program evidence valid uninitialized missing) faithful observations head environments heaps locals agrees actualTyped functionTypes errors completed

end Head
end Solcore.SourceSemantics.CoreLowering.BuiltinAssignmentStatements
