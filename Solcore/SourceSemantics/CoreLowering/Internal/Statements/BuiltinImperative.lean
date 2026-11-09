import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeForMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalControl

/-!
# Builtin imperative statements

Assignments, `for` headers and loops, and matches in bodies with builtin calls.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinAssignmentStatements
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
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
theorem preserves_prefix [FunctionCalls.FaultTokens faults] {updated : Dynamic.Value} {after : Dynamic.Heap}
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
theorem preserves_fault [FunctionCalls.FaultTokens faults] (errors : head.Errors registry faults)
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
theorem reflects [FunctionCalls.FaultTokens faults] (errors : head.Errors registry faults)
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinForHeader
/-! Concrete recursive builtin expressions instantiate all for-header children.
Initializers, discarded expressions, keys and RHS share the same certificate;
source lexical scopes and real marked allocation prefixes remain explicit.
Post restoration keeps newly allocated cells and only restores visible names. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Tail Result Fallthrough)
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Syntax (source : TypedSource) := GenericForHeader.Syntax source (CompatibleExpressionBuiltins.Syntax source)

abbrev Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (definitions : DataEnvironment) (administrative : Core.Context) (type : Ty)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop) :=
  GenericForHeader.Tree layouts owner active frame globals onError values source
    (fun context => CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt)
    definitions administrative type continuation

section Certificates
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {policy : SourceCoreLoops.Policy} {parentSite : SourceCoreElaboration.ErrorSite}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
  {parents : List SourceCoreLocalEvidence.Prepared} {assignmentsTable : SourceCoreAssignmentFaultSites.Table}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
  {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}

theorem tree_of_contextual
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {next : Scope → Except SourceCoreBasic.Error Expr}
    (nextCertificate : ∀ context scope code,
      context.typeVariables = [] → context.residualTypeVariables = false →
      context.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope context →
      next scope = .ok code → continuation context scope code)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm}
    (syntaxTree : Syntax source context items)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {code : Expr} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerForItems policy parentSite fuel source scope items type reasonAt next = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative type continuation
      context scope items code := by
  apply GenericForHeader.tree_of_lowerForItems binderPolicy allocationPolicy assignments unaryPolicy unique ?_
    nextCertificate syntaxTree closed residual sourceSignatures declarations accepted nativeTyped
  intro sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated
  exact ⟨CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures
    syntaxTree found typed readPolicy lowerPolicy leafPolicy (expressionPolicy ▸ generated),
    nativeTyping sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated⟩

end Certificates

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered extension uninitialized missing faithful observations functionTypes in
theorem Tree.preserves_prefix [FunctionCalls.FaultTokens faults] {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative type continuation
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ tail : Tail registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  exact GenericForHeader.Tree.preserves_prefix functions definitions registered extension program evidence (fun context valid => CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing)
    faithful observations tree valid environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered extension uninitialized missing faithful observations functionTypes in
theorem Tree.preserves_fault_reachable [FunctionCalls.FaultTokens faults] {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact GenericForHeader.Tree.preserves_fault_reachable functions definitions registered extension program evidence (fun context valid => CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing)
    faithful observations tree errors valid environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered extension uninitialized missing faithful observations functionTypes in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem Tree.preserves_fault [FunctionCalls.FaultTokens faults] {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  apply Tree.preserves_fault_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

include definitions registered extension uninitialized missing faithful observations functionTypes in
theorem Tree.reflects_reachable [FunctionCalls.FaultTokens faults]     {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    Result registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  exact GenericForHeader.Tree.reflects_reachable functions definitions registered extension program evidence (fun context valid => CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing) (fun context valid => CompatibleExpressionBuiltins.reflects functions extension faithful observations functionTypes program evidence valid uninitialized missing)
    faithful observations functionTypes tree errors valid environments heaps locals agrees actualTyped reference read unmapped evaluated

include definitions registered extension uninitialized missing faithful observations functionTypes in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem Tree.reflects [FunctionCalls.FaultTokens faults]     {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    Result registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  apply Tree.reflects_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

include definitions registered extension uninitialized missing faithful observations functionTypes in
theorem Tree.preserves_post [FunctionCalls.FaultTokens faults] {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative type (Fallthrough type)
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ tail : Tail registry functions source solved evidence administrative frame globals contextLocation native (Fallthrough type) finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      Evaluates actual store (code.rename ξ) (LocalLoop.fallthroughValue type) tail.store ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions := by
  exact GenericForHeader.Tree.preserves_post functions definitions registered extension program evidence (fun context valid => CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing)
    faithful observations tree valid environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered extension uninitialized missing faithful observations functionTypes in
theorem Tree.reflects_post_reachable [FunctionCalls.FaultTokens faults]     {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative type (Fallthrough type)
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    (∃ finalContext finalEnvironment after,
      ∃ tail : Tail registry functions source solved evidence administrative frame globals contextLocation native
        (Fallthrough type) finalContext finalEnvironment after,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧ finalStore = tail.store ∧
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) := by
  exact GenericForHeader.Tree.reflects_post_reachable functions definitions registered extension program evidence (fun context valid => CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing) (fun context valid => CompatibleExpressionBuiltins.reflects functions extension faithful observations functionTypes program evidence valid uninitialized missing)
    faithful observations functionTypes tree errors valid environments heaps locals agrees actualTyped reference read unmapped evaluated

include definitions registered extension uninitialized missing faithful observations functionTypes in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem Tree.reflects_post [FunctionCalls.FaultTokens faults]     {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative type (Fallthrough type)
      context scope items code) (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    (∃ finalContext finalEnvironment after,
      ∃ tail : Tail registry functions source solved evidence administrative frame globals contextLocation native
        (Fallthrough type) finalContext finalEnvironment after,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧ finalStore = tail.store ∧
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) := by
  apply Tree.reflects_post_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.BuiltinForHeader
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinImperativeFor
/-! Recursive builtin expressions close every expression premise in ordinary
lexical control, assignments and while/for loops. Headers, conditions, bodies
and post vectors use one certificate family. Static source typing and actual
native checking remain separate from the finite semantic correspondence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open TypedScopedStatements (Executes)
open TypedLexicalWhile (FlowRep)
open TypedLexicalControl (LexicalResult)
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Syntax (source : TypedSource) := GenericImperativeFor.Syntax source (CompatibleExpressionBuiltins.Syntax source)
abbrev Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (definitions : DataEnvironment) (administrative : Core.Context) :=
  GenericImperativeFor.Tree layouts owner active frame globals onError values source
    (CompatibleExpressionBuiltins.Syntax source)
    (fun context => CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt)
    definitions administrative

section Certificates
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {parentSite : SourceCoreElaboration.ErrorSite}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
  {parents : List SourceCoreLocalEvidence.Prepared} {assignmentsTable : SourceCoreAssignmentFaultSites.Table}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
  {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}

theorem tree_of_contextual_body
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      Tree layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow ∧
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  apply GenericImperativeFor.tree_of_typed_body readPolicy binderPolicy allocationPolicy ?_
    assignments unaryPolicy unique ?_ syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped
  · intro sourceContext closed residual signatures scope fuel id node lowered declarations syntaxTree found typed generated
    exact CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures
      syntaxTree found typed expressionRead lowerRead leafPolicy (expressionPolicy ▸ generated)
  · intro sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated
    exact ⟨CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures
      syntaxTree found typed expressionRead lowerRead leafPolicy (expressionPolicy ▸ generated),
      nativeTyping sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated⟩

end Certificates
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered extension uninitialized missing faithful observations functionTypes in
theorem Tree.preserves_reachable [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  exact GenericImperativeFor.Tree.preserves_reachable functions definitions registered extension program evidence
    (fun context valid => CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing)
    faithful observations tree errors contextValid unique
    environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered extension uninitialized missing faithful observations functionTypes in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem Tree.preserves [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  apply Tree.preserves_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

include definitions registered extension uninitialized missing faithful observations functionTypes in
theorem Tree.reflects_reachable [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  exact GenericImperativeFor.Tree.reflects_reachable functions definitions registered extension program evidence
    (fun context valid => CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing)
    (fun context valid => CompatibleExpressionBuiltins.reflects functions extension faithful observations functionTypes program evidence valid uninitialized missing)
    faithful observations functionTypes tree errors contextValid unique
    environments heaps locals agrees actualTyped reference read unmapped evaluated

include definitions registered extension uninitialized missing faithful observations functionTypes in
/-- Original signature, specialized to the unconditional diagnostic policy. -/
theorem Tree.reflects [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  apply Tree.reflects_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.BuiltinImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatch
/-! Recursive builtin expressions close every expression premise in ordinary
lexical control, assignments and while/for loops. Headers, conditions, bodies
and post vectors use one certificate family. Match branches retain their independent source contexts and the same recursive statement certificate. Static source typing and actual
native checking remain separate from the finite semantic correspondence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open TypedScopedStatements (Executes)
open TypedLexicalWhile (FlowRep)
open TypedLexicalControl (LexicalResult)
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Syntax (source : TypedSource) := GenericImperativeMatch.Syntax source (CompatibleExpressionBuiltins.Syntax source)
abbrev Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (definitions : DataEnvironment) (administrative : Core.Context) :=
  GenericImperativeMatch.Tree layouts owner active frame globals onError values source
    (CompatibleExpressionBuiltins.Syntax source)
    (fun context => CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt)
    definitions administrative

section Certificates
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {parentSite : SourceCoreElaboration.ErrorSite}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
  {parents : List SourceCoreLocalEvidence.Prepared} {assignmentsTable : SourceCoreAssignmentFaultSites.Table}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
  {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}

theorem tree_of_contextual_body
    {matchCompilation : SourceCoreCompatibleDataMatches.Context}
    (matchPolicy : policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : GenericImperativeMatch.MatchChildStatic matchCompilation source
      (fun context => CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt)
      definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      Tree layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow ∧
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  apply GenericImperativeMatch.tree_of_typed_body matchPolicy matchValues matchDefinitions matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy ?_
    assignments unaryPolicy unique ?_ syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped
  · intro sourceContext closed residual signatures scope fuel id node lowered declarations syntaxTree found typed generated
    exact CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures
      syntaxTree found typed expressionRead lowerRead leafPolicy (expressionPolicy ▸ generated)
  · intro sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated
    exact ⟨CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures
      syntaxTree found typed expressionRead lowerRead leafPolicy (expressionPolicy ▸ generated),
      nativeTyping sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated⟩

end Certificates
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered catalogValid extension uninitialized missing faithful observations functionTypes in
theorem Tree.preserves_reachable [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeMatch.Tree.ReachableReady registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  exact GenericImperativeMatch.Tree.preserves_reachable functions definitions registered catalogValid extension program evidence
    (fun context valid => CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing)
    faithful observations tree errors contextValid unique
    environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered catalogValid extension uninitialized missing faithful observations functionTypes in
theorem Tree.preserves [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeMatch.Tree.Ready registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  apply Tree.preserves_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

include definitions registered catalogValid extension uninitialized missing faithful observations functionTypes in
theorem Tree.reflects_reachable [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeMatch.Tree.ReachableReady registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  exact GenericImperativeMatch.Tree.reflects_reachable functions definitions registered catalogValid extension program evidence
    (fun context valid => CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing)
    (fun context valid => CompatibleExpressionBuiltins.reflects functions extension faithful observations functionTypes program evidence valid uninitialized missing)
    faithful observations functionTypes tree errors contextValid unique
    environments heaps locals agrees actualTyped reference read unmapped evaluated

include definitions registered catalogValid extension uninitialized missing faithful observations functionTypes in
theorem Tree.reflects [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeMatch.Tree.Ready registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  apply Tree.reflects_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchBodyMeaning
/-! Actual accepted builtin function bodies with recursive lexical control,
assignment, while, for and match preserve finite source calls and reflect
completed Core calls. All child meaning is closed by the concrete tree.
Escaped loop control retains its independent source fault. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes source_view)
open CompatibleNamedBody (trace_control)
open ImperativeFunctionFinish (result)

structure Certificate (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (definitions : DataEnvironment) (administrative : Core.Context)
    (scope : SourceCoreLocalCell.Scope) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (policy : SourceCoreLoops.Policy)
    (fuel : Nat) (fellThrough escaped : Word) (code : Expr) where private mk ::
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
    statements type reasonAt fellThrough escaped = .ok code
  projection : values.checked.catalog.project expected = .ok type
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
    statements type reasonAt true escaped = .ok flow
  emitted : code = CompatibleStatements.finish type flow fellThrough escaped
  tree : BuiltinImperativeMatch.Tree layouts owner active frame globals onError
    readFuel values source solved reasonAt definitions administrative
    context scope (.statements true statements) expected type flow

/-- Keep the real compiler equation and the exact flow traversal. Their
composition fixes the actual finish code without an additional code equality
supplied by a caller. The tree is independent static evidence. -/
def of_extracted
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {definitions : DataEnvironment} {administrative : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {policy : SourceCoreLoops.Policy}
    {fuel : Nat} {fellThrough escaped : Word} {code flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
      statements type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project expected = .ok type)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      statements type reasonAt true escaped = .ok flow)
    (tree : BuiltinImperativeMatch.Tree layouts owner active frame globals onError
      readFuel values source solved reasonAt definitions administrative
      context scope (.statements true statements) expected type flow) :
    Certificate layouts owner active frame globals onError readFuel values
      source context solved reasonAt definitions administrative scope statements
      expected type policy fuel fellThrough escaped code := by
  have emitted : code = CompatibleStatements.finish type flow fellThrough escaped := by
    unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
    rw [generated] at accepted
    exact Except.ok.inj accepted.symm
  exact ⟨accepted, projection, flow, generated, emitted, tree⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  (program : Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem Certificate.preserves_reachable [FunctionCalls.FaultTokens faults]
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt ambient.definitions administrative scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    (errors : GenericImperativeMatch.Tree.ReachableReady registry faults certificate.tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  obtain ⟨resultContext, control, sourceTrace, exit⟩ := trace_control trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.preserves_reachable functions definitions registered catalogValid extension program function.evidence uninitialized missing
      faithful functionLeaves functionTypes errors contextValid unique environments heaps locals agrees actualTyped reference read unmapped sourceTrace
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow functions (fun next same => by
    cases same
    exact certificate.tree.true_fallthrough_unit unique sourceTrace)
    certificate.projection fellThrough escaped escapedFault represented evaluated
  have evaluated : Evaluates actual store (code.rename ξ) result finalStore := by
    rw [certificate.emitted, ImperativeFunctionFinish.rename]
    exact completed
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, ImperativeFunctionFinish.result related exit,
    finalHeaps, maps, worlds, frame, metadata, ⟨resultContext, control, sourceTrace, exit, lexical⟩⟩

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem Certificate.preserves [FunctionCalls.FaultTokens faults]
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt ambient.definitions administrative scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    (errors : GenericImperativeMatch.Tree.Ready registry faults certificate.tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  apply Certificate.preserves_reachable (functions := functions) (certificate := certificate) (errors := errors.reachable)
  all_goals assumption

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem Certificate.reflects_reachable [FunctionCalls.FaultTokens faults]
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt ambient.definitions administrative scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    (errors : GenericImperativeMatch.Tree.ReachableReady registry faults certificate.tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  rw [certificate.emitted, ImperativeFunctionFinish.rename] at evaluated
  obtain ⟨flowValue, middleStore, flowEval⟩ := ImperativeFunctionFinish.input evaluated
  obtain ⟨resultContext, control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.reflects_reachable functions definitions registered catalogValid extension program function.evidence uninitialized missing
      faithful functionLeaves functionTypes errors contextValid unique environments heaps locals agrees actualTyped reference read unmapped flowEval
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow functions (fun next same => by
    cases same
    exact certificate.tree.true_fallthrough_unit unique trace)
    certificate.projection fellThrough escaped escapedFault represented flowEval
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  have result : ∃ outcome, FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
    generalize raw : function.resultType = expected at related
    cases related with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed =>
        refine ⟨_, .unit raw executed, ?_⟩
        exact ⟨.value .unit, .unit _ rfl⟩
    | returned payload =>
      cases trace with
      | control executed =>
        refine ⟨_, .returned executed, ?_⟩
        exact ⟨.value payload, .returned _⟩
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (certificate.tree.control_not_fault unique executed)
      | fault failed => exact ⟨_, .fault failed, .fault matched, .fault _⟩
    | breaking finalEnvironment matched =>
      cases trace with
      | control executed =>
        exact ⟨_, .escaped executed (.inl ⟨_, rfl⟩), .fault matched, .breaking _⟩
    | continuing finalEnvironment matched =>
      cases trace with
      | control executed =>
        exact ⟨_, .escaped executed (.inr ⟨_, rfl⟩), .fault matched, .continuing _⟩
  obtain ⟨outcome, bodyTrace, result, exit⟩ := result
  exact ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, maps, worlds, frame, metadata,
    ⟨resultContext, control, trace, exit, lexical⟩⟩

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem Certificate.reflects [FunctionCalls.FaultTokens faults]
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt ambient.definitions administrative scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    (errors : GenericImperativeMatch.Tree.Ready registry faults certificate.tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  apply Certificate.reflects_reachable (functions := functions) (certificate := certificate) (errors := errors.reachable)
  all_goals assumption

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
/-- Finite source call completion and completed Core execution are equivalent.
Suspension is outside both sides; no common fuel bound or termination premise
is required. The stronger preceding theorems retain result and heap relations. -/
theorem Certificate.finite_iff_reachable [FunctionCalls.FaultTokens faults]
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt ambient.definitions administrative scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    (errors : GenericImperativeMatch.Tree.ReachableReady registry faults certificate.tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
:
    (∃ runtimeFuel value finalStore,
      Core.runStateful runtimeFuel (.initial (code.rename ξ) actual store) =
        .done value finalStore) ↔
    (∃ outcome after,
      FunctionCallBody.Trace program function context environment before outcome after) := by
  constructor
  · rintro ⟨runtimeFuel, value, finalStore, completed⟩
    obtain ⟨outcome, after, _, _, trace, _⟩ :=
      certificate.reflects_reachable functions extension definitions registered catalogValid program
        contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
        errors environments heaps locals agrees actualTyped reference read unmapped
        (Core.runStateful_evaluation_sound completed)
    exact ⟨outcome, after, trace⟩
  · rintro ⟨outcome, after, trace⟩
    obtain ⟨value, finalStore, _, _, evaluated, _⟩ :=
      certificate.preserves_reachable functions extension definitions registered catalogValid program
        contextValid unique escapedFault uninitialized missing faithful functionLeaves functionTypes
        errors environments heaps locals agrees actualTyped reference read unmapped trace
    obtain ⟨runtimeFuel, completed⟩ :=
      Core.evaluation_runStateful_complete_with_sufficient_fuel evaluated
    exact ⟨runtimeFuel, value, finalStore, completed runtimeFuel (Nat.le_refl _)⟩

include definitions registered catalogValid escapedFault extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem Certificate.finite_iff [FunctionCalls.FaultTokens faults]
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt ambient.definitions administrative scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    (errors : GenericImperativeMatch.Tree.Ready registry faults certificate.tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
:
    (∃ runtimeFuel value finalStore,
      Core.runStateful runtimeFuel (.initial (code.rename ξ) actual store) =
        .done value finalStore) ↔
    (∃ outcome after,
      FunctionCallBody.Trace program function context environment before outcome after) := by
  apply Certificate.finite_iff_reachable (functions := functions) (certificate := certificate) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchExtraction
/-! The actual contextual traversal retains its fixed match ledger. Recursive
builtin certificates close expression extraction, while diagnostic obligations
remain explicit and can be materialized into the existing Ready API. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatch
open Core Frontend SourceInference

abbrev Extraction (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (definitions : DataEnvironment) (administrative : Core.Context) :=
  GenericImperativeMatch.Extraction layouts owner active frame globals onError values source
    (CompatibleExpressionBuiltins.Syntax source)
    (fun context => CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt)
    definitions administrative solved

abbrev ExtractionFor (diagnosticPolicy : AssignmentDiagnosticPolicy) (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (definitions : DataEnvironment) (administrative : Core.Context) :=
  GenericImperativeMatch.ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source
    (CompatibleExpressionBuiltins.Syntax source)
    (fun context => CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt)
    definitions administrative solved

/- Both ledgers come from explicit compiler contexts. Emitted code and value
catalog equality are not used to infer their equality. -/
section Certificates
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {parentSite : SourceCoreElaboration.ErrorSite}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
  {parents : List SourceCoreLocalEvidence.Prepared} {assignmentsTable : SourceCoreAssignmentFaultSites.Table}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
  {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}

theorem extraction_of_contextual_body_for (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {matchCompilation : SourceCoreCompatibleDataMatches.Context}
    (matchPolicy : policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
    (matchLedger : matchCompilation.solvedRequirements = compilation.solvedRequirements)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : GenericImperativeMatch.MatchChildStatic matchCompilation source
      (fun context => CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt)
      definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : ExtractionFor diagnosticPolicy layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  obtain ⟨flow, generated, extracted, same⟩ := GenericImperativeMatch.extraction_of_typed_body_for diagnosticPolicy
    (certificates := fun context => CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt)
    matchPolicy matchValues matchDefinitions matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy
    (fun sourceContext closed residual signatures scope fuel id node lowered declarations syntaxTree found typed generated =>
      CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures
        syntaxTree found typed expressionRead lowerRead leafPolicy (expressionPolicy ▸ generated))
    assignments unaryPolicy unique
    (fun sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated =>
      ⟨CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures
        syntaxTree found typed expressionRead lowerRead leafPolicy (expressionPolicy ▸ generated),
        nativeTyping sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated⟩)
    syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped
  exact ⟨flow, generated, matchLedger ▸ extracted, same⟩

/-- The production loop policy fixes the match ledger and allocator directly.
Only source-hidden freshness, source typing and native typing remain here. -/
theorem extraction_of_contextual_body
    {matchCompilation : SourceCoreCompatibleDataMatches.Context}
    (matchPolicy : policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
    (matchLedger : matchCompilation.solvedRequirements = compilation.solvedRequirements)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : GenericImperativeMatch.MatchChildStatic matchCompilation source
      (fun context => CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt)
      definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : Extraction layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  obtain ⟨flow, generated, extracted, same⟩ := extraction_of_contextual_body_for .unconditional (matchCompilation := matchCompilation) (matchPolicy := matchPolicy) (matchValues := matchValues) (matchDefinitions := matchDefinitions) (matchLedger := matchLedger) (matchAllocator := matchAllocator) (matchChildStatic := matchChildStatic) (readPolicy := readPolicy) (binderPolicy := binderPolicy) (allocationPolicy := allocationPolicy) (assignments := assignments) (unaryPolicy := unaryPolicy) (unique := unique) (ordinary := ordinary) (expressionPolicy := expressionPolicy) (expressionRead := expressionRead) (lowerRead := lowerRead) (leafPolicy := leafPolicy) (nativeTyping := nativeTyping) (context := context) (scope := scope) (statements := statements) (expected := expected) (syntaxTree := syntaxTree) (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations) (fuel := fuel) (type := type) (nativeType := nativeType) (code := code) (fellThrough := fellThrough) (escaped := escaped) (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)
  exact ⟨flow, generated, extracted.to_strict, same⟩

theorem extraction_of_fixed_contextual_body_for (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (fixedPolicy : policy = SourceCoreCompatibleDataMatches.loopPolicy values compilation.solvedRequirements
      assignmentsTable diagnostics compilation.owner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some definitions))
    (hidden : GenericImperativeMatch.MatchHiddenFresh source)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : ExtractionFor diagnosticPolicy layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  exact extraction_of_contextual_body_for diagnosticPolicy
    (matchCompilation := ⟨values, compilation.solvedRequirements,
      some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)),
      some definitions⟩)
    (by rw [fixedPolicy]; rfl) rfl rfl rfl rfl
    (GenericImperativeMatch.MatchChildStatic.of_hidden
      (matchCompilation := ⟨values, compilation.solvedRequirements,
        some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)),
        some definitions⟩)
      (certificates := fun context => CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt)
      (definitions := definitions) (administrative := administrative) hidden)
    (by rw [fixedPolicy]; rfl)
    (by intro scope binder _; rw [fixedPolicy]; rfl)
    (by rw [fixedPolicy]; rfl)
    assignments unaryPolicy unique ordinary expressionPolicy expressionRead lowerRead leafPolicy nativeTyping
    syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped

theorem extraction_of_fixed_contextual_body
    (fixedPolicy : policy = SourceCoreCompatibleDataMatches.loopPolicy values compilation.solvedRequirements
      assignmentsTable diagnostics compilation.owner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some definitions))
    (hidden : GenericImperativeMatch.MatchHiddenFresh source)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : Extraction layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  obtain ⟨flow, generated, extracted, same⟩ := extraction_of_fixed_contextual_body_for .unconditional (fixedPolicy := fixedPolicy) (hidden := hidden) (assignments := assignments) (unaryPolicy := unaryPolicy) (unique := unique) (ordinary := ordinary) (expressionPolicy := expressionPolicy) (expressionRead := expressionRead) (lowerRead := lowerRead) (leafPolicy := leafPolicy) (nativeTyping := nativeTyping) (context := context) (scope := scope) (statements := statements) (expected := expected) (syntaxTree := syntaxTree) (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations) (fuel := fuel) (type := type) (nativeType := nativeType) (code := code) (fellThrough := fellThrough) (escaped := escaped) (projection := projection) (accepted := accepted) (nativeTyped := nativeTyped)
  exact ⟨flow, generated, extracted.to_strict, same⟩

end Certificates
end Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchPreparedDiagnostics
/-! Prepared diagnostics for the real contextual builtin body. The compiler's
fixed match policy supplies ledger, allocator and token provenance. Independent
source syntax/typing, native typing and residual fault interpretation remain
explicit; no runtime child meaning is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatch
open Core Frontend SourceInference
section Certificates
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {parentSite : SourceCoreElaboration.ErrorSite}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
  {parents : List SourceCoreLocalEvidence.Prepared} {assignmentsTable : SourceCoreAssignmentFaultSites.Table}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
  {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}

theorem extraction_of_contextual_body_with_diagnostics (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    {matchCompilation : SourceCoreCompatibleDataMatches.Context}
    (matchPolicy : policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
    (matchLedger : matchCompilation.solvedRequirements = compilation.solvedRequirements)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : GenericImperativeMatch.MatchChildStatic matchCompilation source
      (fun context => CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt)
      definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : ExtractionFor diagnosticPolicy layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  obtain ⟨flow, generated, extracted, same⟩ := GenericImperativeMatch.extraction_of_typed_body_with_diagnostics diagnosticPolicy factory
    (certificates := fun context => CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt)
    matchPolicy matchValues matchDefinitions matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy
    (fun sourceContext closed residual signatures scope fuel id node lowered declarations syntaxTree found typed generated =>
      CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures
        syntaxTree found typed expressionRead lowerRead leafPolicy (expressionPolicy ▸ generated))
    assignments unaryPolicy unique
    (fun sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated =>
      ⟨CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures
        syntaxTree found typed expressionRead lowerRead leafPolicy (expressionPolicy ▸ generated),
        nativeTyping sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated⟩)
    syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped
  exact ⟨flow, generated, matchLedger ▸ extracted, same⟩

/-- Actual prepare supplies every reachable operand law. The returned
predicate consists of remaining place/uninitialized/unary diagnostics and
explicit inclusion of operand table diagnostics in the whole fault relation. -/
theorem extraction_of_prepared_contextual_body {first : Nat}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok assignmentsTable)
    (operandTyping : AssignmentDiagnosticOrigins.OperandsTyped source)
    (fixedPolicy : policy = SourceCoreCompatibleDataMatches.loopPolicy values compilation.solvedRequirements
      assignmentsTable diagnostics compilation.owner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some definitions))
    (hidden : GenericImperativeMatch.MatchHiddenFresh source)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : ExtractionFor .reachable layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  have assignments := CompatibleAssignmentStatements.AssignmentPolicy.actual values compilation.solvedRequirements assignmentsTable diagnostics compilation.owner policy.lowerExpression
    (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError))) (some definitions)
  have assignmentPolicy := fixedPolicy.symm ▸ assignments
  exact extraction_of_contextual_body_with_diagnostics .reachable (AssignmentDiagnosticOrigins.Factory.prepared operandTyping prepared)
    (matchCompilation := ⟨values, compilation.solvedRequirements,
      some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)),
      some definitions⟩)
    (by rw [fixedPolicy]; rfl) rfl rfl rfl rfl
    (GenericImperativeMatch.MatchChildStatic.of_hidden
      (matchCompilation := ⟨values, compilation.solvedRequirements,
        some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)),
        some definitions⟩)
      (certificates := fun context => CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt)
      (definitions := definitions) (administrative := administrative) hidden)
    (by rw [fixedPolicy]; rfl)
    (by intro scope binder _; rw [fixedPolicy]; rfl)
    (by rw [fixedPolicy]; rfl)
    assignmentPolicy
    (show CompatibleBitNotStatements.Policy policy values
      (fun site root => diagnostics.placeReason compilation.owner site root none)
      (fun site root => assignmentsTable.reasonAt site root .bitNot)
      (fun site root type => diagnostics.placeReason compilation.owner site root (some type)) from by rw [fixedPolicy]; rfl)
    unique ordinary expressionPolicy expressionRead lowerRead leafPolicy nativeTyping
    syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped

end Certificates
end Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatch
end
