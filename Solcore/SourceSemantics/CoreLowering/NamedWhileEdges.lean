import Solcore.SourceSemantics.CoreLowering.ProtectedWhileBodyEdges
import Solcore.SourceSemantics.CoreLowering.NamedLexicalAssignments

/-! Concrete named expression and lexical/assignment Trees close both while
edges at the actual caller context. Installed globals, exact captures and frame
histories remain separate runtime entry facts. This unit covers condition/body
edges, not full finite iterations, for post/initializers or contextual extraction.
The lexical body profile excludes break/continue and nested loops. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedWhileEdges
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open TypedScopedStatements (Executes)
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

/-- Same installed authority as recursive named expression/statement consumers. -/
abbrev State (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry)
    (bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) :=
  ProtectedWhile.State (NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
    values registry functions

variable {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {type : Ty} {conditionCode bodyCode : Expr} {selfReason : Word}
  {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

include extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- All condition child/body meaning follows from concrete accepted named Trees. -/
theorem condition_preserves
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason finalMap finalWorld after finalStore :=
  ProtectedWhile.condition_preserves functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners)
    tree found agrees state trace

include extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
/-- Actual condition completion reconstructs its source trace and retained entry. -/
theorem condition_reflects
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason finalMap finalWorld after finalStore :=
  ProtectedWhile.condition_reflects functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing)
    tree found agrees state evaluated

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The concrete lexical body closes child meaning at every reached context;
its outer entry and body-local source context are retained separately. -/
theorem body_preserves
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (tree : NamedLexicalAssignments.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason mapping world before store)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : Executes false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (bodyCode.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after :=
  ProtectedWhile.body_preserves functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedLexicalAssignments.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing tree)
    valid agrees reference state trace

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The concrete lexical body closes child meaning at every reached context;
its outer entry and body-local source context are retained separately. -/
theorem body_reflects
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (tree : NamedLexicalAssignments.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (bodyCode.rename ξ)) value finalStore) :
    ∃ finalContext outcome after finalMap finalWorld,
      Executes false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after :=
  ProtectedWhile.body_reflects functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedLexicalAssignments.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing tree)
    valid agrees reference state evaluated

end Solcore.SourceSemantics.CoreLowering.NamedWhileEdges
