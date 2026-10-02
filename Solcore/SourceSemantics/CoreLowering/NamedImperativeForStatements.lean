import Solcore.SourceSemantics.CoreLowering.ProtectedImperativeForReflection
import Solcore.SourceSemantics.CoreLowering.BuiltinLexicalStatements

/-! One concrete named expression family closes every statement child, including
loop conditions and arbitrary nested loop bodies. Installed global code, exact
captures and frame history remain independent entry facts. Projected unary assignments, match and whole contextual
extraction remain outside this grammar. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedImperativeForStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open CallableIndexedHistory
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

abbrev Tree {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    (bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program)
    (layouts : SourceCoreAllocationLayouts.Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (expressionSyntax : ExpressionId → Prop) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (administrative : Core.Context) :=
  GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
    (fun context => NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
    ambient.definitions administrative

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
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

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The finite statement tree and concrete expression/body certificates close
all runtime child obligations, including after source bindings, condition slots and seven-slot writes. The actual protected entry is retained as a runtime boundary. -/
theorem Tree.preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ
    contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ProtectedImperativeFor.preservesAt functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun context valid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    faithful observations unique tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem Tree.reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ
    contextLocation native value environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ProtectedImperativeFor.reflectsAt functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun context valid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (fun context valid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing)
    faithful observations runtimeViews unique tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

/-- Scoped restoration retains the old canonical caller environment while
transporting its actual observations through all heap/admin suffix effects. -/
theorem retained {scope : Scope} {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
    {before after : Dynamic.Heap} {store finalStore : Store} {canonical : Environment}
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping store finalMap finalStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope finalMap finalWorld after finalStore canonical :=
  (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix).extend installed maps worlds frame metadata

end Solcore.SourceSemantics.CoreLowering.NamedImperativeForStatements
