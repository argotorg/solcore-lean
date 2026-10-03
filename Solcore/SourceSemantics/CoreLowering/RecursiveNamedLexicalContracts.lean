import Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSourceBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedLexicalStatementControl

/-! Pointwise contracts keep the existing three-way lexical FlowRep, exact
installed authority and lexical extension. Source and Core sizes are separate;
these contracts do not turn bounded hypotheses into unbounded meanings. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedScopedStatements (FlowRep)
open TypedLexicalControl (Restored LexicalResult)
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Below := RecursiveNamedBoundedContracts.Below

variable {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)

def PreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_installed : entry scope mapping world before store canonical)
    (_trace : RecursiveNamedLoopContracts.ExecutesAt size mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after

def PreservesAt (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  PreservesAtFor (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) mode statements expected type code

def ReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_installed : entry scope mapping world before store canonical)
    (_evaluated : CoreProof.EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after

def ReflectsAt (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ReflectsAtFor (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) mode statements expected type code

def HeadPreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_installed : entry scope mapping world before store canonical)
    (_trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def HeadPreservesAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  HeadPreservesAtFor (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) id expected type code

def HeadReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_installed : entry scope mapping world before store canonical)
    (_evaluated : CoreProof.EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def HeadReflectsAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  HeadReflectsAtFor (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) id expected type code

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts
