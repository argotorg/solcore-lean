import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalControl
import Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts

/-! Fault posts remain beside each actual ready tuple. These interfaces neither
choose an execution nor provide a finished lexical or function meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedLexicalFlowFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (FlowRep)
open GenericLexicalStatements (Scope ValuesContext)
open TypedLexicalControl (Restored LexicalResult)
open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u v

abbrev HeadFaultPost := Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
  TypedSource → Dynamic.Environment → Dynamic.Heap → StatementId → Dynamic.SemanticFault →
  Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop

abbrev FlowFaultPost := Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
  TypedSource → Dynamic.Environment → Dynamic.Heap → Bool → List StatementId → Dynamic.SemanticFault →
  Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop

def HeadOutcomePost (post : HeadFaultPost) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : StatementId) (type : Core.Ty)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) (result : Value)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) : Prop :=
  match outcome with
  | .fault reason => ∃ token, result = .inLeft (LocalLoop.controlType type) (.word token) ∧
      post program context evidence source environment before id reason after token mapping world store
  | _ => True

def FlowOutcomePost (post : FlowFaultPost) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (mode : Bool) (statements : List StatementId) (type : Core.Ty)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) (result : Value)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) : Prop :=
  match outcome with
  | .fault reason => ∃ token, result = .inLeft (LocalLoop.controlType type) (.word token) ∧
      post program context evidence source environment before mode statements reason after token mapping world store
  | _ => True

def TrivialHead : HeadFaultPost := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => True
def TrivialFlow : FlowFaultPost := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True

/-- The owning statement form is retained by the expression-to-head edge. -/
inductive ExpressionHeadLink (source : TypedSource) (id : StatementId) : ExpressionId → Prop where
  | returning {node expression} (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression)) : ExpressionHeadLink source id expression
  | expression {node expression semicolon} (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression semicolon) : ExpressionHeadLink source id expression
  | initialized {node binder expression} (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some expression)) (mono : binder.scheme.quantified = []) :
      ExpressionHeadLink source id expression
  | condition {node expression thenBody elseBody} (found : source.lookupStatement? id = some node)
      (form : node.form = .ifThen expression thenBody elseBody) : ExpressionHeadLink source id expression

mutual
/-- A causal head path is constructed at the actual semantic join. -/
inductive HeadOrigin (post : ExpressionFailurePostContracts.ExpressionFaultPost)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    SourceSemantics.Context → Dynamic.Environment → Dynamic.Heap → StatementId →
    Dynamic.SemanticFault → Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop where
  | expression {context environment before id expression reason after token mapping world store}
      (link : ExpressionHeadLink source id expression)
      (failed : Dynamic.ExpressionFaults program context evidence source environment before expression reason after)
      (retained : post program context evidence source environment before expression reason after token mapping world store) :
      HeadOrigin post program evidence source context environment before id reason after token mapping world store
  | block {context environment before id node statements reason after token mapping world store}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (retained : FlowOrigin post program evidence source context environment before false statements reason after token mapping world store) :
      HeadOrigin post program evidence source context environment before id reason after token mapping world store
  | selected {context environment before middle id node expression thenBody elseBody boolean reason after token mapping world store}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen expression thenBody elseBody)
      (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before expression (.bool boolean) middle)
      (retained : FlowOrigin post program evidence source context environment middle false
        (if boolean then thenBody else elseBody.getD []) reason after token mapping world store) :
      HeadOrigin post program evidence source context environment before id reason after token mapping world store
/-- Prefix constructors retain the executed Source statement and literal middle configuration. -/
inductive FlowOrigin (post : ExpressionFailurePostContracts.ExpressionFaultPost)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    SourceSemantics.Context → Dynamic.Environment → Dynamic.Heap → Bool → List StatementId →
    Dynamic.SemanticFault → Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop where
  | head {context environment before mode id rest reason after token mapping world store}
      (retained : HeadOrigin post program evidence source context environment before id reason after token mapping world store) :
      FlowOrigin post program evidence source context environment before mode (id :: rest) reason after token mapping world store
  | tailExpression {context environment before id node expression reason after token mapping world store}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (failed : Dynamic.ExpressionFaults program context evidence source environment before expression reason after)
      (retained : post program context evidence source environment before expression reason after token mapping world store) :
      FlowOrigin post program evidence source context environment before true [id] reason after token mapping world store
  | prefix {context nextContext environment next before middle mode id rest reason after token mapping world store}
      (executed : Dynamic.StatementExecutes program context evidence source environment before id nextContext (.fallthrough next) middle)
      (retained : FlowOrigin post program evidence source nextContext next middle mode rest reason after token mapping world store) :
      FlowOrigin post program evidence source context environment before mode (id :: rest) reason after token mapping world store
end

abbrev HeadPost (post : ExpressionFailurePostContracts.ExpressionFaultPost) : HeadFaultPost :=
  fun program context evidence source environment before id reason after token mapping world store =>
    HeadOrigin post program evidence source context environment before id reason after token mapping world store
abbrev FlowPost (post : ExpressionFailurePostContracts.ExpressionFaultPost) : FlowFaultPost :=
  fun program context evidence source environment before mode statements reason after token mapping world store =>
    FlowOrigin post program evidence source context environment before mode statements reason after token mapping world store

/-- Finite causal-edge laws. These laws provide no lexical evaluations. -/
structure Joins (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : HeadFaultPost) (flowPost : FlowFaultPost)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) : Prop where
  expression : ∀ {context environment before id expression reason after token mapping world store},
    ExpressionHeadLink source id expression →
    Dynamic.ExpressionFaults program context evidence source environment before expression reason after →
    expressionPost program context evidence source environment before expression reason after token mapping world store →
    headPost program context evidence source environment before id reason after token mapping world store
  tailExpression : ∀ {context environment before id node expression reason after token mapping world store},
    source.lookupStatement? id = some node → node.form = .expression expression false →
    Dynamic.ExpressionFaults program context evidence source environment before expression reason after →
    expressionPost program context evidence source environment before expression reason after token mapping world store →
    flowPost program context evidence source environment before true [id] reason after token mapping world store
  head : ∀ {context environment before mode id rest reason after token mapping world store},
    headPost program context evidence source environment before id reason after token mapping world store →
    flowPost program context evidence source environment before mode (id :: rest) reason after token mapping world store
  prefixFault : ∀ {context nextContext environment next before middle mode id rest reason after token mapping world store},
    Dynamic.StatementExecutes program context evidence source environment before id nextContext (.fallthrough next) middle →
    flowPost program nextContext evidence source next middle mode rest reason after token mapping world store →
    flowPost program context evidence source environment before mode (id :: rest) reason after token mapping world store
  block : ∀ {context environment before id node statements reason after token mapping world store},
    source.lookupStatement? id = some node → node.form = .block statements →
    flowPost program context evidence source environment before false statements reason after token mapping world store →
    headPost program context evidence source environment before id reason after token mapping world store
  selected : ∀ {context environment before middle id node expression thenBody elseBody boolean reason after token mapping world store},
    source.lookupStatement? id = some node → node.form = .ifThen expression thenBody elseBody →
    Dynamic.ExpressionEvaluates program context evidence source environment before expression (.bool boolean) middle →
    flowPost program context evidence source environment middle false
      (if boolean then thenBody else elseBody.getD []) reason after token mapping world store →
    headPost program context evidence source environment before id reason after token mapping world store

theorem origin_joins (post : ExpressionFailurePostContracts.ExpressionFaultPost)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    Joins post (HeadPost post) (FlowPost post) program evidence source where
  expression := .expression
  tailExpression := .tailExpression
  head := .head
  prefixFault := .prefix
  block := .block
  selected := .selected

theorem trivial_joins (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    Joins ExpressionFailurePostContracts.TrivialExpressionPost TrivialHead TrivialFlow program evidence source where
  expression := by intros; trivial
  tailExpression := by intros; trivial
  head := by intros; trivial
  prefixFault := by intros; trivial
  block := by intros; trivial
  selected := by intros; trivial

section CausalJoins
variable {post : ExpressionFailurePostContracts.ExpressionFaultPost}
  {headPost : HeadFaultPost} {flowPost : FlowFaultPost}
  {program : Program} {context nextContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment next : Dynamic.Environment} {before middle after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {statements rest thenBody : List StatementId}
  {elseBody : Option (List StatementId)} {expression : ExpressionId} {type : Ty}
  {outcome : Dynamic.ControlOutcome} {value : Value} {mapping : LocationMap} {world : StoreTyping} {store : Store}

theorem head_to_flow (joins : Joins post headPost flowPost program evidence source) (retained : HeadOutcomePost headPost program context evidence source environment before id type outcome after value mapping world store)
    (mode : Bool) (rest : List StatementId) :
    FlowOutcomePost flowPost program context evidence source environment before mode (id :: rest) type outcome after value mapping world store := by
  cases outcome <;> try trivial
  obtain ⟨token, same, origin⟩ := retained
  exact ⟨token, same, joins.head origin⟩

theorem prefix_to_flow (joins : Joins post headPost flowPost program evidence source) {mode : Bool}
    (executed : Dynamic.StatementExecutes program context evidence source environment before id nextContext (.fallthrough next) middle)
    (retained : FlowOutcomePost flowPost program nextContext evidence source next middle mode rest type outcome after value mapping world store) :
    FlowOutcomePost flowPost program context evidence source environment before mode (id :: rest) type outcome after value mapping world store := by
  cases outcome <;> try trivial
  obtain ⟨token, same, origin⟩ := retained
  exact ⟨token, same, joins.prefixFault executed origin⟩

theorem block_to_head (joins : Joins post headPost flowPost program evidence source) (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (retained : FlowOutcomePost flowPost program context evidence source environment before false statements type outcome after value mapping world store) :
    HeadOutcomePost headPost program context evidence source environment before id type
      (Dynamic.restoreControl environment outcome) after value mapping world store := by
  cases outcome <;> try trivial
  obtain ⟨token, same, origin⟩ := retained
  exact ⟨token, same, joins.block found form origin⟩

theorem selected_to_head (joins : Joins post headPost flowPost program evidence source) {boolean : Bool}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen expression thenBody elseBody)
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before expression (.bool boolean) middle)
    (retained : FlowOutcomePost flowPost program context evidence source environment middle false
      (if boolean then thenBody else elseBody.getD []) type outcome after value mapping world store) :
    HeadOutcomePost headPost program context evidence source environment before id type
      (Dynamic.restoreControl environment outcome) after value mapping world store := by
  cases outcome <;> try trivial
  obtain ⟨token, same, origin⟩ := retained
  exact ⟨token, same, joins.selected found form evaluated origin⟩
theorem expression_to_head (joins : Joins post headPost flowPost program evidence source)
    (link : ExpressionHeadLink source id expression) {reason : Dynamic.SemanticFault} {expressionType : Ty} {token : Word}
    (failed : Dynamic.ExpressionFaults program context evidence source environment before expression reason after)
    (retained : ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before expression expressionType
      (.fault reason) after (.inLeft expressionType (.word token)) mapping world store) :
    HeadOutcomePost headPost program context evidence source environment before id type (.fault reason) after
      (.inLeft (LocalLoop.controlType type) (.word token)) mapping world store := by
  obtain ⟨word, same, origin⟩ := retained
  have tokenSame : token = word := by injection same with _ same; injection same
  subst word
  exact ⟨token, rfl, joins.expression link failed origin⟩

theorem expression_to_flow (joins : Joins post headPost flowPost program evidence source)
    (link : ExpressionHeadLink source id expression) {reason : Dynamic.SemanticFault} {expressionType : Ty} {token : Word}
    (failed : Dynamic.ExpressionFaults program context evidence source environment before expression reason after)
    (retained : ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before expression expressionType
      (.fault reason) after (.inLeft expressionType (.word token)) mapping world store)
    (mode : Bool) (rest : List StatementId) :
    FlowOutcomePost flowPost program context evidence source environment before mode (id :: rest) type (.fault reason) after
      (.inLeft (LocalLoop.controlType type) (.word token)) mapping world store := by
  exact head_to_flow joins (expression_to_head joins link failed retained) mode rest

theorem tail_to_flow (joins : Joins post headPost flowPost program evidence source)
    (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
    {reason : Dynamic.SemanticFault} {expressionType : Ty} {token : Word}
    (failed : Dynamic.ExpressionFaults program context evidence source environment before expression reason after)
    (retained : ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before expression expressionType
      (.fault reason) after (.inLeft expressionType (.word token)) mapping world store) :
    FlowOutcomePost flowPost program context evidence source environment before true [id] type (.fault reason) after
      (.inLeft (LocalLoop.controlType type) (.word token)) mapping world store := by
  obtain ⟨word, same, origin⟩ := retained
  have tokenSame : token = word := by injection same with _ same; injection same
  subst word
  exact ⟨token, rfl, joins.tailExpression found form failed origin⟩

end CausalJoins

variable {Records : Type v}
variable (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

def PreservesAtFor (post : FlowFaultPost) (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : facts context mode statements expected)
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
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_trace : RecursiveNamedLoopContracts.ExecutesAt size mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      FlowOutcomePost post program context evidence source environment before mode statements type outcome after value finalMap finalWorld finalStore

def ReflectsAtFor (post : FlowFaultPost) (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : facts context mode statements expected)
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
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_evaluated : CoreProof.EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      FlowOutcomePost post program context evidence source environment before mode statements type outcome after value finalMap finalWorld finalStore

def HeadPreservesAtFor (post : HeadFaultPost) (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : headFacts context id expected)
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
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      HeadOutcomePost post program context evidence source environment before id type outcome after value finalMap finalWorld finalStore

def HeadReflectsAtFor (post : HeadFaultPost) (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : headFacts context id expected)
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
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_evaluated : CoreProof.EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      HeadOutcomePost post program context evidence source environment before id type outcome after value finalMap finalWorld finalStore

section Expressions
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (certificate : GenericExpressionMeaning.Certificate)

def ExpressionPreservesAt (post : ExpressionFailurePostContracts.ExpressionFaultPost) (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → exprFacts context id node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      (∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ExpressionPost protocol readiness context node.type outcome reached) ∧
      ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before id
        lowered.type outcome after value finalMap finalWorld finalStore

def ExpressionReflectsAt (post : ExpressionFailurePostContracts.ExpressionFaultPost) (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → exprFacts context id node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      (∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ExpressionPost protocol readiness context node.type outcome reached) ∧
      ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before id
        lowered.type outcome after value finalMap finalWorld finalStore
end Expressions

section Trivial
variable {mode : Bool} {statements : List StatementId} {id : StatementId} {type : Ty}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
  {result : Value} {mapping : LocationMap} {world : StoreTyping} {store : Store} {expected : TypeSystem.Ty}

theorem FlowOutcomePost.of_trivial
    (represented : FlowRep (registry := registry) functions mapping world faults expected type outcome result) :
    FlowOutcomePost TrivialFlow program context evidence source environment before mode statements type outcome after result mapping world store := by
  cases represented <;> try trivial
  exact ⟨_, rfl, trivial⟩

theorem HeadOutcomePost.of_trivial
    (represented : FlowRep (registry := registry) functions mapping world faults expected type outcome result) :
    HeadOutcomePost TrivialHead program context evidence source environment before id type outcome after result mapping world store := by
  cases represented <;> try trivial
  exact ⟨_, rfl, trivial⟩
end Trivial

theorem PreservesAtFor.of_trivial {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    PreservesAtFor (post := TrivialFlow) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, FlowOutcomePost.of_trivial functions program evidence represented⟩

theorem PreservesAtFor.forget {post : FlowFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : PreservesAtFor (post := post) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, _⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩

theorem ReflectsAtFor.of_trivial {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    ReflectsAtFor (post := TrivialFlow) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, FlowOutcomePost.of_trivial functions program evidence represented⟩

theorem ReflectsAtFor.forget {post : FlowFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : ReflectsAtFor (post := post) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, _⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩

theorem HeadPreservesAtFor.of_trivial {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.HeadPreservesAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code) :
    HeadPreservesAtFor (post := TrivialHead) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, HeadOutcomePost.of_trivial functions program evidence represented⟩

theorem HeadPreservesAtFor.forget {post : HeadFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : HeadPreservesAtFor (post := post) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.HeadPreservesAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, _⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩

theorem HeadReflectsAtFor.of_trivial {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.HeadReflectsAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code) :
    HeadReflectsAtFor (post := TrivialHead) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, reached, HeadOutcomePost.of_trivial functions program evidence represented⟩

theorem HeadReflectsAtFor.forget {post : HeadFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : HeadReflectsAtFor (post := post) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.HeadReflectsAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, reached, _⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩

section ExpressionTrivial
variable (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (certificate : GenericExpressionMeaning.Certificate)
theorem ExpressionPreservesAt.of_trivial {size : Nat}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt protocol readiness program evidence model exprFacts certificate (context := context) (source := source) (faults := faults) size) :
    ExpressionPreservesAt (post := ExpressionFailurePostContracts.TrivialExpressionPost) protocol readiness program evidence model exprFacts certificate (context := context) (source := source) (faults := faults) size := by
  intro scope id lowered admitted node found facts mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees typed initial ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ := meaning admitted found facts environments heaps locals agrees typed initial ready trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition, ExpressionFailurePostContracts.OutcomePost.of_trivial represented⟩

theorem ExpressionReflectsAt.of_trivial {size : Nat}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt protocol readiness program evidence model exprFacts certificate (context := context) (source := source) (faults := faults) size) :
    ExpressionReflectsAt (post := ExpressionFailurePostContracts.TrivialExpressionPost) protocol readiness program evidence model exprFacts certificate (context := context) (source := source) (faults := faults) size := by
  intro scope id lowered admitted node found facts mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees typed initial ready evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ := meaning admitted found facts environments heaps locals agrees typed initial ready evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition, ExpressionFailurePostContracts.OutcomePost.of_trivial represented⟩

end ExpressionTrivial

end Solcore.SourceSemantics.CoreLowering.NamedLexicalFlowFaultPostContracts
