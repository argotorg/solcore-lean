import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalFlowBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories

/-! The same accepted discard receipt issues both original expression Roots.
Original closure-frame typing supplies the real nodes; the actual expression
callback and reached view transport supply both accepted compiler actions.
Static call authority is indexed by these exact internally issued proofs.
Preservation and reflection then invoke the constructive flow family once.
The whole-body finish footer and a mixed invoked-body family remain separate.
No expression/body execution callback or desired result is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt NamedSupport ClosureSupportFor)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor Certificate)
open CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditions)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control ResultRepresents)

/-- Both raw nodes are authentic original lookups. The discard head is not
required to have Unit raw type; the terminal node retains the function result. -/
structure OriginalChildren (source : TypedSource) (context : SourceSemantics.Context)
    (firstExpression terminalExpression : ExpressionId) (result : TypeSystem.Ty) where
  first : ExpressionNode
  firstFound : source.lookupExpression? firstExpression = some first
  firstTyped : ExpressionHasType source context firstExpression first.type
  terminal : ExpressionNode
  terminalFound : source.lookupExpression? terminalExpression = some terminal
  terminalResult : terminal.type = result
  terminalTyped : ExpressionHasType source context terminalExpression terminal.type

section Static
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {statementPolicy : SourceCoreLoops.Policy} {fuel : Nat} {view : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {statement next : StatementId} {rest : List StatementId}
  {firstExpression terminalExpression : ExpressionId} {result : Ty}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {invocation : Staging.Recursive.Scope} {changed : List ExpressionId} {roots : List NodeId}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel bodyFuel : Nat}
  {semanticFaults : FunctionCalls.FaultRep}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}

/-- Only actual compiler, original typing and reached-call authority is stored.
The accepted receipt is a fixed index, so both child actions belong to it. -/
structure Static
    (receipt : Receipt statementPolicy fuel view scope statement firstExpression terminalExpression
      (next :: rest) result reasonAt fellThrough escaped code) where
  edited : LocalView invocation.source view changed
  avoids : Avoids invocation.source roots changed
  sourceProfile : PolicyFor policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source scope reasonAt
  viewProfile : PolicyFor policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    view scope reasonAt
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active
  expressionCallback : statementPolicy.lowerExpression = fun childFuel source current id token =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min childFuel bodyFuel)
      compilation source current id token
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  parameters : MonoBindersExtend function.source.owner function.context function.parameters types context
  sameSource : invocation.source = function.source
  body : function.body = statement :: next :: rest
  firstSyntax : Syntax view firstExpression
  terminalSyntax : Syntax view terminalExpression
  firstReached : Reaches invocation.source roots (.expression firstExpression)
  terminalReached : Reaches invocation.source roots (.expression terminalExpression)
  conditions : OriginalConditions compiled policy compilation readFuel context invocation
    reasonAt scope semanticFaults

/-- Option.get selects the actual stored nodes; frame-derived existence is used
only to prove that each lookup succeeds and that its raw properties hold. -/
def Static.originalChildren
    {receipt : Receipt statementPolicy fuel view scope statement firstExpression terminalExpression
      (next :: rest) result reasonAt fellThrough escaped code}
    (packet : Static (compiled := compiled) (function := function) (context := context)
      (types := types) (invocation := invocation) (changed := changed) (roots := roots)
      (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
      (readFuel := readFuel) (bodyFuel := bodyFuel) (semanticFaults := semanticFaults)
      (native := native) (active := active) receipt) :
    OriginalChildren invocation.source context firstExpression terminalExpression function.resultType := by
  have head := receipt.source_head packet.edited.metadata
  have raw := CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion.at_parameters
    packet.frame packet.parameters packet.sameSource packet.body head.1 head.2.1 head.2.2
  have firstAvailable : (invocation.source.lookupExpression? firstExpression).isSome := by
    obtain ⟨first, terminal, firstFound, _⟩ := raw
    exact Option.isSome_of_eq_some firstFound
  have terminalAvailable : (invocation.source.lookupExpression? terminalExpression).isSome := by
    obtain ⟨first, terminal, firstFound, firstTyped, terminalFound, _⟩ := raw
    exact Option.isSome_of_eq_some terminalFound
  let first := (invocation.source.lookupExpression? firstExpression).get firstAvailable
  let terminal := (invocation.source.lookupExpression? terminalExpression).get terminalAvailable
  have firstFound : invocation.source.lookupExpression? firstExpression = some first :=
    Option.eq_some_of_isSome firstAvailable
  have terminalFound : invocation.source.lookupExpression? terminalExpression = some terminal :=
    Option.eq_some_of_isSome terminalAvailable
  have properties : ExpressionHasType invocation.source context firstExpression first.type ∧
      terminal.type = function.resultType ∧
      ExpressionHasType invocation.source context terminalExpression terminal.type := by
    obtain ⟨originalFirst, originalTerminal, foundFirst, typedFirst, foundTerminal,
      sameResult, typedTerminal⟩ := raw
    have firstEq : originalFirst = first := Option.some.inj (foundFirst.symm.trans firstFound)
    have terminalEq : originalTerminal = terminal := Option.some.inj (foundTerminal.symm.trans terminalFound)
    simpa only [firstEq, terminalEq] using And.intro typedFirst (And.intro sameResult typedTerminal)
  exact ⟨first, firstFound, properties.1, terminal, terminalFound, properties.2.1, properties.2.2⟩

variable {receipt : Receipt statementPolicy fuel view scope statement firstExpression terminalExpression
    (next :: rest) result reasonAt fellThrough escaped code}
  (packet : Static (compiled := compiled) (function := function) (context := context)
    (types := types) (invocation := invocation) (changed := changed) (roots := roots)
    (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
    (readFuel := readFuel) (bodyFuel := bodyFuel) (semanticFaults := semanticFaults)
    (native := native) (active := active) receipt)

private def first_authority :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.original_authority packet.conditions
    ⟨packet.originalChildren.first, packet.originalChildren.firstFound, rfl,
      packet.originalChildren.firstTyped⟩
private def terminal_authority :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.original_authority packet.conditions
    ⟨packet.originalChildren.terminal, packet.originalChildren.terminalFound,
      packet.originalChildren.terminalResult, packet.originalChildren.terminalTyped⟩

include packet in
private theorem first_action : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody
    (min receipt.childFuel bodyFuel) compilation view scope firstExpression reasonAt = .ok receipt.first := by
  simpa only [packet.expressionCallback] using receipt.firstGenerated
include packet in
private theorem terminal_action : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody
    (min receipt.tail.childFuel bodyFuel) compilation view scope terminalExpression reasonAt = .ok receipt.tail.child := by
  simpa only [packet.expressionCallback] using receipt.tail.generated

include packet in
/-- This proof is issued by the real recursive extractor from the same first
accepted action, after genuine view transport and original raw typing. -/
theorem first_certificate : Certificate policy lowerBody compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source context reasonAt scope firstExpression receipt.first :=
  CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.issued_certificate
    packet.edited packet.avoids packet.sourceProfile packet.viewProfile packet.callables
    packet.firstSyntax packet.firstReached (first_authority packet) (first_action packet)
include packet in
/-- The tail certificate is indexed by the terminal child actually retained in
the same accepted whole action, with its own authentic compiler budget. -/
theorem terminal_certificate : Certificate policy lowerBody compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source context reasonAt scope terminalExpression receipt.tail.child :=
  CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.issued_certificate
    packet.edited packet.avoids packet.sourceProfile packet.viewProfile packet.callables
    packet.terminalSyntax packet.terminalReached (terminal_authority packet) (terminal_action packet)

/-- Both call ports belong to these exact proofs. They contain static callsite
and selected-body authority, never a caller or body execution law. -/
structure Ready : Prop where
  first : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
    (compiled := compiled) (invocation := invocation) (first_certificate packet)
  terminal : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
    (compiled := compiled) (invocation := invocation) (terminal_certificate packet)

/-- Both real original Roots are manufactured internally. The tail's original
raw result is retained explicitly, independently of its native projected type. -/
def rootPair (ready : Ready packet) :
    RootAt compiled context invocation scope firstExpression receipt.first semanticFaults ×
    { terminalRoot : RootAt compiled context invocation scope terminalExpression receipt.tail.child semanticFaults //
      terminalRoot.rawType = function.resultType } :=
  ⟨CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.rootAt_of_view_action
      packet.edited packet.avoids packet.sourceProfile packet.viewProfile packet.callables
      packet.firstSyntax packet.firstReached (first_authority packet) (first_action packet) ready.first,
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.rootAt_of_view_action
      packet.edited packet.avoids packet.sourceProfile packet.viewProfile packet.callables
      packet.terminalSyntax packet.terminalReached (terminal_authority packet) (terminal_action packet) ready.terminal,
    rfl⟩
end Static

universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), TerminalFor association stages)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    ClosureSupportFor association stages (closureTerminals association))
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

section Bounds
variable {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {scope : SourceCoreLocalCell.Scope} {statement next : StatementId} {rest : List StatementId}
  {firstExpression terminalExpression : ExpressionId} {result : Ty}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
  {statementPolicy : SourceCoreLoops.Policy} {fuel : Nat} {view : TypedSource}
  {function : Dynamic.Closure} {types : List TypeSystem.Ty}
  {changed : List ExpressionId} {roots : List NodeId}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel bodyFuel : Nat}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  {receipt : Receipt statementPolicy fuel view scope statement firstExpression terminalExpression
    (next :: rest) result reasonAt fellThrough escaped code}
  (packet : Static (compiled := compiled) (function := function) (context := context)
    (types := types) (invocation := invocation) (changed := changed) (roots := roots)
    (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
    (readFuel := readFuel) (bodyFuel := bodyFuel) (semanticFaults := semanticFaults)
    (native := native) (active := active) receipt)
  (ready : Ready packet)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents
    (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : GenericHeap.HeapRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport packet ready
  environments heaps locals agrees actualTyped admitted in
/-- The receipt's exact head/tail actions, original frame and static call ports
construct both expression meanings before the original flow is preserved. -/
theorem preserves {size : Nat} {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      stages size invocation context environment before (statement :: next :: rest)
      finalContext bodyOutcome after) :
    finalContext = context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store
        ((LocalSequence.discard (LocalLoop.controlType result) receipt.first.expression
          (LocalLoop.returnValue result receipt.tail.child.expression)).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld function.resultType result callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context function.resultType outcome reached := by
  let pair := rootPair packet ready
  have originalHead := receipt.source_head packet.edited.metadata
  have rawType : pair.2.val.support.node.type = function.resultType :=
    pair.2.val.support.rawResult.trans pair.2.property
  have produced := CallableIndexedOwnedPreparedStagedDiscardTerminalFlowBounds.preserves
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared) (profile := profile)
    (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closureTerminals) (namedTerminals := namedTerminals)
    (closureSupport := closureSupport) (namedSupport := namedSupport)
    (firstRoot := pair.1) (terminalRoot := pair.2.val)
    (contains := originalHead.1) (form := originalHead.2.1) (terminal := originalHead.2.2)
    (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
    (actualTyped := actualTyped) (initial := initial) (admitted := admitted) trace
  simpa only [rawType, receipt.tail.sameType] using produced

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport packet ready
  environments heaps locals agrees actualTyped admitted in
/-- Native inversion uses the same receipt and independently issued children.
The returned original grades and reached state come from the flow family. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalSequence.discard (LocalLoop.controlType result) receipt.first.expression
        (LocalLoop.returnValue result receipt.tail.child.expression)).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before (statement :: next :: rest) context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld function.resultType result callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context function.resultType outcome reached := by
  let pair := rootPair packet ready
  have originalHead := receipt.source_head packet.edited.metadata
  have rawType : pair.2.val.support.node.type = function.resultType :=
    pair.2.val.support.rawResult.trans pair.2.property
  have expanded : EvaluationSize size actual store
      ((LocalSequence.discard (LocalLoop.controlType receipt.tail.child.type) receipt.first.expression
        (LocalLoop.returnValue receipt.tail.child.type receipt.tail.child.expression)).rename ξ) value finalStore := by
    simpa only [receipt.tail.sameType] using completed
  have produced := CallableIndexedOwnedPreparedStagedDiscardTerminalFlowBounds.reflects
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared) (profile := profile)
    (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closureTerminals) (namedTerminals := namedTerminals)
    (closureSupport := closureSupport) (namedSupport := namedSupport)
    (firstRoot := pair.1) (terminalRoot := pair.2.val)
    (contains := originalHead.1) (form := originalHead.2.1) (terminal := originalHead.2.2)
    (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
    (actualTyped := actualTyped) (initial := initial) (admitted := admitted) stageEq expanded
  simpa only [rawType, receipt.tail.sameType] using produced
end Bounds
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds
