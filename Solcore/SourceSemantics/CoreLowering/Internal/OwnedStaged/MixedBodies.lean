import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedCanonicalSupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DiscardTerminals
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler

/-!
# Staged bounds: mixed bodies

A chosen body that is empty, terminal, one discard or a recursive discard sequence: static support, flow and body bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
/-! A chosen called body retains the empty, terminal, one-discard or recursive
discard-sequence receipt for the same actual Code. Original expression Roots
are retained at every Source-selected scope. Packets store no execution or
meaning law. The whole-body assembly derives the raw result from original
body typing and constructs the literal finish footer above this static layer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt SelectedBody)
open CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts (Receipt)

def parameterScope {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative) : SourceCoreLocalCell.Scope :=
  code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope

/-- The statement action is indexed by the exact emitted body, not by a
fresh expression or a guessed compiler view. -/
structure Discard {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (stages : Staging.Recursive.Registry) where
  policy : SourceCoreLoops.Policy
  fuel : Nat
  statement : StatementId
  next : StatementId
  rest : List StatementId
  firstExpression : ExpressionId
  terminalExpression : ExpressionId
  reasonAt : ExpressionId → Word
  fellThrough : Word
  escaped : Word
  body : function.body = statement :: next :: rest
  receipt : Receipt policy fuel code.view (parameterScope code)
    statement firstExpression terminalExpression (next :: rest)
    code.receipt.resultCore reasonAt fellThrough escaped code.receipt.body
  child : Staging.Recursive.Scope
  selected : stages.Closure function child

/-- The recursive receipt is indexed by the original full body and exact
emitted Code. Compiler fuel and diagnostic words belong to that receipt. -/
structure Sequence {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (stages : Staging.Recursive.Registry) where
  policy : SourceCoreLoops.Policy
  fuel : Nat
  reasonAt : ExpressionId → Word
  fellThrough : Word
  escaped : Word
  receipt : CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts.Receipt
    policy fuel code.view (parameterScope code) function.body code.receipt.resultCore
    reasonAt fellThrough escaped code.receipt.body
  child : Staging.Recursive.Scope
  selected : stages.Closure function child

/-- Empty Source bodies retain their literal generated footer and genuine
selected invocation scope. No expression or body meaning is a field. -/
structure Empty {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (stages : Staging.Recursive.Registry) where
  empty : function.body = []
  unit : function.resultType = .unit
  nativeUnit : code.receipt.resultCore = .unit
  emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore
    (LocalLoop.fallthrough code.receipt.resultCore)
    code.compilation.internalReason code.compilation.internalReason
  child : Staging.Recursive.Scope
  selected : stages.Closure function child

/-- The lexical packet retains the actual compiled flow and footer at the
same closure Code. Source shape excludes control statements outside this fragment. -/
structure Lexical {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (stages : Staging.Recursive.Registry) where
  policy : SourceCoreLoops.Policy
  fuel : Nat
  reasonAt : ExpressionId → Word
  fellThrough : Word
  escaped : Word
  allocationOwner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  flow : Expr
  accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel code.view
    (parameterScope code) function.body code.receipt.resultCore reasonAt true escaped = .ok flow
  emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow fellThrough escaped
  shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape function.source function.body
  child : Staging.Recursive.Scope
  selected : stages.Closure function child

/-- The imperative packet retains the actual compiled flow and footer at the
same closure Code. Source shape excludes control statements outside this fragment. -/
structure Imperative {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (stages : Staging.Recursive.Registry) where
  policy : SourceCoreLoops.Policy
  fuel : Nat
  reasonAt : ExpressionId → Word
  fellThrough : Word
  escaped : Word
  allocationOwner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  flow : Expr
  accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel code.view
    (parameterScope code) function.body code.receipt.resultCore reasonAt true escaped = .ok flow
  emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow fellThrough escaped
  shape : CallableIndexedOwnedPreparedStagedBareAssignmentTree.Shape function.source function.body
  child : Staging.Recursive.Scope
  selected : stages.Closure function child

/-- The branching packet retains the actual compiled flow and footer at the
same closure Code. Source shape excludes control statements outside this fragment. -/
structure Branching {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (stages : Staging.Recursive.Registry) where
  policy : SourceCoreLoops.Policy
  fuel : Nat
  reasonAt : ExpressionId → Word
  fellThrough : Word
  escaped : Word
  allocationOwner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  flow : Expr
  accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel code.view
    (parameterScope code) function.body code.receipt.resultCore reasonAt true escaped = .ok flow
  emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow fellThrough escaped
  shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body
  child : Staging.Recursive.Scope
  selected : stages.Closure function child

/-- Every constructor retains its authentic body shape at the same Code. -/
inductive Packet {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (stages : Staging.Recursive.Registry) where
  | nestedBranching (packet : Branching code stages)
  | canonicalBranching (packet : Branching code stages)
  | canonicalTerminal (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages)
  | terminal (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages)
  | discard (packet : Discard code stages)
  | sequence (packet : Sequence code stages)
  | empty (packet : Empty code stages)
  | lexical (packet : Lexical code stages)
  | imperative (packet : Imperative code stages)
  | branching (packet : Branching code stages)

/-- Original raw statement form and both original expression Roots remain
explicit at all genuinely selected scopes. In particular, the first raw type
is unrestricted; only the returned tail has the function's raw result type. -/
structure DiscardSupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry) (packet : Discard code stages)
    (semanticFaults : FunctionCalls.FaultRep) where
  heads : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    ∃ node : StatementNode,
      ContainsStatement child.source packet.statement node ∧
      node.form = .expression packet.firstExpression true ∧
      CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child
        packet.terminalExpression (packet.next :: packet.rest)
  roots : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    RootAt compiled inputs.context child (parameterScope code)
        packet.firstExpression packet.receipt.first semanticFaults ×
      { terminalRoot : RootAt compiled inputs.context child (parameterScope code)
          packet.terminalExpression packet.receipt.tail.child semanticFaults //
        terminalRoot.rawType = function.resultType }

/-- Original full body typing and genuine used-child Roots remain law-free.
Nonempty witnesses are eliminated inside Prop proofs; no data chooser or flow
meaning is stored. This layer imports the compiler receipt, not sequence flow. -/
structure SequenceSupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry) (packet : Sequence code stages)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  roots : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    ∀ expression childCode, packet.receipt.tree.Children expression childCode →
      Nonempty (RootAt compiled inputs.context child (parameterScope code)
        expression childCode semanticFaults)

/-- Empty bodies retain the same independently typed closure frame. -/
structure EmptySupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (_inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry) (_packet : Empty code stages)
    (_semanticFaults : FunctionCalls.FaultRep) : Type where
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function

/-- Every expression keeps its real lexical context and scope after local
allocation. The compiler tree stores syntax and accepted allocations only. -/
structure LexicalSupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry) (packet : Lexical code stages)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  tree : ∀ child, stages.Closure function child →
    GenericLexicalStatements.Tree compiled.indexed.layouts packet.allocationOwner packet.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length packet.onError
      (.initial compiled.compatible.checked) child.source
      (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate child.source
        (fun context scope id lowered => Nonempty (RootAt compiled context child scope id lowered semanticFaults)))
      inputs.context (parameterScope code) true function.body function.resultType code.receipt.resultCore packet.flow

/-- Every expression keeps its real lexical context and scope after local
allocation. The compiler tree stores syntax and accepted allocations only. -/
structure ImperativeSupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry) (packet : Imperative code stages)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  tree : ∀ child, stages.Closure function child →
    GenericImperativeMatch.Tree compiled.indexed.layouts packet.allocationOwner packet.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length packet.onError
      (.initial compiled.compatible.checked) child.source (fun _ => True)
      (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate child.source
        (fun context scope id lowered => Nonempty (RootAt compiled context child scope id lowered semanticFaults)))
      compiled.indexed.layouts.definitions administrative
      inputs.context (parameterScope code) (.statements true function.body) function.resultType code.receipt.resultCore packet.flow

/-- Branches retain the actual compiler tree at each reached lexical context. -/
structure BranchingSupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry) (packet : Branching code stages)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    function.source invalidProjection missingDefault)
  collected : ∀ child, stages.Closure function child →
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected invalidProjection missingDefault (faults := semanticFaults) compiled.indexed.layouts packet.allocationOwner packet.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length packet.onError
      (.initial compiled.compatible.checked) child.source (fun _ => True)
      (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate child.source
        (fun context scope id lowered => Nonempty (RootAt compiled context child scope id lowered semanticFaults)))
      compiled.indexed.layouts.definitions administrative
      inputs.context (parameterScope code) (.statements true function.body) function.resultType code.receipt.resultCore packet.flow

abbrev BranchingSupport.tree {compiled function scope administrative code inputs stages packet semanticFaults}
    (support : @BranchingSupport compiled function scope administrative code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :=
  (support.collected child selected).tree

 theorem BranchingSupport.sites {compiled function scope administrative code inputs stages packet semanticFaults}
    (support : @BranchingSupport compiled function scope administrative code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (registry : SourceCoreRawMetadata.Registry) :
    PreparedBranchingCatalogSites.CatalogSites support.invalidProjection support.missingDefault registry semanticFaults
      (support.tree child selected) :=
  (support.collected child selected).sites registry

/-- The original general expression root keeps the exact retained Code policy,
compiler context and diagnostic function at every actual lexical child. -/
structure CanonicalBranchingSupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry) (packet : Branching code stages)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  readFuel : Nat
  «prefix» : code.compilation.administrativePrefix = 1
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    function.source invalidProjection missingDefault)
  collected : ∀ child, stages.Closure function child →
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected invalidProjection missingDefault (faults := semanticFaults) compiled.indexed.layouts packet.allocationOwner packet.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length packet.onError
      (.initial compiled.compatible.checked) child.source (fun _ => True)
      (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate child.source
        (fun context scope id lowered => Nonempty (Σ rawType,
          CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.CanonicalRoot compiled
            code.policy code.lowerBody code.compilation readFuel context child code.reasonAt
            scope id lowered rawType semanticFaults headers)))
      compiled.indexed.layouts.definitions administrative
      inputs.context (parameterScope code) (.statements true function.body) function.resultType code.receipt.resultCore packet.flow

abbrev CanonicalBranchingSupport.tree {compiled function scope administrative headers code inputs stages packet semanticFaults}
    (support : @CanonicalBranchingSupport compiled function scope administrative headers code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :=
  (support.collected child selected).tree

theorem CanonicalBranchingSupport.sites {compiled function scope administrative headers code inputs stages packet semanticFaults}
    (support : @CanonicalBranchingSupport compiled function scope administrative headers code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (registry : SourceCoreRawMetadata.Registry) :
    PreparedBranchingCatalogSites.CatalogSites support.invalidProjection support.missingDefault registry semanticFaults
      (support.tree child selected) :=
  (support.collected child selected).sites registry

/-- Ordinary bodies can mix canonical calls and genuine nested formation.
The certificate is tied to this actual ordinary support's caller and registry,
so the application route needs no caller equality or new runtime body law. -/
structure NestedBranchingSupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    {code : Code compiled.indexed function scope administrative}
    (ordinary : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults)
    (stages : Staging.Recursive.Registry) (packet : Branching code stages) : Type where
  globals : ordinary.caller.globals = compiled.indexed.base.globals.length
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers
  zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    function.source invalidProjection missingDefault)
  collected : ∀ child, stages.Closure function child →
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected invalidProjection missingDefault (faults := semanticFaults) compiled.indexed.layouts packet.allocationOwner packet.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length packet.onError
      (.initial compiled.compatible.checked) child.source (fun _ => True)
      (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate child.source
        (fun context => CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.Certificate
          headers ordinary.caller bodyRegistry semanticFaults context child))
      compiled.indexed.layouts.definitions administrative
      ordinary.body.context (parameterScope code) (.statements true function.body)
      function.resultType code.receipt.resultCore packet.flow

abbrev NestedBranchingSupport.tree {compiled function scope administrative headers keys bodyRegistry semanticFaults code ordinary stages packet}
    (support : @NestedBranchingSupport compiled function scope administrative headers keys bodyRegistry semanticFaults code ordinary stages packet)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :=
  (support.collected child selected).tree

theorem NestedBranchingSupport.sites {compiled function scope administrative headers keys bodyRegistry semanticFaults code ordinary stages packet}
    (support : @NestedBranchingSupport compiled function scope administrative headers keys bodyRegistry semanticFaults code ordinary stages packet)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (registry : SourceCoreRawMetadata.Registry) :
    PreparedBranchingCatalogSites.CatalogSites support.invalidProjection support.missingDefault registry semanticFaults
      (support.tree child selected) :=
  (support.collected child selected).sites registry

/-- The chosen static support is indexed by the authentic packet and input
context. The sequence branch contains no whole-body result equality. -/
def Support {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry) (packet : Packet code stages)
    (semanticFaults : FunctionCalls.FaultRep) : Type :=
  match packet with
  | .nestedBranching _ => PEmpty
  | .canonicalBranching branching => CanonicalBranchingSupport headers code inputs stages branching semanticFaults
  | .canonicalTerminal terminal =>
      CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.SelectedCanonicalBody
        (headers := headers) code inputs stages terminal semanticFaults
  | .terminal terminal => SelectedBody code inputs stages terminal semanticFaults
  | .discard discard => DiscardSupport code inputs stages discard semanticFaults
  | .sequence sequence => SequenceSupport code inputs stages sequence semanticFaults
  | .empty empty => EmptySupport code inputs stages empty semanticFaults
  | .lexical lexical => LexicalSupport code inputs stages lexical semanticFaults
  | .imperative imperative => ImperativeSupport code inputs stages imperative semanticFaults
  | .branching branching => BranchingSupport code inputs stages branching semanticFaults

/-- The Association is destructed only to retain its real Code and the actual
BodyWith.toContext. Every branch retains that same parameter context. -/
def PacketFor {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association
      headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (stages : Staging.Recursive.Registry) : Type :=
  match association with
  | .ordinary _ _ code _ _ _ _ _ _ _ _ => Packet code stages
  | .principal _ _ code _ _ _ _ _ _ _ _ => Packet code stages

def SupportFor {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association
      headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (stages : Staging.Recursive.Registry)
    (packet : PacketFor association stages) : Type :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
      match packet with
      | .nestedBranching branching => NestedBranchingSupport headers keys support stages branching
      | packet => Support headers code support.body.toContext stages packet semanticFaults
  | .principal _ _ code _ support _ _ _ _ _ _ =>
      Support headers code support.body.toContext stages packet semanticFaults

section NumericProjections
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {bodyRegistry : SourceCoreRawMetadata.Registry}
  {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

/-- The helper law uses the same concrete pool-zero carrier as the numeric
family. It is an internal induction target, not a field of static support. -/
abbrev PreservesBelowAt (context : SourceSemantics.Context) (child : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (expression : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) (size : Nat) : Prop :=
  CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
    (CallableIndexedOwnedBodyRestorationAdmission.bridge
      (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys))
    context
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    stages child
    (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope expression lowered)
    (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size

abbrev ReflectsBelowAt (context : SourceSemantics.Context) (child : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (expression : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) (size : Nat) : Prop :=
  CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
    (CallableIndexedOwnedBodyRestorationAdmission.bridge
      (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram)
      (headers := headers) (keys := keys))
    context
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    stages child
    (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope expression lowered)
    (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) size

/-- Strictness is supplied by the actual evaluated child inversion. The
numeric family closes this hypothesis; no stored packet contains this law. -/
theorem root_preserves_below {context child scope expression lowered}
    (root : RootAt compiled context child scope expression lowered semanticFaults)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget) :
    PreservesBelowAt (completion := completion) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) profile context child scope expression lowered size := by
  intro childSize smaller current id actual point
  exact children childSize (Nat.lt_of_lt_of_le smaller within) root point

theorem root_reflects_below {context child scope expression lowered}
    (root : RootAt compiled context child scope expression lowered semanticFaults)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget) :
    ReflectsBelowAt (completion := completion) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) profile context child scope expression lowered size := by
  intro childSize smaller current id actual point
  exact children childSize (Nat.lt_of_lt_of_le smaller within) root point

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
  {inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
  {packet : Discard code stages}
  (support : DiscardSupport code inputs stages packet semanticFaults)

include support in
/-- Preservation receives each actual Source-selected scope independently. -/
theorem first_preserves_below {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    PreservesBelowAt (completion := completion) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) profile inputs.context child (parameterScope code)
      packet.firstExpression packet.receipt.first size :=
  root_preserves_below profile (support.roots child selected).1 children within

include support in
theorem terminal_preserves_below {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    PreservesBelowAt (completion := completion) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) profile inputs.context child (parameterScope code)
      packet.terminalExpression packet.receipt.tail.child size :=
  root_preserves_below profile (support.roots child selected).2.val children within

include support in
/-- Reflection uses the packet's literal chosen scope and its authentic
selection proof, without quantifying a fresh arbitrary terminal packet. -/
theorem first_reflects_below {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget) :
    ReflectsBelowAt (completion := completion) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) profile inputs.context packet.child (parameterScope code)
      packet.firstExpression packet.receipt.first size :=
  root_reflects_below profile (support.roots packet.child packet.selected).1 children within

include support in
theorem terminal_reflects_below {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget) :
    ReflectsBelowAt (completion := completion) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) profile inputs.context packet.child (parameterScope code)
      packet.terminalExpression packet.receipt.tail.child size :=
  root_reflects_below profile (support.roots packet.child packet.selected).2.val children within
end NumericProjections

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardFlowBounds
/-! Internal discard assembly for the selected mixed-body numeric family.
The genuine strong IH is used only at strict evaluated children. The original
semicolon/terminal inversion and reached parameter-state composition are the
checked discard-flow proof; no body outcome is supplied by a static packet.
The final mixed caller theorem will construct this IH by strong induction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control ResultRepresents)
open GenericExpressionMeaning (agree_prefix rename_prefix)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

section Flow
variable {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {scope : SourceCoreLocalCell.Scope} {firstExpression terminalExpression : ExpressionId}
  {firstCode terminalCode : SourceCoreBasic.LoweredExpr}
  (firstRoot : RootAt compiled context invocation scope firstExpression firstCode semanticFaults)
  (terminalRoot : RootAt compiled context invocation scope terminalExpression terminalCode semanticFaults)
  {statement : StatementId} {rest : List StatementId} {statementNode : StatementNode}
  (contains : ContainsStatement invocation.source statement statementNode)
  (form : statementNode.form = .expression firstExpression true)
  (terminal : Head invocation terminalExpression rest)
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
  (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission
    (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
    context initial)

include firstRoot contains form terminal environments heaps locals agrees actualTyped admitted in
/-- Original statement inversion selects both genuine children. Successful
head effects feed the tail at its reached Admission and the inserted native
temporary binder. The strict numeric Root IH constructs both used child laws internally. -/
theorem preserves_flow {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget) {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      stages size invocation context environment before (statement :: rest) finalContext bodyOutcome after) :
    finalContext = context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store
        ((LocalSequence.discard (LocalLoop.controlType terminalCode.type) firstCode.expression
          (LocalLoop.returnValue terminalCode.type terminalCode.expression)).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld terminalRoot.support.node.type terminalCode.type
        callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        PostAdmission poolBridge context terminalRoot.support.node.type outcome reached := by
  have firstBelow := CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.root_preserves_below
    profile firstRoot children within
  have terminalBelow := CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.root_preserves_below
    profile terminalRoot children within
  rcases CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion.child_and_tail
      firstRoot.support.unique contains form trace with
    ⟨firstSize, failure, sameSize, rfl, rfl, firstTrace⟩ |
    ⟨firstSize, tailSize, sourceValue, middle, sameSize, firstTrace, tailTrace⟩
  · have firstStrict : firstSize < size := by
      rw [sameSize]
      exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      firstBelow firstSize firstStrict ⟨rfl, rfl, rfl⟩ firstRoot.support.found firstRoot.support.typed
        environments heaps locals agrees actualTyped initial admitted firstTrace
    cases represented with
    | fault matched =>
        refine ⟨rfl, .fault failure, rfl, _, finalStore, finalMap, finalWorld, ?_, .fault matched,
          finalHeaps, maps, worlds, frame, metadata, reached, related, post.at_fault_type⟩
        rw [LoopRenaming.discard]
        exact LocalSequence.discard_failure _ evaluated
  · have firstStrict : firstSize < size := by
      rw [sameSize]
      exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
      firstBelow firstSize firstStrict ⟨rfl, rfl, rfl⟩ firstRoot.support.found firstRoot.support.typed
        environments heaps locals agrees actualTyped initial admitted firstTrace
    cases represented with
    | @value sourceValue coreValue payload =>
        obtain ⟨terminalSize, outcome, sameTailSize, rfl, rfl, terminalTrace⟩ :=
          CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body
            terminalRoot.support.unique terminal tailTrace
        have tailWithin : Staging.Recursive.Size.stepSize [terminalSize] ≤ size := by
          rw [← sameTailSize, sameSize]
          exact Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))
        obtain ⟨_tailTrace, value, finalStore, finalMap, finalWorld, second, represented, finalHeaps,
            maps, worlds, frame, metadata, reached, related, post⟩ :=
          CallableIndexedOwnedAdmittedStagedTerminalStatements.preserves poolBridge terminal
            ⟨rfl, rfl, rfl⟩ terminalRoot.support.found terminalRoot.support.typed
            (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (agree_prefix agrees coreValue)
            (.cons ((model).runtime_hasType payload) (actualTyped.weaken firstWorlds))
            middleState firstPost.at_value.2 size terminalBelow terminalTrace tailWithin
        refine ⟨rfl, outcome, rfl, value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
          firstMetadata.trans metadata, reached, firstRelated.trans related, post⟩
        rw [LoopRenaming.discard]
        rw [rename_prefix] at second
        exact LocalSequence.discard_success _ first second

include firstRoot contains form terminal environments heaps locals agrees actualTyped admitted in
/-- Native inversion supplies strict executed children. Reflection rebuilds
the original discard and terminal Source traces with independent grades,
retaining the same stores, record relations and exact nested Failure. -/
theorem reflects_flow {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalSequence.discard (LocalLoop.controlType terminalCode.type) firstCode.expression
        (LocalLoop.returnValue terminalCode.type terminalCode.expression)).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before (statement :: rest) context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld terminalRoot.support.node.type terminalCode.type
        callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        PostAdmission poolBridge context terminalRoot.support.node.type outcome reached := by
  have firstBelow := CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.root_reflects_below
    profile firstRoot children within
  have terminalBelow := CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.root_reflects_below
    profile terminalRoot children within
  have original := completed
  rw [LoopRenaming.discard] at original
  change EvaluationSize size actual store
    (LanguageResult.bind (LocalLoop.controlType terminalCode.type) (firstCode.expression.rename ξ)
      (((LocalLoop.returnValue terminalCode.type terminalCode.expression).rename ξ).weakenAt 0))
    value finalStore at original
  cases CallableIndirectCallBounds.bind_completed original (Nat.le_refl _) with
  | failed first strict =>
      obtain ⟨firstSize, outcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post⟩ :=
        firstBelow _ strict ⟨rfl, rfl, rfl⟩ firstRoot.support.found firstRoot.support.typed
          environments heaps locals agrees actualTyped initial admitted first
      cases represented with
      | fault matched =>
          exact ⟨_, .fault _, after, finalMap, finalWorld,
            .expressionFault contains form firstTrace, .fault matched, finalHeaps,
            maps, worlds, frame, metadata, reached, related, post.at_fault_type⟩
  | continued first remaining firstStrict remainingStrict =>
      obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
          firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        firstBelow _ firstStrict ⟨rfl, rfl, rfl⟩ firstRoot.support.found firstRoot.support.typed
          environments heaps locals agrees actualTyped initial admitted first
      cases represented with
      | @value sourceValue coreValue payload =>
          have shifted := remaining
          rw [← rename_prefix] at shifted
          obtain ⟨tailSize, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            CallableIndexedOwnedAdmittedStagedTerminalStatements.reflects poolBridge terminal
              ⟨rfl, rfl, rfl⟩ terminalRoot.support.found terminalRoot.support.typed
              (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _)
              (.cons ((model).runtime_hasType payload) (actualTyped.weaken firstWorlds))
              middleState firstPost.at_value.2 size terminalBelow shifted (Nat.le_of_lt remainingStrict)
          exact ⟨_, outcome, after, finalMap, finalWorld, .discard contains form firstTrace tailTrace,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans metadata, reached,
            firstRelated.trans related, post⟩
end Flow
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardFlowBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardBodyBounds
/-! Internal whole-body assembly for the genuine selected discard packet.
The strict numeric Root IH produces both evaluated child meanings, and the
same accepted receipt supplies the actual finish footer. The completed body
result is derived from that flow; it is not a static support premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Discard DiscardSupport parameterScope)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control)
open CallableIndexedOwnedPreparedStagedTerminalBodyMeaning (fallback)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {capturedContext : Core.Context} {code : Code compiled.indexed function scope capturedContext}
  {inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
  (packet : Discard code stages)
  (support : DiscardSupport code inputs stages packet semanticFaults)
  {child : Staging.Recursive.Scope} (selected : stages.Closure function child)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable {mapping : LocationMap} {world : StoreTyping}
  {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents
    (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative (parameterScope code) environment canonical
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : GenericHeap.HeapRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before inputs.context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : State headers keys ⟨parameterScope code, mapping, world, before, store, canonical⟩)
  (admitted : Admission
    (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
    inputs.context initial)

include support selected environments heaps locals agrees actualTyped admitted in
/-- The exact original body trace manufactures its flow outcome and literal
footer evaluation at the same reached parameter state. -/
theorem preserves_body {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget)
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      stages size child inputs.context environment before function.body finalContext bodyOutcome after) :
    finalContext = inputs.context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧
      Staging.Recursive.BodyResult function.resultType bodyOutcome outcome ∧
      ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.receipt.body.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        function.resultType code.receipt.resultCore callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys
        ⟨parameterScope code, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          poolBridge inputs.context function.resultType outcome reached := by
  obtain ⟨node, contains, form, terminal⟩ := support.heads child selected
  let roots := support.roots child selected
  rw [packet.body] at trace
  obtain ⟨sameContext, outcome, sameBody, value, finalStore, finalMap, finalWorld,
      flow, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedDiscardFlowBounds.preserves_flow
      (profile := profile) (firstRoot := roots.1) (terminalRoot := roots.2.val)
      (contains := contains) (form := form) (terminal := terminal)
      (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
      (actualTyped := actualTyped) (initial := initial) (admitted := admitted)
      children within trace
  have flowTyped : Evaluates actual store
      ((LocalSequence.discard (LocalLoop.controlType code.receipt.resultCore)
        packet.receipt.first.expression
        (LocalLoop.returnValue code.receipt.resultCore packet.receipt.tail.child.expression)).rename ξ)
      value finalStore := by
    simpa only [packet.receipt.tail.sameType] using flow
  have resultTyped : CallableIndexedOwnedAdmittedStagedTerminalStatements.ResultRepresents
      model finalMap finalWorld function.resultType code.receipt.resultCore callFaults outcome value := by
    simpa only [roots.2.val.support.rawResult, roots.2.property, packet.receipt.tail.sameType] using represented
  have finalPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      poolBridge inputs.context function.resultType outcome reached := by
    simpa only [roots.2.val.support.rawResult, roots.2.property] using post
  obtain ⟨wholeValue, whole, resultRep⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates
      (fallback := (fallback code.receipt.resultCore packet.fellThrough).rename ξ)
      resultTyped flowTyped packet.escaped
  have evaluatedBody : Evaluates actual store (code.receipt.body.rename ξ) wholeValue finalStore := by
    rw [CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerBodyBounds.emitted_rename packet.receipt ξ]
    exact whole
  have bodyResult : Staging.Recursive.BodyResult function.resultType bodyOutcome outcome := by
    rw [sameBody]
    exact CallableIndexedOwnedAdmittedStagedTerminalBody.body_result _ _
  exact ⟨sameContext, outcome, sameBody, bodyResult, wholeValue, finalStore, finalMap, finalWorld,
    evaluatedBody, resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related, finalPost⟩

include support selected environments heaps locals agrees actualTyped admitted in
/-- The literal footer exposes a strict native flow child. Its Source grade
and nested fault remain independent of the original completed native grade. -/
theorem reflects_body {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {size : Nat} (within : size ≤ budget) {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.receipt.body.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        child inputs.context environment before function.body inputs.context (control outcome) after ∧
      Staging.Recursive.BodyResult function.resultType (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        function.resultType code.receipt.resultCore callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys
        ⟨parameterScope code, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          poolBridge inputs.context function.resultType outcome reached := by
  obtain ⟨node, contains, form, terminal⟩ := support.heads child selected
  let roots := support.roots child selected
  have original := completed
  rw [CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerBodyBounds.emitted_rename packet.receipt ξ] at original
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix original (Nat.le_refl size)
  have flowTyped : EvaluationSize flowSize actual store
      ((LocalSequence.discard (LocalLoop.controlType packet.receipt.tail.child.type)
        packet.receipt.first.expression
        (LocalLoop.returnValue packet.receipt.tail.child.type packet.receipt.tail.child.expression)).rename ξ)
      flowValue flowStore := by
    simpa only [packet.receipt.tail.sameType] using flowTrace
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
      finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedDiscardFlowBounds.reflects_flow
      (profile := profile) (firstRoot := roots.1) (terminalRoot := roots.2.val)
      (contains := contains) (form := form) (terminal := terminal)
      (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
      (actualTyped := actualTyped) (initial := initial) (admitted := admitted)
      children (Nat.le_trans (Nat.le_of_lt strict) within) flowTyped
  have resultTyped : CallableIndexedOwnedAdmittedStagedTerminalStatements.ResultRepresents
      model finalMap finalWorld function.resultType code.receipt.resultCore callFaults outcome flowValue := by
    simpa only [roots.2.val.support.rawResult, roots.2.property, packet.receipt.tail.sameType] using represented
  have finalPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      poolBridge inputs.context function.resultType outcome reached := by
    simpa only [roots.2.val.support.rawResult, roots.2.property] using post
  obtain ⟨wholeValue, whole, resultRep⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates
      (fallback := (fallback code.receipt.resultCore packet.fellThrough).rename ξ)
      resultTyped flowTrace.sound packet.escaped
  obtain ⟨same, stores⟩ := evaluation_deterministic original.sound whole
  cases same
  subst stores
  have originalTrace : Staging.Recursive.Size.Statements
      (Program.ofChecked compiled.sourceProgram) stages sourceSize child inputs.context
      environment before function.body inputs.context (control outcome) after := by
    simpa only [packet.body] using trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, originalTrace,
    CallableIndexedOwnedAdmittedStagedTerminalBody.body_result _ _, resultRep,
    finalHeaps, maps, worlds, frame, metadata, reached, related, finalPost⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds
/-! Structural sequence composition over the actual accepted discard children.
Every tail runs at the reached Admission and the exact temporary binder. The
numeric Root family is an internal strict IH; the static tree stores no law.
Native reflection reconstructs independent Source grades and exact failures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control ResultRepresents)
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts (FlowReceipt)

/-- Law-free original-source roots for each exact emitted child. The raw result
is the actual terminal root type; discard child types remain unrestricted. -/
inductive Tree (compiled : SourceCoreUnifiedCompilation.Compiled)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (semanticFaults : FunctionCalls.FaultRep)
    (result : Ty) (rawResult : TypeSystem.Ty) : List StatementId → Expr → Type where
  | terminal {expression statements child}
      (root : RootAt compiled context invocation scope expression child semanticFaults)
      (head : Head invocation expression statements)
      (sameType : child.type = result)
      (sameRaw : root.support.node.type = rawResult) :
      Tree compiled context invocation scope semanticFaults result rawResult statements
        (LocalLoop.returnValue result child.expression)
  | discard {id node expression rest first tailFlow}
      (root : RootAt compiled context invocation scope expression first semanticFaults)
      (contains : ContainsStatement invocation.source id node)
      (form : node.form = .expression expression true)
      (tail : Tree compiled context invocation scope semanticFaults result rawResult rest tailFlow) :
      Tree compiled context invocation scope semanticFaults result rawResult (id :: rest)
        (LocalSequence.discard (LocalLoop.controlType result) first.expression tailFlow)

/-- The same receipt constructs the original statement tree. The supplied
factory issues actual original-source Roots for the literal used children;
raw typing, policy and original compiler authority remain fields of those Roots. -/
theorem Tree.of_receipt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {scope : SourceCoreLocalCell.Scope} {semanticFaults : FunctionCalls.FaultRep}
    {policy : SourceCoreLoops.Policy} {source : TypedSource} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
    {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (receipt : FlowReceipt policy source scope result reasonAt fellThrough escaped fuel statements flow)
    (view : LambdaMetadataViews.MetadataView invocation.source source)
    (roots : ∀ expression child, receipt.Children expression child →
      RootAt compiled context invocation scope expression child semanticFaults) :
    ∃ rawResult, Nonempty (Tree compiled context invocation scope semanticFaults result rawResult
      statements flow) := by
  revert roots
  induction receipt with
  | terminal receipt generated =>
    intro roots
    have root := roots _ _ ⟨rfl, rfl⟩
    exact ⟨root.support.node.type, ⟨.terminal root
      (CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.source_head receipt view)
      receipt.sameType rfl⟩⟩
  | discard found form first firstGenerated tail generated ih =>
    intro roots
    obtain ⟨rawResult, ⟨tailTree⟩⟩ := ih (fun expression child used => roots expression child (.inr used))
    exact ⟨rawResult, ⟨.discard (roots _ _ (.inl ⟨rfl, rfl⟩))
      (lookupStatement?_sound (view.statement found)) form tailTree⟩⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics


section Flow
variable {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {scope : SourceCoreLocalCell.Scope} {result : Ty} {rawResult : TypeSystem.Ty}
  {statements : List StatementId} {flow : Expr}

/-- Only genuine strict Root IHs are consumed. Structural tail recursion retains
its literal reached context, heap, Admission and native temporary binder. -/
theorem preserves_flow
    (tree : Tree compiled context invocation scope semanticFaults result rawResult statements flow)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize) :
    ∀ {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
      {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
      {store : Store} {ξ : Renaming},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    ∀ (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩),
    Admission poolBridge context initial →
    ∀ {size : Nat}, size ≤ budget →
    ∀ {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
      {after : Dynamic.Heap},
    Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before statements finalContext bodyOutcome after →
    finalContext = context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (flow.rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld rawResult result callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PostAdmission poolBridge context rawResult outcome reached := by
  induction tree with
  | terminal root head sameType sameRaw =>
    intro mapping world administrative actualContext environment canonical actual before store ξ
      environments heaps locals agrees actualTyped initial admitted size within finalContext bodyOutcome after trace
    cases sameType
    cases sameRaw
    have below := CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.root_preserves_below
      profile root children within
    obtain ⟨childSize, outcome, sameSize, rfl, rfl, childTrace⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body root.support.unique head trace
    obtain ⟨_sourceTrace, value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
      CallableIndexedOwnedAdmittedStagedTerminalStatements.preserves poolBridge head
        ⟨rfl, rfl, rfl⟩ root.support.found root.support.typed environments heaps locals agrees actualTyped
        initial admitted size below childTrace (by simpa only [sameSize] using Nat.le_refl size)
    exact ⟨rfl, outcome, rfl, value, finalStore, finalMap, finalWorld, evaluated, represented,
      finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
  | discard root contains form tail ih =>
    intro mapping world administrative actualContext environment canonical actual before store ξ
      environments heaps locals agrees actualTyped initial admitted size within finalContext bodyOutcome after trace
    have firstBelow := CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.root_preserves_below
      profile root children within
    rcases CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion.child_and_tail
        root.support.unique contains form trace with
      ⟨firstSize, failure, sameSize, rfl, rfl, firstTrace⟩ |
      ⟨firstSize, tailSize, sourceValue, middle, sameSize, firstTrace, tailTrace⟩
    · have firstStrict : firstSize < size := by
        rw [sameSize]
        exact Staging.Recursive.Size.child_lt_stepSize (by simp)
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post⟩ :=
        firstBelow firstSize firstStrict ⟨rfl, rfl, rfl⟩ root.support.found root.support.typed
          environments heaps locals agrees actualTyped initial admitted firstTrace
      cases represented with
      | fault matched =>
        refine ⟨rfl, .fault failure, rfl, _, finalStore, finalMap, finalWorld, ?_, .fault matched,
          finalHeaps, maps, worlds, frame, metadata, reached, related, post.at_fault_type⟩
        rw [LoopRenaming.discard]
        exact LocalSequence.discard_failure _ evaluated
    · have firstStrict : firstSize < size := by
        rw [sameSize]
        exact Staging.Recursive.Size.child_lt_stepSize (by simp)
      have tailWithin : tailSize ≤ budget := by
        apply Nat.le_trans _ within
        rw [sameSize]
        exact Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
          firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        firstBelow firstSize firstStrict ⟨rfl, rfl, rfl⟩ root.support.found root.support.typed
          environments heaps locals agrees actualTyped initial admitted firstTrace
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨rfl, outcome, sameOutcome, value, finalStore, finalMap, finalWorld, second,
            represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
          ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (agree_prefix agrees coreValue)
            (.cons ((model).runtime_hasType payload) (actualTyped.weaken firstWorlds))
            middleState firstPost.at_value.2 tailWithin tailTrace
        refine ⟨rfl, outcome, sameOutcome, value, finalStore, finalMap, finalWorld, ?_, represented,
          finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
          firstMetadata.trans metadata, reached, firstRelated.trans related, post⟩
        rw [LoopRenaming.discard]
        rw [rename_prefix] at second
        exact LocalSequence.discard_success _ first second

/-- Each native bind inversion selects the actual executed children. Reflection
rebuilds every original discard, retaining independent Source grades and faults. -/
theorem reflects_flow
    (tree : Tree compiled context invocation scope semanticFaults result rawResult statements flow)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize) :
    ∀ {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
      {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
      {store : Store} {ξ : Renaming},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    ∀ (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩),
    Admission poolBridge context initial →
    ∀ {size : Nat}, size ≤ budget → ∀ {value : Value} {finalStore : Store},
    EvaluationSize size actual store (flow.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before statements context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld rawResult result callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ PostAdmission poolBridge context rawResult outcome reached := by
  induction tree with
  | terminal root head sameType sameRaw =>
    intro mapping world administrative actualContext environment canonical actual before store ξ
      environments heaps locals agrees actualTyped initial admitted size within value finalStore completed
    cases sameType
    cases sameRaw
    have below := CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.root_reflects_below
      profile root children within
    exact CallableIndexedOwnedAdmittedStagedTerminalStatements.reflects poolBridge head
      ⟨rfl, rfl, rfl⟩ root.support.found root.support.typed environments heaps locals agrees actualTyped
      initial admitted size below completed (Nat.le_refl size)
  | @discard id node expression rest firstCode tailFlow root contains form tail ih =>
    intro mapping world administrative actualContext environment canonical actual before store ξ
      environments heaps locals agrees actualTyped initial admitted size within value finalStore completed
    have firstBelow := CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.root_reflects_below
      profile root children within
    have original := completed
    rw [LoopRenaming.discard] at original
    change EvaluationSize size actual store
      (LanguageResult.bind (LocalLoop.controlType result) (firstCode.expression.rename ξ)
        ((tailFlow.rename ξ).weakenAt 0)) value finalStore at original
    cases CallableIndirectCallBounds.bind_completed original (Nat.le_refl _) with
    | failed first strict =>
      obtain ⟨firstSize, outcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post⟩ :=
        firstBelow _ strict ⟨rfl, rfl, rfl⟩ root.support.found root.support.typed
          environments heaps locals agrees actualTyped initial admitted first
      cases represented with
      | fault matched =>
        exact ⟨_, .fault _, after, finalMap, finalWorld,
          .expressionFault contains form firstTrace, .fault matched, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post.at_fault_type⟩
    | continued first remaining firstStrict remainingStrict =>
      have tailWithin := Nat.le_trans (Nat.le_of_lt remainingStrict) within
      obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
          firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        firstBelow _ firstStrict ⟨rfl, rfl, rfl⟩ root.support.found root.support.typed
          environments heaps locals agrees actualTyped initial admitted first
      cases represented with
      | @value sourceValue coreValue payload =>
        have shifted := remaining
        rw [← rename_prefix] at shifted
        obtain ⟨tailSize, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps,
            maps, worlds, frame, metadata, reached, related, post⟩ :=
          ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (agree_prefix agrees _)
            (.cons ((model).runtime_hasType payload) (actualTyped.weaken firstWorlds))
            middleState firstPost.at_value.2 tailWithin shifted
        exact ⟨_, outcome, after, finalMap, finalWorld, .discard contains form firstTrace tailTrace,
          represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
          firstFrame.trans frame, firstMetadata.trans metadata, reached,
          firstRelated.trans related, post⟩
end Flow
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardSequenceFlowBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyCompilerSupport
/-! The actual discard compiler issuer constructs the mixed support at each
genuine selected Source scope. Its original frame, parameter context, full
LocalView/Avoids transport and proof-indexed CallsReady remain explicit static
inputs. No expression or body meaning is an input. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyCompilerSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Discard DiscardSupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
  {inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {changed : List ExpressionId} {roots : List NodeId}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel bodyFuel : Nat}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}

/-- Each child receives a static issuer for this same whole receipt and the
actual BodyWith parameter inputs. Varying selected scopes are not collapsed
to source equality or one packet-selected scope. -/
def of_static (packet : Discard code stages)
    (packets : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
      CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.Static
        (compiled := compiled) (function := function) (context := inputs.context)
        (types := inputs.types) (invocation := child) (changed := changed) (roots := roots)
        (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
        (readFuel := readFuel) (bodyFuel := bodyFuel) (semanticFaults := semanticFaults)
        (native := native) (active := active) packet.receipt)
    (ready : ∀ (child : Staging.Recursive.Scope) (selected : stages.Closure function child),
      CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.Ready
        (packets child selected)) :
    DiscardSupport code inputs stages packet semanticFaults where
  heads := fun child selected =>
    ⟨packet.receipt.shape.node,
      packet.receipt.source_head (packets child selected).edited.metadata⟩
  roots := fun child selected =>
    CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.rootPair
      (packets child selected) (ready child selected)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyCompilerSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodySupportCompatibility
/-! Existing compiler support embeds into the Association-specific support.
The new nested-formation branch cannot be produced by the original support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association
      headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (stages : Staging.Recursive.Registry)
    (packet : PacketFor association stages)

/-- The original body support at the actual Association's entry context. -/
def GenericSupportFor : Type :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
      Support headers code support.body.toContext stages packet semanticFaults
  | .principal _ _ code _ support _ _ _ _ _ _ =>
      Support headers code support.body.toContext stages packet semanticFaults

/-- Original support uses every unchanged branch without any extra premise. -/
def SupportFor.of_generic (supported : GenericSupportFor association stages packet) :
    SupportFor association stages packet := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      cases packet <;> first | exact supported | exact nomatch supported
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact supported

/-- A compiler-selected original packet embeds without choosing a new packet. -/
theorem SupportFor.of_generic_packets
    (supported : Nonempty (Σ current : PacketFor association stages,
      GenericSupportFor association stages current)) :
    Nonempty (Σ current : PacketFor association stages, SupportFor association stages current) := by
  obtain ⟨current, supported⟩ := supported
  exact ⟨⟨current, SupportFor.of_generic association stages current supported⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
end
