import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBareAssignmentTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds

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
  collected : ∀ child, stages.Closure function child →
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected compiled.indexed.layouts packet.allocationOwner packet.active
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
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    (support.tree child selected).CatalogSites .reachable registry faults :=
  (support.collected child selected).sites registry faults

/-- The chosen static support is indexed by the authentic packet and input
context. The sequence branch contains no whole-body result equality. -/
def Support {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry) (packet : Packet code stages)
    (semanticFaults : FunctionCalls.FaultRep) : Type :=
  match packet with
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
  match association, packet with
  | .ordinary _ _ code _ support _ _ _ _ _ _, packet =>
      Support code support.body.toContext stages packet semanticFaults
  | .principal _ _ code _ support _ _ _ _ _ _, packet =>
      Support code support.body.toContext stages packet semanticFaults

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
