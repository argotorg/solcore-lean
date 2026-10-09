import Solcore.Test.SourceCoreChosenOrdinaryAcceptedFixture
import Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticTokenPlan
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinCertificates

/-! Finite inventory checks use the unchanged accepted fixture Source. Actual
lookup receipts identify every retained node. Diagnostic typing follows by
absence; builtin row profiles keep original numeric and local metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreChosenOrdinaryAcceptedStaticInventory
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedNamedGeneration SourceCoreChosenOrdinaryAcceptedFixture

/-- The allowed ids name the actual Graph and ParentRows records. -/
def checkInventory (packet : Packet) : Bool :=
  (source packet.named).nodes.all fun
    | .statement node => decide (node.id = statementId packet 0 ∨
        node.id = statementId packet 2 ∨ node.id = statementId packet 4)
    | .expression node => decide (node.id = expressionId packet 1 ∨
        node.id = expressionId packet 3 ∨ node.id = expressionId packet 5 ∨
        node.id = expressionId packet 6 ∨ node.id = expressionId packet 7 ∨
        node.id = expressionId packet 8 ∨ node.id = expressionId packet 9)

structure Inventory (fixture : AcceptedFixture) : Prop where
  nodes : checkInventory fixture.packet = true
  contracts : fixture.packet.compiled.compatible.checked.catalog.callableContracts = true
  parameterType : fixture.packet.named.signature.parameterType = .unit
  resultType : fixture.packet.named.signature.resultType = .word

def inventory (fixture : AcceptedFixture) : Except String (PLift (Inventory fixture)) := do
  if nodes : checkInventory fixture.packet = true then
    if metadata : fixture.packet.compiled.compatible.checked.catalog.callableContracts = true ∧
        fixture.packet.named.signature.parameterType = .unit ∧ fixture.packet.named.signature.resultType = .word then
      pure ⟨⟨nodes, metadata.1, metadata.2.1, metadata.2.2⟩⟩
    else throw "actual callable contract or named signature differs"
  else throw "actual Source node inventory differs"

variable {fixture : AcceptedFixture}

theorem Inventory.statement_ids (given : Inventory fixture) {id : StatementId} {node : StatementNode}
    (found : (source fixture.packet.named).lookupStatement? id = some node) :
    id = statementId fixture.packet 0 ∨ id = statementId fixture.packet 2 ∨ id = statementId fixture.packet 4 := by
  have contains := lookupStatement?_sound found
  have checked := List.all_eq_true.mp given.nodes (.statement node) contains.1
  change decide (node.id = statementId fixture.packet 0 ∨ node.id = statementId fixture.packet 2 ∨
    node.id = statementId fixture.packet 4) = true at checked
  simpa only [contains.2] using of_decide_eq_true checked

theorem Inventory.expression_ids (given : Inventory fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : (source fixture.packet.named).lookupExpression? id = some node) :
    id = expressionId fixture.packet 1 ∨ id = expressionId fixture.packet 3 ∨ id = expressionId fixture.packet 5 ∨
    id = expressionId fixture.packet 6 ∨ id = expressionId fixture.packet 7 ∨
    id = expressionId fixture.packet 8 ∨ id = expressionId fixture.packet 9 := by
  have contains := lookupExpression?_sound found
  have checked := List.all_eq_true.mp given.nodes (.expression node) contains.1
  change decide (node.id = expressionId fixture.packet 1 ∨ node.id = expressionId fixture.packet 3 ∨
    node.id = expressionId fixture.packet 5 ∨ node.id = expressionId fixture.packet 6 ∨
    node.id = expressionId fixture.packet 7 ∨ node.id = expressionId fixture.packet 8 ∨
    node.id = expressionId fixture.packet 9) = true at checked
  simpa only [contains.2] using of_decide_eq_true checked

/-- Full row equality uses genuine lookup receipts, including raw metadata. -/
theorem Inventory.statements (given : Inventory fixture) {id : StatementId} {node : StatementNode}
    (found : (source fixture.packet.named).lookupStatement? id = some node) :
    node = fixture.graph.initialized ∨ node = fixture.graph.returned ∨ node = fixture.graph.outerReturn := by
  rcases given.statement_ids found with rfl | rfl | rfl
  · exact .inl (Option.some.inj (found.symm.trans fixture.graph.initializedFound))
  · exact .inr (.inl (Option.some.inj (found.symm.trans fixture.graph.returnedFound)))
  · exact .inr (.inr (Option.some.inj (found.symm.trans fixture.graph.outerReturnFound)))

theorem Inventory.expressions (given : Inventory fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : (source fixture.packet.named).lookupExpression? id = some node) :
    node = fixture.graph.lambdaNode ∨ node = fixture.graph.literal ∨ node = fixture.graph.parent ∨
    node = fixture.graph.argument ∨ node = fixture.parentRows.left ∨ node = fixture.parentRows.right ∨ node = fixture.graph.callee := by
  rcases given.expression_ids found with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (Option.some.inj (found.symm.trans fixture.graph.lambdaFound))
  · exact .inr (.inl (Option.some.inj (found.symm.trans fixture.graph.literalFound)))
  · exact .inr (.inr (.inl (Option.some.inj (found.symm.trans fixture.graph.parentFound))))
  · exact .inr (.inr (.inr (.inl (Option.some.inj (found.symm.trans fixture.graph.argumentFound)))))
  · exact .inr (.inr (.inr (.inr (.inl (Option.some.inj (found.symm.trans fixture.parentRows.leftFound))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl (Option.some.inj (found.symm.trans fixture.parentRows.rightFound)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (Option.some.inj (found.symm.trans fixture.graph.calleeFound)))))))

private theorem no_statement_forms (given : Inventory fixture) {id : StatementId} {node : StatementNode}
    (found : (source fixture.packet.named).lookupStatement? id = some node) :
    (∀ assignment, node.form ≠ .assignBitNot assignment) ∧
    (∀ assignment operator rhs, node.form ≠ .assignValue assignment operator rhs) ∧
    (∀ initial condition post body, node.form ≠ .forLoop initial condition post body) := by
  rcases given.statements found with rfl | rfl | rfl <;>
    simp [fixture.graph.initializedForm, fixture.graph.returnedForm, fixture.graph.outerReturnForm]

/-- No unary statement or for-header occurrence exists in this full Source. -/
theorem Inventory.unary_typed (given : Inventory fixture) : EmittedDiagnosticTokenPlan.UnaryTyped (source fixture.packet.named) := by
  intro site assignment origin
  cases origin with
  | statement found form => exact ((no_statement_forms given found).1 _ form).elim
  | header found form _ => exact ((no_statement_forms given found).2.2 _ _ _ _ form).elim

/-- No assignment statement or for-header occurrence exists in this full Source. -/
theorem Inventory.operands_typed (given : Inventory fixture) : AssignmentDiagnosticOrigins.OperandsTyped (source fixture.packet.named) := by
  intro site assignment operator rhs origin
  cases origin with
  | statement found form => exact ((no_statement_forms given found).2.1 _ _ _ form).elim
  | header found form _ => exact ((no_statement_forms given found).2.2 _ _ _ _ form).elim

theorem Inventory.typing (given : Inventory fixture) :
    EmittedDiagnosticTokenPlan.UnaryTyped (source fixture.packet.named) ∧
    AssignmentDiagnosticOrigins.OperandsTyped (source fixture.packet.named) := ⟨given.unary_typed, given.operands_typed⟩

/-- Genuine full inventory excludes every constructor, at any static context. -/
theorem Inventory.constructor_law (given : Inventory fixture) (context : SourceSemantics.Context)
    (allowed : ExpressionId → Prop) : CompatibleExpressionInstantiationLaws.ConstructorLaw (source fixture.packet.named) context allowed := by
  intro id node instantiation arguments _allowed found form _valid
  rcases given.expressions found with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [fixture.graph.lambdaForm, fixture.graph.literalForm, fixture.graph.parentForm,
      fixture.graph.argumentForm, fixture.parentRows.leftForm, fixture.parentRows.rightForm, fixture.graph.calleeForm] at form

/-- Local references are the original nongeneralized callee row. -/
theorem Inventory.reference_profile (given : Inventory fixture) {id : ExpressionId} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId} (found : (source fixture.packet.named).lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder)) :
    fixture.packet.compiled.indexed.base.locals.bindings.any (fun binding =>
      decide (binding.caller = fixture.packet.named.signature.key ∧ binding.binder.id = binder)) = false := by
  rcases given.expressions found with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try simp [fixture.graph.lambdaForm, fixture.graph.literalForm, fixture.graph.parentForm,
    fixture.graph.argumentForm, fixture.parentRows.leftForm, fixture.parentRows.rightForm] at form
  have same := ExpressionForm.reference.inj (fixture.graph.calleeForm.symm.trans form)
  have binderEq := ReferenceResolution.local.inj same.2
  rw [← binderEq]
  exact fixture.parentRows.generalized

/-- Only the lambda and indirect call are outside the builtin grammar. -/
private def extraRoot : ExpressionForm → Bool
  | .lambda _ _ _ => true
  | .call _ _ (.indirect _) => true
  | _ => false

private theorem atomic_root {form : ExpressionForm}
    (atomic : CompatibleExpressionLiterals.Atomic form) : extraRoot form = false := by
  cases atomic <;> rfl

private theorem product_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionProducts.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | literal found atomic => exact ⟨_, found, atomic_root atomic⟩
  | read found form => exact ⟨_, found, by rw [form]; rfl⟩
  | group found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | pair found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem primitive_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionPrimitives.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | product child => exact product_root child
  | group found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | pair found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | unary found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | binary found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem conditional_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionConditionals.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | primitive child => exact primitive_root child
  | group found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | pair found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | unary found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | binary found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | conditional found form _ _ _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem constructor_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionConstructors.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | fragment child => exact conditional_root child
  | constructor found form _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem member_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionMembers.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | fragment child => exact constructor_root child
  | member found form _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem recursive_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionRecursive.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | fragment child => exact member_root child
  | group found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | pair found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | unary found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | binary found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | conditional found form _ _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | constructor found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | member found form _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem general_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionGeneral.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | fragment child => exact recursive_root child
  | proxy found form => exact ⟨_, found, by rw [form]; rfl⟩
  | group found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | pair found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | unary found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | binary found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | conditional found form _ _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | constructor found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | member found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | index found form _ _ _ => exact ⟨_, found, by rw [form]; rfl⟩

private theorem builtin_root {view : TypedSource} {id : ExpressionId}
    (tree : CompatibleExpressionBuiltins.Syntax view id) :
    ∃ node, view.lookupExpression? id = some node ∧ extraRoot node.form = false := by
  cases tree with
  | fragment child => exact general_root child
  | proxy found form => exact ⟨_, found, by rw [form]; rfl⟩
  | group found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | pair found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | unary found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | binary found form _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | conditional found form _ _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | constructor found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | member found form _ => exact ⟨_, found, by rw [form]; rfl⟩
  | index found form _ _ _ => exact ⟨_, found, by rw [form]; rfl⟩
  | builtin found form _ => exact ⟨_, found, by rw [form]; rfl⟩

/-- Every actual builtin row is one of the retained numeric/read/pair rows.
This finite root-form inversion never visits semantic children. -/
theorem Inventory.builtin_ids (given : Inventory fixture) {id : ExpressionId}
    (tree : CompatibleExpressionBuiltins.Syntax (source fixture.packet.named) id) :
    id = expressionId fixture.packet 3 ∨ id = expressionId fixture.packet 6 ∨
    id = expressionId fixture.packet 7 ∨ id = expressionId fixture.packet 8 ∨ id = expressionId fixture.packet 9 := by
  obtain ⟨node, found, ordinary⟩ := builtin_root tree
  rcases given.expression_ids found with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have same := Option.some.inj (found.symm.trans fixture.graph.lambdaFound)
    rw [same, fixture.graph.lambdaForm] at ordinary
    cases ordinary
  · exact .inl rfl
  · have same := Option.some.inj (found.symm.trans fixture.graph.parentFound)
    rw [same, fixture.graph.parentForm] at ordinary
    cases ordinary
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr rfl)))

theorem Inventory.fragment_coercions (given : Inventory fixture) {id : ExpressionId} {node : ExpressionNode}
    (tree : CompatibleExpressionBuiltins.Syntax (source fixture.packet.named) id)
    (found : (source fixture.packet.named).lookupExpression? id = some node) : node.coercions = [] := by
  rcases given.builtin_ids tree with rfl | rfl | rfl | rfl | rfl
  · have same := Option.some.inj (found.symm.trans fixture.graph.literalFound)
    exact same ▸ fixture.graph.literalCoercions
  · have same := Option.some.inj (found.symm.trans fixture.graph.argumentFound)
    exact same ▸ fixture.parentRows.argumentCoercions
  · have same := Option.some.inj (found.symm.trans fixture.parentRows.leftFound)
    exact same ▸ fixture.parentRows.leftCoercions
  · have same := Option.some.inj (found.symm.trans fixture.parentRows.rightFound)
    exact same ▸ fixture.parentRows.rightCoercions
  · have same := Option.some.inj (found.symm.trans fixture.graph.calleeFound)
    exact same ▸ fixture.parentRows.calleeCoercions

/-- The three genuine ordinary forms retain the original contextual read and
special callback, including its literal initializer and evidence gates. -/
theorem ordinary_policy {packet : Packet}
    {compilation : Compilation packet.compiled.indexed packet.named
      (effectiveDiagnostics packet.compiled packet.diagnostics) packet.namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := packet.compiled) packet.named (effectiveDiagnostics packet.compiled packet.diagnostics)
      packet.namedCode compilation rootFuel rootSource rootScope rootId
      ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key) rootLowered)
    {childScope : SourceCoreLocalCell.Scope} {childId : ExpressionId} {node : ExpressionNode}
    {owned : List RequirementId}
    (found : (source packet.named).lookupExpression? childId = some node)
    (shape : (∃ name binder, node.form = .reference name (.local binder) ∧
        packet.compiled.indexed.base.locals.bindings.any (fun binding =>
          decide (binding.caller = packet.named.signature.key ∧ binding.binder.id = binder)) = false) ∨
      (∃ ids, node.form = .tuple ids) ∨
      (∃ literal resolution, node.form = .integerLiteral literal resolution))
    (ownedRequirements : SourceCompilationPlan.ordinaryOwnedRequirements? node = some owned)
    (coercions : node.coercions = [])
    (requirements : node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution)
    (ordinary : packet.compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = packet.named.signature.key ∧ binding.initializer = childId)) = none) :
    CallableIndexedOwnedContextualCompilerPolicyProfiles.PointwiseFor root
      (source packet.named) childScope childId
      ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key) := by
  have owner : (context packet.compiled.indexed packet.named).owner = packet.named.signature.key := rfl
  have sameSource : SourceCoreGeneralFunctions.contextualSource packet.compiled.indexed.base.sourceProgram
      (context packet.compiled.indexed packet.named).plan packet.compiled.indexed.base.locals
      (context packet.compiled.indexed packet.named).owner none (source packet.named) childId = .ok (source packet.named) := by
    rcases shape with ⟨name, binder, form, generalized⟩ | ⟨ids, form⟩ | ⟨literal, resolution, form⟩
    · simp only [SourceCoreGeneralFunctions.contextualSource, found, bind, Except.bind, pure, Except.pure, form, owner, generalized, Bool.false_eq_true, ↓reduceIte]
    · simp [SourceCoreGeneralFunctions.contextualSource, found, form]
    · simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  constructor
  · rw [root.selected.readExpression]
    simp only [sameSource, bind, Except.bind]
    rw [CallableIndexedOwnedIndirectCompilerPolicyInputs.representation_read (compiled := packet.compiled) packet.named]
  · intro child budget
    rw [root.selected.special_eq, root.selected.special_body]
    have evidenceNone : SourceCoreEvidence.lowerWithProjector packet.compiled.indexed.base.sourceProgram
        ((representation packet.compiled.indexed).atContext packet.named.signature.key []).expressions.projectType
        packet.named.specialized (context packet.compiled.indexed packet.named) child budget
        (source packet.named) childScope childId
        ((effectiveDiagnostics packet.compiled packet.diagnostics).reasonAt packet.named.signature.key)
        (SourceCoreGeneralFunctions.callablePolicy packet.compiled.indexed.base.callableContext []) = .ok none := by
      rcases requirements with empty | ⟨literal, resolution, form⟩
      · rcases shape with ⟨name, binder, form, _generalized⟩ | ⟨ids, form⟩ | ⟨literal, resolution, form⟩ <;>
          simp [SourceCoreEvidence.lowerWithProjector, found, form, ownedRequirements, coercions, empty]
      · simp [SourceCoreEvidence.lowerWithProjector, found, form, ownedRequirements, coercions]
    simp only [bind, Except.bind]
    rw [sameSource]
    simp only [found, pure, Except.pure, owner, ordinary, Option.filter_none, evidenceNone]
    rcases shape with ⟨name, binder, form, generalized⟩ | ⟨ids, form⟩ | ⟨literal, resolution, form⟩
    · simp only [form, generalized, Bool.false_eq_true, ↓reduceIte]
    · simp only [form]
    · simp only [form]

/-- Whole builtin policy fields follow from actual finite row profiles. The
root selector is supplied once by the original initializer acceptance. -/
theorem Inventory.builtin_policy (given : Inventory fixture)
    {compilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := fixture.packet.compiled) fixture.packet.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      rootFuel rootSource rootScope rootId
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) rootLowered)
    (childScope : SourceCoreLocalCell.Scope) {id : ExpressionId}
    (tree : CompatibleExpressionBuiltins.Syntax (source fixture.packet.named) id) :
    CallableIndexedOwnedContextualCompilerPolicyProfiles.PointwiseFor root
      (source fixture.packet.named) childScope id
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) := by
  have emptyOwned (node : ExpressionNode) (requirements : node.requirements = []) (coercions : node.coercions = []) :
      SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  rcases given.builtin_ids tree with rfl | rfl | rfl | rfl | rfl
  · exact ordinary_policy root fixture.graph.literalFound
      (.inr (.inr ⟨_, _, fixture.graph.literalForm⟩)) fixture.graph.literalOwned fixture.graph.literalCoercions
      (.inr ⟨_, _, fixture.graph.literalForm⟩) fixture.calls.literalOrdinary
  · exact ordinary_policy root fixture.graph.argumentFound (.inr (.inl ⟨_, fixture.graph.argumentForm⟩))
      (emptyOwned _ fixture.parentRows.argumentRequirements fixture.parentRows.argumentCoercions)
      fixture.parentRows.argumentCoercions (.inl fixture.parentRows.argumentRequirements) fixture.parentRows.argumentOrdinary
  · exact ordinary_policy root fixture.parentRows.leftFound (.inr (.inr ⟨_, _, fixture.parentRows.leftForm⟩))
      fixture.parentRows.leftOwned fixture.parentRows.leftCoercions
      (.inr ⟨_, _, fixture.parentRows.leftForm⟩) fixture.parentRows.leftOrdinary
  · exact ordinary_policy root fixture.parentRows.rightFound (.inr (.inr ⟨_, _, fixture.parentRows.rightForm⟩))
      fixture.parentRows.rightOwned fixture.parentRows.rightCoercions
      (.inr ⟨_, _, fixture.parentRows.rightForm⟩) fixture.parentRows.rightOrdinary
  · exact ordinary_policy root fixture.graph.calleeFound (.inl ⟨_, _, fixture.graph.calleeForm, fixture.parentRows.generalized⟩)
      (emptyOwned _ fixture.parentRows.calleeRequirements fixture.parentRows.calleeCoercions)
      fixture.parentRows.calleeCoercions (.inl fixture.parentRows.calleeRequirements) fixture.parentRows.calleeOrdinary

/-- Execute actual full inventory and signature checks over the unchanged
compiler fixture; the sound static facts above remain kernel proofs. -/
def run : IO Unit := do
  match acceptedFixture with
  | .error error => throw (IO.userError error)
  | .ok fixture =>
    match inventory fixture with
    | .error error => throw (IO.userError error)
    | .ok _ => IO.println "accepted static inventory: complete Source nodes, genuine contract/signature and diagnostic/builtin profiles checked"

end Tests.SourceCoreChosenOrdinaryAcceptedStaticInventory
