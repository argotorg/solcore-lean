import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinBodyTree
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewStaticTyping
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewPreparedStaticTransport

/-! Static runtime certificates cross local lambda views only at the reached
body occurrences. Numeric selectors retain their complete node and solved row;
metadata views alone do not supply that evidence. No execution law is stored. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewMatchRuntimeCertificates
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

section Expressions
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
include edited avoids

/-- Full node lookup equality transports the exact selected implementation row. -/
theorem literal {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionLiteralRuntime.Certificate solved source id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionLiteralRuntime.Certificate solved view id lowered := by
  obtain ⟨node, found, leaf, selected⟩ := receipt
  exact ⟨node, (expression_lookup edited avoids reached).symm.trans found, leaf, selected⟩

private theorem products_sites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered}
    (sites : tree.LiteralSites (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code))
    (reached : Reaches source roots (.expression id)) :
    (CallableLambdaViewScalarTrees.products edited avoids tree reached).LiteralSites
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved view id code) := by
  revert reached
  induction sites with
  | literal receipt selected =>
    intro reached
    exact .literal
      (CallableLambdaViewExpressionLeaves.literal edited avoids reached receipt) (literal edited avoids selected reached)
  | read receipt => intro reached; exact .read (CallableLambdaViewExpressionLeaves.loweredRead edited avoids reached receipt)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree childSites ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (CallableLambdaViewScalarTrees.products edited avoids tree child) (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstSites secondSites firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (CallableLambdaViewScalarTrees.products edited avoids firstTree leftReached) (CallableLambdaViewScalarTrees.products edited avoids secondTree rightReached)
      (firstIH leftReached) (secondIH rightReached)

private theorem primitives_sites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id lowered}
    (sites : tree.LiteralSites (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code))
    (reached : Reaches source roots (.expression id)) :
    (CallableLambdaViewScalarTrees.primitives edited avoids tree reached).LiteralSites
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved view id code) := by
  revert reached
  induction sites with
  | product tree childSites => intro reached; exact .product (CallableLambdaViewScalarTrees.products edited avoids tree reached) (products_sites edited avoids childSites reached)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree childSites ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (CallableLambdaViewScalarTrees.primitives edited avoids tree child) (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstSites secondSites firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (CallableLambdaViewScalarTrees.primitives edited avoids firstTree leftReached) (CallableLambdaViewScalarTrees.primitives edited avoids secondTree rightReached)
      (firstIH leftReached) (secondIH rightReached)
  | @unary id node operand childNode operator operandType resultType core childCode receipt form found inputType outputType profile tree childSites ih =>
    intro reached
    have child : Reaches source roots (.expression operand) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans found) inputType outputType profile (CallableLambdaViewScalarTrees.primitives edited avoids tree child) (ih child)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode receipt form leftFound rightFound leftType rightType outputType profile first second firstSites secondSites firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) leftType rightType outputType profile
      (CallableLambdaViewScalarTrees.primitives edited avoids first leftReached) (CallableLambdaViewScalarTrees.primitives edited avoids second rightReached)
      (firstIH leftReached) (secondIH rightReached)

private theorem conditionals_sites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered}
    (sites : tree.LiteralSites (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code))
    (reached : Reaches source roots (.expression id)) :
    (CallableLambdaViewScalarTrees.conditionals edited avoids tree reached).LiteralSites
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved view id code) := by
  revert reached
  induction sites with
  | primitive tree childSites => intro reached; exact .primitive (CallableLambdaViewScalarTrees.primitives edited avoids tree reached) (primitives_sites edited avoids childSites reached)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree childSites ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (CallableLambdaViewScalarTrees.conditionals edited avoids tree child) (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstSites secondSites firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (CallableLambdaViewScalarTrees.conditionals edited avoids firstTree leftReached) (CallableLambdaViewScalarTrees.conditionals edited avoids secondTree rightReached)
      (firstIH leftReached) (secondIH rightReached)
  | @unary id node operand childNode operator operandType resultType core childCode receipt form found inputType outputType profile tree childSites ih =>
    intro reached
    have child : Reaches source roots (.expression operand) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans found) inputType outputType profile (CallableLambdaViewScalarTrees.conditionals edited avoids tree child) (ih child)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode receipt form leftFound rightFound leftType rightType outputType profile first second firstSites secondSites firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) leftType rightType outputType profile
      (CallableLambdaViewScalarTrees.conditionals edited avoids first leftReached) (CallableLambdaViewScalarTrees.conditionals edited avoids second rightReached)
      (firstIH leftReached) (secondIH rightReached)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode receipt form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionSites thenSites elseSites conditionIH thenIH elseIH =>
    intro reached
    have conditionReached : Reaches source roots (.expression condition) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have thenReached : Reaches source roots (.expression thenId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have elseReached : Reaches source roots (.expression elseId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .conditional (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids conditionReached).symm.trans conditionFound)
      ((expression_lookup edited avoids thenReached).symm.trans thenFound)
      ((expression_lookup edited avoids elseReached).symm.trans elseFound) conditionType thenType elseType
      (CallableLambdaViewScalarTrees.conditionals edited avoids conditionTree conditionReached) (CallableLambdaViewScalarTrees.conditionals edited avoids thenTree thenReached) (CallableLambdaViewScalarTrees.conditionals edited avoids elseTree elseReached)
      (conditionIH conditionReached) (thenIH thenReached) (elseIH elseReached)

private theorem constructors_sites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionConstructors.Tree fuel values source context solved reasonAt scope id lowered}
    (sites : tree.LiteralSites (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code))
    (reached : Reaches source roots (.expression id)) :
    (CallableLambdaViewDataTrees.constructors edited avoids tree reached).LiteralSites
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved view id code) := by
  revert reached
  induction sites with
  | fragment tree childSites => intro reached; exact .fragment (CallableLambdaViewScalarTrees.conditionals edited avoids tree reached) (conditionals_sites edited avoids childSites reached)
  | @constructor id node instantiation ids tag word codes receipt form valid count nodeReceipt children childrenSites ih =>
    intro reached
    have childReached := CallableLambdaViewDataTrees.constructor_children reached receipt.metadata.found form
    exact .constructor (CallableLambdaViewDataTrees.header edited avoids reached receipt) form valid count
      (CallableLambdaViewDataTrees.nodes edited avoids nodeReceipt childReached)
      (fun child code member => CallableLambdaViewDataTrees.constructors edited avoids (children child code member) (childReached child (List.of_mem_zip member).1))
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))

private theorem members_sites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionMembers.Tree fuel values source context solved reasonAt scope id lowered}
    (sites : tree.LiteralSites (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code))
    (reached : Reaches source roots (.expression id)) :
    (CallableLambdaViewDataTrees.members edited avoids tree reached).LiteralSites
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved view id code) := by
  revert reached
  induction sites with
  | fragment tree childSites => intro reached; exact .fragment (CallableLambdaViewDataTrees.constructors edited avoids tree reached) (constructors_sites edited avoids childSites reached)
  | @member id node base baseNode name index identity branches result child receipt baseMetadata form layout childTree childSites ih =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .member (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt)
      (CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached baseMetadata) form layout (CallableLambdaViewDataTrees.members edited avoids childTree baseReached) (ih baseReached)

private theorem recursive_sites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope id lowered}
    (sites : tree.LiteralSites (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code))
    (reached : Reaches source roots (.expression id)) :
    (CallableLambdaViewRecursiveTrees.recursive edited avoids tree reached).LiteralSites
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved view id code) := by
  revert reached
  induction sites with
  | fragment tree childSites => intro reached; exact .fragment (CallableLambdaViewDataTrees.members edited avoids tree reached) (members_sites edited avoids childSites reached)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree childSites ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (CallableLambdaViewRecursiveTrees.recursive edited avoids tree child) (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstSites secondSites firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (CallableLambdaViewRecursiveTrees.recursive edited avoids firstTree leftReached) (CallableLambdaViewRecursiveTrees.recursive edited avoids secondTree rightReached)
      (firstIH leftReached) (secondIH rightReached)
  | @unary id node operand childNode operator operandType resultType core childCode receipt form found inputType outputType profile tree childSites ih =>
    intro reached
    have child : Reaches source roots (.expression operand) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans found) inputType outputType profile (CallableLambdaViewRecursiveTrees.recursive edited avoids tree child) (ih child)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode receipt form leftFound rightFound leftType rightType outputType profile first second firstSites secondSites firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) leftType rightType outputType profile
      (CallableLambdaViewRecursiveTrees.recursive edited avoids first leftReached) (CallableLambdaViewRecursiveTrees.recursive edited avoids second rightReached)
      (firstIH leftReached) (secondIH rightReached)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode receipt form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionSites thenSites elseSites conditionIH thenIH elseIH =>
    intro reached
    have conditionReached : Reaches source roots (.expression condition) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have thenReached : Reaches source roots (.expression thenId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have elseReached : Reaches source roots (.expression elseId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .conditional (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids conditionReached).symm.trans conditionFound)
      ((expression_lookup edited avoids thenReached).symm.trans thenFound)
      ((expression_lookup edited avoids elseReached).symm.trans elseFound) conditionType thenType elseType
      (CallableLambdaViewRecursiveTrees.recursive edited avoids conditionTree conditionReached) (CallableLambdaViewRecursiveTrees.recursive edited avoids thenTree thenReached) (CallableLambdaViewRecursiveTrees.recursive edited avoids elseTree elseReached)
      (conditionIH conditionReached) (thenIH thenReached) (elseIH elseReached)

  | @constructor id node instantiation ids tag word codes receipt form valid count nodeReceipt children childrenSites ih =>
    intro reached
    have childReached := CallableLambdaViewDataTrees.constructor_children reached receipt.metadata.found form
    exact .constructor (CallableLambdaViewDataTrees.header edited avoids reached receipt) form valid count
      (CallableLambdaViewDataTrees.nodes edited avoids nodeReceipt childReached)
      (fun child code member => CallableLambdaViewRecursiveTrees.recursive edited avoids (children child code member) (childReached child (List.of_mem_zip member).1))
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))
  | @member id node base baseNode name index identity branches result child receipt baseMetadata form layout childTree childSites ih =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .member (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt)
      (CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached baseMetadata) form layout (CallableLambdaViewRecursiveTrees.recursive edited avoids childTree baseReached) (ih baseReached)

private theorem general_sites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope id lowered}
    (sites : tree.LiteralSites (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code))
    (reached : Reaches source roots (.expression id)) :
    (CallableLambdaViewIndexedTrees.general edited avoids tree reached).LiteralSites
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved view id code) := by
  revert reached
  induction sites with
  | fragment tree childSites => intro reached; exact .fragment (CallableLambdaViewRecursiveTrees.recursive edited avoids tree reached) (recursive_sites edited avoids childSites reached)
  | proxy receipt => intro reached; exact .proxy (CallableLambdaViewExpressionLeaves.proxy edited avoids reached receipt)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree childSites ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (CallableLambdaViewIndexedTrees.general edited avoids tree child) (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstSites secondSites firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (CallableLambdaViewIndexedTrees.general edited avoids firstTree leftReached) (CallableLambdaViewIndexedTrees.general edited avoids secondTree rightReached)
      (firstIH leftReached) (secondIH rightReached)
  | @unary id node operand childNode operator operandType resultType core childCode receipt form found inputType outputType profile tree childSites ih =>
    intro reached
    have child : Reaches source roots (.expression operand) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans found) inputType outputType profile (CallableLambdaViewIndexedTrees.general edited avoids tree child) (ih child)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode receipt form leftFound rightFound leftType rightType outputType profile first second firstSites secondSites firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) leftType rightType outputType profile
      (CallableLambdaViewIndexedTrees.general edited avoids first leftReached) (CallableLambdaViewIndexedTrees.general edited avoids second rightReached)
      (firstIH leftReached) (secondIH rightReached)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode receipt form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionSites thenSites elseSites conditionIH thenIH elseIH =>
    intro reached
    have conditionReached : Reaches source roots (.expression condition) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have thenReached : Reaches source roots (.expression thenId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have elseReached : Reaches source roots (.expression elseId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .conditional (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids conditionReached).symm.trans conditionFound)
      ((expression_lookup edited avoids thenReached).symm.trans thenFound)
      ((expression_lookup edited avoids elseReached).symm.trans elseFound) conditionType thenType elseType
      (CallableLambdaViewIndexedTrees.general edited avoids conditionTree conditionReached) (CallableLambdaViewIndexedTrees.general edited avoids thenTree thenReached) (CallableLambdaViewIndexedTrees.general edited avoids elseTree elseReached)
      (conditionIH conditionReached) (thenIH thenReached) (elseIH elseReached)

  | @constructor id node instantiation ids tag word codes receipt form valid count nodeReceipt children childrenSites ih =>
    intro reached
    have childReached := CallableLambdaViewDataTrees.constructor_children reached receipt.metadata.found form
    exact .constructor (CallableLambdaViewDataTrees.header edited avoids reached receipt) form valid count
      (CallableLambdaViewDataTrees.nodes edited avoids nodeReceipt childReached)
      (fun child code member => CallableLambdaViewIndexedTrees.general edited avoids (children child code member) (childReached child (List.of_mem_zip member).1))
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))
  | @member id node base baseNode name index identity branches result child receipt baseMetadata form layout childTree childSites ih =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .member (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt)
      (CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached baseMetadata) form layout (CallableLambdaViewIndexedTrees.general edited avoids childTree baseReached) (ih baseReached)

  | @index id node base key baseNode keyNode layout comparison first second receipt keyFound form sourceType firstTree secondTree firstSites secondSites firstIH secondIH =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    have keyReached : Reaches source roots (.expression key) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    exact .index (CallableLambdaViewIndexedTrees.header edited avoids reached baseReached receipt)
      ((expression_lookup edited avoids keyReached).symm.trans keyFound) form sourceType (CallableLambdaViewIndexedTrees.general edited avoids firstTree baseReached) (CallableLambdaViewIndexedTrees.general edited avoids secondTree keyReached) (firstIH baseReached) (secondIH keyReached)

private theorem builtins_sites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id lowered}
    (sites : tree.LiteralSites (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code))
    (reached : Reaches source roots (.expression id)) :
    (CallableLambdaViewBuiltinTrees.builtins edited avoids tree reached).LiteralSites
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved view id code) := by
  revert reached
  induction sites with
  | fragment tree childSites => intro reached; exact .fragment (CallableLambdaViewIndexedTrees.general edited avoids tree reached) (general_sites edited avoids childSites reached)
  | proxy receipt => intro reached; exact .proxy (CallableLambdaViewExpressionLeaves.proxy edited avoids reached receipt)
  | @group id node inner innerNode lowered receipt form innerFound sourceType tree childSites ih =>
    intro reached
    have child : Reaches source roots (.expression inner) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .group (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans innerFound) sourceType (CallableLambdaViewBuiltinTrees.builtins edited avoids tree child) (ih child)
  | @pair id node left right leftNode rightNode first second receipt form leftFound rightFound sourceType firstTree secondTree firstSites secondSites firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .pair (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) sourceType
      (CallableLambdaViewBuiltinTrees.builtins edited avoids firstTree leftReached) (CallableLambdaViewBuiltinTrees.builtins edited avoids secondTree rightReached)
      (firstIH leftReached) (secondIH rightReached)
  | @unary id node operand childNode operator operandType resultType core childCode receipt form found inputType outputType profile tree childSites ih =>
    intro reached
    have child : Reaches source roots (.expression operand) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .unary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids child).symm.trans found) inputType outputType profile (CallableLambdaViewBuiltinTrees.builtins edited avoids tree child) (ih child)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode receipt form leftFound rightFound leftType rightType outputType profile first second firstSites secondSites firstIH secondIH =>
    intro reached
    have leftReached : Reaches source roots (.expression left) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have rightReached : Reaches source roots (.expression right) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .binary (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids leftReached).symm.trans leftFound)
      ((expression_lookup edited avoids rightReached).symm.trans rightFound) leftType rightType outputType profile
      (CallableLambdaViewBuiltinTrees.builtins edited avoids first leftReached) (CallableLambdaViewBuiltinTrees.builtins edited avoids second rightReached)
      (firstIH leftReached) (secondIH rightReached)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode receipt form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionSites thenSites elseSites conditionIH thenIH elseIH =>
    intro reached
    have conditionReached : Reaches source roots (.expression condition) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have thenReached : Reaches source roots (.expression thenId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    have elseReached : Reaches source roots (.expression elseId) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .conditional (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form
      ((expression_lookup edited avoids conditionReached).symm.trans conditionFound)
      ((expression_lookup edited avoids thenReached).symm.trans thenFound)
      ((expression_lookup edited avoids elseReached).symm.trans elseFound) conditionType thenType elseType
      (CallableLambdaViewBuiltinTrees.builtins edited avoids conditionTree conditionReached) (CallableLambdaViewBuiltinTrees.builtins edited avoids thenTree thenReached) (CallableLambdaViewBuiltinTrees.builtins edited avoids elseTree elseReached)
      (conditionIH conditionReached) (thenIH thenReached) (elseIH elseReached)

  | @constructor id node instantiation ids tag word codes receipt form valid count nodeReceipt children childrenSites ih =>
    intro reached
    have childReached := CallableLambdaViewDataTrees.constructor_children reached receipt.metadata.found form
    exact .constructor (CallableLambdaViewDataTrees.header edited avoids reached receipt) form valid count
      (CallableLambdaViewDataTrees.nodes edited avoids nodeReceipt childReached)
      (fun child code member => CallableLambdaViewBuiltinTrees.builtins edited avoids (children child code member) (childReached child (List.of_mem_zip member).1))
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))
  | @member id node base baseNode name index identity branches result child receipt baseMetadata form layout childTree childSites ih =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.found (by simp [form, ExpressionForm.references])
    exact .member (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt)
      (CallableLambdaViewExpressionLeaves.metadata edited avoids baseReached baseMetadata) form layout (CallableLambdaViewBuiltinTrees.builtins edited avoids childTree baseReached) (ih baseReached)

  | @index id node base key baseNode keyNode layout comparison first second receipt keyFound form sourceType firstTree secondTree firstSites secondSites firstIH secondIH =>
    intro reached
    have baseReached : Reaches source roots (.expression base) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    have keyReached : Reaches source roots (.expression key) :=
      .expression reached receipt.metadata.found (by simp [form, ExpressionForm.references])
    exact .index (CallableLambdaViewIndexedTrees.header edited avoids reached baseReached receipt)
      ((expression_lookup edited avoids keyReached).symm.trans keyFound) form sourceType (CallableLambdaViewBuiltinTrees.builtins edited avoids firstTree baseReached) (CallableLambdaViewBuiltinTrees.builtins edited avoids secondTree keyReached) (firstIH baseReached) (secondIH keyReached)

  | @builtin id callee arguments function node codes identity contract unknown receipt form sourceType count nodes nativeTypes children childrenSites ih =>
    intro reached
    have childReached : ∀ child, child ∈ arguments → Reaches source roots (.expression child) := by
      intro child member
      exact .expression reached receipt.found (by simp [form, ExpressionForm.references, member])
    exact .builtin (CallableLambdaViewExpressionLeaves.metadata edited avoids reached receipt) form sourceType count
      (CallableLambdaViewDataTrees.nodes edited avoids nodes childReached) nativeTypes
      (fun child code member => CallableLambdaViewBuiltinTrees.builtins edited avoids (children child code member) (childReached child (List.of_mem_zip member).1))
      (fun child code member => ih child code member (childReached child (List.of_mem_zip member).1))

/-- The actual view's full builtin tree and every numeric selector return to
exactly the original reached source nodes. Ordered and repeated children stay
at the same positions and keep the same emitted code. -/
theorem builtin_original {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionBuiltinRuntime.Certificate fuel values view context solved reasonAt scope id lowered)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt scope id lowered := by
  obtain ⟨tree, sites⟩ := receipt
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun expression fresh => (edited.unchanged expression fresh).symm⟩
  exact ⟨CallableLambdaViewBuiltinTrees.builtins reversed (avoids.view edited.metadata) tree (reached.metadata edited.metadata),
    builtins_sites reversed (avoids.view edited.metadata) sites (reached.metadata edited.metadata)⟩
end Expressions


section Static
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)

include edited

private theorem statement_identity : GenericLexicalStatements.StatementSourceIdentity source view := by
  refine ⟨edited.metadata.owner, edited.metadata.inputs, edited.metadata.roots, ?_⟩
  intro id
  cases found : source.lookupStatement? id with
  | some node => exact (edited.metadata.symm.statement found).symm
  | none =>
    cases viewed : view.lookupStatement? id with
    | none => rfl
    | some node => have impossible := edited.metadata.statement viewed; rw [found] at impossible; cases impossible

private theorem pattern_tree {compilation : SourceCoreCompatibleDataMatches.Context}
    {site : StatementId} {span : Syntax.SourceSpan} {scope : SourceCoreLocalCell.Scope}
    {expected : TypeSystem.Ty} {instructions rest : List MatchPatternInstruction}
    {pattern : SourceCoreCompatibleDataMatches.Pattern}
    (tree : CompatiblePatternCertificates.Tree compilation source site span scope expected instructions pattern rest) :
    CompatiblePatternCertificates.Tree compilation view site span scope expected instructions pattern rest := by
  have projectedSame : SourceCoreCompatibleDataMatches.projected compilation source = SourceCoreCompatibleDataMatches.projected compilation view := by
    funext type
    simp only [SourceCoreCompatibleDataMatches.projected, edited.metadata.owner]
  induction tree using CompatiblePatternCertificates.Tree.rec
    (motive_2 := fun types instructions patterns rest _ =>
      CompatiblePatternCertificates.Forest compilation view site span scope types instructions patterns rest) with
  | wildcard projected => exact .wildcard (by simpa only [SourceCoreCompatibleDataMatches.projected, edited.metadata.owner] using projected)
  | binder projected sourceType valid =>
    exact .binder (by simpa only [SourceCoreCompatibleDataMatches.projected, edited.metadata.owner] using projected) sourceType
      (by simpa only [SourceCoreCompatibleDataExpressions.lowerBinder, edited.metadata.owner] using valid)
  | literal projected validated =>
    exact .literal
      (by simpa only [SourceCoreCompatibleDataMatches.projected, edited.metadata.owner] using projected) validated
  | tuple projected unpacked _ projectedChildren ih =>
    exact .tuple (by simpa only [SourceCoreCompatibleDataMatches.projected, edited.metadata.owner] using projected) unpacked ih
      (by simpa only [projectedSame] using projectedChildren)
  | constructor projected result count resolved coreType raw _ projectedChildren registered ih =>
    exact .constructor (by simpa only [SourceCoreCompatibleDataMatches.projected, edited.metadata.owner] using projected)
      result count resolved coreType raw ih
      (by simpa only [projectedSame] using projectedChildren) registered
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

private theorem pattern {compilation : SourceCoreCompatibleDataMatches.Context}
    {site : StatementId} {span : Syntax.SourceSpan} {scope : SourceCoreLocalCell.Scope}
    {expected : TypeSystem.Ty} {pattern : TypedMatchPattern} {compiled : SourceCoreCompatibleDataMatches.Pattern}
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site span expected pattern compiled) :
    CompatiblePatternCertificates.Certificate compilation view scope site span expected pattern compiled := by
  obtain ⟨instructions, root, tree⟩ := certificate.tree
  exact ⟨by simpa only [edited.metadata.owner] using certificate.owned, certificate.type,
    ⟨instructions, root, pattern_tree edited tree⟩, certificate.requirements, certificate.distinctIds, certificate.distinctNames⟩

private theorem arms {compilation : SourceCoreCompatibleDataMatches.Context}
    {site : StatementId} {scope : SourceCoreLocalCell.Scope} {expected : TypeSystem.Ty}
    {bodyCertificate : CompatibleMatchCertificates.BodyCertificate}
    {cases : List TypedMatchCase} {rows : List (SourceCoreCompatibleDataMatches.Pattern × Expr)}
    (receipt : CompatibleMatchCertificates.Arms compilation source site scope expected bodyCertificate cases rows) :
    CompatibleMatchCertificates.Arms compilation view site scope expected bodyCertificate cases rows := by
  induction receipt with
  | nil => exact .nil
  | cons p t b _ ih => exact .cons (pattern edited p) t b ih

private theorem indexed_allocator {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (request : SourceCoreSourceCells.Request) (sameSource : request.source = source) :
    SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError) request =
    SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError) {request with source := view} := by
  subst source
  have a := CallableLambdaViewAllocations.allocator_eq (prepared := layouts) (owner := owner) (active := active) onError
    (request := request) (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata)
  simp only [SourceCoreCallableIndexedAllocationFrames.allocator, SourceCoreCallableIndexedAllocationFrames.annotateWithReceipt]
  split <;> split <;>
    simp_all [Except.map, SourceCoreCallableIndexedAllocationFrames.referenceIndex,
      SourceCoreCallableIndexedAllocationFrames.isNamedInput, edited.metadata.inputs]


private theorem initialized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {compilation : SourceCoreCompatibleDataMatches.Context}
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (scope : SourceCoreLocalCell.Scope) (references : Renaming) (binder : TypedBinder)
    (outputType payloadType : Ty) (initializer body : Expr) :
    SourceCoreSourceCells.letInitialized compilation.sourceCells source scope references binder outputType payloadType initializer body =
    SourceCoreSourceCells.letInitialized compilation.sourceCells view scope references binder outputType payloadType initializer body := by
  simp only [SourceCoreSourceCells.letInitialized, allocator]
  rw [indexed_allocator edited _ rfl]

private theorem bind_arm {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {compilation : SourceCoreCompatibleDataMatches.Context}
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (scope : SourceCoreLocalCell.Scope) (bindings : List (TypedBinder × Ty)) (outputType : Ty) (body : Expr) :
    SourceCoreCompatibleDataMatches.bindArmWithAllocator compilation source scope bindings outputType body =
    SourceCoreCompatibleDataMatches.bindArmWithAllocator compilation view scope bindings outputType body := by
  unfold SourceCoreCompatibleDataMatches.bindArmWithAllocator
  dsimp only
  congr 1
  funext binding continuation
  rcases binding with ⟨⟨binder, type⟩, index⟩
  exact initialized edited allocator _ _ _ _ _ _ _

private theorem branches {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {compilation : SourceCoreCompatibleDataMatches.Context}
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {scope : SourceCoreLocalCell.Scope} {outputType : Ty} {fallback code : Expr}
    {rows : List (SourceCoreCompatibleDataMatches.Pattern × Expr)}
    (receipt : CompatibleMatchCertificates.Branches compilation source scope outputType fallback rows code) :
    CompatibleMatchCertificates.Branches compilation view scope outputType fallback rows code := by
  induction receipt with
  | nil => exact .nil
  | cons allocation _ ih => exact .cons ((bind_arm edited allocator _ _ _ _).symm.trans allocation) ih

include avoids in
private theorem match_certificate {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {compilation : SourceCoreCompatibleDataMatches.Context}
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {before after : CompatibleMatchCertificates.ExpressionCertificate}
    (expressions : ∀ scope id lowered, Reaches source roots (.expression id) → before scope id lowered → after scope id lowered)
    {scope : SourceCoreLocalCell.Scope} {id : StatementId} {resolution : MatchResolution} {type : Ty} {reason : Word}
    {bodyCertificate : CompatibleMatchCertificates.BodyCertificate} {code : Expr}
    (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason before bodyCertificate code)
    (reached : Reaches source roots (.expression resolution.scrutinee)) :
    CompatibleMatchCertificates.Certificate compilation view scope id resolution type reason after bodyCertificate code := by
  cases receipt with
  | @matchWith node statementType scrutineeNode type scrutinee rows fallback body code read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projected expression sameType rowsCertified fallbackCertified branchesCertified hiddenCompiled =>
    have lookup := (statement_identity edited).lookup id
    exact .matchWith
      (by simpa only [SourceCoreCompatibleDataExpressions.readStatement, edited.metadata.owner, lookup] using read)
      allowed form requirements (by simpa only [edited.metadata.owner] using hiddenOwned) hiddenFresh
      (by simpa only [edited.metadata.owner] using scrutineeOwned)
      ((expression_lookup edited avoids reached).symm.trans found)
      (by simpa only [SourceCoreCompatibleDataMatches.projected, edited.metadata.owner] using projected)
      (expressions _ _ _ reached expression) sameType (arms edited rowsCertified) fallbackCertified
      (branches edited allocator branchesCertified)
      (by simpa only [CompatibleMatchCertificates.hiddenBinder] using
        ((initialized edited allocator _ _ _ _ _ _ _).symm.trans hiddenCompiled))

private theorem match_ordinary
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {before after : CompatibleMatchCertificates.ExpressionCertificate}
    {scope : SourceCoreLocalCell.Scope} {id : StatementId} {resolution : MatchResolution} {type : Ty} {reason : Word}
    {bodyCertificate : CompatibleMatchCertificates.BodyCertificate} {code : Expr}
    {receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason before bodyCertificate code}
    {other : CompatibleMatchCertificates.Certificate compilation view scope id resolution type reason after bodyCertificate code}
    (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt) : CompatibleMatchSelectionPrefix.Ordinary other := by
  refine ⟨by simpa only [edited.metadata.inputs] using ordinary.1, ?_⟩
  intro payload expected rows certificates item member binding bound
  have reversed : LocalView view source changed := ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  simpa only [edited.metadata.inputs] using ordinary.2 payload expected rows (arms reversed certificates) item member binding bound

include avoids in
private theorem index_site {checked : SourceCoreCompatibleCatalog.Checked}
    {root keySource valueSource : TypeSystem.Ty} {key : ExpressionId} {layout : OrderedMapping.Layout}
    (site : CompatibleMixedRoute.IndexSite checked source root keySource valueSource key layout)
    (reached : Reaches source roots (.expression key)) :
    CompatibleMixedRoute.IndexSite checked view root keySource valueSource key layout := by
  obtain ⟨node, found, projected⟩ := site.node
  exact {site with owner := by simpa only [edited.metadata.owner] using site.owner
                   node := ⟨node, (expression_lookup edited avoids reached).symm.trans found, projected⟩}

include avoids in
private theorem prepared_path_with_routes {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List SourceCoreCompatibleDataPlaces.PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : CompatibleMixedRoute.PreparedPath checked source site root projections position steps keys leaf)
    (reached : ∀ key ∈ DataPlaceKeyOrder.sourceKeys projections, Reaches source roots (.expression key)) :
    CompatibleMixedRoute.PreparedPath checked view site root projections position steps keys leaf ∧
      (∀ (signatures : ProgramSignatures) (binder : Resolved.LocalId) (initial : TypeSystem.Ty),
        SourceCoreCompatibleDataPlaces.routeSteps checked signatures view site binder initial projections =
          SourceCoreCompatibleDataPlaces.routeSteps checked signatures source site binder initial projections) ∧
      CallableLambdaViewStaticTyping.Within source roots (projections.flatMap PlaceProjection.references) := by
  induction path with
  | nil =>
    exact ⟨.nil, (fun _ _ _ => rfl), fun _ member => by cases member⟩
  | member nominal selected certificate _ ih =>
    refine ⟨.member nominal selected certificate (ih reached).1, ?_, ?_⟩
    · intro signatures binder initial
      simp only [SourceCoreCompatibleDataPlaces.routeSteps, (ih reached).2.1]
    · simpa only [List.flatMap_cons, PlaceProjection.references, List.nil_append] using (ih reached).2.2
  | @index root keySource valueSource leaf key layout projections steps position keys comparison missing certificate generated tail ih =>
    have child := reached _ (by simp only [DataPlaceKeyOrder.sourceKeys, List.mem_cons]; exact Or.inl rfl)
    have rest : ∀ key ∈ DataPlaceKeyOrder.sourceKeys projections, Reaches source roots (.expression key) :=
      fun key member => reached key (by simp [DataPlaceKeyOrder.sourceKeys, member])
    refine ⟨.index (index_site edited avoids certificate child) generated (ih rest).1, ?_, ?_⟩
    · intro signatures binder initial
      simp only [SourceCoreCompatibleDataPlaces.routeSteps, edited.metadata.owner,
        expression_lookup edited avoids child, (ih rest).2.1]
    · intro id member
      simp only [List.flatMap_cons, PlaceProjection.references, List.singleton_append, List.mem_cons] at member
      rcases member with rfl | member
      · exact child
      · exact (ih rest).2.2 id member

include avoids in
private theorem prepared_path {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List SourceCoreCompatibleDataPlaces.PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : CompatibleMixedRoute.PreparedPath checked source site root projections position steps keys leaf)
    (reached : ∀ key ∈ DataPlaceKeyOrder.sourceKeys projections, Reaches source roots (.expression key)) :
    CompatibleMixedRoute.PreparedPath checked view site root projections position steps keys leaf := by
  exact (prepared_path_with_routes edited avoids path reached).1

include avoids in
private theorem key_views {checked : SourceCoreCompatibleCatalog.Checked} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List SourceCoreCompatibleDataPlaces.PreparedStep} {keys : List (ExpressionId × Ty)}
    {path : CompatibleMixedRoute.PreparedPath checked source site root projections position steps keys leaf}
    {types : List TypeSystem.Ty} (views : CompatiblePlaceKeys.KeyViews path types)
    (reached : ∀ key ∈ DataPlaceKeyOrder.sourceKeys projections, Reaches source roots (.expression key)) :
    CompatiblePlaceKeys.KeyViews (prepared_path edited avoids path reached) types := by
  induction views with
  | nil => exact .nil
  | @member root field leaf name index signature arguments identity branches fieldType projections steps position keys nominal selected certificate tail types rest ih =>
    exact .member (nominal := nominal) (selected := selected) (certificate := certificate) (ih reached)
  | @index root keySource valueSource leaf key layout projections steps position keys comparison missing certificate generated tail type types keyView rest ih =>
    exact .index (certificate := index_site edited avoids certificate (reached key (by simp [DataPlaceKeyOrder.sourceKeys])))
      (generated := generated) keyView
      (ih (fun key member => reached key (by simp [DataPlaceKeyOrder.sourceKeys, member])))

include avoids in
private theorem sequence_tree {before after : GenericExpressionMeaning.Certificate}
    (expressions : ∀ scope id lowered, Reaches source roots (.expression id) → before scope id lowered → after scope id lowered)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source before scope ids types codes)
    (reached : ∀ id ∈ ids, Reaches source roots (.expression id)) :
    DataExpressionSequence.Tree view after scope ids types codes := by
  induction tree with
  | single found generated =>
    exact .single ((expression_lookup edited avoids (reached _ (by simp))).symm.trans found)
      (expressions _ _ _ (reached _ (by simp)) generated)
  | nil => exact .nil
  | cons found generated _ ih =>
    exact .cons ((expression_lookup edited avoids (reached _ (by simp))).symm.trans found)
      (expressions _ _ _ (reached _ (by simp)) generated)
      (ih (fun id member => reached id (List.mem_cons_of_mem _ member)))

include avoids in
private theorem assignment_shape {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
    {before after : GenericExpressionMeaning.Certificate}
    (expressions : ∀ scope id lowered, Reaches source roots (.expression id) → before scope id lowered → after scope id lowered)
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {place : PlaceResolution} {prepared : SourceCoreCompatibleDataPlaces.Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {leaf : TypeSystem.Ty}
    (shape : GenericAssignmentStatements.Shape values source context before scope administrative definitions place prepared codes leaf)
    (reached : ∀ key ∈ DataPlaceKeyOrder.sourceKeys place.projections, Reaches source roots (.expression key)) :
    GenericAssignmentStatements.Shape values view context after scope administrative definitions place prepared codes leaf := by
  cases shape with
  | bare empty layout => exact .bare empty layout
  | @projected codes leaf sourceTypes site layout ordinary =>
    refine .projected (sourceTypes := sourceTypes) (site := site) ?_ ordinary
    exact {layout with path := prepared_path edited avoids layout.path reached
                       views := key_views edited avoids layout.views reached
                       children := sequence_tree edited avoids expressions layout.children reached}

private def assignment_head {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
    {before after : GenericExpressionMeaning.Certificate}
    (expressions : ∀ scope id lowered, Reaches source roots (.expression id) → before scope id lowered → after scope id lowered)
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (head : GenericAssignmentStatements.Head values source context before scope administrative definitions assignment operator rhs)
    (reached : ∀ id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections, Reaches source roots (.expression id)) :
    GenericAssignmentStatements.Head values view context after scope administrative definitions assignment operator rhs :=
  {head with shape := assignment_shape edited avoids expressions head.shape (fun id member => reached id (List.mem_cons_of_mem _ member))
             found := (expression_lookup edited avoids (reached rhs (by simp))).symm.trans head.found
             right := expressions _ _ _ (reached rhs (by simp)) head.right}


include avoids in
private theorem assignment_prepared_at {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
    {before after : GenericExpressionMeaning.Certificate}
    (expressions : ∀ scope id lowered, Reaches source roots (.expression id) → before scope id lowered → after scope id lowered)
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {head : GenericAssignmentStatements.Head values source context before scope administrative definitions assignment operator rhs}
    {site : SourceCoreElaboration.ErrorSite} {fuel : Nat} {invalid : Word} {missing : TypeSystem.Ty → Word}
    (receipt : head.PreparedAt site fuel invalid missing)
    (reached : ∀ id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections, Reaches source roots (.expression id)) :
    (assignment_head edited avoids expressions head reached).PreparedAt site fuel invalid missing := by
  cases receipt with
  | bare empty => exact .bare empty
  | @projected sourceTypes route layout ordinary shape described preparedBy =>
    have keys := fun id member => reached id (List.mem_cons_of_mem _ member)
    let mapped : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values view after
        scope site assignment.target head.prepared head.codes sourceTypes head.leaf administrative :=
      {layout with path := prepared_path edited avoids layout.path keys,
                   views := key_views edited avoids layout.views keys,
                   children := sequence_tree edited avoids expressions layout.children keys}
    refine .projected route mapped ordinary ?_ ?_ preparedBy
    · dsimp only [assignment_head]
    · have routes := (prepared_path_with_routes edited avoids layout.path keys).2.1
      have rootEq : SourceCoreCompatibleDataPlaces.rootBinder view assignment.target.root =
          SourceCoreCompatibleDataPlaces.rootBinder source assignment.target.root :=
        (CallableLambdaBodyReachability.rootBinder edited.metadata _).symm
      simpa only [SourceCoreCompatibleDataPlaces.describe, rootEq, routes] using described

private theorem assignment_occurs {tracked : Bool} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (origin : AssignmentDiagnosticOrigins.OccursFor tracked source site assignment operator rhs) :
    AssignmentDiagnosticOrigins.OccursFor tracked view site assignment operator rhs := by
  cases tracked with
  | false => trivial
  | true => cases origin with
    | statement found form => exact .statement (edited.metadata.symm.statement found) form
    | header found form member => exact .header (edited.metadata.symm.statement found) form member

private theorem unary_occurs {tracked : Bool} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution}
    (origin : EmittedDiagnosticTokenPlan.UnaryOccursFor tracked source site assignment) :
    EmittedDiagnosticTokenPlan.UnaryOccursFor tracked view site assignment := by
  cases tracked with
  | false => trivial
  | true => cases origin with
    | statement found form => exact .statement (edited.metadata.symm.statement found) form
    | header found form member => exact .header (edited.metadata.symm.statement found) form member

omit edited avoids in
private theorem projections_nil_type {context : SourceSemantics.Context} {initial final : TypeSystem.Ty}
    (typing : SourceProjectionsHaveType source context initial [] final) : initial = final := by
  cases typing
  rfl

include avoids in
/-- The packet crosses only the actual reached keys and RHS of this chosen head. -/
theorem assignment_payload {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
    {before after : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (expressions : ∀ context scope id lowered, Reaches source roots (.expression id) → before context scope id lowered → after context scope id lowered)
    (unique : NodeOccurrencesUnique source)
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {head : GenericAssignmentStatements.Head values source context (before context) scope administrative definitions assignment operator rhs}
    {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
    {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
    {targetFactory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy view invalidOperand}
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    (receipt : GenericForHeader.Structural.PreparedAssignment (values := values) (certificates := before) (administrative := administrative) (definitions := definitions) factory invalidProjection missingDefault head)
    (reached : ∀ id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections, Reaches source roots (.expression id)) :
    GenericForHeader.Structural.PreparedAssignment (values := values) (certificates := after) (administrative := administrative) (definitions := definitions) targetFactory invalidProjection missingDefault
      (assignment_head edited avoids (expressions context) head reached) := by
  cases receipt with
  | intro site origin same sourceTyped rightTyped profile fuel prepared =>
    refine .intro site (assignment_occurs edited origin) same ?_
      (CallableLambdaViewStaticTyping.expression edited avoids unique rightTyped (reached rhs (by simp))) profile fuel
      (assignment_prepared_at edited avoids (expressions context) prepared reached)
    intro binder declared
    have original := sourceTyped binder ((CallableLambdaBodyReachability.rootBinder edited.metadata _).trans declared)
    cases prepared with
    | bare empty =>
      rw [empty] at original ⊢
      rw [← projections_nil_type original]
      exact .nil _
    | projected route layout ordinary shape described preparedBy =>
      exact CallableLambdaViewStaticTyping.projections edited avoids unique original
        (prepared_path_with_routes edited avoids layout.path (fun id member => reached id (List.mem_cons_of_mem _ member))).2.2

/-- Unary payloads keep their exact owning occurrence and original token. -/
theorem unary_payload {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {assignment : AssignmentResolution} {head : CompatibleBitNotStatements.Head context scope assignment}
    {tracked : Bool} {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    (receipt : GenericForHeader.Structural.PreparedUnary tracked source invalidUnary head) :
    GenericForHeader.Structural.PreparedUnary tracked view invalidUnary head := by
  cases receipt with
  | intro writable bare profile site origin same =>
    refine .intro ?_ bare profile site (unary_occurs edited origin) same
    intro binder declared
    exact writable binder ((CallableLambdaBodyReachability.rootBinder edited.metadata _).trans declared)

omit edited in
private theorem sourceKeys_references {projections : List PlaceProjection} {id : ExpressionId}
    (member : id ∈ DataPlaceKeyOrder.sourceKeys projections) :
    .expression id ∈ projections.flatMap PlaceProjection.references := by
  induction projections with
  | nil => cases member
  | cons projection rest ih =>
    cases projection with
    | member name index => exact List.mem_append_right _ (ih member)
    | index key =>
      simp only [DataPlaceKeyOrder.sourceKeys, List.mem_cons] at member
      rcases member with rfl | member
      · simp [PlaceProjection.references]
      · exact List.mem_append_right _ (ih member)

section Headers
open CallableLambdaViewStaticTyping (Within)
open TypedLexicalWhile (absentRequest initializedRequest sequence)
variable {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {administrative : Core.Context}
    {before after : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (expressions : ∀ context scope id lowered, Reaches source roots (.expression id) →
      before context scope id lowered → after context scope id lowered)
include avoids expressions

private theorem header_tree {type : Ty} {continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {items : List ForItemForm} {code : Expr}
    (tree : GenericForHeader.Tree layouts owner active frame globals onError values source before definitions administrative type continuation context scope items code)
    (reached : Within source roots (items.flatMap ForItemForm.references)) :
    GenericForHeader.Tree layouts owner active frame globals onError values view after definitions administrative type continuation context scope items code := by
  induction tree with
  | nil next => exact .nil next
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocated annotation same remaining ih =>
    let allocation := CallableLambdaViewAllocations.allocation
      (request := absentRequest source scope binder payload)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := absentRequest source scope binder payload) edited.metadata annotation
    rw [← identical]
    exact .uninitialized mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary) projected allocation annotated
      (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same)
      (ih (fun child member => reached child (by simp [ForItemForm.references, member])))
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary initializerFound sourceType initial allocated annotation same remaining ih =>
    have child : Reaches source roots (.expression initializer) := reached _ (by simp [ForItemForm.references])
    let allocation := CallableLambdaViewAllocations.allocation
      (request := initializedRequest source scope binder lowered.type)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := initializedRequest source scope binder lowered.type) edited.metadata annotation
    rw [← identical]
    exact .initialized mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary)
      ((expression_lookup edited avoids child).symm.trans initializerFound) sourceType
      (expressions context scope initializer lowered child initial) allocation annotated
      (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same)
      (ih (fun child member => reached child (by simp [ForItemForm.references, member])))
  | @discard context scope expression expressionNode rest lowered body found value remaining ih =>
    have child : Reaches source roots (.expression expression) := reached _ (by simp [ForItemForm.references])
    exact .discard ((expression_lookup edited avoids child).symm.trans found)
      (expressions context scope expression lowered child value)
      (ih (fun child member => reached child (by simp [ForItemForm.references, member])))
  | @assign context scope assignment operator rhs rest body head remaining ih =>
    have children : ∀ id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections,
        Reaches source roots (.expression id) := by
      intro id member
      rcases List.mem_cons.mp member with rfl | member
      · exact reached _ (by simp [ForItemForm.references])
      · exact reached _ (by simp only [List.flatMap_cons, ForItemForm.references, AssignmentResolution.references,
          PlaceResolution.references, List.mem_append]; exact Or.inl (Or.inl (sourceKeys_references member)))
    exact .assign (assignment_head edited avoids (expressions context) head children)
      (ih (fun child member => reached child (List.mem_append_right _ member)))
  | bitNot head remaining ih =>
    exact .bitNot head
      (ih (fun child member => reached child (List.mem_append_right _ member)))
/-- The original header mapping carries a constructor payload on the same target tree. -/
theorem header_payload_with {type : Ty} {continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {items : List ForItemForm} {code : Expr}

    (AP : GenericForHeader.Structural.AssignmentPayload values source before administrative definitions)
    (UP : GenericForHeader.Structural.UnaryPayload)
    (mappedAP : GenericForHeader.Structural.AssignmentPayload values view after administrative definitions)
    (mappedUP : GenericForHeader.Structural.UnaryPayload)
    (P : CallableLambdaViewPreparedStaticTransport.Header.PacketMotive
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := view) (certificates := after)
      (definitions := definitions) (administrative := administrative) (type := type) (continuation := continuation))
    (target : CallableLambdaViewPreparedStaticTransport.Header.PacketAlgebra
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (type := type) (continuation := continuation) mappedAP mappedUP P)
    (assignments : ∀ {context scope assignment operator rhs}
      (head : GenericAssignmentStatements.Head values source context (before context) scope administrative definitions assignment operator rhs)
      (children : ∀ id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections, Reaches source roots (.expression id)),
      AP head → mappedAP (assignment_head edited avoids (expressions context) head children))
    (unaries : ∀ {context scope assignment} (head : CompatibleBitNotStatements.Head context scope assignment), UP head → mappedUP head)
    (sites : GenericForHeader.Structural.Eliminates
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (type := type) (continuation := continuation) AP UP context scope items code)
    (reached : Within source roots (items.flatMap ForItemForm.references)) :
    ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values view after definitions administrative type continuation context scope items code,
      P tree := by
  classical
  apply sites (fun context scope items code => Within source roots (items.flatMap ForItemForm.references) →
    ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values view after definitions administrative type continuation context scope items code, P tree) ?_ reached
  refine { nil := ?_, uninitialized := ?_, initialized := ?_, discard := ?_, assign := ?_, bitNot := ?_ }
  · intro context scope code next
    intro reached
    refine ⟨.nil next, ?_⟩
    exact target.nil
      (next := next)

  · intro context nextContext scope binder rest body payload mono extended ordinary projected allocated annotation same ih
    intro reached
    let allocation := CallableLambdaViewAllocations.allocation
      (request := absentRequest source scope binder payload)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := absentRequest source scope binder payload) edited.metadata annotation
    rw [← identical]
    refine ⟨.uninitialized mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary) projected allocation annotated
      (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same)
      (ih (fun child member => reached child (by simp [ForItemForm.references, member]))).choose, ?_⟩
    exact target.uninitialized
      (monomorphic := mono)
      (extended := (by simpa only [edited.metadata.owner] using extended))
      (ordinary := (by simpa only [edited.metadata.inputs] using ordinary))
      (projected := projected)
      (allocation := allocation)
      (annotation := annotated)
      (same := (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same))
      (remaining := (ih (fun child member => reached child (by simp [ForItemForm.references, member]))).choose)
      ((ih (fun child member => reached child (by simp [ForItemForm.references, member]))).choose_spec)
  · intro context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary initializerFound sourceType initial allocated annotation same ih
    intro reached
    have child : Reaches source roots (.expression initializer) := reached _ (by simp [ForItemForm.references])
    let allocation := CallableLambdaViewAllocations.allocation
      (request := initializedRequest source scope binder lowered.type)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := initializedRequest source scope binder lowered.type) edited.metadata annotation
    rw [← identical]
    refine ⟨.initialized mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary)
      ((expression_lookup edited avoids child).symm.trans initializerFound) sourceType
      (expressions context scope initializer lowered child initial) allocation annotated
      (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same)
      (ih (fun child member => reached child (by simp [ForItemForm.references, member]))).choose, ?_⟩
    exact target.initialized
      (monomorphic := mono)
      (extended := (by simpa only [edited.metadata.owner] using extended))
      (ordinary := (by simpa only [edited.metadata.inputs] using ordinary))
      (initializerFound := ((expression_lookup edited avoids child).symm.trans initializerFound))
      (sourceType := sourceType)
      (initial := (expressions context scope initializer lowered child initial))
      (allocation := allocation)
      (annotation := annotated)
      (same := (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same))
      (remaining := (ih (fun child member => reached child (by simp [ForItemForm.references, member]))).choose)
      ((ih (fun child member => reached child (by simp [ForItemForm.references, member]))).choose_spec)
  · intro context scope expression expressionNode rest lowered body found value ih
    intro reached
    have child : Reaches source roots (.expression expression) := reached _ (by simp [ForItemForm.references])
    refine ⟨.discard ((expression_lookup edited avoids child).symm.trans found)
      (expressions context scope expression lowered child value)
      (ih (fun child member => reached child (by simp [ForItemForm.references, member]))).choose, ?_⟩
    exact target.discard
      (found := ((expression_lookup edited avoids child).symm.trans found))
      (value := (expressions context scope expression lowered child value))
      (remaining := (ih (fun child member => reached child (by simp [ForItemForm.references, member]))).choose)
      ((ih (fun child member => reached child (by simp [ForItemForm.references, member]))).choose_spec)
  · intro context scope assignment operator rhs rest body head headErrors ih
    intro reached
    have children : ∀ id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections,
        Reaches source roots (.expression id) := by
      intro id member
      rcases List.mem_cons.mp member with rfl | member
      · exact reached _ (by simp [ForItemForm.references])
      · exact reached _ (by simp only [List.flatMap_cons, ForItemForm.references, AssignmentResolution.references,
          PlaceResolution.references, List.mem_append]; exact Or.inl (Or.inl (sourceKeys_references member)))
    refine ⟨.assign (assignment_head edited avoids (expressions context) head children)
      (ih (fun child member => reached child (List.mem_append_right _ member))).choose, ?_⟩
    exact target.assign
      (head := (assignment_head edited avoids (expressions context) head children))
      (remaining := (ih (fun child member => reached child (List.mem_append_right _ member))).choose)
      ((ih (fun child member => reached child (List.mem_append_right _ member))).choose_spec) (assignments head children headErrors)
  · intro context scope assignment rest body head headErrors ih
    intro reached
    refine ⟨.bitNot head
      (ih (fun child member => reached child (List.mem_append_right _ member))).choose, ?_⟩
    exact target.bitNot
      (head := head)
      (remaining := (ih (fun child member => reached child (List.mem_append_right _ member))).choose)
      ((ih (fun child member => reached child (List.mem_append_right _ member))).choose_spec) (unaries head headErrors)

private theorem header_sites {diagnosticPolicy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {type : Ty} {continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {items : List ForItemForm} {code : Expr}
    {tree : GenericForHeader.Tree layouts owner active frame globals onError values source before definitions administrative type continuation context scope items code}
    (sites : tree.ErrorsFor diagnosticPolicy registry faults)
    (reached : Within source roots (items.flatMap ForItemForm.references)) :
    ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values view after definitions administrative type continuation context scope items code,
      tree.ErrorsFor diagnosticPolicy registry faults := by
  exact header_payload_with edited avoids expressions
    (fun head => head.ErrorsFor diagnosticPolicy registry faults) (fun head => head.Errors faults)
    (fun head => head.ErrorsFor diagnosticPolicy registry faults) (fun head => head.Errors faults)
    (fun tree => tree.ErrorsFor diagnosticPolicy registry faults)
    CallableLambdaViewPreparedStaticTransport.Header.legacy_algebra
    (fun head children receipt => by cases diagnosticPolicy <;> exact ⟨receipt.missing, receipt.uninitialized, receipt.operands⟩)
    (fun _ receipt => receipt)
    (CallableLambdaViewPreparedStaticTransport.Header.of_errors sites) reached

end Headers

section Statements
open GenericImperativeMatch
open CallableLambdaViewStaticTyping (Within)

private def positionNodes : Position → List NodeId
  | .statements _ statements => statements.map NodeId.statement
  | .initializers items condition post statements =>
      items.flatMap ForItemForm.references ++ [.expression condition] ++
        post.flatMap ForItemForm.references ++ statements.map NodeId.statement

private def PositionReached (source : TypedSource) (roots : List NodeId) : Position → Prop
  | .statements _ statements => ∀ id ∈ statements, Reaches source roots (.statement id)
  | .initializers items condition post statements => Within source roots
      (items.flatMap ForItemForm.references ++ [.expression condition] ++
        post.flatMap ForItemForm.references ++ statements.map NodeId.statement)

private theorem scoped_context {parent child : SourceSemantics.Context} {hiddenIds : List Resolved.LocalId}
    {type : TypeSystem.Ty} {cases : List TypedMatchCase} {fallback : Option (List StatementId)}
    {request : GenericMatchChildren.Request}
    (related : GenericMatchChildren.ScopedContextFor view parent hiddenIds type cases fallback request child) :
    GenericMatchChildren.ScopedContextFor source parent hiddenIds type cases fallback request child := by
  cases related with
  | arm member statements typed extended ids =>
    exact .arm member statements typed (by simpa only [edited.metadata.owner] using extended) ids
  | default statements ids => exact .default statements ids

variable {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {administrative : Core.Context}
    {beforeSyntax afterSyntax : ExpressionId → Prop}
    {before after : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique source)
    (syntaxTransport : ∀ id, Reaches source roots (.expression id) → beforeSyntax id → afterSyntax id)
    (expressions : ∀ context scope id lowered, Reaches source roots (.expression id) →
      before context scope id lowered → after context scope id lowered)
include avoids unique syntaxTransport expressions

/-- Transport the actual finite match/for/lexical Tree, with its original
emitted code. The only child interface transports the same reached static
expression certificate. Dead suffixes retain their original compiler issuer. -/
theorem transport_with {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
      beforeSyntax before definitions administrative context scope position expected type code)
    (reached : PositionReached source roots position) :
    GenericImperativeMatch.Tree layouts owner active frame globals onError values view
      afterSyntax after definitions administrative context scope position expected type code := by
  induction tree with
  | body syntaxTree body =>
    exact .body (CallableLambdaViewSourceTyping.lexical_syntax_with edited avoids unique syntaxTransport syntaxTree reached)
      (CallableLambdaViewBodyTree.transport edited avoids expressions body reached)
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocated annotation same remaining ih =>
    let allocation := CallableLambdaViewAllocations.allocation
      (request := absentRequest source scope binder payload)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := absentRequest source scope binder payload) edited.metadata annotation
    rw [← identical]
    exact .uninitialized (edited.metadata.symm.statement found) form mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary) projected allocation annotated
      (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same) (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initializerFound sourceType initial allocated annotation same remaining ih =>
    have child : Reaches source roots (.expression initializer) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    let allocation := CallableLambdaViewAllocations.allocation
      (request := initializedRequest source scope binder lowered.type)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := initializedRequest source scope binder lowered.type) edited.metadata annotation
    rw [← identical]
    exact .initialized (edited.metadata.symm.statement found) form mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary)
      ((expression_lookup edited avoids child).symm.trans initializerFound) sourceType
      (expressions context scope initializer lowered child initial) allocation annotated (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same)
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining ih =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .discard (edited.metadata.symm.statement found) form notTail
      ((expression_lookup edited avoids child).symm.trans expressionFound)
      (expressions context scope expression lowered child value)
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH restIH =>
    exact .block (edited.metadata.symm.statement found) form
      (innerIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH restIH =>
    have child : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .ifThen (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType
      (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree)
      (thenIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (elseIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member)))

  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix exactUnique found form inner stops issued innerIH =>
    exact .terminalBlock (edited.metadata.unique exactUnique) (edited.metadata.symm.statement found) form
      (innerIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (stops.transport (statement_identity edited)) (issued.transport (statement_identity edited))
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    have child : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .terminalIf (edited.metadata.unique exactUnique) (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType
      (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree)
      (thenIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (elseIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (thenStops.transport (statement_identity edited)) (elseStops.transport (statement_identity edited))
      (issued.transport (statement_identity edited))

  | breaking found form => exact .breaking (edited.metadata.symm.statement found) form
  | continuing found form => exact .continuing (edited.metadata.symm.statement found) form
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopIH restIH =>
    have child : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .whileLoop (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType
      (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree)
      (loopIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))) nativeTyped
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining ih =>
    have children : ∀ child ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections,
        Reaches source roots (.expression child) := by
      intro child member
      apply Reaches.statement (reached id (by simp)) found
      rcases List.mem_cons.mp member with rfl | member
      · simp [form, StatementForm.references]
      · simpa only [form, StatementForm.references, AssignmentResolution.references, PlaceResolution.references,
          List.mem_append, List.mem_singleton] using (Or.inl (sourceKeys_references member) :
          .expression child ∈ assignment.target.projections.flatMap PlaceProjection.references ∨ NodeId.expression child = NodeId.expression rhs)
    exact .assign (edited.metadata.symm.statement found) form
      (assignment_head edited avoids (expressions context) head children)
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | bitNot found form head remaining ih =>
    exact .bitNot (edited.metadata.symm.statement found) form head
      (ih (fun child member => reached child (List.mem_cons_of_mem _ member)))
  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialIH restIH =>
    exact .forLoop (edited.metadata.symm.statement found) form
      (initialIH (fun child member => .statement (reached id (by simp)) found
        (by simpa only [form, StatementForm.references] using member)))
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopIH =>
    have child : Reaches source roots (.expression condition) := reached _ (by simp)
    exact .initializersDone ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType
      (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree)
      (loopIH (fun child member => reached _ (by simp [member])))
      (header_tree edited avoids expressions postTree (fun child member => reached child (by simp [member]))) nativeTyped
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocated annotation same remaining ih =>
    let allocation := CallableLambdaViewAllocations.allocation
      (request := absentRequest source scope binder payload)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := absentRequest source scope binder payload) edited.metadata annotation
    rw [← identical]
    exact .initializerUninitialized mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary) projected allocation annotated
      (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same)
      (ih (fun child member => reached child (by simpa only [List.flatMap_cons, ForItemForm.references, Option.map_none, Option.toList_none, List.nil_append] using member)))
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary initializerFound sourceType initial allocated annotation same remaining ih =>
    have child : Reaches source roots (.expression initializer) := reached _ (by simp [ForItemForm.references])
    let allocation := CallableLambdaViewAllocations.allocation
      (request := initializedRequest source scope binder lowered.type)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := initializedRequest source scope binder lowered.type) edited.metadata annotation
    rw [← identical]
    exact .initializerInitialized mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary)
      ((expression_lookup edited avoids child).symm.trans initializerFound) sourceType
      (expressions context scope initializer lowered child initial) allocation annotated
      (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same)
      (ih (fun child member => reached child (by simpa only [List.flatMap_cons, ForItemForm.references,
        Option.map_some, Option.toList_some, List.singleton_append, List.cons_append, List.nil_append, List.mem_cons] using Or.inr member)))
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found value remaining ih =>
    have child : Reaches source roots (.expression expression) := reached _ (by simp [ForItemForm.references])
    exact .initializerDiscard ((expression_lookup edited avoids child).symm.trans found)
      (expressions context scope expression lowered child value)
      (ih (fun child member => reached child (by simpa only [List.flatMap_cons, ForItemForm.references,
        List.singleton_append, List.cons_append, List.nil_append, List.mem_cons] using Or.inr member)))
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining ih =>
    have children : ∀ id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections,
        Reaches source roots (.expression id) := by
      intro id member
      rcases List.mem_cons.mp member with rfl | member
      · exact reached _ (by simp [ForItemForm.references])
      · apply reached
        simp only [List.flatMap_cons, ForItemForm.references, AssignmentResolution.references,
          PlaceResolution.references, List.mem_append]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (sourceKeys_references member)))))
    exact .initializerAssign (assignment_head edited avoids (expressions context) head children)
      (ih (fun child member => reached child (by
        simpa only [List.flatMap_cons, List.append_assoc] using List.mem_append_right _ member)))
  | initializerBitNot head remaining ih =>
    exact .initializerBitNot head (ih (fun child member => reached child (by
      simpa only [List.flatMap_cons, List.append_assoc] using List.mem_append_right _ member)))

  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining childrenIH restIH =>
    have refs : Within source roots resolution.references :=
      fun child member => .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using member)
    have scrutineeReached : Reaches source roots (.expression resolution.scrutinee) := refs _ (by simp [MatchResolution.references])
    have casesReached : Within source roots (resolution.cases.flatMap TypedMatchCase.references) :=
      fun child member => refs child (by simp [MatchResolution.references, member])
    have fallbackReached : Within source roots ((resolution.defaultBody.getD []).map NodeId.statement) :=
      fun child member => refs child (by simp [MatchResolution.references, member])
    have typedDefault : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType view control context statements finalContext facts := by
      intro statements same
      obtain ⟨finalContext, facts, typed⟩ := defaultTyped statements same
      exact ⟨_, _, CallableLambdaViewStaticTyping.statements edited avoids unique typed
        (by simpa only [same, Option.getD_some] using fallbackReached)⟩
    have transformed := match_certificate edited avoids allocator (expressions context) receipt scrutineeReached
    apply GenericImperativeMatch.Tree.matchWith (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids scrutineeReached).symm.trans scrutineeFound)
      (CallableLambdaViewStaticTyping.expression edited avoids unique scrutineeTyped scrutineeReached)
      (CallableLambdaViewStaticTyping.matchCases edited avoids unique casesTyped casesReached)
      typedDefault compilation sameValues sameDefinitions allocator requests transformed (match_ordinary edited ordinary)
    · intro request member childContext related
      have original := scoped_context edited related
      apply childrenIH request member childContext original
      intro statement present
      cases original with
      | arm armMember sameBody _ _ _ =>
        apply casesReached
        exact List.mem_flatMap.mpr ⟨_, armMember, List.mem_map.mpr ⟨statement, sameBody ▸ present, rfl⟩⟩
      | default sameBody _ =>
        apply fallbackReached
        simpa only [sameBody, Option.getD_some, List.mem_map, NodeId.statement.injEq] using
          (List.mem_map.mpr ⟨statement, present, rfl⟩ : .statement statement ∈ request.statements.map NodeId.statement)
    · exact restIH (fun child member => reached child (List.mem_cons_of_mem id member))

  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued childrenIH =>
    have refs : Within source roots resolution.references :=
      fun child member => .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using member)
    have scrutineeReached : Reaches source roots (.expression resolution.scrutinee) := refs _ (by simp [MatchResolution.references])
    have casesReached : Within source roots (resolution.cases.flatMap TypedMatchCase.references) :=
      fun child member => refs child (by simp [MatchResolution.references, member])
    have fallbackReached : Within source roots ((resolution.defaultBody.getD []).map NodeId.statement) :=
      fun child member => refs child (by simp [MatchResolution.references, member])
    have typedDefault : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType view control context statements finalContext facts := by
      intro statements same
      obtain ⟨finalContext, facts, typed⟩ := defaultTyped statements same
      exact ⟨_, _, CallableLambdaViewStaticTyping.statements edited avoids unique typed
        (by simpa only [same, Option.getD_some] using fallbackReached)⟩
    have transformed := match_certificate edited avoids allocator (expressions context) receipt scrutineeReached
    apply GenericImperativeMatch.Tree.terminalMatch (edited.metadata.unique exactUnique) (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids scrutineeReached).symm.trans scrutineeFound)
      (CallableLambdaViewStaticTyping.expression edited avoids unique scrutineeTyped scrutineeReached)
      (CallableLambdaViewStaticTyping.matchCases edited avoids unique casesTyped casesReached)
      typedDefault compilation sameValues sameDefinitions allocator requests transformed (match_ordinary edited ordinary)
    · intro request member childContext related
      have original := scoped_context edited related
      apply childrenIH request member childContext original
      intro statement present
      cases original with
      | arm armMember sameBody _ _ _ =>
        apply casesReached
        exact List.mem_flatMap.mpr ⟨_, armMember, List.mem_map.mpr ⟨statement, sameBody ▸ present, rfl⟩⟩
      | default sameBody _ =>
        apply fallbackReached
        simpa only [sameBody, Option.getD_some, List.mem_map, NodeId.statement.injEq] using
          (List.mem_map.mpr ⟨statement, present, rfl⟩ : .statement statement ∈ request.statements.map NodeId.statement)
    · exact stops.transport (statement_identity edited)
    · exact issued.transport (statement_identity edited)

/-- The original static position mapping carries a payload on its exact target tree. -/
theorem transport_payload_with {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

    (AP : Structural.AssignmentPayload (values := values) (source := source) (certificates := before) (administrative := administrative) (definitions := definitions))
    (UP : Structural.UnaryPayload)
    (HP : Structural.HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (certificates := before) (definitions := definitions) (administrative := administrative))
    (MP : Structural.MatchPayload)
    (mappedAP : Structural.AssignmentPayload (values := values) (source := view) (certificates := after) (administrative := administrative) (definitions := definitions))
    (mappedUP : Structural.UnaryPayload)
    (mappedHP : Structural.HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := view) (certificates := after) (definitions := definitions) (administrative := administrative))
    (mappedMP : Structural.MatchPayload)
    (P : CallableLambdaViewPreparedStaticTransport.Match.PacketMotive
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := view) (expressionSyntax := afterSyntax)
      (certificates := after) (definitions := definitions) (administrative := administrative))
    (target : CallableLambdaViewPreparedStaticTransport.Match.PacketAlgebra
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := view) (expressionSyntax := afterSyntax)
      (certificates := after) (definitions := definitions) (administrative := administrative) mappedAP mappedUP mappedHP mappedMP P)
    (assignments : ∀ {context scope assignment operator rhs}
      (head : GenericAssignmentStatements.Head values source context (before context) scope administrative definitions assignment operator rhs)
      (children : ∀ id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections, Reaches source roots (.expression id)),
      AP head → mappedAP (assignment_head edited avoids (expressions context) head children))
    (unaries : ∀ {context scope assignment} (head : CompatibleBitNotStatements.Head context scope assignment), UP head → mappedUP head)
    (headers : ∀ {context scope items type code}
      (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source before definitions administrative
        type (TypedForHeader.Fallthrough type) context scope items code),
      HP postTree → Within source roots (items.flatMap ForItemForm.references) →
      ∃ postTree : GenericForHeader.Tree layouts owner active frame globals onError values view after definitions administrative
        type (TypedForHeader.Fallthrough type) context scope items code, mappedHP postTree)
    (matchPayloads : ∀ compilation context, MP compilation context → mappedMP compilation context)
    (sites : Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressionSyntax := beforeSyntax)
      (certificates := before) (definitions := definitions) (administrative := administrative) AP UP HP MP context scope position expected type code)
    (reached : PositionReached source roots position) :
    ∃ tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values view
      afterSyntax after definitions administrative context scope position expected type code, P tree := by
  classical
  apply sites (fun context scope position expected type code => PositionReached source roots position →
    ∃ tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values view
      afterSyntax after definitions administrative context scope position expected type code, P tree) ?_ reached
  refine { body := ?_, uninitialized := ?_, initialized := ?_, discard := ?_, block := ?_, ifThen := ?_, terminalBlock := ?_, terminalIf := ?_, breaking := ?_, continuing := ?_, whileLoop := ?_, assign := ?_, bitNot := ?_, forLoop := ?_, initializersDone := ?_, initializerUninitialized := ?_, initializerInitialized := ?_, initializerDiscard := ?_, initializerAssign := ?_, initializerBitNot := ?_, matchWith := ?_, terminalMatch := ?_ }
  · intro context scope mode statements expected type code syntaxTree body
    intro reached
    refine ⟨.body (CallableLambdaViewSourceTyping.lexical_syntax_with edited avoids unique syntaxTransport syntaxTree reached)
      (CallableLambdaViewBodyTree.transport edited avoids expressions body reached), ?_⟩
    exact target.body
      (syntaxTree := (CallableLambdaViewSourceTyping.lexical_syntax_with edited avoids unique syntaxTransport syntaxTree reached))
      (body := (CallableLambdaViewBodyTree.transport edited avoids expressions body reached))
  · intro context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocated annotation same remaining ih
    intro reached
    let allocation := CallableLambdaViewAllocations.allocation
      (request := absentRequest source scope binder payload)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := absentRequest source scope binder payload) edited.metadata annotation
    rw [← identical]
    refine ⟨.uninitialized (edited.metadata.symm.statement found) form mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary) projected allocation annotated
      (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same) (ih (fun child member => reached child (List.mem_cons_of_mem id member))).choose, ?_⟩
    exact target.uninitialized
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (monomorphic := mono)
      (extended := (by simpa only [edited.metadata.owner] using extended))
      (ordinary := (by simpa only [edited.metadata.inputs] using ordinary))
      (projected := projected)
      (allocation := allocation)
      (annotation := annotated)
      (same := (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same))
      (remaining := (ih (fun child member => reached child (List.mem_cons_of_mem id member))).choose)
      ((ih (fun child member => reached child (List.mem_cons_of_mem id member))).choose_spec)
  · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initializerFound sourceType initial allocated annotation same remaining ih
    intro reached
    have child : Reaches source roots (.expression initializer) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    let allocation := CallableLambdaViewAllocations.allocation
      (request := initializedRequest source scope binder lowered.type)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := initializedRequest source scope binder lowered.type) edited.metadata annotation
    rw [← identical]
    refine ⟨.initialized (edited.metadata.symm.statement found) form mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary)
      ((expression_lookup edited avoids child).symm.trans initializerFound) sourceType
      (expressions context scope initializer lowered child initial) allocation annotated (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same)
      (ih (fun child member => reached child (List.mem_cons_of_mem id member))).choose, ?_⟩
    exact target.initialized
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (monomorphic := mono)
      (extended := (by simpa only [edited.metadata.owner] using extended))
      (ordinary := (by simpa only [edited.metadata.inputs] using ordinary))
      (initializerFound := ((expression_lookup edited avoids child).symm.trans initializerFound))
      (sourceType := sourceType)
      (initial := (expressions context scope initializer lowered child initial))
      (allocation := allocation)
      (annotation := annotated)
      (same := (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same))
      (remaining := (ih (fun child member => reached child (List.mem_cons_of_mem id member))).choose)
      ((ih (fun child member => reached child (List.mem_cons_of_mem id member))).choose_spec)
  · intro context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining ih
    intro reached
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    refine ⟨.discard (edited.metadata.symm.statement found) form notTail
      ((expression_lookup edited avoids child).symm.trans expressionFound)
      (expressions context scope expression lowered child value)
      (ih (fun child member => reached child (List.mem_cons_of_mem id member))).choose, ?_⟩
    exact target.discard
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (notTail := notTail)
      (expressionFound := ((expression_lookup edited avoids child).symm.trans expressionFound))
      (value := (expressions context scope expression lowered child value))
      (remaining := (ih (fun child member => reached child (List.mem_cons_of_mem id member))).choose)
      ((ih (fun child member => reached child (List.mem_cons_of_mem id member))).choose_spec)
  · intro context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH restIH
    intro reached
    refine ⟨.block (edited.metadata.symm.statement found) form
      (innerIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose, ?_⟩
    exact target.block
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (inner := (innerIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose)
      (remaining := (restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose)
      ((innerIH (fun child member => .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member]))).choose_spec) ((restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose_spec)
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH restIH
    intro reached
    have child : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    refine ⟨.ifThen (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType
      (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree)
      (thenIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose
      (elseIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose, ?_⟩
    exact target.ifThen
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (conditionFound := ((expression_lookup edited avoids child).symm.trans conditionFound))
      (conditionType := conditionType)
      (conditionTree := (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree))
      (thenTree := (thenIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose)
      (elseTree := (elseIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose)
      (remaining := (restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose)
      ((thenIH (fun child member => .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member]))).choose_spec) ((elseIH (fun child member => .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member]))).choose_spec) ((restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose_spec)
  · intro context scope mode id node rest expected type found form
    intro reached
    refine ⟨.breaking (edited.metadata.symm.statement found) form, ?_⟩
    exact target.breaking
      (found := (edited.metadata.symm.statement found))
      (form := form)
  · intro context scope mode id node rest expected type found form
    intro reached
    refine ⟨.continuing (edited.metadata.symm.statement found) form, ?_⟩
    exact target.continuing
      (found := (edited.metadata.symm.statement found))
      (form := form)
  · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopIH restIH
    intro reached
    have child : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    refine ⟨.whileLoop (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType
      (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree)
      (loopIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose nativeTyped
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose, ?_⟩
    exact target.whileLoop
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (conditionFound := ((expression_lookup edited avoids child).symm.trans conditionFound))
      (conditionType := conditionType)
      (conditionTree := (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree))
      (loopBody := (loopIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose)
      (nativeTyped := nativeTyped)
      (remaining := (restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose)
      ((loopIH (fun child member => .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member]))).choose_spec) ((restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose_spec)
  · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining ih headErrors
    intro reached
    have children : ∀ child ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections,
        Reaches source roots (.expression child) := by
      intro child member
      apply Reaches.statement (reached id (by simp)) found
      rcases List.mem_cons.mp member with rfl | member
      · simp [form, StatementForm.references]
      · simpa only [form, StatementForm.references, AssignmentResolution.references, PlaceResolution.references,
          List.mem_append, List.mem_singleton] using (Or.inl (sourceKeys_references member) :
          .expression child ∈ assignment.target.projections.flatMap PlaceProjection.references ∨ NodeId.expression child = NodeId.expression rhs)
    refine ⟨.assign (edited.metadata.symm.statement found) form
      (assignment_head edited avoids (expressions context) head children)
      (ih (fun child member => reached child (List.mem_cons_of_mem id member))).choose, ?_⟩
    exact target.assign
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (head := (assignment_head edited avoids (expressions context) head children))
      (remaining := (ih (fun child member => reached child (List.mem_cons_of_mem id member))).choose)
      ((ih (fun child member => reached child (List.mem_cons_of_mem id member))).choose_spec) (assignments head children headErrors)
  · intro context scope mode id node assignment rest expected type body found form head remaining ih headErrors
    intro reached
    refine ⟨.bitNot (edited.metadata.symm.statement found) form head
      (ih (fun child member => reached child (List.mem_cons_of_mem _ member))).choose, ?_⟩
    exact target.bitNot
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (head := head)
      (remaining := (ih (fun child member => reached child (List.mem_cons_of_mem _ member))).choose)
      ((ih (fun child member => reached child (List.mem_cons_of_mem _ member))).choose_spec) (unaries head headErrors)
  · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialIH restIH
    intro reached
    refine ⟨.forLoop (edited.metadata.symm.statement found) form
      (initialIH (fun child member => .statement (reached id (by simp)) found
        (by simpa only [form, StatementForm.references] using member))).choose
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose, ?_⟩
    exact target.forLoop
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (initial := (initialIH (fun child member => .statement (reached id (by simp)) found
        (by simpa only [form, StatementForm.references] using member))).choose)
      (remaining := (restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose)
      ((initialIH (fun child member => .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using member))).choose_spec) ((restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose_spec)
  · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopIH postErrors
    intro reached
    have child : Reaches source roots (.expression condition) := reached _ (by simp)
    refine ⟨.initializersDone ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType
      (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree)
      (loopIH (fun child member => reached _ (by simp [member]))).choose
      (headers postTree postErrors (fun child member => reached child (by simp [member]))).choose nativeTyped, ?_⟩
    exact target.initializersDone
      (conditionFound := ((expression_lookup edited avoids child).symm.trans conditionFound))
      (conditionType := conditionType)
      (conditionTree := (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree))
      (loopBody := (loopIH (fun child member => reached _ (by simp [member]))).choose)
      (postTree := (headers postTree postErrors (fun child member => reached child (by simp [member]))).choose)
      (nativeTyped := nativeTyped)
      ((loopIH (fun child member => reached _ (by simp [member]))).choose_spec) ((headers postTree postErrors (fun child member => reached child (by simp [member]))).choose_spec)
  · intro context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocated annotation same remaining ih
    intro reached
    let allocation := CallableLambdaViewAllocations.allocation
      (request := absentRequest source scope binder payload)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := absentRequest source scope binder payload) edited.metadata annotation
    rw [← identical]
    refine ⟨.initializerUninitialized mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary) projected allocation annotated
      (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same)
      (ih (fun child member => reached child (by simpa only [List.flatMap_cons, ForItemForm.references, Option.map_none, Option.toList_none, List.nil_append] using member))).choose, ?_⟩
    exact target.initializerUninitialized
      (monomorphic := mono)
      (extended := (by simpa only [edited.metadata.owner] using extended))
      (ordinary := (by simpa only [edited.metadata.inputs] using ordinary))
      (projected := projected)
      (allocation := allocation)
      (annotation := annotated)
      (same := (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same))
      (remaining := (ih (fun child member => reached child (by simpa only [List.flatMap_cons, ForItemForm.references, Option.map_none, Option.toList_none, List.nil_append] using member))).choose)
      ((ih (fun child member => reached child (by simpa only [List.flatMap_cons, ForItemForm.references, Option.map_none, Option.toList_none, List.nil_append] using member))).choose_spec)
  · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary initializerFound sourceType initial allocated annotation same remaining ih
    intro reached
    have child : Reaches source roots (.expression initializer) := reached _ (by simp [ForItemForm.references])
    let allocation := CallableLambdaViewAllocations.allocation
      (request := initializedRequest source scope binder lowered.type)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := initializedRequest source scope binder lowered.type) edited.metadata annotation
    rw [← identical]
    refine ⟨.initializerInitialized mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary)
      ((expression_lookup edited avoids child).symm.trans initializerFound) sourceType
      (expressions context scope initializer lowered child initial) allocation annotated
      (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same)
      (ih (fun child member => reached child (by simpa only [List.flatMap_cons, ForItemForm.references,
        Option.map_some, Option.toList_some, List.singleton_append, List.cons_append, List.nil_append, List.mem_cons] using Or.inr member))).choose, ?_⟩
    exact target.initializerInitialized
      (monomorphic := mono)
      (extended := (by simpa only [edited.metadata.owner] using extended))
      (ordinary := (by simpa only [edited.metadata.inputs] using ordinary))
      (initializerFound := ((expression_lookup edited avoids child).symm.trans initializerFound))
      (sourceType := sourceType)
      (initial := (expressions context scope initializer lowered child initial))
      (allocation := allocation)
      (annotation := annotated)
      (same := (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same))
      (remaining := (ih (fun child member => reached child (by simpa only [List.flatMap_cons, ForItemForm.references,
        Option.map_some, Option.toList_some, List.singleton_append, List.cons_append, List.nil_append, List.mem_cons] using Or.inr member))).choose)
      ((ih (fun child member => reached child (by simpa only [List.flatMap_cons, ForItemForm.references, Option.map_some, Option.toList_some, List.singleton_append, List.cons_append, List.nil_append, List.mem_cons] using Or.inr member))).choose_spec)
  · intro context scope expression expressionNode rest lowered body condition post statements expected type found value remaining ih
    intro reached
    have child : Reaches source roots (.expression expression) := reached _ (by simp [ForItemForm.references])
    refine ⟨.initializerDiscard ((expression_lookup edited avoids child).symm.trans found)
      (expressions context scope expression lowered child value)
      (ih (fun child member => reached child (by simpa only [List.flatMap_cons, ForItemForm.references,
        List.singleton_append, List.cons_append, List.nil_append, List.mem_cons] using Or.inr member))).choose, ?_⟩
    exact target.initializerDiscard
      (found := ((expression_lookup edited avoids child).symm.trans found))
      (value := (expressions context scope expression lowered child value))
      (remaining := (ih (fun child member => reached child (by simpa only [List.flatMap_cons, ForItemForm.references,
        List.singleton_append, List.cons_append, List.nil_append, List.mem_cons] using Or.inr member))).choose)
      ((ih (fun child member => reached child (by simpa only [List.flatMap_cons, ForItemForm.references, List.singleton_append, List.cons_append, List.nil_append, List.mem_cons] using Or.inr member))).choose_spec)
  · intro context scope assignment operator rhs rest body condition post statements expected type head remaining ih headErrors
    intro reached
    have children : ∀ id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections,
        Reaches source roots (.expression id) := by
      intro id member
      rcases List.mem_cons.mp member with rfl | member
      · exact reached _ (by simp [ForItemForm.references])
      · apply reached
        simp only [List.flatMap_cons, ForItemForm.references, AssignmentResolution.references,
          PlaceResolution.references, List.mem_append]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (sourceKeys_references member)))))
    refine ⟨.initializerAssign (assignment_head edited avoids (expressions context) head children)
      (ih (fun child member => reached child (by
        simpa only [List.flatMap_cons, List.append_assoc] using List.mem_append_right _ member))).choose, ?_⟩
    exact target.initializerAssign
      (head := (assignment_head edited avoids (expressions context) head children))
      (remaining := (ih (fun child member => reached child (by
        simpa only [List.flatMap_cons, List.append_assoc] using List.mem_append_right _ member))).choose)
      ((ih (fun child member => reached child (by simpa only [List.flatMap_cons, List.append_assoc] using List.mem_append_right _ member))).choose_spec) (assignments head children headErrors)
  · intro context scope assignment rest body condition post statements expected type head remaining ih headErrors
    intro reached
    refine ⟨.initializerBitNot head (ih (fun child member => reached child (by
      simpa only [List.flatMap_cons, List.append_assoc] using List.mem_append_right _ member))).choose, ?_⟩
    exact target.initializerBitNot
      (head := head)
      (remaining := (ih (fun child member => reached child (by
      simpa only [List.flatMap_cons, List.append_assoc] using List.mem_append_right _ member))).choose)
      ((ih (fun child member => reached child (by simpa only [List.flatMap_cons, List.append_assoc] using List.mem_append_right _ member))).choose_spec) (unaries head headErrors)
  · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining matchPayload childrenIH restIH
    intro reached
    have refs : Within source roots resolution.references :=
      fun child member => .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using member)
    have scrutineeReached : Reaches source roots (.expression resolution.scrutinee) := refs _ (by simp [MatchResolution.references])
    have casesReached : Within source roots (resolution.cases.flatMap TypedMatchCase.references) :=
      fun child member => refs child (by simp [MatchResolution.references, member])
    have fallbackReached : Within source roots ((resolution.defaultBody.getD []).map NodeId.statement) :=
      fun child member => refs child (by simp [MatchResolution.references, member])
    have typedDefault : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType view control context statements finalContext facts := by
      intro statements same
      obtain ⟨finalContext, facts, typed⟩ := defaultTyped statements same
      exact ⟨_, _, CallableLambdaViewStaticTyping.statements edited avoids unique typed
        (by simpa only [same, Option.getD_some] using fallbackReached)⟩
    have transformed := match_certificate edited avoids allocator (expressions context) receipt scrutineeReached
    have transportedChildren : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor view context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        ∃ tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values view
            afterSyntax after definitions administrative childContext request.scope
            (.statements false request.statements) expected type request.code,
          P tree := by
      intro request member childContext related
      have original := scoped_context edited related
      apply childrenIH request member childContext original
      intro statement present
      cases original with
      | arm armMember sameBody _ _ _ =>
        apply casesReached
        exact List.mem_flatMap.mpr ⟨_, armMember, List.mem_map.mpr ⟨statement, sameBody ▸ present, rfl⟩⟩
      | default sameBody _ =>
        apply fallbackReached
        simpa only [sameBody, Option.getD_some, List.mem_map, NodeId.statement.injEq] using
          (List.mem_map.mpr ⟨statement, present, rfl⟩ : .statement statement ∈ request.statements.map NodeId.statement)
    refine ⟨.matchWith (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids scrutineeReached).symm.trans scrutineeFound)
      (CallableLambdaViewStaticTyping.expression edited avoids unique scrutineeTyped scrutineeReached)
      (CallableLambdaViewStaticTyping.matchCases edited avoids unique casesTyped casesReached)
      typedDefault compilation sameValues sameDefinitions allocator requests transformed (match_ordinary edited ordinary)
      (fun request member childContext related => (transportedChildren request member childContext related).choose) (restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose, ?_⟩
    exact target.matchWith
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (scrutineeFound := ((expression_lookup edited avoids scrutineeReached).symm.trans scrutineeFound))
      (scrutineeTyped := (CallableLambdaViewStaticTyping.expression edited avoids unique scrutineeTyped scrutineeReached))
      (casesTyped := (CallableLambdaViewStaticTyping.matchCases edited avoids unique casesTyped casesReached))
      (defaultTyped := typedDefault)
      (compilation := compilation)
      (sameValues := sameValues)
      (sameDefinitions := sameDefinitions)
      (allocator := allocator)
      (requests := requests)
      (receipt := transformed)
      (ordinary := (match_ordinary edited ordinary))
      (children := (fun request member childContext related => (transportedChildren request member childContext related).choose))
      (remaining := (restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose)
       (matchPayloads compilation context matchPayload) (fun request member childContext related => (transportedChildren request member childContext related).choose_spec) (restIH (fun child member => reached child (List.mem_cons_of_mem id member))).choose_spec
  · intro context scope mode id node statements rest expected type innerCode suffix exactUnique found form inner stops issued innerIH
    intro reached
    refine ⟨.terminalBlock (edited.metadata.unique exactUnique) (edited.metadata.symm.statement found) form
      (innerIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose
      (stops.transport (statement_identity edited)) (issued.transport (statement_identity edited)), ?_⟩
    exact target.terminalBlock
      (unique := (edited.metadata.unique exactUnique))
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (inner := (innerIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose)
      (stops := (stops.transport (statement_identity edited)))
      (issued := (issued.transport (statement_identity edited)))
      ((innerIH (fun child member => .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member]))).choose_spec)
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH
    intro reached
    have child : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    refine ⟨.terminalIf (edited.metadata.unique exactUnique) (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType
      (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree)
      (thenIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose
      (elseIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose
      (thenStops.transport (statement_identity edited)) (elseStops.transport (statement_identity edited))
      (issued.transport (statement_identity edited)), ?_⟩
    exact target.terminalIf
      (unique := (edited.metadata.unique exactUnique))
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (conditionFound := ((expression_lookup edited avoids child).symm.trans conditionFound))
      (conditionType := conditionType)
      (conditionTree := (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree))
      (thenTree := (thenIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose)
      (elseTree := (elseIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member]))).choose)
      (thenStops := (thenStops.transport (statement_identity edited)))
      (elseStops := (elseStops.transport (statement_identity edited)))
      (issued := (issued.transport (statement_identity edited)))
      ((thenIH (fun child member => .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member]))).choose_spec) ((elseIH (fun child member => .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member]))).choose_spec)
  · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued matchPayload childrenIH
    intro reached
    have refs : Within source roots resolution.references :=
      fun child member => .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using member)
    have scrutineeReached : Reaches source roots (.expression resolution.scrutinee) := refs _ (by simp [MatchResolution.references])
    have casesReached : Within source roots (resolution.cases.flatMap TypedMatchCase.references) :=
      fun child member => refs child (by simp [MatchResolution.references, member])
    have fallbackReached : Within source roots ((resolution.defaultBody.getD []).map NodeId.statement) :=
      fun child member => refs child (by simp [MatchResolution.references, member])
    have typedDefault : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType view control context statements finalContext facts := by
      intro statements same
      obtain ⟨finalContext, facts, typed⟩ := defaultTyped statements same
      exact ⟨_, _, CallableLambdaViewStaticTyping.statements edited avoids unique typed
        (by simpa only [same, Option.getD_some] using fallbackReached)⟩
    have transformed := match_certificate edited avoids allocator (expressions context) receipt scrutineeReached
    have transportedChildren : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor view context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        ∃ tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values view
            afterSyntax after definitions administrative childContext request.scope
            (.statements false request.statements) expected type request.code,
          P tree := by
      intro request member childContext related
      have original := scoped_context edited related
      apply childrenIH request member childContext original
      intro statement present
      cases original with
      | arm armMember sameBody _ _ _ =>
        apply casesReached
        exact List.mem_flatMap.mpr ⟨_, armMember, List.mem_map.mpr ⟨statement, sameBody ▸ present, rfl⟩⟩
      | default sameBody _ =>
        apply fallbackReached
        simpa only [sameBody, Option.getD_some, List.mem_map, NodeId.statement.injEq] using
          (List.mem_map.mpr ⟨statement, present, rfl⟩ : .statement statement ∈ request.statements.map NodeId.statement)
    refine ⟨.terminalMatch (edited.metadata.unique exactUnique) (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids scrutineeReached).symm.trans scrutineeFound)
      (CallableLambdaViewStaticTyping.expression edited avoids unique scrutineeTyped scrutineeReached)
      (CallableLambdaViewStaticTyping.matchCases edited avoids unique casesTyped casesReached)
      typedDefault compilation sameValues sameDefinitions allocator requests transformed (match_ordinary edited ordinary)
      (fun request member childContext related => (transportedChildren request member childContext related).choose) (stops.transport (statement_identity edited)) (issued.transport (statement_identity edited)), ?_⟩
    exact target.terminalMatch
      (unique := (edited.metadata.unique exactUnique))
      (found := (edited.metadata.symm.statement found))
      (form := form)
      (scrutineeFound := ((expression_lookup edited avoids scrutineeReached).symm.trans scrutineeFound))
      (scrutineeTyped := (CallableLambdaViewStaticTyping.expression edited avoids unique scrutineeTyped scrutineeReached))
      (casesTyped := (CallableLambdaViewStaticTyping.matchCases edited avoids unique casesTyped casesReached))
      (defaultTyped := typedDefault)
      (compilation := compilation)
      (sameValues := sameValues)
      (sameDefinitions := sameDefinitions)
      (allocator := allocator)
      (requests := requests)
      (receipt := transformed)
      (ordinary := (match_ordinary edited ordinary))
      (children := (fun request member childContext related => (transportedChildren request member childContext related).choose))
      (stops := (stops.transport (statement_identity edited)))
      (issued := (issued.transport (statement_identity edited)))
       (matchPayloads compilation context matchPayload) (fun request member childContext related => (transportedChildren request member childContext related).choose_spec)


theorem transport_sites_with {diagnosticPolicy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
      beforeSyntax before definitions administrative context scope position expected type code}
    (sites : tree.CatalogSites diagnosticPolicy registry faults)
    (reached : PositionReached source roots position) :
    ∃ tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values view
      afterSyntax after definitions administrative context scope position expected type code,
      tree.CatalogSites diagnosticPolicy registry faults := by
  exact transport_payload_with edited avoids unique syntaxTransport expressions
    (fun head => head.ErrorsFor diagnosticPolicy registry faults) (fun head => head.Errors faults)
    (fun tree => tree.ErrorsFor diagnosticPolicy registry faults)
    (fun compilation context => SignatureCatalogWellFormed values.checked.signatures ∧ GenericImperativeMatch.Tree.MatchContextFields compilation context)
    (fun head => head.ErrorsFor diagnosticPolicy registry faults) (fun head => head.Errors faults)
    (fun tree => tree.ErrorsFor diagnosticPolicy registry faults)
    (fun compilation context => SignatureCatalogWellFormed values.checked.signatures ∧ GenericImperativeMatch.Tree.MatchContextFields compilation context)
    (fun tree => tree.CatalogSites diagnosticPolicy registry faults)
    CallableLambdaViewPreparedStaticTransport.Match.legacy_algebra
    (fun head children receipt => by cases diagnosticPolicy <;> exact ⟨receipt.missing, receipt.uninitialized, receipt.operands⟩)
    (fun _ receipt => receipt)
    (fun _ receipt reached => header_sites edited avoids expressions receipt reached)
    (fun _ _ receipt => receipt)
    (Structural.of_catalog_sites sites) reached

omit syntaxTransport in
theorem transport {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
      (CompatibleExpressionBuiltins.Syntax source) before definitions administrative context scope position expected type code)
    (reached : PositionReached source roots position) :
    GenericImperativeMatch.Tree layouts owner active frame globals onError values view
      (CompatibleExpressionBuiltins.Syntax view) after definitions administrative context scope position expected type code :=
  transport_with edited avoids unique
    (fun _id reached value => CallableLambdaViewSourceTyping.expression_syntax edited avoids unique value reached)
    expressions tree reached

omit syntaxTransport in
theorem transport_sites {diagnosticPolicy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
      (CompatibleExpressionBuiltins.Syntax source) before definitions administrative context scope position expected type code}
    (sites : tree.CatalogSites diagnosticPolicy registry faults)
    (reached : PositionReached source roots position) :
    ∃ tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values view
      (CompatibleExpressionBuiltins.Syntax view) after definitions administrative context scope position expected type code,
      tree.CatalogSites diagnosticPolicy registry faults :=
  transport_sites_with edited avoids unique
    (fun _id reached value => CallableLambdaViewSourceTyping.expression_syntax edited avoids unique value reached)
    expressions sites reached

end Statements

end Static

/-- The concrete runtime builtin family returns from the actual view to the
canonical body. Every imperative constructor keeps the same emitted code,
ordered requests and diagnostic tokens. Compiler acceptance remains at view. -/
theorem original
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : SourceCoreCompatibleValues.Context} {source view : TypedSource} {changed : List ExpressionId}
    {definitions : DataEnvironment} {administrative : Core.Context} {readFuel : Nat}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {diagnosticPolicy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (edited : LocalView source view changed)
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique source)
    {tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values view
      (CompatibleExpressionBuiltins.Syntax view)
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate readFuel values view context solved reasonAt)
      definitions administrative context scope (.statements mode statements) expected type code}
    (sites : tree.CatalogSites diagnosticPolicy registry faults) :
    ∃ canonical : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
      (CompatibleExpressionBuiltins.Syntax source)
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate readFuel values source context solved reasonAt)
      definitions administrative context scope (.statements mode statements) expected type code,
      canonical.CatalogSites diagnosticPolicy registry faults := by
  have reverse : LocalView view source changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  refine transport_sites reverse (avoids.view edited.metadata) (edited.metadata.unique unique)
    (fun _ _ _ _ reached certificate => builtin_original edited avoids certificate (reached.metadata edited.metadata.symm)) sites ?_
  intro id member
  exact .root (List.mem_map.mpr ⟨id, member, rfl⟩)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewMatchRuntimeCertificates
