import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.AcceptedFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.CompilerProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
import Solcore.SourceSemantics.ProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.IndirectDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthorityReception
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalSupport
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.Staging.SelectedProgramPreservation
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalClosureHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedPhysicalClosureArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection

/-!
# Public program support and session state

The vocabulary of the public-session theorems.

Main declarations:
- `CompilerProgramStaticProfile.StaticProfile`, the static profile, an explicit premise
  of the profiled sessions;
- `SelectedCompilationNamedSupport.Support` and
  `SelectedCompilationPhysicalProgramSupport.Support`, what a program supplies to a
  session;
- `SelectedCompilationPublicSessionState.State`, `SelectedCompilationPublicSessionState.StartedCall`
  and `SelectedCompilationPublicSessionState.SourceCall`, one session and its calls.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompilerProgramStaticProfile
/-! Executable finite checks inspect every actual cache row and every original
lambda. They retain raw forms, edges, metadata, target ranges and evidence.
The accepted compiler actions supply body and expression proofs separately. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CompilerProgramStaticProfile
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedOrdinarySyntaxTable (Table)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Eligible)
open CallableIndexedOwnedPreparedScopedMethodAdmission (Excluded)

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by
        intro item member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail item member⟩

def LambdaAllowed (allowed : Option ExpressionNode) : Node → Prop
  | .statement _ => True
  | .expression node => match node.form with
    | .lambda _ _ _ => allowed = some node
    | _ => True

def lambdas? (source : TypedSource) (allowed : Option ExpressionNode) :
    Option (PLift (∀ node ∈ source.nodes, LambdaAllowed allowed node)) :=
  allProof? (LambdaAllowed allowed) (fun node => by
    cases node with
    | statement statement => exact some ⟨True.intro⟩
    | expression expression =>
      cases form : expression.form
      case lambda parameters result body =>
        exact if same : allowed = some expression then
          some ⟨by simpa only [LambdaAllowed, form] using same⟩ else none
      all_goals exact some ⟨by simp only [LambdaAllowed, form]⟩) source.nodes

abbrev ExpressionProfile (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly : Bool) := AcceptedCompilerExpressionProfile.Profile compiled.indexed named
      named.specialized.function.typedBody rows directOnly (!directOnly) (!directOnly)

structure Scoped (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly : Bool) where
  expressions : ExpressionProfile compiled named rows directOnly
  body : AcceptedCompilerBodyProfile.Profile named.specialized.function.typedBody expressions.Reached
  finish : AcceptedCompilerBodyCompletion.Finish named.specialized.function.typedBody
    named.specialized.function.inferredBodyType true (statements named.specialized.function.typedBody)
  lambdas : ∀ node ∈ named.specialized.function.typedBody.nodes, LambdaAllowed none node

def scoped? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction)
    (directOnly : Bool) : Option (Scoped compiled named rows directOnly) := do
  let expressions ← AcceptedCompilerExpressionProfile.certify compiled.indexed named
    named.specialized.function.typedBody rows directOnly (!directOnly) (!directOnly)
  let ⟨body⟩ ← AcceptedCompilerBodyProfile.validate named.specialized.function.typedBody expressions.Reached
  let ⟨finish⟩ ← AcceptedCompilerBodyCompletion.finish? named.specialized.function.typedBody
    named.specialized.function.inferredBodyType true (statements named.specialized.function.typedBody)
  let ⟨lambdas⟩ ← lambdas? named.specialized.function.typedBody none
  pure ⟨expressions, body, finish, lambdas⟩

/-- The factory lane records the original outer return and singleton inner
return. Every lambda in the complete original node table is accounted for. -/
structure Factory (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) where
  expressions : ExpressionProfile compiled named rows true
  outer : StatementId
  rest : List StatementId
  outerNode : StatementNode
  expression : ExpressionId
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statement : StatementId
  returnNode : StatementNode
  inner : ExpressionId
  roots : statements named.specialized.function.typedBody = outer :: rest
  outerFound : named.specialized.function.typedBody.lookupStatement? outer = some outerNode
  outerForm : outerNode.form = .returnStmt (some expression)
  found : named.specialized.function.typedBody.lookupExpression? expression = some node
  form : node.form = .lambda parameters result [statement]
  requirements : node.requirements = []
  coercions : node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding => decide
    (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
      binding.initializer = expression)) = none
  returnFound : named.specialized.function.typedBody.lookupStatement? statement = some returnNode
  returnForm : returnNode.form = .returnStmt (some inner)
  innerReached : expressions.Reached inner
  lambdas : ∀ actual ∈ named.specialized.function.typedBody.nodes, LambdaAllowed (some node) actual

def factory? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) :
    Option (Factory compiled named rows) := do
  let expressions ← AcceptedCompilerExpressionProfile.certify compiled.indexed named
    named.specialized.function.typedBody rows true
  match roots : statements named.specialized.function.typedBody with
  | [] => none
  | outer :: rest =>
    match outerFound : named.specialized.function.typedBody.lookupStatement? outer with
    | none => none
    | some outerNode =>
      match outerForm : outerNode.form with
      | .returnStmt (some expression) =>
        match found : named.specialized.function.typedBody.lookupExpression? expression with
        | none => none
        | some node =>
          match form : node.form with
          | .lambda parameters result [statement] =>
            if requirements : node.requirements = [] then
              if coercions : node.coercions = [] then
                if ordinary : compiled.indexed.base.locals.bindings.find? (fun binding => decide
                    (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
                      binding.initializer = expression)) = none then
                  match returnFound : named.specialized.function.typedBody.lookupStatement? statement with
                  | none => none
                  | some returnNode =>
                    match returnForm : returnNode.form with
                    | .returnStmt (some inner) =>
                      if innerReached : expressions.Reached inner then do
                        let ⟨lambdas⟩ ← lambdas? named.specialized.function.typedBody (some node)
                        pure ⟨expressions, outer, rest, outerNode, expression, node, parameters, result,
                          statement, returnNode, inner, roots, outerFound, outerForm, found, form,
                          requirements, coercions, ordinary, returnFound, returnForm, innerReached, lambdas⟩
                      else none
                    | _ => none
                else none
              else none
            else none
          | _ => none
      | _ => none

structure CoercedFactory (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) where
  outer : StatementId
  rest : List StatementId
  outerNode : StatementNode
  expression : ExpressionId
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statement : StatementId
  returnNode : StatementNode
  inner : ExpressionId
  roots : statements named.specialized.function.typedBody = outer :: rest
  outerFound : named.specialized.function.typedBody.lookupStatement? outer = some outerNode
  outerForm : outerNode.form = .returnStmt (some expression)
  found : named.specialized.function.typedBody.lookupExpression? expression = some node
  form : node.form = .lambda parameters result [statement]
  requirements : node.requirements = []
  coercions : node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding => decide
    (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
      binding.initializer = expression)) = none
  returnFound : named.specialized.function.typedBody.lookupStatement? statement = some returnNode
  returnForm : returnNode.form = .returnStmt (some inner)
  innerProfile : CompilerCoercedExpressionProfile.Profile compiled named named.specialized.function.typedBody rows inner
  lambdas : ∀ actual ∈ named.specialized.function.typedBody.nodes, LambdaAllowed (some node) actual

def coercedFactory? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) :
    Option (CoercedFactory compiled named rows) := do
  match roots : statements named.specialized.function.typedBody with
  | [] => none
  | outer :: rest =>
    match outerFound : named.specialized.function.typedBody.lookupStatement? outer with
    | none => none
    | some outerNode =>
      match outerForm : outerNode.form with
      | .returnStmt (some expression) =>
        match found : named.specialized.function.typedBody.lookupExpression? expression with
        | none => none
        | some node =>
          match form : node.form with
          | .lambda parameters result [statement] =>
            if requirements : node.requirements = [] then
              if coercions : node.coercions = [] then
                if ordinary : compiled.indexed.base.locals.bindings.find? (fun binding => decide
                    (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
                      binding.initializer = expression)) = none then
                  match returnFound : named.specialized.function.typedBody.lookupStatement? statement with
                  | none => none
                  | some returnNode =>
                    match returnForm : returnNode.form with
                    | .returnStmt (some inner) =>
                      do
                        let innerProfile ← CompilerCoercedExpressionProfile.certify compiled named
                          named.specialized.function.typedBody rows inner
                        let ⟨lambdas⟩ ← lambdas? named.specialized.function.typedBody (some node)
                        pure ⟨outer, rest, outerNode, expression, node, parameters, result,
                          statement, returnNode, inner, roots, outerFound, outerForm, found, form,
                          requirements, coercions, ordinary, returnFound, returnForm, innerProfile, lambdas⟩
                    | _ => none
                else none
              else none
            else none
          | _ => none
      | _ => none

/-- The scoped factory retains its complete original lambda body. A flat
statement subset covers that body's roots and every nested loop child. -/
structure ScopedFactory (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) where
  expressions : ExpressionProfile compiled named rows false
  outer : StatementId
  rest : List StatementId
  outerNode : StatementNode
  expression : ExpressionId
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  roots : CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements named.specialized.function.typedBody = outer :: rest
  outerFound : named.specialized.function.typedBody.lookupStatement? outer = some outerNode
  outerForm : outerNode.form = .returnStmt (some expression)
  found : named.specialized.function.typedBody.lookupExpression? expression = some node
  form : node.form = .lambda parameters result statements
  requirements : node.requirements = []
  coercions : node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding => decide
    (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
      binding.initializer = expression)) = none
  body : AcceptedCompilerBodySubsetProfile.Profile named.specialized.function.typedBody expressions.ids statements result
  lambdas : ∀ actual ∈ named.specialized.function.typedBody.nodes, LambdaAllowed (some node) actual

def scopedFactory? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) :
    Option (ScopedFactory compiled named rows) := do
  let expressions ← AcceptedCompilerExpressionProfile.certify compiled.indexed named
    named.specialized.function.typedBody rows false true true
  match roots : statements named.specialized.function.typedBody with
  | [] => none
  | outer :: rest =>
    match outerFound : named.specialized.function.typedBody.lookupStatement? outer with
    | none => none
    | some outerNode =>
      match outerForm : outerNode.form with
      | .returnStmt (some expression) =>
        match found : named.specialized.function.typedBody.lookupExpression? expression with
        | none => none
        | some node =>
          match form : node.form with
          | .lambda parameters result bodyRoots =>
            if requirements : node.requirements = [] then
              if coercions : node.coercions = [] then
                if ordinary : compiled.indexed.base.locals.bindings.find? (fun binding => decide
                    (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
                      binding.initializer = expression)) = none then do
                  let ⟨body⟩ ← AcceptedCompilerBodySubsetProfile.validate named.specialized.function.typedBody expressions.ids bodyRoots result
                  let ⟨lambdas⟩ ← lambdas? named.specialized.function.typedBody (some node)
                  pure ⟨expressions, outer, rest, outerNode, expression, node, parameters, result, bodyRoots,
                    roots, outerFound, outerForm, found, form, requirements, coercions, ordinary, body, lambdas⟩
                else none
              else none
            else none
          | _ => none
      | _ => none

inductive Ordinary (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) where
  | scoped (profile : Scoped compiled named rows false)
  | factory (profile : Factory compiled named rows)
  | scopedFactory (profile : ScopedFactory compiled named rows)

def ordinary? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) :
    Option (Ordinary compiled named rows) :=
  match scoped? compiled named rows false with
  | some profile => some (.scoped profile)
  | none =>
    match factory? compiled named rows with
    | some profile => some (.factory profile)
    | none => (scopedFactory? compiled named rows).map Ordinary.scopedFactory

def NoOrdinary (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) : Prop :=
  ∀ signature ∈ compiled.sourceProgram.signatures.functions, named.specialized.declaration ≠ signature.id

theorem primitive_lambdas {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function}
    (profile : CompilerCoercedMethodProfile.Primitive compiled named) :
    ∀ node ∈ named.specialized.function.typedBody.nodes, LambdaAllowed none node := by
  obtain ⟨receipt, accepted⟩ := profile.formsAccepted
  have all := SelectedCompilationPrimitiveMethodNodeFacts.nodes_of_accepted accepted
  intro node member
  cases node with
  | statement node => exact True.intro
  | expression node =>
    have allowed := all (.expression node) member node rfl
    cases form : node.form
    case lambda parameters result body =>
      rw [form] at allowed
      cases allowed
    all_goals simp only [LambdaAllowed, form]

inductive Row (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (rows : List SourceSpecialization.SpecializedFunction) where
  | ordinary (eligible : Eligible compiled named.specialized) (excluded : Excluded compiled named)
      (profile : Ordinary compiled named rows)
  | coercedFactory (eligible : Eligible compiled named.specialized) (excluded : Excluded compiled named)
      (profile : CoercedFactory compiled named rows) (closed : CompilerCoercedMethodProfile.Closed compiled)
  | closedMethod (profile : CompilerCoercedMethodProfile.Primitive compiled named)
      (closed : CompilerCoercedMethodProfile.Closed compiled)
  | method (excluded : NoOrdinary compiled named)
      (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
        (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
        named.specialized.parameterSubstitution)
      (forms : CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots.DirectSource
        named.specialized.function.typedBody)
      (profile : Scoped compiled named rows true)

def row? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {index : Nat} (named : SourceCoreGeneralFunctions.Function)
    (selected : compiled.indexed.base.functions[index]? = some named)
    (rows : List SourceSpecialization.SpecializedFunction) : Option (Row compiled named rows) := do
  if absent : compiled.sourceProgram.signatures.functions.all (fun signature =>
      decide (named.specialized.declaration ≠ signature.id)) = true then
    let ⟨range⟩ ← CallableIndexedOwnedPreparedOrdinarySyntaxTable.range?
      compiled.sourceProgram.signatures (max 1 compiled.indexed.fuel) named.specialized.parameterSubstitution
    let ⟨forms⟩ ← CallableIndexedOwnedPreparedScopedMethodAdmission.directSource? named.specialized.function.typedBody
    let profile ← scoped? compiled named rows true
    pure (.method (fun signature member => of_decide_eq_true (List.all_eq_true.mp absent signature member))
      range forms profile)
  else
    let ⟨eligible⟩ ← CallableIndexedOwnedPreparedOrdinarySyntaxTable.eligible? compiled wellFormed
      (max 1 compiled.indexed.fuel) named selected
    if excluded : (Program.ofChecked compiled.sourceProgram).methods.all (fun definition =>
        decide (named.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
      let profile ← ordinary? compiled named rows
      pure (.ordinary eligible (fun definition member =>
        of_decide_eq_true (List.all_eq_true.mp excluded definition member)) profile)
    else none

structure StaticProfile (compiled : SourceCoreUnifiedCompilation.Compiled) where
  table : Table compiled
  catalog : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog compiled
  rows : ∀ index : Fin compiled.indexed.base.functions.length,
    Nonempty (Row compiled compiled.indexed.base.functions[index.val] table.rows)
  callable : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program

/-- The only traversal budgets bound original type formation. Body and
expression acceptance comes from the retained compiler receipts. -/
def validateProfile (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Option (StaticProfile compiled) := do
  if callable : compiled.compatible.checked.catalog.callableContracts = true then
    match present : compiled.indexed.base.diagnostics with
    | none => none
    | some diagnostics =>
      let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed
        (max 1 compiled.indexed.fuel)
      let ⟨catalog⟩ ← CallableIndexedOwnedPreparedOriginsMethodAdmission.certify compiled
      let ⟨rows⟩ ← allProof?
        (fun index : Fin compiled.indexed.base.functions.length =>
          Nonempty (Row compiled compiled.indexed.base.functions[index.val] table.rows))
        (fun index => do
          let profile ← row? compiled wellFormed compiled.indexed.base.functions[index.val]
            (List.getElem?_eq_getElem index.isLt) table.rows
          pure ⟨⟨profile⟩⟩) (List.finRange compiled.indexed.base.functions.length)
      pure ⟨table, catalog, fun index => rows index (List.mem_finRange index), callable, diagnostics, present⟩
  else none

end Solcore.SourceSemantics.CoreLowering.CompilerProgramStaticProfile
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile
/-! The finite profile scans the complete actual cache using signature facts.
Its original row receipts and acceptance checks are preserved. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile
open Core Frontend SourceInference
open CompilerProgramStaticProfile

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by
        intro item member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail item member⟩

private def ordinaryRow? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {index : Nat} (named : SourceCoreGeneralFunctions.Function)
    (selected : compiled.indexed.base.functions[index]? = some named)
    (rows : List SourceSpecialization.SpecializedFunction) : Option (Row compiled named rows) := do
  if absent : compiled.sourceProgram.signatures.functions.all (fun signature =>
      decide (named.specialized.declaration ≠ signature.id)) = true then
    let ⟨range⟩ ← CallableIndexedOwnedPreparedOrdinarySyntaxTable.range?
      compiled.sourceProgram.signatures (max 1 compiled.indexed.fuel) named.specialized.parameterSubstitution
    let ⟨forms⟩ ← CallableIndexedOwnedPreparedScopedMethodAdmission.directSource? named.specialized.function.typedBody
    let profile ← scoped? compiled named rows true
    pure (.method (fun signature member => of_decide_eq_true (List.all_eq_true.mp absent signature member))
      range forms profile)
  else
    let ⟨eligible⟩ ← SelectedCompilationOrdinarySyntaxTable.eligible? compiled signatures
      (max 1 compiled.indexed.fuel) named selected
    if excluded : (Program.ofChecked compiled.sourceProgram).methods.all (fun definition =>
        decide (named.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
      let profile ← ordinary? compiled named rows
      pure (.ordinary eligible (fun definition member =>
        of_decide_eq_true (List.all_eq_true.mp excluded definition member)) profile)
    else none

/-- The existing accepted lane has priority. Only its rejected rows try the
closed coercion extension, which retains the same original cache position. -/
def row? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {index : Nat} (named : SourceCoreGeneralFunctions.Function)
    (selected : compiled.indexed.base.functions[index]? = some named)
    (rows : List SourceSpecialization.SpecializedFunction) : Option (Row compiled named rows) :=
  match ordinaryRow? compiled signatures named selected rows with
  | some profile => some profile
  | none => do
    let closed ← CompilerCoercedMethodProfile.certify compiled
    if _absent : compiled.sourceProgram.signatures.functions.all (fun signature =>
        decide (named.specialized.declaration ≠ signature.id)) = true then
      let profile ← CompilerCoercedMethodProfile.primitive? compiled named
      pure (.closedMethod profile closed)
    else
      let ⟨eligible⟩ ← SelectedCompilationOrdinarySyntaxTable.eligible? compiled signatures
        (max 1 compiled.indexed.fuel) named selected
      if excluded : (Program.ofChecked compiled.sourceProgram).methods.all (fun definition =>
          decide (named.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
        let profile ← coercedFactory? compiled named rows
        pure (.coercedFactory eligible (fun definition member =>
          of_decide_eq_true (List.all_eq_true.mp excluded definition member)) profile closed)
      else none

def validateProfile (compiled : SourceCoreUnifiedCompilation.Compiled)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures) :
    Option (StaticProfile compiled) := do
  if callable : compiled.compatible.checked.catalog.callableContracts = true then
    match present : compiled.indexed.base.diagnostics with
    | none => none
    | some diagnostics =>
      let table := SelectedCompilationOrdinarySyntaxTable.collect compiled signatures
        (max 1 compiled.indexed.fuel)
      let ⟨catalog⟩ ← CallableIndexedOwnedPreparedOriginsMethodAdmission.certify compiled
      let ⟨rows⟩ ← allProof?
        (fun index : Fin compiled.indexed.base.functions.length =>
          Nonempty (Row compiled compiled.indexed.base.functions[index.val] table.rows))
        (fun index => do
          let profile ← row? compiled signatures compiled.indexed.base.functions[index.val]
            (List.getElem?_eq_getElem index.isLt) table.rows
          pure ⟨⟨profile⟩⟩) (List.finRange compiled.indexed.base.functions.length)
      pure ⟨table, catalog, fun index => rows index (List.mem_finRange index), callable, diagnostics, present⟩
  else none

/-- Genuine checker success supplies the signature catalog internally. -/
def validateCheckedProfile (compiled : SourceCoreUnifiedCompilation.Compiled)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    Option (StaticProfile compiled) :=
  validateProfile compiled (SignatureCatalogWellFormed.ofCheckProgram checked)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerStaticProfile
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport
/-! Static coverage of the actual named, closure and method bodies supplies both
semantic directions at every reached public receiver. A successful compilation
does not by itself supply this coverage. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)

theorem stagePrepared (compiled : SourceCoreUnifiedCompilation.Compiled) :
    RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected

def stages (compiled : SourceCoreUnifiedCompilation.Compiled) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry (stagePrepared compiled)

/-- Every support field retains an actual compiler packet or original Source.
The body laws follow from the closed physical family below. -/
structure Support (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed) where
  profile : compiled.compatible.checked.catalog.callableContracts = true
  bodyTyping : SelectedCompilationBodyTyping.Bodies compiled
  certificates : ∀ header, header ∈ headers → SelectedCompilationNamedSourceTyping.Certified header
  issued : IssuedAt compiled.indexed initial.entry initial.result.context.registry
    initial.result.extension initial.result.diagnostics
  registry : initial.result.context.registry = compiled.compatible.checked.staticRegistry
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program
  bodies : ∀ header, header ∈ headers → CallableIndexedOwnedPreparedStagedNamedBodies.Body header
  bodySupport : ∀ header (member : header ∈ headers),
    SelectedCompilationPhysicalNamedBodySupport.Support
      (headers := headers) (bodyRegistry := initial.result.context.registry)
      (stages := stages compiled)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      header (bodies header member)
  closurePackets : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys
      initial.result.context.registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result),
    SelectedCompilationPhysicalClosureStaticSupport.PacketFor association (stages compiled)
  closureSupport : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys
      initial.result.context.registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result),
    SelectedCompilationPhysicalClosureStaticSupport.SupportFor association
      (stages compiled) (closurePackets association)
  owners : ∀ owner : OwnedKey keys, CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers
  methods : SelectedCompilationPhysicalMixedCallerFamily.MixedMethodSupports
    (compiled := compiled) (headers := headers) (stages := stages compiled)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}

def functions (support : Support compiled headers keys initial) :=
  CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys initial.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics) support.profile

theorem observations (support : Support compiled headers keys initial) :
    CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
      (functions support) (CallableIndexedLambdaValues.Identity compiled.indexed) :=
  CallableIndexedOwnedPreparedPhysicalCellOrigins.observations support.profile

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys initial)
  (issued : IssuedAt compiled.indexed receiving.entry receiving.result.context.registry
    receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)

include support extension in
theorem static_extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    receiving.result.context.registry := by
  change SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry _
  rw [← support.registry]
  exact extension

include support issued extension in
theorem semantic_extension : ∀ reason token,
    CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
  obtain ⟨program, present⟩ := support.diagnostics
  intro reason token represented
  exact CompatibleRegistryDiagnosticExtension.semantic_preserved compiled
    support.issued issued present extension represented

include support issued extension in
theorem preserves_bodies (header) (member : header ∈ headers)
    {child : Staging.Recursive.Scope} (selected : (stages compiled).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support))
      (stages compiled) child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  exact SelectedCompilationPhysicalMixedNamedFamilyPorts.preserves_with_methods
    issued (stagePrepared compiled) support.profile support.bodyTyping support.certificates (observations support)
    (static_extension support extension) (semantic_extension support issued extension)
    support.bodies support.bodySupport support.closurePackets support.closureSupport support.owners support.methods
    header member selected budget

include support issued extension in
theorem reflects_bodies (header) (member : header ∈ headers)
    {child : Staging.Recursive.Scope} (selected : (stages compiled).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support))
      (stages compiled) child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  exact SelectedCompilationPhysicalMixedNamedFamilyPorts.reflects_with_methods
    issued (stagePrepared compiled) support.profile support.bodyTyping support.certificates (observations support)
    (static_extension support extension) (semantic_extension support issued extension)
    support.bodies support.bodySupport support.closurePackets support.closureSupport support.owners support.methods
    rfl header member selected budget

include issued in
/-- The actual issued receiver interprets each retained assignment origin. -/
theorem assignment_interpretation :
    PreparedAssignmentDiagnosticAuthority.Interprets compiled receiving.result.context.registry
      (fun reason token => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        receiving.result.diagnostics (.semantic reason) token) :=
  PreparedAssignmentDiagnosticAuthority.interprets issued

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSupport
/-! Named execution consumes original selected body typing and preservation for
its actual prepared registry. The legacy whole-program API is an adapter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSupport
open Core Frontend SourceInference

structure Support (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  bodyTyping : SelectedCompilationBodyTyping.Bodies compiled
  registryBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
    (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled)

theorem Support.of_program {compiled : SourceCoreUnifiedCompilation.Compiled}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) : Support compiled :=
  ⟨.of_program wellFormed, .of_program wellFormed⟩

theorem Support.certified {compiled : SourceCoreUnifiedCompilation.Compiled}
    (support : Support compiled)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)) :
    SelectedCompilationNamedSourceTyping.Certified header :=
  SelectedCompilationHeaderCertificates.certified support.bodyTyping header

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
/-! An actual public session carries its indexed runtime, Source heap and
positive physical history. Calls retain their own public options and receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev StartedCall := @RecursiveNamedPublicPhysicalSessionState.StartedCall
abbrev Call := @RecursiveNamedPublicPhysicalSessionState.Call
abbrev FunctionCall := @RecursiveNamedPublicPhysicalSessionState.FunctionCall
abbrev SourceCall := @RecursiveNamedPublicPhysicalSessionState.SourceCall
abbrev PlainValue := @RecursiveNamedPublicPhysicalSessionState.PlainValue
abbrev PlainFault := @RecursiveNamedPublicPhysicalSessionState.PlainFault
abbrev FailureProjection := @RecursiveNamedPublicPhysicalSessionState.FailureProjection

section SourceOutcomes
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {anchor header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap} {arguments : List Dynamic.Value}

theorem SourceCall.value_plain {value : Dynamic.Value}
    (trace : SourceCall anchor header invocation before arguments (.value value) after) :
    PlainValue anchor header invocation before arguments value after :=
  RecursiveNamedPublicPhysicalSessionState.SourceCall.value_plain trace

theorem SourceCall.semanticFault_plain {reason : Dynamic.SemanticFault}
    (trace : SourceCall anchor header invocation before arguments (.fault (.semantic reason)) after) :
    PlainFault anchor header invocation before arguments reason after :=
  RecursiveNamedPublicPhysicalSessionState.SourceCall.semanticFault_plain trace

theorem SourceCall.failure_plain {failure : Staging.Recursive.Failure}
    (trace : SourceCall anchor header invocation before arguments (.fault failure) after) :
    FailureProjection anchor header invocation before arguments failure after :=
  RecursiveNamedPublicPhysicalSessionState.SourceCall.failure_plain trace
end SourceOutcomes

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)}

def functions (rows : Inventory inputs)
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CallableIndexedOwnedPreparedPhysicalCellOrigins.functions (headers rows) (keys compiled)
    initial.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics) profile

structure State (rows : Inventory inputs)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (recipe : SourceCoreIndexedSession.Recipe)
    {publicArtifact : SourceCoreExecution.Artifact}
    (publicSession : SourceCoreExecution.Session publicArtifact) (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers rows)
    (keys compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicPhysicalHistory.History (headers := headers rows)
    (keys := keys compiled) (functions := functions rows initial profile)
    (receiving := receiving.result.context.registry) (anchor := anchor)
    session mapping world heap store caller entries

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
end
