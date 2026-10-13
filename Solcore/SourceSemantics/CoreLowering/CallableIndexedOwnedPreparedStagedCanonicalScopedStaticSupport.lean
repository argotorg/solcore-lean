import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites

/-! General recursive expressions share the existing named scoped compiler
flow with legacy expressions and ordinary formation. Each canonical child
retains its actual compiler prefix; no runtime globals or body law is stored. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (CanonicalRootAt)
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Existing recursive/formation certificates remain explicit alternatives.
The canonical branch retains only static root and compiler-prefix authority. -/
inductive Certificate
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop where
  | legacy (actual : CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Certificate
      header bodyRegistry semanticFaults context invocation scope id lowered)
  | canonical (root : CanonicalRootAt compiled headers context invocation scope id lowered semanticFaults)
      («prefix» : root.compilation.administrativePrefix = 1)

/-- The same authentic branching receipt covers lexical bodies, branches and
finite loops. Collected retains its own compiler tree and catalog sites. -/
structure NamedSupport
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (stages : Staging.Recursive.Registry) (receipt : Receipt header)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers
  zero : ∀ owner : OwnedKey keys, owner.key.capturePrefix = 0
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  tree : ∀ child, stages.Closure header.function child →
    ∃ expressionSyntax : ExpressionId → Prop,
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) child.source expressionSyntax
      (TypedCertificate child.source (fun context => Certificate headers header bodyRegistry semanticFaults context child))
      compiled.indexed.layouts.definitions
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      header.context (parameterScope header) (.statements true header.function.body)
      header.function.resultType header.output receipt.flow

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport
