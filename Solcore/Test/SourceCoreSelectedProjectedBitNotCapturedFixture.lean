import Solcore.Test.SourceCoreSelectedProjectedBitNotFixture
import Solcore.Test.SourceCoreSelectedProjectedBitNotCapturedSource

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedProjectedBitNot.Captured
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

/-- Observe original compiler nodes and binders; no completed execution is read. -/
def observeShape (source : TypedSource) : IO (Shape source) := do
  let [table] := source.inputs | throw (IO.userError "captured mapping input")
  let [.statement outerId] := source.roots | throw (IO.userError "captured mapping root")
  let some outer := source.lookupStatement? outerId | throw (IO.userError "captured outer lookup")
  let .returnStmt (some lambdaId) := outer.form | throw (IO.userError "captured outer return")
  let some lambda := source.lookupExpression? lambdaId | throw (IO.userError "captured lambda lookup")
  let .lambda [key] .word [assignedId, returnedId] := lambda.form | throw (IO.userError "captured lambda body")
  let some assigned := source.lookupStatement? assignedId | throw (IO.userError "captured assignment lookup")
  let some returned := source.lookupStatement? returnedId | throw (IO.userError "captured inner return lookup")
  let .assignBitNot resolution := assigned.form | throw (IO.userError "captured unary form")
  let [.index keyId] := resolution.target.projections | throw (IO.userError "captured unary key")
  let some keyNode := source.lookupExpression? keyId | throw (IO.userError "captured key lookup")
  let keyRead ← Tests.SourceCoreNamedBranch.observeRead source key keyNode .word
  let .returnStmt (some resultId) := returned.form | throw (IO.userError "captured result return")
  let some resultNode := source.lookupExpression? resultId | throw (IO.userError "captured result lookup")
  let .index tableId resultKeyId := resultNode.form | throw (IO.userError "captured result index")
  let some tableNode := source.lookupExpression? tableId | throw (IO.userError "captured table lookup")
  let some resultKeyNode := source.lookupExpression? resultKeyId | throw (IO.userError "captured result key lookup")
  let tableRead ← Tests.SourceCoreNamedBranch.observeRead source table tableNode mappingType
  let resultKey ← Tests.SourceCoreNamedBranch.observeRead source key resultKeyNode .word
  let ⟨resultFound⟩ ← observed (source.lookupExpression? resultNode.id = some resultNode) "captured result identity"
  let ⟨resultForm⟩ ← observed (resultNode.form = .index tableRead.node.id resultKey.node.id) "captured result children"
  let ⟨resultRequirements⟩ ← observed (resultNode.requirements = []) "captured result requirements"
  let ⟨resultCoercions⟩ ← observed (resultNode.coercions = []) "captured result coercions"
  let result : IndexRead source tableRead.node.id resultKey.node.id :=
    ⟨resultNode, resultFound, resultForm, resultRequirements, resultCoercions⟩
  let ⟨inputs⟩ ← observed (source.inputs = [table]) "captured inputs"
  let ⟨tableScheme⟩ ← observed (table.scheme = .mono mappingType) "captured mapping scheme"
  let ⟨keyScheme⟩ ← observed (key.scheme = .mono .word) "captured key scheme"
  let ⟨keyTable⟩ ← observed (key.id ≠ table.id) "captured distinct binders"
  let ⟨roots⟩ ← observed (source.roots = [.statement outer.id]) "captured roots"
  let ⟨assignedFound⟩ ← observed (source.lookupStatement? assigned.id = some assigned) "captured assignment identity"
  let ⟨assignedForm⟩ ← observed (assigned.form = .assignBitNot resolution) "captured assignment operator"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = table.id) "captured target binder"
  let ⟨targetProjections⟩ ← observed (resolution.target.projections = [.index keyRead.node.id]) "captured target key"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "captured original leaf type"
  let ⟨returnedFound⟩ ← observed (source.lookupStatement? returned.id = some returned) "captured return identity"
  let ⟨returnedForm⟩ ← observed (returned.form = .returnStmt (some result.node.id)) "captured return form"
  let ⟨lambdaFound⟩ ← observed (source.lookupExpression? lambda.id = some lambda) "captured lambda identity"
  let ⟨lambdaForm⟩ ← observed (lambda.form = .lambda [key] .word [assigned.id, returned.id]) "captured lambda children"
  let ⟨lambdaRequirements⟩ ← observed (lambda.requirements = []) "captured lambda requirements"
  let ⟨lambdaCoercions⟩ ← observed (lambda.coercions = []) "captured lambda coercions"
  let ⟨outerFound⟩ ← observed (source.lookupStatement? outer.id = some outer) "captured outer identity"
  let ⟨outerForm⟩ ← observed (outer.form = .returnStmt (some lambda.id)) "captured outer child"
  return ⟨table, key, resolution, assigned, returned, outer, lambda, keyRead, tableRead, resultKey, result,
    inputs, tableScheme, keyScheme, keyTable, roots, assignedFound, assignedForm, targetRoot,
    targetProjections, targetType, returnedFound, returnedForm, lambdaFound, lambdaForm,
    lambdaRequirements, lambdaCoercions, outerFound, outerForm⟩

structure ObservedFactory (fixture : CompiledFixture) where
  row : Row fixture
  shape : Shape row.original.function.typedBody
  resultType : row.original.function.inferredBodyType = .function .word .word

def observeFactory (fixture : CompiledFixture) : IO (ObservedFactory fixture) := do
  let row ← observeRow fixture "make"
  let shape ← observeShape row.original.function.typedBody
  let ⟨resultType⟩ ← observed (row.original.function.inferredBodyType = .function .word .word)
    "captured factory result type"
  return ⟨row, shape, resultType⟩

end Tests.SourceCoreSelectedProjectedBitNot.Captured
