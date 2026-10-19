import Solcore.Test.SourceCoreGeneralizedExportInventory
import Solcore.Test.SourceCoreGeneralizedExportWellFormed
import Solcore.Test.SourceCoreGeneralizedExportMaterializedProfile

/-! All finite observations concern the unchanged complete three-function
program. No target execution is used to construct typing or source shapes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

structure Observed where
  fixture : ProfiledFixture
  cache : ObservedCache fixture.original fixture.original.recipe.compiled.indexed.base.functions
  make : Row fixture.original
  makeShape : MakeShape make.original.function.typedBody
  makeProfile : MaterializedRow fixture.original make
  makeResult : make.original.function.inferredBodyType = .product (.function .word .word) (.function .bool .bool)
  capture : Row fixture.original
  captureShape : CaptureShape capture.original.function.typedBody
  captureProfile : MaterializedRow fixture.original capture
  captureResult : capture.original.function.inferredBodyType = .function .bool .word
  tick : Row fixture.original
  tickShape : TickShape tick.original.function.typedBody
  tickResult : tick.original.function.inferredBodyType = .bool
  typing : OriginalTyping fixture.original
  callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observe : IO Observed := do
  let fixture ← compileProfiledFixture
  let cache ← observeCache fixture.original fixture.original.recipe.compiled.indexed.base.functions
  let make ← observeRow fixture.original "make"
  let makeProfile ← observeMaterializedRow fixture.original make
  let makeShape ← observeMake make.original.function.typedBody
  let ⟨makeResult⟩ ← observed
    (make.original.function.inferredBodyType = .product (.function .word .word) (.function .bool .bool))
    "make original result type"
  let capture ← observeRow fixture.original "capture"
  let captureProfile ← observeMaterializedRow fixture.original capture
  let captureShape ← observeCapture capture.original.function.typedBody
  let ⟨captureResult⟩ ← observed (capture.original.function.inferredBodyType = .function .bool .word)
    "capture original result type"
  let tick ← observeRow fixture.original "tick"
  let tickShape ← observeTick tick.original.function.typedBody
  let ⟨tickResult⟩ ← observed (tick.original.function.inferredBodyType = .bool) "tick original result type"
  let typing ← observeOriginalTyping fixture.original
  let ⟨callableProfile⟩ ← observed
    (fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true)
    "generalized export actual callable profile"
  return ⟨fixture,cache,make,makeShape,makeProfile,makeResult,capture,captureShape,captureProfile,captureResult,
    tick,tickShape,tickResult,typing,callableProfile⟩

end Tests.SourceCoreGeneralizedExport
