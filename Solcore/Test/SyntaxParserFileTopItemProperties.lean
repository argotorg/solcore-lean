import Solcore.Syntax.Parser.FileTopItemProperties

/-! External consumers for top-level wrapping and derive attachment. -/

namespace Tests

open Solcore.Syntax.Parser

example := @FileInternals.TopItemSpanAligned
example := @FileInternals.TopItemContract
example := @FileInternals.wrapImport_contract
example := @FileInternals.wrapExport_contract
example := @FileInternals.wrapPragma_contract
example := @FileInternals.wrapTypeAlias_contract
example := @FileInternals.wrapFunction_contract
example := @FileInternals.wrapEnum_contract
example := @FileInternals.wrapTrait_contract
example := @FileInternals.wrapImpl_contract
example := @FileInternals.wrapContract_contract
example := @FileInternals.extendTopItemStart_contract
example := @FileInternals.attachDeriveAttribute_reply_validFor
example := @FileInternals.attachDeriveAttribute_preservesTokenWindow
example := @FileInternals.attachDeriveAttribute_preservesTokensOnSuccess
example := @FileInternals.attachDeriveAttribute_cursorMonotoneOnSuccess
example := @FileInternals.attachDeriveAttribute_preservesDeriveStartOnSuccess

end Tests
