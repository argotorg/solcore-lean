import Solcore.Test.SourceCoreGeneralizedBodyExpressionFixture
import Solcore.Test.SourceCoreMixedImperativeTyping

/-! The duplicate/captured/numeric regression shares the original declarative typing observer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedBodyExpression
abbrev BodyTyping := Tests.SourceCoreMixedImperative.BodyTyping
abbrev observeBodyTyping := Tests.SourceCoreMixedImperative.observeBodyTyping
end Tests.SourceCoreGeneralizedBodyExpression
