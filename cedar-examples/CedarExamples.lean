import Inputs.Decimal
import Outputs.Decimal.spec
import Outputs.Decimal.parser
import Outputs.Decimal.soundness
import Proofs.Decimal.RuleRegistrySoundness
import Inputs.Duration
import Outputs.Duration.spec
import Outputs.Duration.parser
import Outputs.Duration.soundness
import Inputs.Datetime
import Outputs.Datetime.spec
import Outputs.Datetime.parser
import Outputs.Datetime.soundness
import Inputs.IPv4
import Outputs.IPv4.spec
import Outputs.IPv4.parser
import Outputs.IPv4.soundness
import Proofs.IPv4.GrammarView
import Inputs.IPv6
import Outputs.IPv6.spec
import Outputs.IPv6.parser
import Outputs.IPv6.soundness
import Proofs.IPv6.GrammarView
import Proofs.Datetime.ComponentView

/-!
# Cedar examples

Worked formats, generated artifacts, parser-validation obligations, component views, and
conformance tests. This companion package is intentionally separate from Cedar-free Triptych
core; its Lake manifest owns the optional cedar-lean dependency.
-/
