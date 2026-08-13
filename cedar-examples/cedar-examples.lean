import Outputs.Decimal.parser
import Outputs.Duration.parser
import Outputs.Datetime.parser
import Outputs.IPv4.parser
import Outputs.IPv6.parser

/-!
This is the default lean4web buffer for the Triptych Cedar examples.
Use the Examples menu to open the complete Decimal, Duration, Datetime, IPv4, or IPv6 source.
-/

#eval CedarExamples.Decimal.Decimal.parse "-12.34"
#eval CedarExamples.Duration.Duration.parse "1d2h30m"
#eval CedarExamples.Datetime.Datetime.parse "2024-01-15T10:30:45.123Z"
#eval CedarExamples.IPv4.IPv4.parse "8.8.8.8/24"
#eval CedarExamples.IPv6.IPv6.parse "2001:db8::1"
