/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# External-parser proof-rule registry

`triptych_parser` is the backend-neutral registry used by Triptych's static external-parser
automation. A parser backend extends it by proving a successful-path equivalence and tagging that
theorem with `@[triptych_parser]`.

The registry is declared in its own module because Lean custom simp attributes must be initialized
before declarations can be added to them.
-/

/-- Successful-path rewrite rules used by `triptych_sound`. -/
register_simp_attr triptych_parser
