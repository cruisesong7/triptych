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

import Triptych.Reference.Decoder
import Triptych.Reference.DecodeLemmas
import Triptych.Reference.DecodeRepLemmas
import Triptych.Reference.ScannerProfile

/-!
# Reference semantics

The materializing reference decoder is the semantic anchor of every generated parser theorem:
`scan_eq_decode` connects the runtime scanner to it, and `decodeSome_iff_IsWf` connects it to the
readable grammar denotation. Generated parsers never execute it. This umbrella module exposes the
decoder, its capture-preserving proof lemmas, and proof-only scanner profiles for verification,
diagnostics, and benchmarks.
-/
