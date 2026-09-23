# Archived Verus runtime

`RuntimeProgram.rs.in` is the retired bytecode-style parser runtime kept for design history.

The production backend no longer imports or emits this file. It emits the source-faithful direct
scanner embedded from `Triptych/Backend/Verus/RuntimeParser.rs.in`.
