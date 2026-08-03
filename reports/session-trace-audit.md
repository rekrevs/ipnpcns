# Session-Trace Audit for the Formalization History

## Scope

The Codex session trace materially changes what can be said about abandoned proof
attempts. The Wotan logs summarize completed work, and Git preserves selected durable
states. The session trace additionally preserves the tool-mediated editing and
compiler-feedback loop, including scratch files later removed from the working tree.

This audit uses the main CLI session, not the smaller guardian sidecar. The source is
external to the repository:

```text
~/.codex/sessions/2026/08/03/
rollout-2026-08-03T17-08-12-019fc82b-0c51-7ca0-b4a9-ebc331a426a7.jsonl
```

The session metadata identifies:

- session id `019fc82b-0c51-7ca0-b4a9-ebc331a426a7`;
- originator `codex-tui`, source `cli`, version `0.146.0`;
- working directory `/Users/sverker/repos/ipnpcns`;
- start timestamp `2026-08-03T15:10:21.863Z`.

The audited immutable prefix is the first 6,276 JSONL records, ending at
`2026-08-03T21:13:08.987Z`. It contained 50,164,906 bytes when selected. Its SHA-256
is:

```text
80e1b5977d4ff07fbfc696f319eb2a31db33d57636464e20b81d1063ba763ba5
```

The digest is reproducible even though the live session file subsequently grows:

```text
head -n 6276 <session-log> | shasum -a 256
```

## What was and was not inspected

The audit inspected session metadata, user and agent messages, tool-call names and
timestamps, command and patch inputs, command outputs, compiler diagnostics, and
`patch_apply_end` events. It did not inspect or reproduce model-internal `reasoning`
records. Raw log payloads were not copied into the repository, and unrelated or
potentially sensitive content was not included in report artifacts.

The audited prefix contains 4,317 response items and 1,916 event messages. The
observable event subset includes 108 agent updates, 427 successful patch-completion
events, 15 completed web searches, 12 context-compaction events, and the seven owner
messages received through the cutoff. These are instrumentation counts, not measures
of theorem difficulty or proof quality.

## Preservation of scratch work

Every one of the 427 recorded patch-completion events succeeded. For an added file,
the event records its full content; for an update, it records a unified diff; for a
move or deletion, it records the corresponding state transition. Tool outputs retain
the associated Lean diagnostics, and call identifiers connect inputs to outputs.

Within the audited prefix there are 174 patch change-events across 33 scratch, probe,
or axiom-audit files:

| Change kind | Count |
|---|---:|
| Addition | 34 |
| Update | 128 |
| Deletion | 12 |
| **Total** | **174** |

The largest scratch histories are not present in the final tree but remain
reconstructible from the trace:

| Scratch or probe | Recorded patch events | Role |
|---|---:|---|
| `ScratchT17.lean` | 33 | Exact Hann-window Fourier integrals, `L2` lifting, and NNLS examples |
| `ScratchT18.lean` | 26 | Kernel analysis operator, finite-rank approximation, and causal Volterra filter |
| `ScratchT20.lean` | 15 | Exponential membrane kernel, exact integral decomposition, and quadratic remainder |
| `/private/tmp/nnls-proto.lean` | 13 | Loss expansion, directional derivative, KKT equivalence, and contraction iteration |
| `/private/tmp/gram-proto.lean` | 12 | Active Gram expansion and exact off-diagonal counting |
| `/private/tmp/check-ipnpcns.lean` | 11 | Focused mathlib API and theorem-name probes |
| `ScratchT25.lean` | 9 | Independent two-message occupancy experiment |
| `ScratchT16.lean` | 6 | Rank-deficient Fejer and compactness convergence route |
| `ScratchT19.lean` | 5 | Cone-projection homogeneity and span reduction |
| `TmpCheck.lean` | 4 | Subspace and product-space typeclass probes |
| `ScratchT21.lean` | 3 | Exponential occupancy error estimate |

The trace records `ScratchT17.lean` moving into
`IPNPCNS/Examples/OrthonormalWavelets.lean` at `19:06:47Z`, `ScratchT18.lean` moving
into `IPNPCNS/Signal/Volterra.lean` at `19:39:56Z`, and `ScratchT20.lean` moving into
`IPNPCNS/Signal/Membrane.lean` at `20:01:35Z`. The apparently clean permanent modules
therefore have recoverable prehistories rather than appearing fully formed.

## Selected error-correction chains

The following chains are selected because they changed proof structure, exposed a
mathematical boundary, or illustrate the actual scratch-to-module workflow. Ordinary
syntax and local simplifier repairs are present in the trace but are not individually
retold in the report.

### Library probe and dependency recovery

The first probe was added at `15:23:31Z`. Its attempted check of
`ContinuousLinearMap.singularValues` was corrected at `15:24:02Z` to the actual
`LinearMap.singularValues` API. Later, dependency materialization failed with a DNS
error from `curl` (`call_MsEYLwOn28IKQ4c7JS8YqjTh`) and two Git exit-code-128
failures. The project recovered from the installed version-matched mathlib cache and
fetched only the missing pinned dependency. This is a technical recovery, not a
mathematical change.

### Moreau and double rejection

The permanent cone modules were edited directly. The trace retains a failed rewrite
in `MetricProjection.lean` at `15:48:16Z`, an unavailable theorem identifier in
`Moreau.lean` at `15:49:14Z`, a failed linear-arithmetic closure at `15:49:25Z`, and
an application mismatch in `Operations.lean` at `15:51:15Z`. The contemporaneous
update at `15:51:45Z` then reports the full Moreau, bipolar, closure-safe operation,
and double-rejection stack compiling. The sequence shows local API and elaboration
repairs inside a proof architecture that remained stable.

### Sparse Gram proof

`/private/tmp/gram-proto.lean` received 12 patches between `16:21:27Z` and
`16:26:51Z`. Diagnostics include an unavailable `inner_sum_left`, a failed
`Finset.sum_congr` application, a coercion failure under `mod_cast`, and unresolved
goals in the off-diagonal estimate. The completed argument did not route through
eigenvalues. It expanded the active quadratic form and counted ordered pairs with
`2 |x_i x_j| <= x_i^2 + x_j^2`, preserving the source constant `k-1`.

### NNLS optimality and convergence prototype

`/private/tmp/nnls-proto.lean` received 13 patches, accompanied by 11 focused API
probes. The trace records failed attempts to use unavailable derivative combinators,
rewrite failures in the loss expansion, and type mismatches in the convergence tail.
The surviving route first established an exact finite loss-increment identity, then
derived the directional derivative and KKT equivalence, and only afterward added the
iteration theorem under a named contraction predicate. This is stronger historical
evidence for decomposition than the polished final modules alone provide.

### Moore-Penrose construction

`IPNPCNS/Subspace/MoorePenrose.lean` was patched 25 times. The trace includes a
missing orthogonal-membership theorem, several dependent-motive rewrite failures, and
unsolved projector equalities between `18:12Z` and `18:26Z`. No scratch file hides
this path: the successive permanent-module diffs are present. The eventual
effective-map construction avoided an SVD and used extensional equality to cross the
dependent projector-instance boundary.

### Exact wavelets

`ScratchT17.lean` is the richest discarded proof record. It begins with unavailable
integral theorem names and a deterministic elaboration timeout. Later diagnostics
track interval-integrability obligations, product-to-sum rewrites, Gram entries,
`L2` representatives, and the NNLS examples. After 33 patches, test-prefixed names
were mechanically normalized and the complete file was moved into its permanent
module. The trace also preserves the earlier false alarm that the normalization
constant might be wrong; rendered-formula inspection and exact integration resolved
the issue without changing the paper's constant.

### Compact causal convolution

`ScratchT18.lean` encountered stuck typeclass inference, rewrite failures, and a
deterministic `whnf` heartbeat timeout at `19:24:14Z`. Increasing the heartbeat limit
did not by itself provide the final architecture. The proof was reorganized around a
general kernel-to-operator map, simple-function density, explicit rank-one operators,
and norm-closedness of compact operators. Once the prefix-kernel and norm estimates
compiled, the scratch file moved to `Signal/Volterra.lean`. This is an actual change
of proof route, not just syntax repair.

### Later exactification tasks

The trace retains five patches for span reduction, 15 for the membrane theorem, three
for the exponential occupancy bound, and nine for the product-overlap theorem. In the
membrane scratch proof, failed algebraic normalization and implicit-parameter
inference were resolved before the exact integral decomposition compiled. In the
two-message proof, direct unfolding of structure predicates failed; changing the
goals to the literal finite-expectation equalities exposed the Cartesian-product
factorization used by the final theorem.

### Audit and report loops

The source-wide axiom audit first raced the build and observed a missing wavelet
object file. A later run corrected five temporary endpoint namespace spellings and
passed. The scientific report then recorded a failed first LaTeX compilation and ten
source patches. Rendered-page inspection found title-band clipping, an unnecessarily
sparse contents page, and misleading dynamic headers; each defect was corrected
before the PDF was frozen.

## Consequences for the historical report

The session trace supports three claims that Git and Wotan cannot support alone:

1. **Discarded code is substantially recoverable.** The scratch files were removed
   from the final tree, but their additions, successive diffs, compiler diagnostics,
   and migrations remain in the session prefix.
2. **Not every failure had the same status.** Missing theorem names and tactic
   mismatches were local engineering failures; rank-deficient contraction was a
   mathematical obstruction; the Volterra proof underwent an architectural change;
   source and PDF findings were verification and communication corrections.
3. **The clean commit history is a curated endpoint sequence.** The session trace
   exposes the much denser compiler-guided search between those endpoints.

It would still be too strong to call the trace a complete record of cognition or of
all process state. It does, however, invalidate the earlier blanket statement that no
record preserves abandoned tactics or scratch proofs. For this session's
tool-mediated edits, there is an unusually detailed and cryptographically bounded
record.

## Reproducibility notes

Useful read-only extraction patterns are:

```text
# Patch targets and change kinds
head -n 6276 <session-log> |
  jq -r 'select(.type == "event_msg" and
                .payload.type == "patch_apply_end") |
         .payload.changes | to_entries[] |
         [.key, .value.type] | @tsv'

# Tool outputs containing Lean diagnostics
head -n 6276 <session-log> |
  jq -r 'select(.type == "response_item" and
                .payload.type == "custom_tool_call_output") |
         .payload.output'
```

The report cites the curated findings in this audit rather than embedding the raw
50 MB session prefix.
