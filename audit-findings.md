# Proof Audit - `dafny_examples`

**Date:** 2026-07-03  
**Scope:** all 60 `.dfy` files, README, and GitHub Actions CI.

## TL;DR

- Full verification is green: every `.dfy` file verifies with `--verification-time-limit 30`.
- Runtime tests are green: all 7 files containing `{:test}` pass `dafny test --verification-time-limit 30` when run per file.
- The previous audit was useful but stale. Its two HIGH findings and the concrete medium/low spec/comment issues have now been fixed.
- A second return-contract escape-hatch sweep found one additional low-severity issue in `0167-two-sum-ii.dfy`; it has also been fixed.
- There are no remaining known unscoped escape-hatch contracts in the LeetCode or library corpus.

## Method

This redo added a mechanical pass that the earlier audit did not apply consistently:

- Every method returning a value was scanned for sentinel/range escape hatches.
- Guarded postconditions of the form `returned_value condition ==> ...` were checked for a separate range/sentinel postcondition.
- Pair-returning two-sum methods were checked for fully specified failure sentinels.
- `{:axiom}` and `assume` sites were scanned.
- Comments and README claims were checked against current specs, CI, and examples.
- Concrete `{:test}` files were run through `dafny test`; all `.dfy` files were run through `dafny verify`.

## Verification

Commands run locally:

```powershell
$files = @(rg --files -g "*.dfy")
foreach ($f in $files) {
  & 'C:\Users\shaob\dafny-4.11.0\dafny\Dafny.exe' verify --verification-time-limit 30 $f
}

$tests = @(rg -l -F "{:test}" -g "*.dfy")
foreach ($f in $tests) {
  & 'C:\Users\shaob\dafny-4.11.0\dafny\Dafny.exe' test --verification-time-limit 30 $f
}
```

Results:

- `dafny verify`: all 60 `.dfy` files passed with 0 errors.
- `dafny test`: all 7 test-bearing files passed.
- `git diff --check`: passed.

## Findings Fixed In This Pass

### High severity escape hatches

| Location | Previous issue | Fix |
|---|---|---|
| `leetcode/0277-find-the-celebrity.dfy` | `findCelebrity` only constrained `r` under guards, so out-of-range values such as `-2` or `n` satisfied the contract vacuously. | Added `ensures r == -1 || 0 <= r < n`. |
| `leetcode/1492-kthfactor.dfy` | `r == 0` could evade the biconditional specs even when the k-th factor exists. | Added `ensures r == -1 || r > 0`. |

### Medium/low spec gaps

| Location | Previous issue | Fix |
|---|---|---|
| `leetcode/0001-two-sum.dfy` | No-solution case did not pin `r.1`; comment said the map kept the earliest complement even though repeated keys overwrite. | Added `ensures r.0 == -1 ==> r.1 == -1`; corrected comment to latest equal-valued complement. |
| `leetcode/0167-two-sum-ii.dfy` | Redone audit found the same no-solution sentinel gap for `r.1`. | Added `ensures r.0 == -1 ==> r.1 == -1` and strengthened `CaseShape`. |
| `leetcode/0155-min-stack.dfy` | `Pop()` updated stack state but did not specify the returned value. | Added `ensures val == old(dataSeq)[0]`. |
| `test_shuffle.dfy` | `in_set_of_seq` and `subset_set_of_seq` were trusted `{:axiom}` lemmas. | Replaced them with proof bodies. |
| `test_modules.dfy` | Scratch random methods were trusted `{:axiom}` declarations. | Replaced them with deterministic bodies satisfying the same bounds. |
| `getRandomDataEntry.dfy` | Root helper used an axiomatic bounded-choice method. | Replaced it with a deterministic representative body. |
| `getAllShuffledDataEntriesWithAvoidSet.dfy` | Root helper used an axiomatic bounded-choice method. | Replaced it with a deterministic representative body. |

### Comment/README corrections

| Location | Previous issue | Fix |
|---|---|---|
| `README.md` | CI section only mentioned `dafny verify` and omitted `dafny test` and the explicit 30-second Dafny verification limit. | Updated CI paragraph. |
| `leetcode/0226-invert-binary-tree.dfy` | Comment overstated the in-order reversal lemma as a full structural characterization. | Reworded it as a corroborating property; structural definition is `Mirror`. |
| `leetcode/0772-basic-calculator-iii.dfy` | Comments around AST lemmas sounded like parser theorems. | Reworded them as Eval facts for AST shapes. |
| `leetcode/0772-basic-calculator-iii.dfy` | Examples did not pin multi-digit parsing or left associativity. | Added `Calculate("12+3") == 15` and `Calculate("8-4-2") == 2`. |
| `leetcode/0123-stocks-iii.dfy` | Comment said `s1 < b2`; spec/proofs use `s1 <= b2`. | Corrected comment. |
| `lib/math/Factors.dfy` | Stale comment mentioned an old unproved `{:axiom}` and triggered audit scans. | Reworded comment. |

## Current Scoped Limitations

These are not hidden bugs; they are deliberately scoped and documented limits of what the repo proves.

| Area | Current status |
|---|---|
| `leetcode/0407-trapping-rain-water-ii.dfy` | Heap flood implementation proves safety, termination, nonnegative output, and exact boundary-only equivalence. Full arbitrary-grid equivalence to the denotational escape-level spec is not claimed. The exact denotational solution lives in `0407-trapping-rain-water-ii-correct.dfy`. |
| `leetcode/0004-median-two-sorted-arrays.dfy` | Implementation is algorithmically binary partition search, but the repo proves value correctness only, not a formal cost theorem. |
| `leetcode/0146-lru-cache.dfy` | Proves behavioral LRU correctness using a sequence model, not the LeetCode O(1) cost contract. |
| `lib/adt/PriorityQueue.dfy` | Proves heap/order behavior, not an asymptotic cost or balance theorem. |
| Random/shuffle examples | Now use executable deterministic representatives of bounded choice. They do not claim probabilistic randomness, independence, or uniformity. |
| `leetcode/0312-burst-balloons.dfy` | Public spec is tied to a physical last-burst recurrence. The separate first-burst enumerator remains a sanity model, not a proved all-input equivalent public spec. |
| `leetcode/0772-basic-calculator-iii.dfy` | Parser is total/terminating and concrete examples exercise precedence, associativity, parentheses, division, and multi-digit parsing. There is still no general grammar soundness/completeness theorem. |

## Redone Audit Result

After the fixes above and the added escape-hatch pass:

- Open high findings: 0
- Open medium findings: 0
- Open low actionable findings: 0
- Live `{:axiom}` declarations: 0
- Live `assume` statements: 0 found by scan; remaining occurrences are comments.

The remaining items are explicit proof-scope limitations, not contradictions between code and claimed specs.
