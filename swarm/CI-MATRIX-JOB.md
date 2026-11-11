# The matrix job, if you want it at the job level

The submission gating is parallel *inside* `scripts/verify.py` (see below), which needed no workflow
change. A true matrix job — one runner per claimed route — cannot be added from this session: the
GitHub App behind the connected repository has no `workflows` permission, and pushes that touch
`.github/workflows/build.yml` are rejected. That is a boundary, not a bug to route around.

If you want the job-level version, paste this into `.github/workflows/build.yml` after the existing
`check` job. It reuses the same gate, so there is nothing to maintain twice.

```yaml
  # One runner per claimed route. The list is generated from swarm/submissions/MANIFEST.tsv, so
  # adding a claim adds a job and nothing else changes.
  claimed-routes:
    needs: check                     # only spend runners if the library itself is green
    runs-on: ubuntu-latest
    timeout-minutes: 45
    strategy:
      fail-fast: false
      matrix:
        submission:
          - m1.lean
          - m2.lean
          - m6.lean
          - m7.lean
          - signature-m4.lean
          - signature-m5.lean
          - signature-m6.lean
          - signature-m3.lean
          - signature-m1.lean
          - radical-m1.lean
          - radical-m3.lean
          - radical-m4.lean
          - radical-m5.lean
          - order5-m4.lean
          - order5-m2.lean
          - order5-m5.lean
          - order5-m3.lean
    steps:
      - uses: actions/checkout@v5
        with:
          persist-credentials: false
      - name: Free disk space
        run: sudo rm -rf /usr/share/dotnet /usr/local/lib/android /opt/ghc || true
      - name: Install the pinned Lean toolchain
        run: |
          set -euo pipefail
          curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$RUNNER_TEMP/elan-init.sh"
          bash "$RUNNER_TEMP/elan-init.sh" -y --default-toolchain "$(cat lean-toolchain)"
          echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
      - name: Resolve Mathlib at the pinned tag and fetch its cache
        run: |
          set -euo pipefail
          lake update
          lake exe cache get
      - name: Gate ${{ matrix.submission }}
        run: |
          set -euo pipefail
          lake build
          lake env python3 scripts/gate.py --submission "swarm/submissions/${{ matrix.submission }}" --partial
```

## What it costs and what it buys

Each matrix cell pays its own checkout, toolchain install and Mathlib cache download — currently
about four minutes before any Lean runs — against roughly twenty-five seconds of actual gating. So
the wall-clock gain is small, and the runner-minutes multiply by the number of cells: seventeen jobs
of about five minutes instead of one job of about eleven. **That is a worse trade than the parallel
version**, which is why the parallel version is what is implemented.

The case for the matrix job is isolation, not speed: a route that fails does so in its own job, with
its own log, and `fail-fast: false` means a broken claim does not hide the ten that still pass. If
that isolation is what you want, take the YAML above. If what you want is a faster run, the parallel
gating already in `verify.py` is the better answer, and it is measured: the submission step went from
232 s to 81 s on four workers and 131 s on two.

## The parallel gating that is implemented

`scripts/verify.py` gates the first manifested claim serially — that run fills the shared definition
cache in `verification/build` — then the rest concurrently, four at a time on a four-core machine,
`min(4, cpu_count)` otherwise, overridable with `COXETER_GATE_JOBS`. Each run gets its own scratch
directory and report file (`gate.py --work-dir`, `--report`), so parallel runs cannot collide on the
single `verification/work/Submission.lean` the serial version used.
