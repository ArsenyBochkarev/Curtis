# Curtis

Curtis is a small model checker for [TVL](https://github.com/ArsenyBochkarev/TVL) language written in Lean 4. It operates on TVL IR and checks temporal properties over all of its states.

**Warning**: the TVL IR output format is still under construction, so no parser currently is implemented.

## Supported temporal logics

- **LTL** — with a Partial Order Reduction optimization
- **CTL**

## Correctness proofs
TODO

## Layout

```
Main.lean       demo executable entry point
TVL/            IR semantics, atomic propositions, LTL/CTL syntax, DOT export
Engine/         LTL and CTL checking algorithms
Opts/           partial order reduction
Test/           unit and end-to-end tests
```

## Building and testing

Requires the Lean toolchain pinned in `lean-toolchain`

```bash
lake build            # build the library and the executable
lake exe curtis  # TODO

lake test -- all      # run all tests (Unit + E2E)
lake test -- Unit     # only unit tests
lake test -- E2E      # only end-to-end tests
```

Mathlib is fetched automatically on the first build.
