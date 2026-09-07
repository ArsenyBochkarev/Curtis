# Curtis

Curtis is a small model checker for [TVL](https://github.com/ArsenyBochkarev/TVL) language written in Lean 4. It operates on TVL IR and checks temporal properties over all of its states.

**Warning**: the TVL IR output format is still under construction, so no parser currently is implemented.

## Supported temporal logics

- **LTL** (`Engine/LTL.lean`) — builds the product of the program with a Büchi automaton constructed from negated initial formula and runs a nested DFS over it; an accepting cycle is a counterexample lasso (prefix + loop). Comes with a Partial Order Reduction optimization.
- **CTL** (`Engine/CTL.lean`) — explores the full state graph with a DFS, then labels it bottom-up: backward BFS for `EU`, Kosaraju's SCCs for `EG`. A failed property gets a witness trace, and the labeled graph can be dumped to a Graphviz `.dot` file with the counterexample path highlighted.

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
