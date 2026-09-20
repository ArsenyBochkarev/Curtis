# Curtis

Curtis is a small model checker for [TVL](https://github.com/ArsenyBochkarev/TVL) language written in Lean 4. It operates on TVL IR and checks temporal properties over all of its states.

Curtis reads `.tvir` files — the IR dumps produced by the [TVL](https://github.com/ArsenyBochkarev/TVL) translator. It creates the model from them and checks every spec the dump carries.

## Supported temporal logics

- **LTL** (`Engine/LTL.lean`) — builds the product of the program with a Büchi automaton constructed from negated initial formula and runs a nested DFS over it. An accepting cycle is a counterexample lasso. Comes with a Partial Order Reduction optimization.
- **CTL** (`Engine/CTL.lean`) — explores the full state graph with a DFS, then labels it bottom-up: backward BFS for `EU`, Kosaraju's SCCs for `EG`. A failed property gets a witness trace, and the labeled graph can be dumped to a Graphviz `.dot` file with the counterexample path highlighted.

For detailed description of specification language, see the [`docs/specifications`](https://github.com/ArsenyBochkarev/TVL/tree/main/docs/specifications) of the TVL repo.

## Usage

```
usage: curtis [--debug] [--dot FILE] [--channel-size N] <input.tvir>
  --debug             model summary, expanded formulas and state counts on stderr
  --dot FILE          also write the state graph as DOT (counterexample highlighted)
  --channel-size N    bound each message queue to N messages (default: 10);
                      a send into a full queue blocks until it drains
```

```bash
lake build                      # build the library and the executable
lake exe curtis Examples/simple.tvir
# [ltl] FinishingProperty: HOLDS
# [ltl] RecoveryProperty_R2_fail_send_0: HOLDS
# [ltl] FinishDuplicate: HOLDS
# [ltl] RecoveryProperty_R2_fail_send_0: HOLDS
# [ctl] CanFinish: HOLDS

lake exe curtis Examples/loop.tvir        # a VIOLATED spec + a lasso counterexample
lake exe curtis --dot graph.dot Examples/simple.tvir   # state graph as Graphviz DOT
```

## Correctness proofs
TODO

## Layout

```
Main.lean       the curtis CLI
TVL/            IR semantics, atomic propositions, LTL/CTL syntax, DOT export
 └──TVIR/       .tvir parsing: the document scanner and the spec frontend
Engine/         LTL and CTL checking algorithms
Opts/           partial order reduction
Test/           unit and end-to-end tests
Examples/       sample .tvir dumps
```

## Building and testing

Requires the Lean toolchain pinned in `lean-toolchain`

```bash
lake build            # build the library and the executable

lake test -- all      # run all tests (Unit + E2E)
lake test -- Unit     # only unit tests
lake test -- E2E      # only end-to-end tests
```

Mathlib is fetched automatically on the first build.
