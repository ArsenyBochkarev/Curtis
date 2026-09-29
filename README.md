# Curtis

Curtis is a small explicit-state model checker for [TVL](https://github.com/ArsenyBochkarev/TVL) language written in Lean 4. It operates on TVL IR and checks temporal properties over all of its states.

Curtis reads `.tvir` files — the IR dumps produced by the [TVL](https://github.com/ArsenyBochkarev/TVL) translator. It creates the model from them and checks every spec the dump carries.

## Supported temporal logics

- **LTL** (`Engine/LTL.lean`) — builds the product of the program with a Büchi automaton constructed from negated initial formula and runs a nested DFS over it. An accepting cycle is a counterexample lasso. Comes with a Partial Order Reduction optimization.
- **CTL** (`Engine/CTL.lean`) — explores the full state graph with a DFS, then labels it bottom-up: backward BFS for `EU`, Kosaraju's SCCs for `EG`

For detailed description of specification language, see the [`docs/specifications`](https://github.com/ArsenyBochkarev/TVL/tree/main/docs/specifications) of the TVL repo.

## Installation (Linux)
After Curtis build, you can either run the installation script:

```bash
lake run install      # writes the ~/.local/bin/curtis wrapper
lake run uninstall    # removes it
```

or write the wrapper by hand (into `~/.local/bin/curtis`, then `chmod +x` it):

```bash
#!/bin/bash
exec /path/to/Curtis/.lake/build/bin/curtis "$@"
```

## Usage

```bash
curtis [--debug] [--dot FILE] [--channel-size N] <input.tvir>
  --debug             model summary, expanded formulas and state counts on stderr
  --dot FILE          also write the state graph as DOT (counterexample highlighted)
  --channel-size N    bound each message queue to N messages (default: 10);
                      a send into a full queue blocks until it drains
  --help              print this help and exit
```

## Building from scratch for the first time
```bash
lake exe cache get              # this might take some time
lake build                      # build the library and the executable
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

## Run tests

```bash
lake test -- all      # run all tests (Unit + E2E)
lake test -- Unit     # only unit tests
lake test -- E2E      # only end-to-end tests
```
