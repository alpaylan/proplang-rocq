# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Property-Based Testing (PBT) benchmark framework comparing testing strategies across Rocq/Coq and Haskell. The project implements PropLang, a domain-specific language for expressing and testing properties with multiple generation and fuzzing strategies.

## Build Commands

### Rocq/Coq Workloads

Build a workload (e.g., BSTProplang):
```bash
cd workloads/Rocq/BSTProplang
./build           # Generates Makefile from _CoqProject and runs make
./build -c        # Clean before build
./build -i        # Install after build
```

The build script runs:
1. `coq_makefile -f _CoqProject -o Makefile`
2. `make`

Build test runners for specific strategies:
```bash
./build_generator BespokeGenerator    # Build generator-based strategy
./build_fuzzer TypeBasedFuzzer        # Build fuzzer-based strategy
```

Run tests:
```bash
./BespokeGenerator_test_runner.native InsertPost
```

### Haskell (quick-cover)

```bash
cd workloads/Haskell/quick-cover
stack build
stack test
```

## Architecture

### PropLang Framework (`workloads/Rocq/Lib/`)

The core property testing DSL with these key components:

- **PropLang.v**: Core property language with `CProp` type representing contextual properties
  - `ForAll`, `ForAllMaybe`: Universal quantifiers with generators/mutators/shrinkers
  - `Check`, `Implies`: Property assertions and preconditions
  - `generate_and_run`, `mutate_and_run`: Test execution strategies

- **loops/**: Testing loop implementations
  - `FuzzLoop.v`: Mutation-based fuzzing with seed pools
  - `CoverageLoop.v`: Coverage-guided testing with instrumentation feedback
  - `TargetLoop.v`: Target-based search
  - `ParLoop.v`: Parallel testing
  - `PerfFuzzLoop.v`: Performance-aware fuzzing

- **seedpool/**: Seed pool data structures for fuzzing
  - `Heap.v`: Leftist heap (priority-based selection)
  - `Queue.v`: FIFO/FILO queues
  - `SeedPool.v`: Unified seed pool interface with energy levels

### Workload Structure (`workloads/Rocq/<Workload>/`)

Each workload follows this structure:
```
<Workload>/
├── Src/
│   ├── Impl.v        # Data structure implementation with mutations
│   └── Spec.v        # Properties to test
├── Strategies/
│   ├── BespokeGenerator.v           # Custom generators
│   ├── TypeBasedGenerator.v         # Type-directed generation
│   ├── SpecificationBasedGenerator.v # Spec-driven generation
│   ├── BespokeFuzzer.v              # Custom mutation-based
│   └── TypeBasedFuzzer.v            # Type-directed fuzzing
├── Runners/
│   └── *_test_runner.v    # Executable test entry points
├── _CoqProject            # Coq build configuration
├── build                  # Build script
├── build_generator        # Strategy-specific builder
└── build_fuzzer           # Fuzzer-specific builder
```

### Test Configuration (`tests/`)

JSON files define benchmark tasks:
```json
{
  "language": "Rocq",
  "workload": "BST",
  "mutations": ["insert_1"],
  "trials": 10,
  "timeout": 60,
  "tasks": [{ "strategy": "BespokeGenerator", "property": "InsertPost" }]
}
```

### Workflow Configuration (`workloads/Rocq/steps.json`)

Defines setup/build/test pipeline stages and strategy tags (generator vs fuzzer).

## Key Patterns

### Adding a New Property

1. Define the property in `Src/Spec.v` as a `CProp` expression
2. Add it to the relevant strategy files in `Strategies/`
3. Reference it in the test runner

### Adding a New Strategy

1. Create `Strategies/<StrategyName>.v` defining `cprop_<PropertyName>` definitions
2. Create `Runners/<StrategyName>_test_runner.v` with extraction directives
3. Add to `_CoqProject`
4. Add tag in `steps.json` (generator or fuzzer)

### Mutation Testing

Mutations are defined in `Impl.v` (e.g., `insert_1`, `insert_2`, `insert_3` for BST). The `variables.json` files configure which mutations to test.

## Dependencies

- **Rocq/Coq 8.20.0+** with QuickChick library
- **OCaml** toolchain for native extraction
- **Stack** for Haskell builds (resolver: lts-16.24)
- **Python 3** with benchtool for benchmark orchestration
