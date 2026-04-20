# ROSE
ROSE is a state-variable-driven symbolic execution framework. Instead of treating raw command-line input strings as symbolic, ROSE shifts symbolic analysis to the core program state variables that actually govern behavior. ROSE is built on top of KLEE.

## Setup
### Build ROSE
ROSE is built with CMake. The following dependencies are required:
- LLVM 13.0.1 (with clang)
- Z3

A build script is provided at `scripts/build.sh`. Fill in the paths then run the script from the `scripts/` directory:
```bash
cd scripts
./build.sh
```

### Prepare Benchmarks
The `benchmarks/` directory contains zip archives of the benchmark program source code. To prepare the `.bc` files required by ROSE:

1. **Unzip** the archive for each benchmark:
   ```bash
   unzip benchmarks/<program>.zip -d benchmarks/<program>
   ```

2. **Build with `wllvm`** to produce a whole-program LLVM bitcode file. Install `wllvm` first if needed (`pip install wllvm`), then configure and build with `clang` as the compiler:
   ```bash
   cd benchmarks/<program>
   CC=wllvm CXX=wllvm++ ./configure   # or cmake -DCMAKE_C_COMPILER=wllvm ...
   make
   ```

3. **Extract the `.bc` file** from the compiled binary:
   ```bash
   extract-bc <binary>
   ```
   This produces `<binary>.bc`, which is the bitcode file to pass to ROSE.

## Usage
* Basic usage

  ```
  rose --libc=uclibc --posix-runtime --solver-backend=z3 --search=rose <.bc>
  ```

* For additional options, refer to the [KLEE documentation](https://klee-se.org/)

## Main Repository Structure

```
ROSE/
├── llm/                          
│   ├── repo_analyzer.py          # LLM-Powered Semantic Analyzer
│   └── prompts/                  # LLM prompt templates
│       ├── query-core-svs.txt    # Prompt: extract core state variables
│       ├── query-effects.txt     # Prompt: extract how options affect core state variables
│       ├── query-options.txt     # Prompt: extract CLI options
│       ├── query-location.txt    # Prompt: locate the symbolization site
│       ├── query-entry.txt       # Prompt: identify the program entry
│       └── feedback.txt          # Prompt: iterative feedback loop
│
└── klee/                         # State-Variable-Driven Symbolic Executor (modified KLEE)
    └── lib/
        └── Core/
            └── Executor.cpp      # Main executor
```

## Benchmarks
Benchmark archives are provided in the `benchmarks/` directory.

|           |           |            |            |           |
|-----------|-----------|------------|------------|-----------|
| bc        | bsdtar    | cmark      | gawk       | grep      |
| jpegoptim | nm        | pdftops    | pdftotext  | sed       |
| speexdec  | tiffcp    | tree       | xmlcatalog | xmllint   |

## License
The KLEE code uses the [KLEE Release License](https://github.com/klee/klee/blob/master/LICENSE.TXT) and the ROSE code uses GPL-3.0 license.