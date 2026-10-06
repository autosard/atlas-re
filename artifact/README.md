# Artifact

This artifact consists of (1) a docker image bundling a pre-built version of the tool together with the example benchmark programs and (2) a copy of our Github source repo with frozen dependency versions to ensure reusability and reproducibility.

# Usage

First unzip the artifact. This produces a directory `artifact`, which we assume to be the base directory for the rest of the instructions.
```
unzip artifact.zip
cd artifact
```

The provided docker image `image.tar.gz` can be imported to docker as follows.
```
docker load -i image.tar.gz
```

We include the corresponding `Dockerfile` for reference, but it can be safely ignored for the tests. The image runs `atlas-re` directly, with the example programs (`/usr/share/atlas/examples`) on its search path, so all arguments after the image name are passed to the tool:
```
docker run --rm atlas-re:jar --help
docker run --rm atlas-re:jar analyze --help
```

# Smoke Test

The following smoke test type checks the annotated bounds of the splay heap benchmark and should finish within seconds.
```
docker run --rm atlas-re:jar analyze Heap.Splay
```
It should report `Proof found`. The exit code is 0 if a proof was found and 1 otherwise.

# Running the Analysis

Benchmarks are addressed by their module name, which corresponds to the file path below the examples directory, e.g. `Heap.Splay` for `Heap/Splay.atl`. A single function and its dependencies are analysed by appending its name, e.g. `Heap.Splay.insert`. The available benchmarks can be listed with
```
docker run --rm --entrypoint find atlas-re:jar /usr/share/atlas/examples -name '*.atl'
```
The modules below `Data` and `Potential` define data types and potential functions used by the benchmarks and are not benchmarks themselves.

## Type Checking

By default, the tool checks the bounds annotated in the example files:
```
docker run --rm atlas-re:jar analyze <module>
```

## Type Inference

With `--analysis-mode infer`, the tool infers the bounds from scratch, ignoring the annotations:
```
docker run --rm atlas-re:jar analyze --analysis-mode infer <module>
```

## Inspecting Proofs

For every run, the tool writes an HTML page with the derivation and the inferred bounds (or, if no proof exists, the unsatisfiable core) to `/work/out` inside the container. To keep it, mount a directory:
```
docker run --rm -v "$PWD/out:/work/out" atlas-re:jar analyze --analysis-mode infer Heap.Splay
```
and open `out/index.html` in a browser. Adding `--user "$(id -u):$(id -g)"` to any `docker run` command makes the written files owned by your user instead of root.

# Reproducing our Results

The script `bench.sh` runs all benchmarks, prints a summary and writes the inferred bound of every function to `bounds.tsv` in its results directory:
```
docker run --rm -v "$PWD/results:/work/bench-results" --entrypoint bench.sh atlas-re:jar --mode infer --timeout 7200
```
Use `--help` for further options, e.g. to restrict the run to some modules (`bench.sh --mode infer Heap SearchTree.Splay`).

<!-- TODO: hardware and measured running times of the evaluation -->

# Building the Image

The image can be rebuilt from the `Dockerfile`, which clones the tool and the examples from Github. The build arguments `ATLAS_REF` and `EXAMPLES_REF` select a branch or tag of the respective repository:
```
docker build -t atlas-re:jar --build-arg ATLAS_REF=jar --build-arg EXAMPLES_REF=atlas-revisited .
```

# Building the Tool Yourself

The sources for our tool are hosted on Github under the GPL-3.0 License, at the following URL: https://github.com/autosard/atlas-re/ .

*Requirements*:
- A working Haskell toolchain (GHC 9.6.7 and Cabal >= 3.12.1.0). The easiest way to set those up is [GHCup](https://www.haskell.org/ghcup/), which provides a one-line install for Linux, macOS, FreeBSD and WSL2.
- A recent z3 (>= 4.8, <= 4.15.4). z3 should be available in the package repositories for most distributions. Make sure that `libz3` is included.

## Build Bundle (recommended)

Instead of cloning the repository, you can use the provided copy of the source repo. It provides a `cabal.project.freeze` file, which freezes the dependencies to ensure reproducibility, and in contrast to the git repo it includes a tarball for the dependency `haskell-z3`. `haskell-z3` is packaged externally, because the version on Hackage is out of date (see https://github.com/IagoAbal/haskell-z3/issues/96).

## Build Steps

Build the tool with Cabal. This will pull the frozen versions of our dependencies from Hackage and will therefore require internet access.
```
cd source
cabal build
```

## Run the Tool

Once built, you can run it via Cabal:
```
cabal run -- atlas-re --search examples analyze --analysis-mode infer Heap.Splay
```

## (Optional) Install to PATH

```
cabal install
```
