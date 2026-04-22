# Artifact Submission 

The artifact consists of (1) a docker image bundling a pre-built version of the tool together with a set of example benchmark programs and test scripts for functional evaluation (2) a copy of our Github source repo with frozen dependency versions to ensure reuseability and reproducablity. 

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

## Smoke Test

The following smoke test will type check one instance of the skew heap benchmark.

```
docker run --entrypoint smoke-test.sh artifact10
```

The script should return instantly and produce the following output:

```
Running: atlas-re --search /usr/share/atlas/examples/leftist-heaps analyze --analysis-mode check-coeffs  SkewHeap3over2
Analyzing module SkewHeap3over2(bal, meld, delete_min, insert, min) ...
Done. Saved proof to "file:///out/index.html"

potential functions:
	Tree Num: rk(e1)
	Tree Base: 
	List Base: 

bal:
	1/2 * log(|u| + |t|) - 1/2 * log(|u|)
delete_min:
	3/2 * log(|x|)
insert:
	3 + 1/2 * log(|x| + 2) + 1/2 * log(|x|)
meld:
	1/2 * log(|y| + |x| - 1) + 1/2 * log(|x|) + 1/2 * log(|y|)
min:
	0

where (e1,...,en) := f x1 ... xm
```

The amortised bounds for the different functions in the benchmark can be read of here. For example the function `meld` has a bound of `1/2 * log(|y| + |x| - 1) + 1/2 * log(|x|) + 1/2 * log(|y|)`. 

## Reproducing our results (Functional)

The script `full-test.sh` runs full type inference for all examples listed in the paper, reproducing Table 2. This mode infers the bounds of the functions without considering the any annotations. This is expected to take some time, since the SMT solver will optimise a large number of constraints (~ 14 hours on our machine). The benchmark `RankBiased` is the most expensive, taking roughly 10 hours alone. For an estimate on individual runtimes you can consult the evaluation metrics given in the next section.

```
docker run --entrypoint full-test.sh artifact10
```

### Evaluation Metrics

In the following we provide the number of assertions, runtime and process memory we obtained for our benchmarks. It was suggested by the reviewers to include these performance metrics, but the primary contribution that should be verified are the produced complexity bounds (Table 2). These metrics serve more as an orientation for anyone trying to reproduce our results. The second table additionally provides a description of the benchmarks, to make them more easily identifiable. The numbers were obtained with the dockerized artefact provided and ran on the following hardware:

CPU: AMD Ryzen 5 5600 6-Core
RAM: 16 GB
os: alpine 3.22 (Docker)
z3 version: 4.15.0


| Benchmark      | Number of assertions | Runtime  | Memory    |
|----------------|----------------------|----------|-----------|
| SkewHeapST     | 9429                 | 33s      | 365.4 MiB |
| SkewHeap2      | 6392                 | 40s      | 299.3 MiB |
| SkewHeap3over2 | 8809                 | 9m09s    | 834.7 MiB |
| SkewHeapGolden | 8797                 | 32m50s   | 917.8 MiB |
| WeightBiased   | 8996                 | 43m03s   | 912.0 MiB |
| WeightBiasedWC | 8097                 | 50s      | 384.6 MiB |
| RankBiased     | 11886                | 1h23m22s | 780.3 MiB |
| RankBiasedWC   | 6887                 | 11s      | 268.1 MiB |


| Benchmark      | Description                                               |
|----------------|-----------------------------------------------------------|
| SkewHeapST     | Skew heap with piece-wise potential Φ_[t<u]               |
| SkewHeap2      | Skew heap with sum-of-logs potential Φ_u                  |
| SkewHeap3over2 | Skew heap with sum-of-logs potential Φ_(-t)               |
| SkewHeapGolden | Skew heap with sum-oflogs potential Φ_ϕ                   |
| WeightBiased   | Weight-biased leftist heap with sum-of-logs potential Φ_ϕ |
| WeightBiasedWC | Worst-case analysis for weight-biased leftist heap        |
| RankBiased     | Rank-biased leftist heap with rank potential.             |
| RankBiasedWC   | Worst-case analysis for rank-biased leftist heap.         |
	
## Optional further tests

The smoke-test and full-test scripts utilise a wrapper script around the actual tool binary, that simplifies calling the tool and allows to list the available benchmarks:
```
docker run artifact10 list-examples
```
Optionally the reviewers might want to modify examples or or test them in isolation. The following example shows how access the example files in the docker image and how to invoke the wrapper script manually. 
```
> docker run -ti --entrypoint /bin/sh artifact10
# vi /usr/share/atlas/examples/leftist-heaps/SkewHeap2.ml
# wrapper.sh infer SkewHeap2
```

### Type Checking

In this mode the tool type checks the annotation present in example file,
```
docker run atlas-artifact check <example>
```
- `<example>` should be replaced with the name of a program from list-examples.
- This process is typically fast (seconds to minutes).

### Type Inference

Alternatively the tool can infer the type (amortised bounds) from scratch. 

```
docker run atlas-artifact infer <example>
```
This process is much more expensive computationally and can take hours on some benchmarks.

### Running the full tool (with arbitrary examples)

Please note that the wrapper script does not support all examples but only the ones relevant for the paper (subdirectory `leftist-heaps`). The tool can also be invoked without the wrapper, exposing its full set of cli options: 

```
# atlas-re --help
atlas - automated amortized complexity analysis

Usage: atlas-re [-s|--search PATH] (COMMAND | COMMAND | COMMAND)

  A static analysis tool for Automated (Expected) Amortised Complexity Analysis.

Available options:
  -s,--search PATH         Search for modules in PATH.
  -h,--help                Show this help text

Available commands:
  analyze                  Perform amortized resource analysis for the given
                           functions.
  eval                     Evaluate the given expression in the context of the
                           given module.
  bench                    Run the given benchmark.
```
The wrapper outputs the exact command it ran for each benchmark, so it should be easy to modify if needed.


# Building the tool yourself (Reusable)

The sources for our tool are hosted on Github under the GPL-3.0 License, at the following URL: https://github.com/autosard/atlas-re/ .

*Requirements*:
- To build the tool from scratch, a working Haskell toolchain is required (GHC (>= 9.6.7) + Cabal (>= 3.12.1.0)). The easiest way to set those tools up is the project [https://www.haskell.org/ghcup/](GHCUp), which provides a one-line install Linux, macOS, FreeBSD and WSL2. 
- A recent z3 (>= 4.8, <= 4.15.4) installed. z3 should be available in the package repositories for most distributions. Make sure that `libz3` is included.


## Offline build bundle (recommended)

Instead of cloning the repository, you can use the provided copy of the source repo. It provides a `cabal.project.freeze` file which freezes the dependencies to ensure reproduceability and in contrast to git repo it includes a tarball for the dependency `haskell-z3`. `haskell-z3` is packaged externally, because the version on Hackage is hopelessly out-of-date (see https://github.com/IagoAbal/haskell-z3/issues/96).

*Note*: 

## Build steps (offline)

Build the tool with cabal. This will pull the frozen version of our dependencies from Hackage and will therefore require internet access. 

```
cd source
cabal build 
```

## Run the tool

Once built, you can run it via Cabal:

```
cabal run -- atlas-re --search examples/leftist-heaps analyze --analysis-mode infer SkewHeap3over2
```

## (Optional) Install to PATH

If you want to install it globally:
```
cabal install --offline
```
