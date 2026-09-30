# atlas-re

Research focused static program analysis tool for the automated amortized complexity analysis of data structures. It derives amortized cost bounds for data structure operations with an automated variant of the potential method based on type inference. Different template potentials are implemeted as modules.

## Build 

The project is build with cabal, so after running

```
cabal install
```

the binary should be symlinked to your PATH. 

```
atlas-re --help
```

### Working with newer z3 versions

Unfortunatly the `haskell-z3` project is currently poorly maintained and lastest official release happend almost 5 years ago. If your z3 installation is newer than version 4.8, the bindings will break. As a workaround you can clone the [repo](https://github.com/IagoAbal/haskell-z3), and use the main branch for version 4.11 (also works with newer versions e.g. 4.14). To achieve this follow those steps:

Clone `haskell-z3` repo.  
```
git clone https://github.com/IagoAbal/haskell-z3.git
```
Adapt dependency in `atlas-re.cabal`.
```
library:
	build-depends:
		...
		z3 ^>= 411
		...
```

Add a `cabal.project`, to tell cabal to also build `haskell-z3`. 
```
packages: .
          path/to/cloned/repo
```

## Examples

Example input programs can be found under `examples`. They are maintained in a seperate [repository](https://github.com/autosard/atlas-examples/tree/atlas-revisited). 

Checking the annotated cost bound of the splay operation on splay trees:

```
$ atlas-re --search examples analyze SearchTree.Splay.splay
Loading   SearchTree.Splay
Analyzing 1 function: splay
Proof found (2.6s).
Proof: file:///atlas-re/out/index.html
```

The derivation, the found bounds and, if no proof exists, the unsat core can be inspected in the linked HTML proof. Use `--analysis-mode infer` to infer cost bounds instead of checking the annotated ones, and `--output DIR` to write the proof somewhere else than `out`. The exit code is 0 if a proof was found and 1 otherwise.
