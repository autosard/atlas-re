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

Checking cost bound for the splay operation on splay trees:

```
atlas-re --search examples analyze --analysis-mode check-coeffs SplayTree.splay

Analyzing module SplayTree(splay).
Saved proof to "file:///atlas-re/out/index.html"
Potential functions:
	1/2 * rk(e1) + 1 (Tree Base )
	0 (List Base )

splay:
	3/2 * log(|t|)
```

Infering the cost bound for a purely functional queue:

```
$ atlas-re --search examples analyze --analysis-mode infer Queue

Saved proof to "file:///atlas-re/out/index.html"
Potential functions:
	0 (Tree Base )
	1/4 + |e2| (List Base )

head:
	1
moveToFront:
	0
snoc:
	2
tail:
	1
```
