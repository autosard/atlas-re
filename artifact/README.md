# Artifact Submission for Atlas

This docker image provides a wrapper around the atlas tool for automated amortized analysis. The image contains a pre-built version of atlas together with a set of example benchmark programs for evaluation.

The provided archive can be imported to docker as follows.
```
docker load -i artifact.tar.gz
```

# Provided Examples
 
Run the following to obtain a list of the available benchmarks. 

```
docker run atlas-artifact list-examples
```

This will print the names of the bundled benchmark programs that can be used with the commands below.

# Usage

## Type Inference 

In this mode the tool type checks the annotation present in example file,
```
docker run atlas-artifact check <example>
```
- `<example>` should be replaced with the name of a program from list-examples.
- This process is typically fast (seconds to minutes).

## Type Inference

Alternatively the tool can infer the type (amortized bounds) from scratch. 

```
docker run atlas-artifact infer <example>
```
- This process is much more expensive computationally and can take hours on some benchmarks.
- Recommended for smaller benchmarks or if you want to test the inference capabilities in detail.
